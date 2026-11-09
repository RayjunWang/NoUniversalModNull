#!/usr/bin/env python3
"""Bundle COMPLETE local Lean modules, then check the exact published target.

Only parsed import-command byte spans are replaced. Complete module bodies,
including every declaration and proof, are retained verbatim. Anonymous sections
isolate module-local commands; Lean's frontend supplies the number of EOF scopes
to close. Definitions already published on Prove2Me remain external imports.

Examples:
  python scripts/prepare_upload.py all --target haar
  python scripts/prepare_upload.py all --target compact
  python scripts/prepare_upload.py all --target main

The script uses no network, credentials, or external application writes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parents[1]
UPLOAD = ROOT / "upload"
TARGETS = {
    "haar": ("HaarAmplification", "Solutions.HaarAmplification"),
    "compact": ("CompactCosetUnboundedness", "Solutions.CompactCosetUnboundedness"),
    "main": ("Main", "Solutions.Main"),
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_path(module: str) -> Path:
    return ROOT.joinpath(*module.split(".")).with_suffix(".lean")


def run_lean(args: list[str], log: Path) -> tuple[str, float]:
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("lake executable is not on PATH")
    start = time.monotonic()
    result = subprocess.run([lake, "env", "lean", *args], cwd=ROOT, capture_output=True)
    log.write_bytes(result.stdout)
    log.with_suffix(log.suffix + ".stderr").write_bytes(result.stderr)
    if result.returncode:
        raise RuntimeError(f"Lean exited {result.returncode}; see {log.relative_to(ROOT)}")
    return (result.stdout + b"\n" + result.stderr).decode("utf-8", errors="replace"), time.monotonic() - start


def oracle(paths: list[Path], log: Path, *, header_only: bool) -> dict[str, dict]:
    if not header_only and len(paths) > 1:
        # Lean's import initializer state is process-wide. Each elaborated
        # module gets a fresh process, matching a normal `lean File.lean` call.
        def extract_one(path: Path) -> dict[str, dict]:
            name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
            return oracle([path], log.with_name(log.stem + "." + name + log.suffix),
                          header_only=False)
        records = {}
        with ThreadPoolExecutor(max_workers=2) as executor:
            for result in executor.map(extract_one, paths):
                records.update(result)
        log.write_text("\n".join(json.dumps(v) for v in records.values()) + "\n", encoding="utf-8")
        log.with_suffix(log.suffix + ".stderr").write_text(
            "Records generated successfully in isolated processes; see individual stderr logs.\n",
            encoding="utf-8")
        return records
    cache_path = None
    if not header_only and len(paths) == 1:
        path = paths[0]
        digest = sha(path.read_bytes())
        cache_dir = UPLOAD / "module-cache"
        cache_dir.mkdir(exist_ok=True)
        cache_path = cache_dir / (digest + ".json")
        if cache_path.exists():
            cached = json.loads(cache_path.read_text(encoding="utf-8"))
            if cached["file"] == path.relative_to(ROOT).as_posix():
                name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
                log.write_text(json.dumps(cached) + "\n", encoding="utf-8")
                return {name: cached}
    before = {path: sha(path.read_bytes()) for path in paths}
    args = ["--run", "scripts/extract_module_info.lean"]
    if header_only:
        args.append("--header-only")
    args.extend(path.relative_to(ROOT).as_posix() for path in paths)
    output, _ = run_lean(args, log)
    records = {}
    for line in output.splitlines():
        if line.startswith("{"):
            record = json.loads(line)
            if "import_spans" in record:
                name = ".".join(Path(record["file"]).with_suffix("").parts)
                records[name] = record
    for path, digest in before.items():
        if sha(path.read_bytes()) != digest:
            raise RuntimeError(f"Source changed while Lean examined it: {path}")
    if len(records) != len(paths):
        raise RuntimeError("Lean did not return exactly one record per input module")
    if cache_path is not None:
        cache_path.write_text(json.dumps(next(iter(records.values()))) + "\n", encoding="utf-8")
    return records


def signature(target: dict) -> str:
    statement = target["formal_statement"].strip()
    prefix = "theorem " + target["theorem_name"]
    suffix = ":= by sorry"
    if not statement.startswith(prefix) or not statement.endswith(suffix):
        raise RuntimeError("Published statement format changed; inspect the authoritative target")
    return statement[len(prefix):-len(suffix)]


def original_import_spans(source: bytes, spans: list[dict]) -> list[dict]:
    # Lean Parser.mkInputContext universally normalizes CRLF to LF before parsing.
    # Map its UTF-8 byte offsets back to the original, preserving source newlines.
    if b"\r\n" not in source:
        return spans
    offsets, position = [0], 0
    while position < len(source):
        position += 2 if source[position:position + 2] == b"\r\n" else 1
        offsets.append(position)
    return [{"start": offsets[s["start"]], "stop": offsets[s["stop"]]} for s in spans]


def retained_body(source: bytes, spans: list[dict]) -> bytes:
    # Mask only Lean-parsed import commands; preserve all other original bytes.
    result = bytearray(source)
    previous_stop = 0
    for span in spans:
        start, stop = span["start"], span["stop"]
        if not previous_stop <= start < stop <= len(source):
            raise RuntimeError("Invalid or overlapping import span from Lean")
        command = source[start:stop].decode("utf-8")
        if not command.startswith("import "):
            raise RuntimeError("Unexpected import syntax; inspect Lean's header facts")
        for i in range(start, stop):
            if result[i] not in (10, 13):
                result[i] = 32
        previous_stop = stop
    return bytes(result)


def prepare(key: str, root_module: str, label: str, target: dict) -> Path:
    UPLOAD.mkdir(exist_ok=True)
    sources = sorted(path for folder in ("Definitions", "NoBorelUpperBound", "ModNullProof", "Solutions")
                     for path in (ROOT / folder).rglob("*.lean"))
    source_digests = {path: sha(path.read_bytes()) for path in sources}
    headers = oracle(sources, UPLOAD / f"{label}.headers.jsonl", header_only=True)
    ordered, external, seen, active = [], set(), set(), []

    def visit(module: str) -> None:
        if module in active:
            raise RuntimeError("Local import cycle: " + " -> ".join(active + [module]))
        if module in seen:
            return
        seen.add(module)
        if module.startswith("Definitions.") or module.startswith("Mathlib"):
            external.add(module)
            return
        if module not in headers:
            raise RuntimeError(f"Unsupported external or missing local module: {module}")
        active.append(module)
        for dep in headers[module]["imports"]:
            visit(dep)
        active.pop()
        ordered.append(module)

    visit(root_module)
    paths = [module_path(module) for module in ordered]
    scopes = oracle(paths, UPLOAD / f"{label}.module-info.jsonl", header_only=False)
    chunks = [("\n".join("import " + module for module in sorted(external)) + "\n").encode()]
    records = []
    for module, path in zip(ordered, paths):
        source = path.read_bytes()
        if sha(source) != source_digests[path]:
            raise RuntimeError("Source changed during bundle generation: " + module)
        if source.startswith(b"\xef\xbb\xbf"):
            raise RuntimeError("UTF-8 BOM needs an explicit offset strategy: " + str(path))
        record = scopes[module]
        if record["imports"] != headers[module]["imports"]:
            raise RuntimeError("Imports changed during bundle preparation: " + module)
        depth = record["scope_depth"]
        if depth < 1:
            raise RuntimeError("Lean did not report a valid final scope depth")
        spans = original_import_spans(source, record["import_spans"])
        body = retained_body(source, spans)
        chunks.extend([
            ("\n-- BEGIN COMPLETE MODULE " + module + "\nsection\n").encode(),
            body,
            b"\n" + b"end\n" * depth,
            ("-- END COMPLETE MODULE " + module + "\n").encode(),
        ])
        records.append({"module": module, "path": path.relative_to(ROOT).as_posix(),
                        "source_sha256": sha(source), "source_bytes": len(source),
                        "retained_body_sha256": sha(body), "scope_depth": depth,
                        "import_spans": spans, "parser_import_spans": record["import_spans"]})
    sig = signature(target)
    name = target["theorem_name"]
    chunks.append(("\nset_option autoImplicit false\n\ntheorem solution" + sig +
                   ":= by\n  first\n  | exact @" + name +
                   "\n  | apply @" + name + " <;> assumption\n\n#print axioms solution\n").encode())
    content = b"".join(chunks)
    destination = UPLOAD / f"{label}.lean"
    destination.write_bytes(content)
    manifest = {
        "target_key": key, "target_id": target["theorem_id"], "target_name": name,
        "root_module": root_module, "mathlib_rev": target["mathlib_rev"],
        "solution": destination.relative_to(ROOT).as_posix(),
        "sha256": sha(content), "bytes": len(content), "modules": records,
        "imports": sorted(external), "published_preamble": target["preamble"],
        "published_formal_statement": target["formal_statement"],
        "only_source_edits": "Lean-parsed import spans replaced by spaces; complete bodies retained",
    }
    (UPLOAD / f"{label}.manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"label": label, "modules": len(ordered), "bytes": len(content),
                      "sha256": manifest["sha256"], "prepared": True}), flush=True)
    return destination


def compile_bundle(label: str, target: dict) -> None:
    path = UPLOAD / f"{label}.lean"
    manifest_path = UPLOAD / f"{label}.manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    digest = sha(path.read_bytes())
    if digest != manifest["sha256"]:
        raise RuntimeError("Bundle bytes changed after preparation")
    olean = ROOT / ".lake" / "build" / "lib" / "lean" / "upload" / f"{label}.olean"
    olean.parent.mkdir(parents=True, exist_ok=True)
    output, elapsed = run_lean(["-o", str(olean), path.relative_to(ROOT).as_posix()],
                               UPLOAD / f"{label}.local-check.log")
    reports = re.findall(r"'solution' depends on axioms:\s*\[([^\]]*)\]", output)
    if len(reports) != 1:
        raise RuntimeError("Missing or ambiguous solution axiom report")
    actual = {item.strip() for item in reports[0].split(",") if item.strip()}
    if not actual <= ALLOWED_AXIOMS:
        raise RuntimeError("Unexpected solution axioms: " + repr(actual - ALLOWED_AXIOMS))
    # This second declaration copies the authoritative statement exactly except
    # for its binding name and proof. Its proof contains no reference placeholder.
    check = ("import upload." + label + "\nimport Lean\n\n" +
             target["preamble"] + "\ntheorem publishedTargetReference" + signature(target) +
             ":= by\n  first\n  | exact @solution\n  | apply @solution <;> assumption\n\n" +
             "run_meta do\n  let actual ← Lean.getConstInfo `solution\n" +
             "  let expected ← Lean.getConstInfo `publishedTargetReference\n" +
             "  unless (← Lean.Meta.isDefEq actual.type expected.type) do\n" +
             '    throwError "Solution type differs from the exact published target"\n' +
             '  Lean.logInfo "Exact published target type matched by Lean"\n')
    check_path = UPLOAD / f"{label}.typecheck.lean"
    check_path.write_bytes(check.encode())
    check_output, check_elapsed = run_lean([check_path.relative_to(ROOT).as_posix()],
                                          UPLOAD / f"{label}.target-type-check.log")
    if "Exact published target type matched by Lean" not in check_output:
        raise RuntimeError("Lean did not confirm exact target-type equality")
    if sha(path.read_bytes()) != digest:
        raise RuntimeError("Bundle bytes changed during compilation")
    manifest.update({"local_compile_seconds": round(elapsed, 2),
                     "typecheck_seconds": round(check_elapsed, 2),
                     "exact_target_type": True, "standard_axioms_only": True,
                     "axioms": sorted(actual), "compiled_sha256": digest})
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"label": label, "compiled": True, "seconds": round(elapsed, 2),
                      "sha256": digest, "exact_target_type": True, "axioms": sorted(actual)}), flush=True)


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "compile", "all"))
    parser.add_argument("--target", required=True, choices=TARGETS)
    parser.add_argument("--root-module")
    parser.add_argument("--label")
    parser.add_argument("--targets", type=Path, default=ROOT / "docs" / "prove2me-targets.json")
    args = parser.parse_args()
    label, root_module = TARGETS[args.target]
    label, root_module = args.label or label, args.root_module or root_module
    target = json.loads(args.targets.read_text(encoding="utf-8"))["theorems"][args.target]
    if args.action in ("prepare", "all"):
        prepare(args.target, root_module, label, target)
    if args.action in ("compile", "all"):
        compile_bundle(label, target)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
