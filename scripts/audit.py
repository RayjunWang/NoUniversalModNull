#!/usr/bin/env python3
"""Audit delivered proof sources, fixed definitions, exact statement, and axioms."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TOOLCHAIN = "leanprover/lean4:v4.30.0"
DEFINITION_HASHES = {'Def_ModNullCompact20261109.lean': '73d1414aa1463f6354a6906fdcc2cfc02cf73d60bdd16d6a2338ff7f970ecd4f', 'Def_ModNullCore20261109.lean': '69eb631ab3e37a00ae1a37cd21ea7e7f418935c0383738eab63950502de8c822', 'Def_NoBorelUpperBound20261101.lean': 'b975725aad231fd83ce6e507a6088331c1deee4f73bd9a32fef25292164414ed', 'Def_NoBorelUpperBoundTransfer20261101.lean': '70350cdb2c3d623068d22cdbbdf3c706b4535dc39fc1c35e0ca21bc339f207fb', 'Def_NoUniversalFSigma261031052.lean': '17689fb14e3cc735b114813507089ac8212369f83a44b4c57abe978563d14b67'}

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_THEOREMS = {
    "ModNullUniversality.theorem1_1",
    "ModNullUniversality.compact_coset_unboundedness",
    "ModNullUniversality.haar_amplification",
    "ModNullUniversality.CompactTensor.image_coordinates_difference_ksigma",
    "ModNullUniversality.CompactTensor.compactFamily_lowComplexity",
    "ModNullUniversality.CompactTensor.compactFamily_unbounded",
    "ModNullUniversality.AEPower.exists_measurable_code",
}


def lean_code(text: str) -> str:
    """Mask nested Lean comments and strings while preserving line numbers."""
    result = list(text)
    index = depth = 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                result[index:index + 2] = "  "
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                result[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    result[index] = " "
                index += 1
        elif text.startswith("/-", index):
            result[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                result[index] = " "
                index += 1
        elif text[index] == '"':
            result[index] = " "
            index += 1
            closed = False
            while index < len(text):
                char = text[index]
                if char != "\n":
                    result[index] = " "
                index += 1
                if char == "\\" and index < len(text):
                    if text[index] != "\n":
                        result[index] = " "
                    index += 1
                elif char == '"':
                    closed = True
                    break
            if not closed:
                raise ValueError("unterminated string")
        else:
            index += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(result)


def source_files() -> list[Path]:
    # Deliberate allowlist: remote reference metadata may contain target stubs.
    # It, scratch experiments, .lake, and other project data are not proof inputs.
    files = [ROOT / "ModNullUniversalityProof.lean", ROOT / "scripts/audit_axioms.lean"]
    for folder in ("Definitions", "NoBorelUpperBound", "ModNullProof", "Solutions"):
        files.extend(sorted((ROOT / folder).rglob("*.lean")))
    return files


def check_sources() -> list[str]:
    errors: list[str] = []
    for name, expected in DEFINITION_HASHES.items():
        content = (ROOT / "Definitions" / name).read_bytes()
        if hashlib.sha256(content).hexdigest() != expected:
            errors.append(f"Definitions/{name}: fixed mission definitions changed")
    modules: dict[str, str] = {}
    forbidden = re.compile(
        r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by|extern)\b"
        r"|debug\.skipKernelTC")
    for path in source_files():
        relative = path.relative_to(ROOT)
        try:
            code = lean_code(path.read_text(encoding="utf-8-sig"))
        except (OSError, ValueError) as error:
            errors.append(f"{relative}: {error}")
            continue
        module = ".".join(relative.with_suffix("").parts)
        modules[module] = code
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: forbidden proof construct {match.group()}")
    graph: dict[str, list[str]] = {}
    for module, code in modules.items():
        imported = re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", code, re.M)
        graph[module] = [name for name in imported if name in modules]
        for name in imported:
            if name.startswith(("NoBorelUpperBound.", "Definitions.", "ModNullProof.", "Solutions.")) and name not in modules:
                errors.append(f"{module}: missing delivered local dependency {name}")
    active: list[str] = []
    done: set[str] = set()

    def visit(module: str) -> None:
        if module in active:
            errors.append("local import cycle: " + " -> ".join(active + [module]))
            return
        if module in done:
            return
        active.append(module)
        for dependency in graph[module]:
            visit(dependency)
        active.pop()
        done.add(module)

    for module in graph:
        visit(module)
    if (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip() != TOOLCHAIN:
        errors.append("lean-toolchain differs from the supported Lean revision")
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8-sig")
    if not re.search(r'require\s+mathlib\s+from\s+git\s+"https://github\.com/leanprover-community/mathlib4"\s*@\s*"'
                     + MATHLIB_REV + r'"', lakefile):
        errors.append("lakefile.lean does not pin the supported Mathlib revision")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    mathlib = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
    if mathlib is None or mathlib.get("rev") != MATHLIB_REV:
        errors.append("lake-manifest.json Mathlib revision differs from the supported revision")
    return errors


def check_axiom_log(log: str) -> list[str]:
    errors: list[str] = []
    seen: set[str] = set()
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        seen.add(name)
        actual = {item.strip() for item in axioms.split(",") if item.strip()}
        unexpected = actual - ALLOWED_AXIOMS
        if unexpected:
            errors.append(f"{name}: unexpected axioms: {', '.join(sorted(unexpected))}")
    seen.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
    for name in sorted(REQUIRED_THEOREMS - seen):
        errors.append(f"missing kernel axiom report for {name}")
    if re.search(r"\b(?:sorryAx|ofReduceBool)\b", log):
        errors.append("axiom report contains a proof hole or unchecked evaluation axiom")
    return errors


def main() -> int:
    # Lean diagnostics contain Unicode; Windows consoles may otherwise default to GBK.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true",
                        help="scan sources without claiming theorem completion")
    args = parser.parse_args()
    try:
        errors = check_sources()
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors = [f"source integrity check could not complete: {error}"]
    if not args.source_only:
        lake = shutil.which("lake")
        if not lake:
            errors.append("lake executable not found on PATH")
        else:
            try:
                # Rebuild the import closure so stale oleans cannot certify edited sources.
                build = subprocess.run([lake, "build"], cwd=ROOT,
                    text=True, encoding="utf-8", errors="replace", capture_output=True)
                print(build.stdout + build.stderr, end="")
                if build.returncode:
                    errors.append(f"Lean proof build failed with exit code {build.returncode}")
                else:
                    process = subprocess.run([lake, "env", "lean", "scripts/audit_axioms.lean"],
                        cwd=ROOT, text=True, encoding="utf-8", errors="replace", capture_output=True)
                    log = process.stdout + process.stderr
                    print(log, end="")
                    if process.returncode:
                        errors.append(f"Lean statement/axiom audit failed with exit code {process.returncode}")
                    errors.extend(check_axiom_log(log))
            except OSError as error:
                errors.append(f"could not execute Lean axiom audit: {error}")
    if errors:
        for error in errors:
            print("ERROR:", error, file=sys.stderr)
        return 1
    print("Source integrity checks passed; theorem audit not run." if args.source_only else
          "Source integrity, exact theorem statement, and kernel axiom audits passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
