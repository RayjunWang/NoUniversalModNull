"""Create a source-only GitHub archive from an explicit credential-free allowlist."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT.parent / 'modnull-universality-lean-github.zip'
DIRECTORIES = ('Definitions', 'NoBorelUpperBound', 'ModNullProof', 'Solutions', 'Prove2Me')
FILES = (
    'README.md', 'LICENSE', 'NOTICE.md', '.gitignore', '.gitattributes', '.github/workflows/lean.yml',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'ModNullUniversalityProof.lean',
    'scripts/audit.py', 'scripts/audit_axioms.lean', 'scripts/prepare_upload.py',
    'scripts/extract_module_info.lean', 'scripts/package_release.py',
    'scripts/prove2me_api.py', 'scripts/submit_checked.py', 'scripts/verify_readback.py',
    'docs/ModNullUniversality.tex', 'docs/source-bindings.json',
    'docs/dependency-integrity.json', 'docs/proof-outline.md',
    'docs/verification.md', 'docs/review-compact-transfer.md',
    'docs/prove2me-targets.json', 'docs/prove2me-acceptance.json',
    'docs/explanation-main.md', 'docs/explanation-compact.md', 'docs/explanation-haar.md',
)


def main():
    acceptance = json.loads((ROOT / 'docs/prove2me-acceptance.json').read_text(encoding='utf-8'))
    assert len(acceptance['proofs']) == 3
    assert all(p['status'] == 'ACCEPTED' and p['theorem_status'] == 'Proved'
               and p['readback_sha256_matches'] for p in acceptance['proofs'])
    paths = [ROOT / name for name in FILES]
    paths.extend(p for directory in DIRECTORIES for p in sorted((ROOT / directory).glob('*.lean')))
    paths.extend(sorted((ROOT / 'Prove2Me').glob('*.json')))
    paths.extend(sorted((ROOT / 'Prove2Me').glob('*.md')))
    paths.extend(sorted((ROOT / 'docs/prove2me').glob('*.json')))
    paths = sorted(set(paths))
    assert all(p.is_file() for p in paths), 'A required release file is missing'
    manuscript = ROOT / 'docs/ModNullUniversality.tex'
    bindings = json.loads((ROOT / 'docs/source-bindings.json').read_text(encoding='utf-8'))
    assert hashlib.sha256(manuscript.read_bytes()).hexdigest() == bindings['revised_manuscript_sha256']
    manifest = {'format': 1, 'files': [
        {'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size,
         'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]}
    payload = (json.dumps(manifest, indent=2) + '\n').encode('utf-8')
    (ROOT / 'docs/source-manifest.json').write_bytes(payload)
    with zipfile.ZipFile(DEST, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for path in paths:
            archive.write(path, 'modnull-universality-lean/' + path.relative_to(ROOT).as_posix())
        archive.writestr('modnull-universality-lean/docs/source-manifest.json', payload)
    digest = hashlib.sha256(DEST.read_bytes()).hexdigest()
    DEST.with_suffix(DEST.suffix + '.sha256').write_text(digest + '  ' + DEST.name + '\n', encoding='utf-8')
    print(json.dumps({'archive': str(DEST), 'files': len(paths) + 1,
                      'bytes': DEST.stat().st_size, 'sha256': digest}))


if __name__ == '__main__':
    main()
