"""Verify terminal server verdicts and byte equality of accepted proof sources."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
from prove2me_api import request

ROOT = Path(__file__).resolve().parents[1]
LABELS = ('HaarAmplification', 'CompactCosetUnboundedness', 'Main')


def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def main():
    public = ROOT / 'Prove2Me'
    public.mkdir(exist_ok=True)
    evidence = ROOT / 'docs/prove2me'
    proofs = []
    for label in LABELS:
        receipt = json.loads((evidence / (label + '.submission.json')).read_text(encoding='utf-8'))
        sid = receipt['submission_id']
        verdict = request('verify?submission_id=' + sid)
        save(evidence / (label + '.verdict.json'), verdict)
        assert verdict['status'] == 'ACCEPTED', label + ': ' + verdict['status']
        target = request('theorems/' + verdict['theorem_id'])
        save(evidence / (label + '.proved-target.json'), target)
        assert target['status'] == 'Proved'
        manifest = json.loads((ROOT / 'upload' / (label + '.manifest.json')).read_text(encoding='utf-8'))
        local = (ROOT / manifest['solution']).read_bytes()
        remote = request('submissions/' + sid + '/solution')['content'].encode('utf-8')
        digest = hashlib.sha256(local).hexdigest()
        assert remote == local
        assert digest == manifest['sha256'] == manifest['compiled_sha256']
        (public / (label + '.lean')).write_bytes(remote)
        manifest['release_solution'] = 'Prove2Me/' + label + '.lean'
        save(public / (label + '.manifest.json'), manifest)
        item = {'theorem_name': target['theorem_name'], 'theorem_id': target['theorem_id'],
                'submission_id': sid, 'status': verdict['status'], 'theorem_status': target['status'],
                'sha256': digest, 'bytes': len(local), 'readback_sha256_matches': True,
                'local_compile_seconds': manifest['local_compile_seconds'],
                'exact_target_type': manifest['exact_target_type'], 'axioms': manifest['axioms'],
                'release_solution': manifest['release_solution']}
        save(evidence / (label + '.source-readback.json'), item)
        proofs.append(item)
        print(json.dumps(item), flush=True)
    proposal = request('mission-proposals/64fe8c53-821d-476f-adfe-19f21c5d18f6')
    result = {'verified_at_utc': datetime.now(timezone.utc).isoformat(),
              'mathlib_rev': 'c5ea00351c28e24afc9f0f84379aa41082b1188f',
              'toolchain': 'leanprover/lean4:v4.30.0', 'proofs': proofs,
              'proposal': {key: proposal.get(key) for key in
                           ('id', 'name', 'mission_type', 'visibility', 'status', 'mission_id')}}
    save(ROOT / 'docs/prove2me-acceptance.json', result)


if __name__ == '__main__':
    main()
