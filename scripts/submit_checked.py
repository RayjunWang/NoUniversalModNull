"""Submit an exact, locally audited bundle; resume by polling its saved receipt."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
from prove2me_api import request, submit_proof

ROOT = Path(__file__).resolve().parents[1]
LABELS = {'haar': 'HaarAmplification', 'compact': 'CompactCosetUnboundedness', 'main': 'Main'}


def save(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target', choices=LABELS)
    parser.add_argument('--poll', action='store_true')
    args = parser.parse_args()
    label = LABELS[args.target]
    evidence = ROOT / 'docs' / 'prove2me'
    evidence.mkdir(exist_ok=True)
    receipt = evidence / (label + '.submission.json')
    if receipt.exists():
        submission = json.loads(receipt.read_text(encoding='utf-8'))
        verdict = request('verify?submission_id=' + submission['submission_id'])
        save(evidence / (label + '.verdict.json'), verdict)
        print(json.dumps(verdict, ensure_ascii=True), flush=True)
        if verdict['status'] == 'ACCEPTED':
            theorem = request('theorems/' + verdict['theorem_id'])
            save(evidence / (label + '.proved-target.json'), theorem)
            assert theorem['status'] == 'Proved'
        return
    assert not args.poll, 'No recorded submission to poll'
    manifest = json.loads((ROOT / 'upload' / (label + '.manifest.json')).read_text(encoding='utf-8'))
    path = ROOT / manifest['solution']
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert manifest['exact_target_type'] and manifest['standard_axioms_only']
    assert digest == manifest['sha256'] == manifest['compiled_sha256']
    assert set(manifest['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    target = request('theorems/' + manifest['target_id'])
    assert target['formal_statement'] == manifest['published_formal_statement']
    assert target['preamble'] == manifest['published_preamble']
    assert target['mathlib_rev'] == manifest['mathlib_rev'] == 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
    for module in manifest['modules']:
        actual = hashlib.sha256((ROOT / module['path']).read_bytes()).hexdigest()
        assert actual == module['source_sha256'], 'Source changed since bundle compilation'
    explanation = (ROOT / 'docs' / ('explanation-' + args.target + '.md')).read_text(encoding='utf-8')
    attempt = evidence / (label + '.attempt.json')
    assert not attempt.exists(), 'An upload has an unknown outcome; reconcile before retrying'
    save(attempt, {'target_id': manifest['target_id'], 'sha256': digest,
                  'started_at': datetime.now(timezone.utc).isoformat()})
    result = submit_proof(manifest['target_id'], path.read_bytes().decode('utf-8'), explanation)
    save(receipt, result)
    print(json.dumps(result, ensure_ascii=True), flush=True)


if __name__ == '__main__':
    main()
