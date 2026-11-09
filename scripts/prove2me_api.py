"""Restricted-origin API access; secrets stay in memory and are never logged."""
from pathlib import Path
import json
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request

BASE = 'https://prove2.me/api/v1/'
VERSION = '0.13.9'
_token = None
_expires = 0

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise RuntimeError('API redirect refused')

_opener = urllib.request.build_opener(NoRedirect())

def request(path, body=None, authenticated=True, method=None):
    global _token, _expires
    url = BASE + path.lstrip('/')
    if not url.startswith(BASE) or urllib.parse.urlparse(url).netloc != 'prove2.me':
        raise ValueError('Refusing a non-Prove2Me API destination')
    if authenticated and (_token is None or _expires < time.time() + 90):
        creds = json.loads((Path.home() / 'prove2me_workspace/credentials.json').read_text(encoding='utf-8'))
        refreshed = request('agent/refresh', {'api_key': creds['api_key']}, authenticated=False)
        if refreshed.get('version') != VERSION:
            raise RuntimeError('Platform version changed; re-read current instructions')
        _token = refreshed['access_token']
        _expires = time.time() + 3500
    headers = {'Accept': 'application/json', 'User-Agent': 'ModNullUniversality-local-draft'}
    if authenticated:
        headers['Authorization'] = 'Bearer ' + _token
    if body is not None:
        headers['Content-Type'] = 'application/json'
    data = json.dumps(body, ensure_ascii=False).encode('utf-8') if body is not None else None
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with _opener.open(req, timeout=60) as response:
            content = response.read()
            return json.loads(content) if content else None
    except urllib.error.HTTPError as error:
        raise RuntimeError(f'Prove2Me HTTP {error.code} for {path}') from None


def submit_proof(theorem_id, proof, explanation):
    """Upload a proof to the sole allowed origin, with redirects disabled."""
    uuid.UUID(theorem_id)
    request('theorems/' + theorem_id)  # refresh and version-check before upload
    boundary = 'Prove2Me' + uuid.uuid4().hex
    parts = []
    for name,value in [('theorem_id',theorem_id),('proof_type','prove'),('explanation',explanation)]:
        parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n').encode('utf-8'))
    parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode())
    parts.append(proof.encode('utf-8'))
    parts.append(f'\r\n--{boundary}--\r\n'.encode())
    req = urllib.request.Request(BASE+'verify', data=b''.join(parts), method='POST', headers={
        'Authorization':'Bearer '+_token, 'Accept':'application/json',
        'Content-Type':'multipart/form-data; boundary='+boundary})
    with _opener.open(req, timeout=60) as response:
        return json.loads(response.read())
