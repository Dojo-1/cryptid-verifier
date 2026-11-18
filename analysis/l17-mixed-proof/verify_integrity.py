"""Verify the sealed continuation files and explicitly listed repository inputs."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def verify():
    manifest = json.loads((HERE/'integrity.json').read_text())
    if manifest.get('algorithm') != 'sha256' or not manifest.get('files'):
        raise ValueError('invalid integrity manifest')
    for name, digest in manifest['files'].items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError('missing or out-of-repository integrity input: '+name)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError('checksum mismatch: '+name)
    print('Integrity verified:', len(manifest['files']), 'files')


if __name__ == '__main__':
    verify()
