"""Check the shipped file hashes before regenerating evidence."""
from pathlib import Path
import hashlib
import json


def main():
    here = Path(__file__).resolve().parent
    root = here.parent.parent
    rows = json.loads((here/'integrity.json').read_text())['files']
    errors = []
    for name, row in rows.items():
        path = root/name
        if not path.resolve().is_relative_to(root) or not path.is_file():
            errors.append([name, 'missing or outside repository'])
            continue
        data = path.read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            errors.append([name, 'changed'])
    print(json.dumps(dict(passed=not errors, checked_files=len(rows), errors=errors), indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
