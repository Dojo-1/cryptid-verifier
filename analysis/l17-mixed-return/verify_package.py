from pathlib import Path
import hashlib,json
def main():
    here=Path(__file__).resolve().parent;root=here.parent;rows=json.loads((here/'integrity.json').read_text())['files'];errors=[]
    for name,row in rows.items():
        p=root/name
        if not p.is_file():errors.append([name,'missing']);continue
        b=p.read_bytes()
        if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:errors.append([name,'changed'])
    print(json.dumps(dict(passed=not errors,checked_files=len(rows),errors=errors),indent=2))
    if errors:raise SystemExit(1)
if __name__=='__main__':main()
