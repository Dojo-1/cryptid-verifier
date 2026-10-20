"""Literal request/response transport for the separate C++ comparator."""
from __future__ import annotations
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import os

_remaining=None
_ledger=None


def set_budget(remaining,ledger=None):
    global _remaining,_ledger
    if remaining<0:raise ValueError('Prior work already exceeds the fixed budget')
    _remaining=remaining
    _ledger=Path(ledger) if ledger else None


def reserve(requests):
    maximum=sum(row['limit'] for row in requests)
    if _remaining is not None and maximum>_remaining:raise ValueError('Fresh requests exceed the remaining raw-transition budget')


def encode(records):
    rows=[]
    for row in records:
        cells=row['ones']
        header=[row['id'],row['machine'],row['q'],row['head'],row['limit'],int(row.get('trace',False)),len(cells)]
        rows.append(' '.join(map(str,header+cells)))
    return ('\n'.join(rows)+'\n').encode()


def execute(binary,requests,path=None):
    global _remaining
    payload=encode(requests)
    request_hash=hashlib.sha256(payload).hexdigest()
    metadata_path=Path(str(path)+'.meta.json') if path else None
    if path and metadata_path.exists() and Path(path).exists():
        metadata=json.loads(metadata_path.read_text())
        with gzip.open(path,'rb') as f:stored=f.read()
        if metadata['request_sha256']==request_hash and metadata['response_sha256']==hashlib.sha256(stored).hexdigest() and metadata['binary_sha256']==hashlib.sha256(Path(binary).read_bytes()).hexdigest():
            data=[json.loads(line) for line in stored.splitlines()]
            if len(data)==len(requests) and all(out['id']==req['id'] for out,req in zip(data,requests)):
                return data,dict(metadata,cache_reused=True,executed_defined_transitions=0)
    reserve(requests)
    result=subprocess.run([str(Path(binary).resolve())],input=payload,capture_output=True,check=False,timeout=120)
    if result.returncode:raise RuntimeError(result.stderr.decode())
    data=[json.loads(line) for line in result.stdout.splitlines()]
    if len(data)!=len(requests):raise RuntimeError('Response count mismatch')
    if any(out['id']!=req['id'] for out,req in zip(data,requests)):raise RuntimeError('Response identity mismatch')
    total=sum(x['steps'] for x in data)
    if _remaining is not None:_remaining-=total
    if _ledger is not None:
        charge={'executed_defined_transitions':total,'request_sha256':request_hash,
                'response_sha256':hashlib.sha256(result.stdout).hexdigest(),
                'binary_sha256':hashlib.sha256(Path(binary).read_bytes()).hexdigest()}
        with _ledger.open('a') as ledger:
            ledger.write(json.dumps(charge,sort_keys=True)+'\n');ledger.flush();os.fsync(ledger.fileno())
    if path:
        with open(path,'wb') as f:
            with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as compressed:compressed.write(result.stdout)
    metadata={'requests':len(requests),'defined_transitions':total,'executed_defined_transitions':total,'cache_reused':False,
        'request_sha256':request_hash,'response_sha256':hashlib.sha256(result.stdout).hexdigest(),
        'binary_sha256':hashlib.sha256(Path(binary).read_bytes()).hexdigest(),'stderr':result.stderr.decode()}
    if path:metadata_path.write_text(json.dumps(metadata,indent=2)+'\n')
    return data,metadata


def transform_machine(machine,permutation=None,reflect=False):
    rows=machine.split('_');result=['']*6
    permutation=list(range(6)) if permutation is None else permutation
    for q,row in enumerate(rows):
        tokens=[]
        for b in range(2):
            token=row[3*b:3*b+3]
            if token!='---':
                direction=('L' if token[1]=='R' else 'R') if reflect else token[1]
                token=token[0]+direction+chr(65+permutation[ord(token[2])-65])
            tokens.append(token)
        result[permutation[q]]=''.join(tokens)
    return '_'.join(result)
