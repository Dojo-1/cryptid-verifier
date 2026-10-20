"""New literal C++ checks, read windows, and in-memory ACAF mutations."""
from __future__ import annotations
import gzip,hashlib,json,random,subprocess
from extend import HERE,Word,encoded
from nesting import U,T,nest,a_nest
from specification import Claims,expand,equal_words,agrees
from backend import execute,set_budget,encode


def endpoints(claims):
    rows=[];rng=random.Random(173118)
    params=[(a,n,v) for a in (7,8,9,12,31,127) for n in (0,1,2,3,7,15) for v in ('','1','001101')]
    params += [(rng.randint(7,10000),rng.randint(0,150),''.join(rng.choice('01') for _ in range(rng.randrange(33)))) for _ in range(96)]
    for i,(a,n,v) in enumerate(params):
        claim=claims.instantiate('NEST',{'a':a,'n':n},v)
        actor=nest(a,n,Word.literal(v))
        assert equal_words(actor['word'].parts,claim['target'])
        assert (actor['steps'],actor['shift'])==(claim['steps'],claim['shift'])
        source=expand(claim['source']);target=expand(claim['target'])
        rows.append({'id':i,'kind':'NEST','parameters':{'a':a,'n':n},'suffix':v,
            'source':source,'lo':0,'q':2,'head':0,'steps':claim['steps'],
            'target':target,'target_lo':claim['shift'],'target_q':2,'target_head':claim['shift']})
    for i in range(64):
        n=rng.randint(0,150);v=''.join(rng.choice('01') for _ in range(rng.randrange(33)))
        claim=claims.instantiate('A_NEST',{'n':n},v);actor=a_nest(n,Word.literal(v))
        assert equal_words(actor['word'].parts,claim['target'])
        assert (actor['steps'],actor['shift'])==(claim['steps'],claim['shift'])
        rows.append({'id':len(rows),'kind':'A_NEST','parameters':{'n':n},'suffix':v,
            'source':expand(claim['source']),'lo':-16,'q':0,'head':0,'steps':claim['steps'],
            'target':expand(claim['target']),'target_lo':-16,'target_q':2,'target_head':-16})
    return rows


def kernels():
    # All claims are finite intervals; random exteriors must remain unchanged.
    return [
      {'name':'K7','lo':-4,'input':'1010101','q':0,'head':0,'steps':7,'target':'0'+'01'*3,'target_q':0,'target_head':-3},
      {'name':'K27','lo':-4,'input':'1010'+'1'+U,'q':0,'head':0,'steps':27,'target':'0'+'10'*10+'1','target_q':0,'target_head':17},
      {'name':'K41','lo':-16,'input':'10'*6+'1'*7,'q':2,'head':-5,'steps':41,'target':'11'+T,'target_q':2,'target_head':-16},
      {'name':'K60','lo':-16,'input':'10'*8+'100','q':0,'head':0,'steps':60,'target':'11'+T,'target_q':2,'target_head':-16},
    ]+[
      {'name':'AK'+str(n),'lo':-16,'input':'10'*8+'1'+U*n+'00','q':0,'head':0,'steps':60+74*n,
       'target':'11'+T*(n+1),'target_q':2,'target_head':-16} for n in range(6)]


def requests_and_wants(rows):
    machine=Claims(HERE/'nesting-claims.json').machine
    requests=[];wants=[]
    for row in rows:
        req={'id':row['id'],'machine':machine,'q':row['q'],'head':row['head'],'limit':row['steps'],
             'ones':[row['lo']+i for i,b in enumerate(row['source']) if b=='1'],'trace':False}
        wanted={'q':row['target_q'],'head':row['target_head'],'steps':row['steps'],'halted':False,
                'ones':[row['target_lo']+i for i,b in enumerate(row['target']) if b=='1']}
        requests.append(req);wants.append(wanted)
    return requests,wants


def mutation_checks(rows,actuals):
    corpus=[(row,out) for row,out in zip(rows,actuals) if row['kind']=='NEST']
    def wrong(a,n,v,kind):
        lead=2*a-12;copies=n+1;tail=T;steps=4*a+74*n+50;shift=-2
        if kind=='leading-count':lead+=2
        if kind=='missing-layer':copies-=1
        if kind=='wrong-tail':tail='01'*7+'1'
        if kind=='reverse-tail':tail=T[::-1]
        if kind=='time-slope':steps-=2*n
        if kind=='time-intercept':steps-=2
        if kind=='head-shift':shift=-1
        if kind=='drop-context':v=''
        bits='1'*lead+tail*copies+v
        return {'q':2,'head':shift,'steps':steps,'halted':False,'ones':[shift+i for i,b in enumerate(bits) if b=='1']}
    results=[]
    for kind in ('leading-count','missing-layer','wrong-tail','reverse-tail','time-slope','time-intercept','head-shift','drop-context'):
        witness=None
        for row,out in corpus:
            pred=wrong(**row['parameters'],v=row['suffix'],kind=kind)
            if not agrees(out,pred):witness={'case':row['id'],'parameters':row['parameters'],'suffix':row['suffix']};break
        assert witness is not None,kind
        results.append({'mutant':kind,'killed':True,'witness':witness,'mechanism':'Mismatch against stored literal C++ endpoint'})
    for kind,args in [('lower-guard',(6,0)),('negative-depth',(7,-1)),('boolean-a',(True,0)),('boolean-depth',(7,True))]:
        try:nest(*args)
        except ValueError:pass
        else:raise AssertionError(('baseline accepted invalid input',args))
        # Mutant removes the input predicate, which would accept this exact call.
        results.append({'mutant':kind,'killed':True,'witness':list(args),'mechanism':'Required input rejection; no raw-machine claim on an invalid argument'})
    return results


def main():
    claims=Claims(HERE/'nesting-claims.json');rows=endpoints(claims)
    set_budget(1024*200000,HERE/'validation-budget-ledger.jsonl')
    builds={};source=HERE.parent/'l17-hardening'/'raw_comparator.cpp'
    for label,flags in [('O2',['-O2']),('O0',['-O0']),('UBSan',['-O1','-g','-fsanitize=undefined','-fno-sanitize-recover=all'])]:
        binary=HERE/('comparator-'+label);cmd=['g++','-std=c++17',*flags,str(source),'-o',str(binary)]
        run=subprocess.run(cmd,capture_output=True,text=True,check=True)
        builds[label]={'command':cmd,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                       'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'stderr':run.stderr}
    builds['compiler']=subprocess.run(['g++','--version'],capture_output=True,text=True,check=True).stdout
    (HERE/'builds.json').write_text(json.dumps(builds,indent=2)+'\n')
    req,wants=requests_and_wants(rows)
    got,meta=execute(HERE/'comparator-O2',req,HERE/'nesting-raw.jsonl.gz')
    failures=[row['id'] for row,out,wanted in zip(rows,got,wants) if not agrees(out,wanted)]
    if failures:
        (HERE/'validation-failure.json').write_text(json.dumps({'cases':failures},indent=2)+'\n')
        raise AssertionError(failures)
    rng=random.Random(173119);window_requests=[];window_wants=[];descriptions=[]
    for k in kernels():
        for trial in range(8):
            lo=k['lo'];hi=lo+len(k['input'])-1
            outside={i for i in list(range(lo-16,lo))+list(range(hi+1,hi+17)) if rng.randrange(2)}
            ones=outside|{lo+i for i,b in enumerate(k['input']) if b=='1'}
            output=outside|{lo+i for i,b in enumerate(k['target']) if b=='1'}
            ident=10000+len(window_requests)
            window_requests.append({'id':ident,'machine':claims.machine,'q':k['q'],'head':k['head'],
                  'limit':k['steps'],'ones':sorted(ones),'trace':True})
            window_wants.append({'q':k['target_q'],'head':k['target_head'],'steps':k['steps'],'halted':False,'ones':sorted(output)})
            descriptions.append({'id':ident,'kernel':k['name'],'lo':lo,'hi':hi,'outside':sorted(outside)})
    windows,window_meta=execute(HERE/'comparator-O2',window_requests,HERE/'nesting-windows.jsonl.gz')
    for actual,wanted,desc in zip(windows,window_wants,descriptions):
        assert agrees(actual,wanted),desc
        assert actual['read_min']>=desc['lo'] and actual['read_max']<=desc['hi'],desc
    stability={}
    for label in ('O0','UBSan'):
        other,m=execute(HERE/('comparator-'+label),req[:64],HERE/('nesting-'+label+'.jsonl.gz'))
        assert other==got[:64]
        stability[label]=m
    mutations=mutation_checks(rows,got)
    huge=[]
    for i in range(64):
        a=(1<<(256+i*17))+7;n=(1<<(256+i*11))+i;v=Word((('001101',1<<i),('1',1)))
        act=nest(a,n,v);claim=claims.instantiate('NEST',{'a':a,'n':n},v.parts)
        assert equal_words(act['word'].parts,claim['target'])
        assert (act['steps'],act['shift'])==(claim['steps'],claim['shift'])
        huge.append({'a_bits':a.bit_length(),'n_bits':n.bit_length(),'suffix_repetitions_bits':i+1,'passed':True})
    (HERE/'nesting-cases.json').write_text(json.dumps(rows,indent=2)+'\n')
    (HERE/'window-cases.json').write_text(json.dumps(descriptions,indent=2)+'\n')
    (HERE/'mutations.json').write_text(json.dumps(mutations,indent=2)+'\n')
    (HERE/'huge-checks.json').write_text(json.dumps(huge,indent=2)+'\n')
    report={'status':'Bounded measurements plus exact compressed-word checks; universal proof is in NESTING.md, not Lean.',
        'claims_sha256':hashlib.sha256((HERE/'nesting-claims.json').read_bytes()).hexdigest(),
        'raw_endpoints':len(rows),'raw_metadata':meta,'windows':len(windows),'window_metadata':window_meta,
        'compiler_stability':stability,'mutants_killed':len(mutations),'mutants_total':len(mutations),'huge_arithmetic_checks':len(huge),
        'validation_probes':len(req)+len(window_requests)+128}
    (HERE/'nesting-validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':main()
