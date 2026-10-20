"""One fixed, provenance-bound ACAF/comparator campaign; stdlib plus a C++ compiler."""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime,timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
from actor_bridge import Actor
from backend import execute,encode,transform_machine,set_budget
from controls import known_answers,metamorphic,representations
from corpus import frozen_cases,acaf_cases,guard_cases,huge_cases,window_requests,kernels
from mutations import campaign
from specification import Claims,request,want,agrees,equal_words
from trace_critic import check_trace

ROOT=Path(__file__).resolve().parent


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,data):Path(path).write_text(json.dumps(data,indent=2)+'\n')


def default_actor():
    for name in ('l17-stacked-section','l17-frontier'):
        path=ROOT.parent/name
        if path.is_dir():return path
    raise ValueError('Use --actor-root for the original frozen handoff directory')


def build():
    source=ROOT/'raw_comparator.cpp';records={}
    version=subprocess.run(['g++','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0]
    for name,flags in (('O2',['-O2']),('O0',['-O0']),('UBSan',['-O1','-fsanitize=undefined','-fno-sanitize-recover=all'])):
        binary=ROOT/('comparator-'+name)
        command=['g++','-std=c++17',*flags,'-Wall','-Wextra','-Wconversion','-pedantic','-Werror',str(source),'-o',str(binary)]
        result=subprocess.run(command,capture_output=True,text=True,check=True)
        if binary.stat().st_size==0 or not os.access(binary,os.X_OK):raise RuntimeError('Compiler did not leave an executable: '+name)
        records[name]={'compiler':version,'flags':command[1:-3],'source_sha256':sha(source),'binary_sha256':sha(binary),'stderr':result.stderr}
    write(ROOT/'compiler-build.json',records)
    return records


def freeze_check(actor_root):
    record=json.loads((ROOT/'frozen-input.json').read_text());prefix='analysis/l17-stacked-section/'
    consumed={}
    for name,digest in record['entries'].items():
        if name.startswith(prefix):
            path=actor_root/name[len(prefix):]
            if sha(path)!=digest:raise ValueError('Frozen input changed: '+name)
            consumed[name]=digest
    return consumed


def invalid_inputs(binary,machine):
    valid=f'0 {machine} 2 0 0 0 0'
    rows=[('', 'empty'),('0 bad 2 0 0 0 0','machine'),(f'0 {machine} 6 0 0 0 0','state'),
          (f'0 {machine} 2 0 -1 0 0','negative-budget'),(f'0 {machine} 2 0 200001 0 0','oversized-budget'),
          (f'0 {machine} 2 0 0 0 2 7 7','duplicate-cell'),(f'0 {machine} 2 -9223372036854775808 0 0 0','coordinate-domain'),
          (f'0 {machine} 2 0 1001 1 0','trace-limit'),(valid+' extra','trailing-input')]
    result=[]
    for line,name in rows:
        out=subprocess.run([str(binary)],input=(line+'\n').encode(),capture_output=True)
        assert out.returncode==2 and not out.stdout,(name,out.stdout,out.stderr)
        result.append({'name':name,'exit_code':out.returncode,'diagnostic':out.stderr.decode().strip()})
    return result


def main(actor_root):
    started=datetime.now(timezone.utc).isoformat();actor_root=Path(actor_root).resolve()
    consumed=freeze_check(actor_root);claims_hash=sha(ROOT/'claims.json')
    claims=Claims(ROOT/'claims.json');protocol=json.loads((ROOT/'protocol.json').read_text());seed=protocol['seed']
    prior_work=0
    for p in ROOT.glob('attempt-*/attempt-summary.json'):
        x=json.loads(p.read_text());prior_work+=x.get('corrected_total_defined_cpp_transitions',x['defined_cpp_transitions_before_stop'])
    ledger=ROOT/'raw-work-ledger.jsonl'
    if not ledger.exists() and (ROOT/'execution.json').exists():
        old_execution=json.loads((ROOT/'execution.json').read_text())
        bootstrap=old_execution['counts']['cumulative_executed_defined_cpp_transitions']-prior_work
        ledger.write_text(json.dumps({'executed_defined_transitions':bootstrap,'origin':'Completed run before adding the durable per-batch work ledger.'})+'\n')
    if ledger.exists():prior_work+=sum(json.loads(line)['executed_defined_transitions'] for line in ledger.read_text().splitlines())
    if (ROOT/'execution.json').exists():
        history=ROOT/'completed-runs';history.mkdir(exist_ok=True)
        number=len(list(history.glob('*.json')))+1
        (history/(str(number)+'.json')).write_bytes((ROOT/'execution.json').read_bytes())
    set_budget(protocol['budgets']['maximum_total_defined_raw_transitions']-prior_work,ledger)
    compiler=build();print('Comparator compiled at O2, O0 and UBSan.',flush=True)
    actor=Actor(actor_root);old=frozen_cases(actor_root,claims);new=acaf_cases(claims,seed);cases=old+new
    actor_counts=Counter();actor_failures=[]
    for index,case in enumerate(cases):
        result=actor.compare(case,equal_words);actor_counts[result['status']]+=1
        if result['status']=='mismatch':actor_failures.append({'index':index,'case':case,'result':result})
    write(ROOT/'actor-comparisons.json',{'counts':dict(actor_counts),'failures':actor_failures})
    if actor_failures:raise AssertionError('Actor/spec discrepancy; see actor-comparisons.json')
    print('Actor versus separately consumed specification:',dict(actor_counts),flush=True)
    raw=[request(case,i,case['head']) for i,case in enumerate(cases)]
    expected=[want(case,case['head']) for case in cases]
    budget=sum(x['limit'] for x in raw)
    if budget>protocol['budgets']['maximum_total_defined_raw_transitions']:raise ValueError('Campaign exceeds total raw limit before execution')
    results,main_provenance=execute(ROOT/'comparator-O2',raw,ROOT/'raw-rule-results.jsonl.gz')
    failures=[{'index':i,'case':cases[i],'actual':actual,'expected':expected[i]} for i,actual in enumerate(results) if not agrees(actual,expected[i])]
    write(ROOT/'rule-comparisons.json',{'frozen':len(old),'new_acaf':len(new),'by_claim':dict(Counter(c['rule'] for c in cases)),
        'provenance':main_provenance,'failures':failures,'scope':'Separate C++ literal TM against claims.json, including exact physical support.'})
    if failures:raise AssertionError('Raw endpoint discrepancy; see rule-comparisons.json')
    print('C++ complete endpoint comparisons:',len(cases),'passed;',main_provenance['defined_transitions'],'defined transitions; cached literal output:',main_provenance['cache_reused'],flush=True)
    windows=window_requests(actor_root,claims.machine,seed)
    wreq=[]
    for i,row in enumerate(windows):q=dict(row['request']);q['id']=i;wreq.append(q)
    wresults,wprov=execute(ROOT/'comparator-O2',wreq,ROOT/'window-results.jsonl.gz')
    window_failures=[]
    known_kernels=kernels(actor_root)
    for index,(row,out) in enumerate(zip(windows,wresults)):
        kernel=known_kernels[row['kernel']]
        reads=[[ord(q)-65,h,b] for q,h,b in kernel['reads']]
        good=agrees(out,row['expected']) and row['read_bounds'][0]<=out['read_min'] and out['read_max']<=row['read_bounds'][1] and out['reads']==reads
        if not good:window_failures.append({'index':index,'record':row,'actual':out})
    write(ROOT/'window-comparisons.json',{'kernels':len(known_kernels),'variants_per_kernel':12,'checks':len(windows),'provenance':wprov,'failures':window_failures})
    if window_failures:raise AssertionError('Locality discrepancy; see window-comparisons.json')
    print('Arbitrary two-sided read-window contexts:',len(windows),'passed.',flush=True)
    stored=json.loads((actor_root/'validation-results.json').read_text())['independent_block_checks']
    controls=[]
    for row in stored:
        cells=[row['head']+i for i,b in enumerate(row['word']) if b=='1']
        req={'id':len(controls),'machine':claims.machine,'q':row['q'],'head':row['head'],'limit':row['steps'],'ones':cells,'trace':False}
        oracle=actor.reference.run(row['word'],row['steps'],row['q'],row['head'])
        controls.append({'request':req,'expected':{'q':oracle['q'],'head':oracle['head'],'steps':oracle['steps'],'halted':oracle['halted'],'ones':sorted(oracle['tape'])},'origin':'frozen/random-control'})
    analytic=known_answers(claims.machine)
    for row in analytic:q=dict(row['request']);q['id']=len(controls);controls.append(dict(row,request=q))
    creq=[x['request'] for x in controls];cout,cprov=execute(ROOT/'comparator-O2',creq,ROOT/'control-results.jsonl.gz')
    assert all(agrees(out,row['expected']) for row,out in zip(controls,cout)),'Raw control discrepancy'
    variants=metamorphic(creq,cout,seed)
    mreq=[]
    for i,row in enumerate(variants):q=dict(row['request']);q['id']=i;mreq.append(q)
    mout,mprov=execute(ROOT/'comparator-O2',mreq,ROOT/'metamorphic-results.jsonl.gz')
    assert all(agrees(out,row['expected']) for row,out in zip(variants,mout)),'Frame/metamorphic discrepancy'
    # Same input requests under distinct compiler settings, including all known answers.
    matched=creq[:64]+[x['request'] for x in controls[-len(analytic):]]+wreq[:12]
    for i,row in enumerate(matched):row=dict(row);row['id']=i;matched[i]=row
    compiler_results={};reference_outputs=None
    for name in ('O2','O0','UBSan'):
        if sha(ROOT/('comparator-'+name))!=compiler[name]['binary_sha256']:raise RuntimeError('Compiled binary changed before control: '+name)
        out,provenance=execute(ROOT/('comparator-'+name),matched,ROOT/('compiler-'+name+'-results.jsonl.gz'))
        if reference_outputs is None:reference_outputs=out
        else:assert out==reference_outputs,'Compiler setting discrepancy'
        compiler_results[name]=provenance
    negative=invalid_inputs(ROOT/'comparator-UBSan',claims.machine)
    # Two genuine semantic changes must be rejected, rather than called conjugacies.
    base=analytic[1];bad_requests=[]
    wrong_table=claims.machine.replace('1RB','0RB',1)
    bad_requests.append(dict(base['request'],id=0,machine=wrong_table))
    bad_requests.append(dict(base['request'],id=1,machine=transform_machine(claims.machine,[5,1,2,3,4,0])))
    bad_results,badprov=execute(ROOT/'comparator-O2',bad_requests)
    assert all(not agrees(out,base['expected']) for out in bad_results),'Semantic negative control failed'
    write(ROOT/'controls.json',{'random_raw':len(stored),'analytic_known_answers':len(analytic),'frame_variants':len(variants),
        'raw_provenance':cprov,'frame_provenance':mprov,'matched_compiler_variants':compiler_results,
        'malformed_requests_rejected':negative,'semantic_changes_rejected':badprov})
    reps=representations(actor,seed);write(ROOT/'representation-checks.json',{'checks':len(reps),'cases':reps})
    huge=huge_cases(claims,seed);huge_results=[]
    for case in huge:
        out=actor.compare(case,equal_words);assert out['status']=='pass',case['rule']
        huge_results.append({'rule':case['rule'],'bits':case['bits'],'parameters':case['parameters'],'steps':case['steps'],'shift':case['shift']})
    write(ROOT/'huge-integer-checks.json',{'checks':len(huge),'results':huge_results,'scope':'Exact expression/word comparison, not raw simulation or a universal proof.'})
    guards=guard_cases(claims);guard_results=[]
    for case in guards:
        try:claims.instantiate(case['rule'],case['parameters'],case['suffix'])
        except ValueError:pass
        else:raise AssertionError('Critic accepted invalid guard')
        try:actor.endpoint(case)
        except (ValueError,TypeError,IndexError):guard_results.append(dict(case,status='rejected'))
        else:raise AssertionError('Actor accepted an invalid guard')
    write(ROOT/'guard-checks.json',{'cases':guard_results})
    print('Raw controls, frame changes, compiler/UBSan parity, word representations and huge counters passed.',flush=True)
    trace=check_trace(actor_root/'symbolic-extension.json',claims)
    short=check_trace(actor_root/'validation-results.json',claims)
    write(ROOT/'trace-comparisons.json',{'extended':trace,'original':short,'scope':'Separate arithmetic-edge audit; counts are not new raw-machine steps.'})
    mutants=campaign(actor_root,claims,cases,guards);write(ROOT/'mutation-results.json',{'mutants':mutants,'counts':dict(Counter(r['status'] for r in mutants))})
    print('Mutation results:',dict(Counter(r['status'] for r in mutants)),flush=True)
    # Recheck each minimized in-guard rule witness against the literal TM.
    minimized=[];min_cases=[]
    for row in mutants:
        if 'minimized' not in row:continue
        x=row['minimized'];case=claims.instantiate(x['rule'],x['parameters'],x['suffix']);case['machine']=claims.machine
        if case['steps']<=200000:min_cases.append(case);minimized.append(request(case,len(minimized)))
    min_out,min_provenance=execute(ROOT/'comparator-O2',minimized,ROOT/'minimized-witness-results.jsonl.gz')
    assert all(agrees(out,want(case)) for out,case in zip(min_out,min_cases)),'Minimized baseline witness failed'
    raw_total=sum(p['defined_transitions'] for p in (main_provenance,wprov,cprov,mprov,badprov,min_provenance))+sum(p['defined_transitions'] for p in compiler_results.values())
    newly_executed=sum(p['executed_defined_transitions'] for p in (main_provenance,wprov,cprov,mprov,badprov,min_provenance))+sum(p['executed_defined_transitions'] for p in compiler_results.values())
    assert prior_work+newly_executed<=protocol['budgets']['maximum_total_defined_raw_transitions']
    assert claims_hash==sha(ROOT/'claims.json')
    assert consumed==freeze_check(actor_root)
    write(ROOT/'execution.json',{'started_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),
        'claims_consumed':{'path':'claims.json','sha256':claims_hash},'frozen_actor_files':consumed,
        'protocol_sha256':sha(ROOT/'protocol.json'),'mutation_plan_sha256':sha(ROOT/'mutation-plan.json'),
        'compiler':compiler,'counts':{'frozen_rule_checks':len(old),'new_acaf_rule_checks':len(new),'actor':dict(actor_counts),
            'window_contexts':len(windows),'random_raw_controls':len(stored),'analytic_controls':len(analytic),
            'frame_variants':len(variants),'word_representation_cases':len(reps),'huge_integer_cases':len(huge),
            'guard_rejections':len(guards),'trace_edges':trace['edges']+short['edges'],
            'mutants':len(mutants),'mutant_results':dict(Counter(r['status'] for r in mutants)),
            'minimized_witnesses_rechecked':len(minimized),'defined_transitions_in_consumed_traces':raw_total,
            'additional_defined_cpp_transitions_this_attempt':newly_executed,'prior_attempt_defined_cpp_transitions':prior_work,
            'cumulative_executed_defined_cpp_transitions':prior_work+newly_executed},
        'source_hashes':{p.name:sha(p) for p in ROOT.glob('*.py')},
        'minimized_witness_provenance':min_provenance,
        'scope':'Finite comparator/ACAF hardening by one author with separate code paths; no new Lean build, orbit extension, complete stack system or non-halting proof.'})
    print('Complete. Cumulative executed C++ transitions:',prior_work+newly_executed,'of 80000000 budget.',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--actor-root',type=Path)
    args=parser.parse_args()
    try:main(args.actor_root or default_actor())
    except Exception as exc:
        write(ROOT/'failure.json',{'type':type(exc).__name__,'message':str(exc),'status':'Campaign stopped; no passing conclusion for this run.'})
        raise
