"""Explicit actor boundary: this is the only layer that loads the frozen Python code."""
from __future__ import annotations
import importlib.util
from pathlib import Path
import sys


class Actor:
    def __init__(self,root,mutated_rules=None,mutated_words=None):
        root=Path(root).resolve()
        if str(root) not in sys.path:sys.path.insert(0,str(root))
        import rules,words,reference,block_sim
        self.rules=rules if mutated_rules is None else mutated_rules
        self.Word=words.Word if mutated_words is None else mutated_words.Word
        self.reference=reference;self.block=block_sim
        spec=importlib.util.spec_from_file_location('frozen_one_tail_validator',root/'validate_tail_family.py')
        self.tail_module=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.tail_module)

    def endpoint(self,case):
        name=case['rule'];p=case['parameters'];v=self.Word.literal(case['suffix']);r=self.rules
        if name=='F100':return r.core100(p['a'],p['c'],v)
        if name=='F111':return r.core111(p['a'],p['c'],v)
        if name=='F1100':return r.core1100(p['a'],p['c'],v)
        if name.startswith('S') and name[1:].isdigit():return r.core1100_small(p['a'],int(name[1:]),v)
        if name in ('R1','R2'):return r.residue(3*p['j']+(7 if name=='R1' else 8))
        if name in ('T0','T2'):
            return self.tail_module.one_tail(p['a'],0 if name=='T0' else 2,p['c'],p['r'])
        if name=='E':a=0;tail=v.prepend(('1',1))
        elif name=='Z':a=p['a'];tail=v.prepend(('00',1))
        elif name=='P':a=p['a'];tail=v.prepend(('11',1))
        elif name=='D':a=p['a'];tail=v.prepend(('111',1))
        elif name=='Q':
            if p['q']==0:return None
            a=p['a'];tail=v.prepend(('1',3*p['q']))
        elif name=='N':a=p['a'];tail=v.prepend(('01',p['q']))
        else:raise ValueError(name)
        return r.rewrite(a,tail)

    def compare(self,case,word_equal):
        endpoint=self.endpoint(case)
        if endpoint is None:return {'status':'not_applicable','reason':'No direct frozen actor function for identity Q(q=0)'}
        if isinstance(endpoint,dict):return {'status':'mismatch','reason':'Actor dispatch unsupported','actor':endpoint}
        parts=[('01',endpoint.a)]+list(endpoint.tail.parts)
        result=(endpoint.steps==case['steps'] and endpoint.shift==case['shift'] and word_equal(parts,case['target']))
        return {'status':'pass' if result else 'mismatch','actor_rule':endpoint.rule,
                'actor_steps':endpoint.steps,'actor_shift':endpoint.shift,'actor_word':parts}
