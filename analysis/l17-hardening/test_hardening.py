"""Tests of the new critic and its isolation, including the bug found by ACAF."""
from __future__ import annotations
import ast
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import backend
from mutations import alter_function
from specification import Claims,equal_words,trim,skip,first_bits,matching_prefix,integer,agrees

ROOT=Path(__file__).resolve().parent


class CriticChecks(unittest.TestCase):
    def test_zero_repetition_regression_and_exterior_zero_scope(self):
        self.assertEqual(trim([('10',0)]),[])
        self.assertTrue(equal_words([('10',0)],[]))
        self.assertTrue(equal_words([('101100',0),('0',12)],[]))
        self.assertTrue(equal_words([('101',1),('0',12)],[('101',1)]))
        self.assertFalse(equal_words([('101',1)],[('11',1)]))

    def test_periodic_word_comparison_against_explicit_oracle(self):
        patterns=[''.join(x) for n in range(1,4) for x in itertools.product('01',repeat=n)]
        for a in patterns:
            for b in patterns:
                for na in range(4):
                    for nb in range(4):
                        self.assertEqual(equal_words([(a,na)],[(b,nb)]),(a*na).rstrip('0')==(b*nb).rstrip('0'))

    def test_cursor_prefix_and_skip_against_explicit_strings(self):
        for n in range(9):
            for data in itertools.product('01',repeat=n):
                bits=''.join(data);chunks=[(b,1) for b in bits]
                for k in (0,n//2,n,n+1):
                    self.assertEqual(first_bits(chunks,k),(bits+'0'*k)[:k])
                    self.assertTrue(equal_words(skip(chunks,k),[(bits[k:],1)] if bits[k:] else []))
                for p in ('0','1','01','10','001'):
                    length=0
                    while length<n and bits[length]==p[length%len(p)]:length+=1
                    self.assertEqual(matching_prefix(chunks,p),length)

    def test_arithmetic_language_is_integer_only_and_has_no_calls(self):
        n=1<<4096
        self.assertEqual(integer('60*j*j+136*j+215',{'j':n}),60*n*n+136*n+215)
        for text in ('1/2','2**10','float(1)','__import__("os")','a[0]','1.5','True'):
            with self.assertRaises(ValueError):integer(text,{'a':1})

    def test_guard_boundaries_and_unknown_fields(self):
        c=Claims(ROOT/'claims.json')
        c.instantiate('F100',{'a':7,'c':0})
        c.instantiate('F111',{'a':5,'c':1})
        for name,p in (('F100',{'a':6,'c':0}),('F111',{'a':5,'c':0}),('F1100',{'a':7,'c':6}),('R1',{'j':-1})):
            with self.assertRaises(ValueError):c.instantiate(name,p)
        with self.assertRaises(ValueError):c.instantiate('E',{'undeclared':1})
        with self.assertRaises(ValueError):c.instantiate('F100',{'a':True,'c':0})

    def test_mutator_can_find_a_method_inside_a_class(self):
        source='class C:\n    def f(self):\n        return 7\n'
        changed=alter_function(source,'f','return 7','return 8')
        tree=ast.parse(changed)
        self.assertEqual(tree.body[0].body[0].body[0].value.value,8)

    def test_budget_rejection_precedes_process_execution(self):
        old=backend._remaining
        try:
            backend.set_budget(0)
            row={'id':0,'machine':'not-executed','q':2,'head':0,'limit':1,'ones':[]}
            with self.assertRaises(ValueError):backend.execute('/nonexistent-comparator',[row])
            with self.assertRaises(ValueError):backend.set_budget(-1)
        finally:backend._remaining=old

    def test_critic_modules_do_not_import_actor_dependencies(self):
        for name in ('specification.py','backend.py','corpus.py','trace_critic.py'):
            tree=ast.parse((ROOT/name).read_text())
            imports=[]
            for node in ast.walk(tree):
                if isinstance(node,ast.Import):imports.extend(x.name for x in node.names)
                if isinstance(node,ast.ImportFrom):imports.append(node.module)
            self.assertFalse(set(imports)&{'rules','words','reference','block_sim','actor_bridge'},name)

    def test_minimized_historical_word_keeps_its_absolute_position(self):
        binary=ROOT/'comparator-O2'
        if not binary.exists():self.skipTest('Run the comparator campaign to build the executable first')
        row={'id':0,'machine':Claims(ROOT/'claims.json').machine,'q':2,'head':0,'limit':0,'ones':[2]}
        actual,_=backend.execute(binary,[row])
        self.assertTrue(agrees(actual[0],{'q':2,'head':0,'steps':0,'halted':False,'ones':[2]}))

    def test_modules_import_quietly_without_working_directory_writes(self):
        modules=['specification','backend','corpus','trace_critic','actor_bridge','controls','mutations','run_hardening']
        code='import importlib\n'+''.join('importlib.import_module('+repr(x)+')\n' for x in modules)
        with tempfile.TemporaryDirectory() as d:
            env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONPATH=str(ROOT))
            result=subprocess.run([sys.executable,'-c',code],cwd=d,env=env,capture_output=True,text=True)
            self.assertEqual((result.returncode,result.stdout,result.stderr),(0,'',''))
            self.assertFalse(list(Path(d).iterdir()))


if __name__=='__main__':unittest.main()
