"""Falsification controls for the source policy and theorem-output inventory."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from audit_trust import audit, lean_tokens, printed_theorems


class TrustAuditTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / 'Probe.lean'
        self.good = 'theorem visible : True := True.intro\n#print axioms visible\n'
        self.log = "'visible' does not depend on any axioms\n"
        self.inventory = {'projects': {'core': {'sources': ['Probe.lean'], 'theorems': ['visible']}}}

    def check_source(self, source=None, log=None, inventory=None):
        self.source.write_text(self.good if source is None else source)
        return audit(self.root, self.log if log is None else log, 'core',
                     self.inventory if inventory is None else inventory)[0]

    def test_clean_control(self):
        self.assertEqual(self.check_source(), [])

    def test_modified_axiom_declarations_are_rejected(self):
        for declaration in (
            'axiom injected : False',
            'private axiom injected : False',
            'namespace N\nprotected axiom injected : False\nend N',
            'noncomputable axiom injected : False',
            '@[simp] private axiom injected : False',
            'private/- nested /- comment -/ -/axiom injected : False',
        ):
            with self.subTest(declaration=declaration):
                errors = self.check_source(self.good + declaration + '\n')
                self.assertTrue(any('forbidden axiom' in e for e in errors), errors)

    def test_unprinted_direct_sorryAx_is_rejected(self):
        for term in ('sorryAx (α := False) false', '_root_.sorryAx (α := False) false',
                     '«sorryAx» (α := False) false'):
            with self.subTest(term=term):
                errors = self.check_source(self.good + 'theorem hidden : False := ' + term + '\n')
                self.assertTrue(any('forbidden sorryAx' in e for e in errors), errors)

    def test_other_forbidden_terms_are_rejected(self):
        for term in ('sorry', 'admit', 'native_decide'):
            with self.subTest(term=term):
                self.assertTrue(any('forbidden ' + term in e for e in
                                    self.check_source(self.good + 'example : True := by ' + term)))

    def test_comments_and_literal_strings_are_not_declarations(self):
        text = self.good + '''
/- axiom fake : False /- sorry native_decide -/ admit -/
-- sorryAx axiom
def ordinary := "axiom /- sorry -- native_decide \\" quoted"
def raw := r#"axiom /- sorry -- "quoted""#
def marker : Char := 'x'
'''
        self.assertEqual(self.check_source(text), [])

    def test_comment_marker_inside_string_cannot_hide_following_axiom(self):
        for prefix in ('def marker := "/-"\n', 'def marker := r#"/-"#\n',
                       'def marker := "--"\n'):
            with self.subTest(prefix=prefix):
                errors = self.check_source(self.good + prefix + 'private axiom injected : False\n')
                self.assertTrue(any('forbidden axiom' in e for e in errors), errors)

    def test_identifier_substrings_are_not_forbidden_tokens(self):
        self.assertEqual(self.check_source(self.good + "def axiomatic := 1\ndef sorryAxSuffix := 2\ndef axiom' := 3\n"), [])

    def test_unterminated_lexical_constructs_fail(self):
        for suffix in ('/- unfinished', 'def s := "unfinished', 'def s := r#"unfinished', 'def «unfinished'):
            with self.subTest(suffix=suffix):
                self.assertTrue(any('unterminated' in e for e in self.check_source(self.good + suffix)))

    def test_comment_boundaries_and_line_numbers(self):
        tokens = lean_tokens('private/- nested\n/- comment -/ -/axiom bad : False')
        self.assertEqual([(t.value, t.line) for t in tokens[:2]], [('private', 1), ('axiom', 2)])

    def test_qualified_unicode_and_apostrophe_print_names(self):
        tokens = lean_tokens("#print axioms N.ξ_floor\n#print axioms N.lemma'\n")
        self.assertEqual(printed_theorems(tokens), {'N.ξ_floor', "N.lemma'"})
        inv = {'projects': {'core': {'sources': ['Probe.lean'], 'theorems': ["lemma'"]}}}
        self.assertEqual(self.check_source("#print axioms lemma'\n", "'lemma'' does not depend on any axioms\n", inv), [])

    def test_missing_named_output_fails_even_with_clean_unrelated_record(self):
        errors = self.check_source(log="'unrelated' does not depend on any axioms\n")
        self.assertIn('core: missing axiom output for inventoried theorem: visible', errors)

    def test_removing_print_command_does_not_accept_stale_log(self):
        errors = self.check_source('theorem visible : True := True.intro\n')
        self.assertIn('core: inventoried theorem has no #print axioms command: visible', errors)

    def test_new_print_command_requires_inventory_update(self):
        errors = self.check_source(self.good + '#print axioms additional\n')
        self.assertTrue(any('register #print axioms' in e for e in errors), errors)

    def test_nonstandard_axioms_in_expected_or_extra_records_fail(self):
        for log in ("'visible' depends on axioms: [sorryAx]\n",
                    self.log + "'unrelated' depends on axioms: [Injected.falsehood]\n"):
            with self.subTest(log=log):
                self.assertTrue(any('non-standard axioms' in e for e in self.check_source(log=log)))

    def test_conflicting_duplicate_record_cannot_hide_bad_dependency(self):
        self.assertTrue(any('non-standard axioms' in e for e in self.check_source(
            log=self.log + "'visible' depends on axioms: [sorryAx]\n")))

    def test_standard_axiom_records_pass(self):
        self.assertEqual(self.check_source(log="'visible' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"), [])

    def test_empty_log_fails(self):
        self.assertTrue(self.check_source(log=''))

    def test_empty_duplicate_and_unknown_inventories_fail(self):
        for inv in ({}, [], {'projects': {'core': {'sources': ['Probe.lean'], 'theorems': []}}},
                    {'projects': {'core': {'sources': ['Probe.lean'], 'theorems': ['visible', 'visible']}}}):
            with self.subTest(inventory=inv):
                self.assertTrue(any('invalid trust inventory' in e for e in self.check_source(inventory=inv)))

    def test_missing_inventory_source_fails(self):
        inv = {'projects': {'core': {'sources': ['Missing.lean'], 'theorems': ['visible']}}}
        self.assertTrue(any('missing/outside inventory source' in e for e in self.check_source(inventory=inv)))

    def test_build_directories_are_excluded_from_local_source_policy(self):
        directory = self.root / '.lake/packages/dependency'
        directory.mkdir(parents=True)
        (directory / 'Bad.lean').write_text('axiom imported : False\n')
        self.assertEqual(self.check_source(), [])

    def test_cli_missing_inventory_fails_closed(self):
        log = self.root / 'build.log'
        log.write_text(self.log)
        script = Path(__file__).with_name('audit_trust.py')
        result = subprocess.run([sys.executable, str(script), str(log), '--root', str(self.root),
                                 '--inventory', str(self.root/'missing.json')], text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('trust audit failed', result.stdout)


if __name__ == '__main__':
    unittest.main()
