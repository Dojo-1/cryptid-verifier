"""Exercise orchestration and real subprocess failures without pretending to run Lean."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import verify


FAKE_LAKE = '''\
from pathlib import Path
import sys
project = Path.cwd()
name = project.name if project.name in ('mathlib', 'link') else 'core'
root = project.parent if name != 'core' else project
if sys.argv[1:] == ['exe', 'cache', 'get']:
    if (root / 'fail-cache').exists():
        sys.exit(19)
    if name == 'link':
        for directory in ('baselines', 'artifacts'):
            path = project / '.lake/packages/Cryptids' / directory
            path.mkdir(parents=True, exist_ok=True)
            (path / 'input.txt').write_text('pinned input', encoding='utf-8')
    print('cache ready')
elif sys.argv[1:] == ['build']:
    assert not (root / '.lake/build/stale').exists()
    assert not (project / '.lake/build/stale').exists()
    if name == 'link':
        assert len(list((project / 'CryptidLink/Generated').glob('*.lean'))) == 5
        for directory in ('baselines', 'artifacts'):
            assert (project / directory / 'input.txt').read_text() == 'pinned input'
            assert not (project / directory).is_symlink()
    print('build stdout', flush=True)
    print('build stderr', file=sys.stderr, flush=True)
    if (root / 'fail-build').exists() and (root / 'fail-build').read_text() == name:
        sys.exit(17)
    print("'Demo.visible' does not depend on any axioms", flush=True)
    build = root / '.lake/build'
    build.mkdir(parents=True, exist_ok=True)
    (build / 'stale').touch()
else:
    sys.exit(23)
'''


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'checkout with spaces'
        self.root.mkdir()
        for relative in ('scripts/audit_trust.py', 'analysis/leads/l17_gen_orbit.py',
                         'analysis/leads/l17_orbit2.py', 'link/generated-orbit.json'):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(verify.ROOT / relative, target)
        for name, relative in verify.PROJECTS.items():
            project = self.root / relative
            project.mkdir(parents=True, exist_ok=True)
            (project / 'lean-toolchain').write_text(f'test-pin-{name}\n', encoding='utf-8')
            build = project / '.lake/build'
            build.mkdir(parents=True)
            (build / 'stale').touch()
        (self.root / 'Proof.lean').write_text(
            'theorem visible : True := True.intro\n#print axioms Demo.visible\n', encoding='utf-8')
        inventory = {'projects': {name: {'sources': ['Proof.lean'], 'theorems': ['Demo.visible']}
                                  for name in verify.PROJECTS}}
        (self.root / 'scripts/trust_inventory.json').write_text(json.dumps(inventory), encoding='utf-8')
        self.fake = self.root / 'fake lake.py'
        self.fake.write_text(FAKE_LAKE, encoding='utf-8')
        self.calls = []
        original_run = verify.run

        def bridge(command, cwd, log=None):
            self.calls.append((command, cwd))
            if command[0] == 'fake-lake':
                command = [sys.executable, str(self.fake), *command[1:]]
            original_run(command, cwd, log)

        self.runner = patch.object(verify, 'run', side_effect=bridge)
        self.runner.start()
        self.addCleanup(self.runner.stop)

    def test_all_projects_prepare_build_and_really_audit_from_paths_with_spaces(self):
        verify.verify(self.root, tuple(verify.PROJECTS), 'fake-lake')
        builds = [cwd for command, cwd in self.calls if command[1:] == ['build']]
        self.assertEqual(builds, [self.root, self.root / 'mathlib', self.root / 'link'])
        audits = [command for command, _ in self.calls if 'audit_trust.py' in command[1]]
        self.assertEqual([c[c.index('--project') + 1] for c in audits], list(verify.PROJECTS))
        for relative in verify.PROJECTS.values():
            log = (self.root / relative / 'build.log').read_text(encoding='utf-8')
            self.assertIn('build stdout', log)
            self.assertIn('build stderr', log)
            self.assertIn("'Demo.visible' does not depend on any axioms", log)

    def test_failed_build_preserves_log_and_stops_before_audit_or_next_project(self):
        (self.root / 'fail-build').write_text('core')
        with self.assertRaises(subprocess.CalledProcessError) as error:
            verify.verify(self.root, tuple(verify.PROJECTS), 'fake-lake')
        self.assertEqual(error.exception.returncode, 17)
        self.assertEqual(len(self.calls), 1)
        self.assertIn('build stderr', (self.root / 'build.log').read_text())
        self.assertFalse((self.root / 'mathlib/build.log').exists())

    def test_failed_audit_stops_before_next_project(self):
        with (self.root / 'Proof.lean').open('a', encoding='utf-8') as source:
            source.write('private axiom injected : False\n')
        with self.assertRaises(subprocess.CalledProcessError) as error:
            verify.verify(self.root, tuple(verify.PROJECTS), 'fake-lake')
        self.assertEqual(error.exception.returncode, 1)
        self.assertEqual(len(self.calls), 2)
        self.assertFalse((self.root / 'mathlib/build.log').exists())

    def test_failed_cache_cannot_fall_through_to_build_or_audit(self):
        (self.root / 'fail-cache').touch()
        with self.assertRaises(subprocess.CalledProcessError) as error:
            verify.verify(self.root, ('link',), 'fake-lake')
        self.assertEqual(error.exception.returncode, 19)
        self.assertFalse(any(command[1:] == ['build'] for command, _ in self.calls))
        self.assertFalse((self.root / 'link/build.log').exists())

    def test_data_copies_refresh_but_unexpected_files_are_preserved_and_rejected(self):
        project = self.root / 'link'
        for name in ('baselines', 'artifacts'):
            source = project / '.lake/packages/Cryptids' / name
            source.mkdir(parents=True)
            (source / 'input.txt').write_text('pinned')
        verify.copy_upstream_data(project)
        (project / 'baselines/input.txt').write_text('stale')
        verify.copy_upstream_data(project)
        self.assertEqual((project / 'baselines/input.txt').read_text(), 'pinned')
        unexpected = project / 'baselines/user-data.txt'
        unexpected.write_text('keep me')
        with self.assertRaisesRegex(RuntimeError, 'unexpected files'):
            verify.copy_upstream_data(project)
        self.assertEqual(unexpected.read_text(), 'keep me')

    def test_cli_returns_the_failed_child_status(self):
        with patch.object(sys, 'argv', ['verify.py', '--project', 'core']), \
                patch.object(verify.shutil, 'which', return_value='fake-lake'), \
                patch.object(verify, 'verify', side_effect=subprocess.CalledProcessError(17, ['lake', 'build'])):
            self.assertEqual(verify.main(), 17)


if __name__ == '__main__':
    unittest.main()
