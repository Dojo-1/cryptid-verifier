"""Generation drift and clean-checkout controls; Lean validates the proofs in CI."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
LEADS = ROOT / 'analysis/leads'
sys.path.insert(0, str(LEADS))
spec = importlib.util.spec_from_file_location('generated_orbit', LEADS / 'l17_gen_orbit.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
sys.path.remove(str(LEADS))


class GeneratedOrbitTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name) / 'generated proofs with spaces'

    def test_clean_generation_check_and_tamper_detection(self):
        generator.generate(self.output)
        self.assertEqual(len(list(self.output.glob('*.lean'))), 5)
        generator.generate(self.output, check=True)
        source = self.output / 'L17Orbit4.lean'
        source.write_bytes(source.read_bytes().replace(b'theorem o1250', b'theorem changed'))
        with self.assertRaisesRegex(ValueError, 'modified generated source'):
            generator.generate(self.output, check=True)
        self.assertIn(b'theorem changed', source.read_bytes())  # Check mode does not repair.
        generator.generate(self.output)
        generator.generate(self.output, check=True)

    def test_recipe_drift_fails_before_writing(self):
        manifest = json.loads(generator.MANIFEST.read_text())
        manifest['sha256']['L17Orbit0.lean'] = '0' * 64
        path = Path(self.tmp.name) / 'changed-manifest.json'
        path.write_text(json.dumps(manifest))
        with patch.object(generator, 'MANIFEST', path), \
                self.assertRaisesRegex(ValueError, 'differs from link/generated-orbit.json'):
            generator.generate(self.output)
        self.assertFalse(self.output.exists())

    def test_stale_extra_source_is_rejected_without_deletion(self):
        generator.generate(self.output)
        extra = self.output / 'L17Orbit999.lean'
        extra.write_text('-- stale extra source\n')
        with self.assertRaisesRegex(ValueError, 'unexpected generated Lean files'):
            generator.generate(self.output)
        self.assertTrue(extra.exists())

    def test_cli_runs_outside_checkout_and_missing_output_fails_check(self):
        command = [sys.executable, str(LEADS / 'l17_gen_orbit.py'), '--output', str(self.output)]
        def call(*extra):
            return subprocess.run([*command, *extra], cwd=self.tmp.name, capture_output=True, text=True)
        self.assertNotEqual(call('--check').returncode, 0)
        generated = call()
        self.assertEqual(generated.returncode, 0, generated.stderr)
        checked = call('--check')
        self.assertEqual(checked.returncode, 0, checked.stderr)


if __name__ == '__main__':
    unittest.main()
