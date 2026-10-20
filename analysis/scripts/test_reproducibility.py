"""Bounded arithmetic, metamorphic, and statistical-oracle checks.

Run: python -m unittest discover -s analysis/scripts -p 'test_*.py' -v
These tests are a separate implementation path, not an external replication.
"""
import collections
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

import numpy as np

from antihydra_fast import advance_chunk, generate_parities
from predictions_p1_p3_p4 import calibrate_p4, prediction_report, window_statistics


def direct_reference(b, n):
    parities = bytearray()
    for _ in range(n):
        parities.append(b % 2)
        b = (3 * b + 4) // 2
    return parities, b


class AccelerationTests(unittest.TestCase):
    def test_known_orbit(self):
        self.assertEqual(list(generate_parities(4)[0]), [0, 0, 0, 1])
        self.assertEqual(generate_parities(4)[1], 36)

    def test_empty(self):
        self.assertEqual(generate_parities(0, start=4), (bytearray(), 4))
        self.assertEqual(advance_chunk(13, 0), (bytearray(), 13))

    def test_exhaustive_parity_bijection_and_direct_endpoint(self):
        for k in range(1, 10):
            words = set()
            for b in range(1 << k):
                result = advance_chunk(b, k)
                self.assertEqual(result, direct_reference(b, k))
                words.add(bytes(result[0]))
            self.assertEqual(len(words), 1 << k)

    def test_random_starts_and_chunk_sizes(self):
        rng = random.Random(20261020)
        for _ in range(60):
            b = rng.getrandbits(rng.randrange(0, 1200))
            n = rng.randrange(0, 1200)
            chunk = rng.choice([1, 2, 7, 64, 127, 4096])
            self.assertEqual(generate_parities(n, b, chunk), direct_reference(b, n))

    def test_fifty_thousand_direct_steps_and_partial_last_chunk(self):
        self.assertEqual(generate_parities(50_000), direct_reference(4, 50_000))

    def test_concatenation_and_restarting(self):
        p, b = generate_parities(731, chunk_size=128)
        q, end = generate_parities(1559, start=b, chunk_size=97)
        self.assertEqual((p + q, end), generate_parities(2290, chunk_size=4096))

    def test_low_bits_determine_parities_not_endpoint(self):
        for k in (1, 2, 7, 64, 257):
            p, end = advance_chunk(13, k)
            q, shifted = advance_chunk(13 + (123 << k), k)
            self.assertEqual(p, q)
            self.assertEqual(shifted - end, 123 * 3 ** k)

    def test_fixed_point_shadows(self):
        for k in (1, 2, 9, 128, 1024):
            self.assertEqual(advance_chunk((2 << k) - 3, k)[0], bytearray([1] * k))
            self.assertEqual(advance_chunk((2 << k) - 4, k)[0], bytearray(k))

    def test_invalid_arguments(self):
        for args in [(-1, 4, 4096), (5, -1, 4096), (5, 4, 0)]:
            with self.assertRaises(ValueError):
                generate_parities(*args)
        with self.assertRaises(ValueError):
            advance_chunk(1, -1)

    def test_imports_have_no_file_or_simulation_side_effects(self):
        root = str(Path(__file__).resolve().parent)
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(
                [sys.executable, '-c',
                 'import sys; sys.path.insert(0, sys.argv[1]); '
                 'import antihydra_fast, predictions_p1_p3_p4', root],
                cwd=directory, capture_output=True, text=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, '')
            self.assertEqual(list(Path(directory).iterdir()), [])


class MonitorTests(unittest.TestCase):
    def test_chi_square_matches_naive_counter_oracle(self):
        p = np.random.default_rng(7).integers(0, 2, 300, dtype=np.uint8)
        for row in window_statistics(p, 6):
            j, k = row['j'], row['k']
            length = j + k
            joint = collections.Counter(
                (tuple(p[i:i+j]), tuple(p[i+j:i+length]))
                for i in range(len(p) - length + 1))
            left, right = collections.Counter(), collections.Counter()
            for (a, b), count in joint.items():
                left[a] += count
                right[b] += count
            n = sum(joint.values())
            expected_chi = 0
            for a, ca in left.items():
                for b, cb in right.items():
                    e = ca * cb / n
                    expected_chi += (joint[a, b] - e) ** 2 / e
            self.assertEqual(row['samples'], n)
            self.assertAlmostEqual(row['chi2'], expected_chi, places=9)

    def test_halting_counter_and_initial_peak_are_reported(self):
        report = prediction_report(np.ones(100, dtype=np.uint8), lo=2, max_window=6)
        self.assertEqual(report['walk']['first_negative_t'], 1)
        self.assertEqual(report['P1']['endpoint_drawdown'], 100)
        self.assertIsNone(report['P4']['descriptive_abs_z_le_4'])

    def test_no_new_records_is_not_a_pass(self):
        report = prediction_report(np.zeros(100, dtype=np.uint8), lo=2, max_window=6)
        self.assertTrue(report['P1']['no_records_is_inconclusive'])
        self.assertIsNone(report['P1']['record_band_0_8_1_25'])

    def test_null_calibration_uses_same_family_and_is_reproducible(self):
        p = np.arange(4096, dtype=np.int64) % 2
        a = calibrate_p4(p, max_window=6, replicates=9, seed=17)
        b = calibrate_p4(p, max_window=6, replicates=9, seed=17)
        self.assertEqual(a, b)
        self.assertEqual(a['steps_per_stream'], 4096)
        self.assertEqual(a['exceedances'], 0)
        self.assertEqual(a['monte_carlo_tail_rank'], 0.1)

    def test_degenerate_calibration_is_rejected(self):
        with self.assertRaises(ValueError):
            calibrate_p4(np.zeros(100, dtype=np.uint8), 6, 9)

    def test_invalid_data(self):
        for p in ([], [0, 2, 1], [[0, 1]], [0, 0.5, 1]):
            with self.assertRaises(ValueError):
                window_statistics(p, 2)
        with self.assertRaises(ValueError):
            prediction_report([0, 1], lo=3, max_window=2)


if __name__ == '__main__':
    unittest.main()
