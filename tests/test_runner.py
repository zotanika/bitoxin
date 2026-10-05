"""Behavior tests: reject malformed input, exact pass limits, orderly signal stop."""
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import unittest

RUNNER = os.environ.get('BITOXIN_RUNNER', str(Path('build/bitoxin-run').resolve()))

class RunnerTests(unittest.TestCase):
    def run_cli(self, *args):
        return subprocess.run([RUNNER, *args], text=True, capture_output=True, timeout=20)

    def test_exact_passes_and_independent_workers(self):
        r = self.run_cli('--kib', '1', '--threads', '2', '--passes', '3', '--seed', '7', '--chunk', '17')
        self.assertEqual(r.returncode, 0, r.stderr)
        data = json.loads(r.stdout)
        self.assertEqual(data['status'], 'complete')
        self.assertEqual(len(data['workers']), 2)
        for w in data['workers']:
            self.assertEqual(w['passes'], 3)
            self.assertEqual(w['operations'], 3 * 1024 * 9)
            self.assertEqual(w['error'], 'ok')
        self.assertNotEqual(data['workers'][0]['seed'], data['workers'][1]['seed'])

    def test_rejects_invalid_configuration(self):
        for args in [('--kib', '3'), ('--kib', '0'), ('--threads', '0'),
                     ('--threads', '33'), ('--seed', '0'), ('--chunk', '0'),
                     ('--passes', '-1'), ('--kib', '999999999999999999999'),
                     ('--passes', '12junk'), ('--kib',), ('--unknown', '1'),
                     ('--kib', '131072', '--threads', '3')]:
            with self.subTest(args=args):
                r = self.run_cli(*args)
                self.assertEqual(r.returncode, 2, r.stdout + r.stderr)

    def test_two_kib_seed_wrap_does_not_false_fail(self):
        r = self.run_cli('--kib', '2', '--threads', '2', '--passes', '2',
                         '--seed', '16383', '--chunk', '65536')
        self.assertEqual(r.returncode, 0, r.stderr)
        data = json.loads(r.stdout)
        self.assertEqual([w['seed'] for w in data['workers']], [16383, 1])
        self.assertEqual([w['operations'] for w in data['workers']], [36864, 36864])

    def test_interrupt_is_not_reported_as_complete(self):
        with subprocess.Popen([RUNNER, '--kib', '64', '--passes', '0'],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as p:
            time.sleep(0.2)
            p.send_signal(signal.SIGTERM)
            out, err = p.communicate(timeout=10)
            self.assertEqual(p.returncode, 130, err)
            data = json.loads(out)
            self.assertEqual(data['status'], 'interrupted')
            self.assertTrue(data['workers'][0]['operations'] > 0)

if __name__ == '__main__':
    unittest.main()
