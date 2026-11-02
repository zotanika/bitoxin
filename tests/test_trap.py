"""A fault-injected runner must decode the same register in record and trap mode."""
import json
import os
from pathlib import Path
import platform
import shlex
import signal
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CC = shlex.split(os.environ.get('CC', 'cc'))
FLAGS = shlex.split(os.environ.get('CFLAGS', '-O2 -g')) + [
    '-std=c11', '-Wall', '-Wextra', '-Wpedantic', '-Werror', '-DBX_SIMD',
    '-I' + str(ROOT), '-I' + str(ROOT / 'tools')]


def runner(directory, name, defines):
    target = Path(directory) / name
    subprocess.run([*CC, *FLAGS, *defines, str(ROOT / 'tools/bitoxin-run.c'),
                    str(ROOT / 'bitoxin_core.c'), '-pthread', '-o', str(target)], check=True)
    return str(target)


class TrapDecodeTest(unittest.TestCase):
    def check(self, define):
        with tempfile.TemporaryDirectory(prefix='bitoxin-trap-') as directory:
            binary = runner(directory, 'fault', [define])
            record = subprocess.run([binary, '--kib', '1', '--passes', '1'],
                                    capture_output=True, text=True, timeout=30)
            data = json.loads(record.stdout)
            if data['backend'] == 'portable-c':
                self.skipTest('native lane required')
            self.assertEqual(record.returncode, 1)
            worker = data['workers'][0]
            self.assertEqual(worker['error'], 'register_error')
            expected = worker['lane_reg']
            self.assertTrue(expected)
            trapped = subprocess.run([binary, '--kib', '1', '--passes', '1', '--trap'],
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual(trapped.returncode, 1, trapped.stderr)
            event = json.loads(trapped.stdout)
            self.assertEqual(event['status'], 'trapped')
            self.assertEqual(event['lane_reg'], expected)
            # The same failing step: the token in A, the check word in C (bit
            # position | expected bit << 8; the expected bit starts at 1 and
            # flips every pass) and the same deviating value.
            self.assertEqual((event['worker'], event['pass'], event['bit']),
                             (worker['id'], worker['passes'], worker['error_bit']))
            self.assertEqual(event['a'], worker['expected'])
            polarity = 1 - worker['passes'] % 2
            self.assertEqual(int(event['c'], 16), (worker['error_bit'] & 7) | polarity << 8)
            self.assertEqual((event['lane_expected'], event['lane_observed']),
                             (worker['lane_expected'], worker['lane_observed']))
            return event

    def test_gpr_fault(self):
        self.assertEqual(self.check('-DBX_LANE_FAULT=5')['kind'], 'register')

    def test_simd_fault(self):
        self.assertEqual(self.check('-DBX_SIMD_FAULT=7')['kind'], 'simd')

    @unittest.skipUnless(platform.machine() in ('arm64', 'aarch64', 'riscv64'),
                         '__builtin_trap raises SIGTRAP on AArch64 and RISC-V only')
    def test_foreign_trap_is_not_decoded(self):
        """The portable lane traps with __builtin_trap, which has no marker."""
        with tempfile.TemporaryDirectory(prefix='bitoxin-trap-') as directory:
            binary = runner(directory, 'portable', ['-DBX_PORTABLE', '-DBX_LANE_FAULT=5'])
            trapped = subprocess.run([binary, '--kib', '1', '--passes', '1', '--trap'],
                                     capture_output=True, text=True, timeout=30)
            self.assertEqual(trapped.returncode, -signal.SIGTRAP, trapped.stderr)
            self.assertEqual(trapped.stdout, '')


if __name__ == '__main__':
    unittest.main()
