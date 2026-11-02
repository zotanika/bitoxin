"""Fault-injection builds: every lane position must decode to itself."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CC = shlex.split(os.environ.get('CC', 'cc'))
FLAGS = shlex.split(os.environ.get('CFLAGS', '-O2 -g')) + [
    '-std=c11', '-Wall', '-Wextra', '-Wpedantic', '-Werror', '-I' + str(ROOT)]


def build(directory, name, defines):
    target = Path(directory) / name
    subprocess.run([*CC, *FLAGS, *defines, str(ROOT / 'tests/test_lane_decode.c'),
                    str(ROOT / 'bitoxin_core.c'), '-o', str(target)], check=True)
    return str(target)


class LaneDecodeTest(unittest.TestCase):
    def check_variant(self, extra):
        with tempfile.TemporaryDirectory(prefix='bitoxin-decode-') as directory:
            count = int(subprocess.run([build(directory, 'count', extra)], text=True,
                                       capture_output=True, check=True).stdout)
            self.assertGreaterEqual(count, 22)
            for k in range(count):
                with self.subTest(position=k, variant=extra):
                    binary = build(directory, f'fault{k}', [*extra, f'-DBX_LANE_FAULT={k}'])
                    result = subprocess.run([binary], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_native_lane(self):
        self.check_variant([])

    def test_portable_lane(self):
        self.check_variant(['-DBX_PORTABLE'])


if __name__ == '__main__':
    unittest.main()
