"""Fault-injection builds: every lane position must decode to itself."""
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import platform
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
# Chain length of the native lane per host; other hosts use the portable lane.
NATIVE_LENGTH = {'aarch64': 24, 'arm64': 24, 'riscv64': 22}
SIMD_LENGTH = 30
# Single-bit high-half faults (BX_SIMD_FAULT_HALF): first, middle, last.
HALF_POSITIONS = (0, 14, 29)
CC = shlex.split(os.environ.get('CC', 'cc'))
FLAGS = shlex.split(os.environ.get('CFLAGS', '-O2 -g')) + [
    '-std=c11', '-Wall', '-Wextra', '-Wpedantic', '-Werror', '-I' + str(ROOT)]


def build(directory, name, defines):
    target = Path(directory) / name
    subprocess.run([*CC, *FLAGS, *defines, str(ROOT / 'tests/test_lane_decode.c'),
                    str(ROOT / 'bitoxin_core.c'), '-o', str(target)], check=True)
    return str(target)


def build_and_run(directory, name, defines):
    return subprocess.run([build(directory, name, defines)], text=True, capture_output=True)


def build_and_run_all(directory, jobs):
    """Build and run {name: defines} in parallel (emulated hosts spend minutes
    otherwise). Returns {name: future CompletedProcess}; a failed build raises
    from its own future, inside the caller's subTest."""
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
        return {name: pool.submit(build_and_run, directory, name, defines)
                for name, defines in jobs.items()}


class LaneDecodeTest(unittest.TestCase):
    def assert_ran(self, future):
        result = future.result()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def check_variant(self, extra, length):
        with tempfile.TemporaryDirectory(prefix='bitoxin-decode-') as directory:
            jobs = {'count': extra}
            jobs.update({f'fault{k}': [*extra, f'-DBX_LANE_FAULT={k}'] for k in range(length)})
            results = build_and_run_all(directory, jobs)
            count = int(self.assert_ran(results['count']).stdout)
            self.assertEqual(count, length)
            for k in range(count):
                with self.subTest(position=k, variant=extra):
                    self.assert_ran(results[f'fault{k}'])

    def check_simd(self, extra):
        simd = [*extra, '-DBX_SIMD']
        with tempfile.TemporaryDirectory(prefix='bitoxin-simd-') as directory:
            jobs = {'clean': simd}
            jobs.update({f'simd{p}': [*simd, f'-DBX_SIMD_FAULT={p}']
                         for p in range(SIMD_LENGTH)})
            jobs.update({f'half{p}': [*simd, f'-DBX_SIMD_FAULT={p}', '-DBX_SIMD_FAULT_HALF=1']
                         for p in HALF_POSITIONS})
            results = build_and_run_all(directory, jobs)
            self.assert_ran(results['clean'])
            for p in range(SIMD_LENGTH):
                with self.subTest(position=p, variant=extra):
                    self.assert_ran(results[f'simd{p}'])
            for p in HALF_POSITIONS:
                with self.subTest(position=p, variant=extra, half=True):
                    self.assert_ran(results[f'half{p}'])

    def test_native_lane(self):
        self.check_variant([], NATIVE_LENGTH.get(platform.machine(), 24))

    def test_portable_lane(self):
        self.check_variant(['-DBX_PORTABLE'], 24)

    def test_native_simd_lane(self):
        self.check_simd([])

    def test_portable_simd_lane(self):
        self.check_simd(['-DBX_PORTABLE'])


if __name__ == '__main__':
    unittest.main()
