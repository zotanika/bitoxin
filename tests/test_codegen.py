#!/usr/bin/env python3
"""Check the optimized AArch64 register-result -> byte-store dependency.

A C equality guard can let the optimizer substitute the original input for the
checked result. Track register data flow in the generated walk block, rather
than matching particular allocated registers or source spelling. This checks
architectural data dependence only, not physical fault coverage.
"""
import os
import platform
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
REG = re.compile(r'\b[wx](\d+)\b')


def register_ids(text):
    return {int(n) for n in REG.findall(text)}


def stored_value_depends_on_lane(assembly):
    # The lane ends by copying x14 to a compiler-allocated result register.
    match = re.search(r'^\s*mov\s+(x\d+),\s*x14\s*$', assembly, re.M)
    if not match:
        raise AssertionError('cannot find the register lane output')
    tail = assembly[match.end():]
    end = re.search(r'(?:InlineAsm End|#NO_APP|;\s*0\s+\"\"\s+2)', tail)
    if not end:
        raise AssertionError('cannot find inline-assembly boundary')
    live = register_ids(match.group(1))
    for raw in tail[end.end():].splitlines():
        line = raw.split('//', 1)[0].split(';', 1)[0].strip()
        if not line or line.startswith(('.', '#')) or line.endswith(':'):
            continue
        parts = line.split(None, 1)
        if len(parts) < 2:
            continue
        op, operands = parts
        args = [s.strip() for s in operands.split(',')]
        if op == 'strb':
            return bool(register_ids(args[0]) & live)
        if op == 'b' or op.startswith('b.') or op in {'cmp', 'cmn', 'tst', 'cbz', 'cbnz', 'tbz', 'tbnz'}:
            continue  # Control dependence is not data dependence.
        if op.startswith('st'):
            continue
        dest = register_ids(args[0])
        if op.startswith('ld'):
            if op.startswith('ldp') and len(args) > 1:
                dest |= register_ids(args[1])
            live -= dest
        elif op in {'mov', 'eor', 'and', 'orr', 'bic', 'lsl', 'lsr', 'asr',
                    'ror', 'add', 'sub', 'mul', 'mvn', 'ubfx', 'uxtb', 'sxtb'}:
            depends = bool(register_ids(','.join(args[1:])) & live)
            live -= dest
            if depends:
                live |= dest
        else:
            raise AssertionError('unhandled instruction before byte store: ' + line)
    raise AssertionError('cannot find the byte store after the register lane')


@unittest.skipUnless(platform.machine().lower() in {'aarch64', 'arm64'},
                     'native AArch64 compiler required')
class CodegenTest(unittest.TestCase):
    def test_lane_result_supplies_store_after_successful_check(self):
        compiler = shlex.split(os.environ.get('CC', 'cc'))
        with tempfile.TemporaryDirectory(prefix='bitoxin-codegen-') as directory:
            for optimization in ['-O2', '-O3']:
                with self.subTest(optimization=optimization):
                    target = Path(directory) / 'core.s'
                    subprocess.run([*compiler, '-std=c11', optimization, '-S',
                                    '-I' + str(ROOT), str(ROOT / 'bitoxin_core.c'),
                                    '-o', str(target)], check=True)
                    self.assertTrue(stored_value_depends_on_lane(target.read_text()),
                                    'byte store bypasses the checked register-chain result')


if __name__ == '__main__':
    unittest.main()
