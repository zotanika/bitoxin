#!/usr/bin/env python3
"""Check the optimized lane-result -> byte-store dependency in generated code.

A C equality guard can let the optimizer substitute the original input for the
checked result. Track register data flow from the lane output to the byte store
in the generated walk block. This checks architectural data dependence only.
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
ARCH = {'arm64': 'aarch64'}.get(platform.machine().lower(), platform.machine().lower())
ABI = {'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4, 't0': 5, 't1': 6, 't2': 7,
       's0': 8, 'fp': 8, 's1': 9, **{f'a{i}': 10 + i for i in range(8)},
       **{f's{i}': 16 + i for i in range(2, 12)}, **{f't{i}': 25 + i for i in range(3, 7)}}
CONFIG = {
    'aarch64': dict(lane_end=r'^\s*mov\s+x0,\s*x28\s*$', store='strb',
                    other_store=re.compile(r'st'),
                    reg=re.compile(r'\b[wx](\d+)\b'), zero=set(),
                    flow={'mov', 'eor', 'and', 'orr', 'bic', 'lsl', 'lsr', 'asr', 'ror',
                          'add', 'sub', 'mul', 'mvn', 'ubfx', 'uxtb', 'sxtb'},
                    control={'cmp', 'cmn', 'tst', 'cbz', 'cbnz', 'tbz', 'tbnz', 'b', 'bl',
                             # GCC spells conditional branches without the dot (beq).
                             *('b' + c for c in ('eq', 'ne', 'cs', 'hs', 'cc', 'lo', 'mi',
                                                 'pl', 'vs', 'vc', 'hi', 'ls', 'ge', 'lt',
                                                 'gt', 'le'))}),
    'riscv64': dict(lane_end=r'^\s*mv\s+a0,\s*t6\s*$', store='sb',
                    other_store=re.compile(r'(?:s[hwd]|sc\.[wd])$'),
                    reg=re.compile(r'\b(' + '|'.join(sorted(ABI, key=len, reverse=True)) + r')\b'),
                    zero={0},
                    flow={'mv', 'xor', 'xori', 'and', 'andi', 'or', 'ori', 'sll', 'slli',
                          'srl', 'srli', 'add', 'addi', 'addw', 'addiw', 'sub', 'not', 'neg',
                          'zext.b', 'sext.w', 'slliw', 'srliw'},
                    control={'beq', 'bne', 'beqz', 'bnez', 'blt', 'bge', 'bltu', 'bgeu',
                             'bgtu', 'bleu', 'bgt', 'ble', 'j', 'call', 'jal'}),
}


def register_ids(cfg, text):
    if cfg is CONFIG['riscv64']:
        return {ABI[n] for n in cfg['reg'].findall(text)} - cfg['zero']
    return {int(n) for n in cfg['reg'].findall(text)}


def stored_value_depends_on_lane(cfg, assembly):
    match = re.search(cfg['lane_end'], assembly, re.M)
    if not match:
        raise AssertionError('cannot find the register lane output')
    tail = assembly[match.end():]
    end = re.search(r'(?:InlineAsm End|#NO_APP|;\s*0\s+\"\"\s+2)', tail)
    if not end:
        raise AssertionError('cannot find inline-assembly boundary')
    live = register_ids(cfg, 'x0' if ARCH == 'aarch64' else 'a0')
    for raw in tail[end.end():].splitlines():
        line = raw.split('//', 1)[0].split(';', 1)[0].strip()
        if not line or line.startswith(('.', '#')) or line.endswith(':'):
            continue
        parts = line.split(None, 1)
        op, operands = parts[0], parts[1] if len(parts) > 1 else ''
        args = [s.strip() for s in operands.split(',')]
        if op == 'ret':
            raise AssertionError('reached a return before the byte store')
        if op == cfg['store']:
            value = register_ids(cfg, args[0])
            if not value:
                continue  # Constant (zero-register) store, e.g. an error flag.
            return bool(value & live)
        if op in cfg['control'] or op.startswith('b.'):
            continue  # Control dependence is not data dependence.
        if cfg['other_store'].match(op):
            continue  # Other stores; s-prefixed ALU ops (subs, srai) are not skipped.
        dest = register_ids(cfg, args[0])
        if op.startswith('ldp'):
            dest |= register_ids(cfg, args[1])  # Load pair writes two registers.
        if op.startswith(('ld', 'l')) and op not in cfg['flow']:
            live -= dest
        elif op in cfg['flow']:
            depends = bool(register_ids(cfg, ','.join(args[1:])) & live)
            live -= dest
            if depends:
                live |= dest
        else:
            raise AssertionError('unhandled instruction before byte store: ' + line)
    raise AssertionError('cannot find the byte store after the register lane')


@unittest.skipUnless(ARCH in CONFIG, 'native AArch64 or RISC-V compiler required')
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
                    self.assertTrue(stored_value_depends_on_lane(CONFIG[ARCH], target.read_text()),
                                    'byte store bypasses the checked register-chain result')


if __name__ == '__main__':
    unittest.main()
