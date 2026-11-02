#!/usr/bin/env python3
"""Check the optimized lane-result -> byte-store dependency in generated code.

A C equality guard can let the optimizer substitute the original input for the
checked result. Track register data flow from the lane output to the byte store
in the generated walk block. This checks architectural data dependence only.
The -DBX_SIMD build (what bitoxin-run ships) stores the FP/SIMD lane output,
so there the flow starts at that lane's result instead.
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
A64_COND = ('eq', 'ne', 'cs', 'hs', 'cc', 'lo', 'mi', 'pl', 'vs', 'vc', 'hi', 'ls',
            'ge', 'lt', 'gt', 'le')
CONFIG = {
    'aarch64': dict(lane_end=r'^\s*mov\s+x0,\s*x28\s*$',
                    # Apple clang prints umov x0, v30.d[0] as mov.d x0, v30[0].
                    simd_lane_end=r'^\s*(?:umov|mov)(?:\.d)?\s+x0,\s*v30(?:\.d)?\[0\]\s*$',
                    result='x0',
                    store={'strb', 'sturb', 'stlrb'},
                    exclusive=re.compile(r'stl?x[rp][bh]?$'),
                    other_store=re.compile(r'st'),
                    reg=re.compile(r'\b[wx](\d+)\b'), zero=set(),
                    flow={'mov', 'eor', 'and', 'orr', 'bic', 'lsl', 'lsr', 'asr', 'ror',
                          'add', 'sub', 'mul', 'mvn', 'ubfx', 'uxtb', 'sxtb'},
                    # GCC spells conditional branches without the dot (beq).
                    control={'cmp', 'cmn', 'tst', 'cbz', 'cbnz', 'tbz', 'tbnz',
                             *('b' + c for c in A64_COND)},
                    jump={'b'}, call={'bl', 'blr'}, caller_saved={*range(19), 30}),
    'riscv64': dict(lane_end=r'^\s*mv\s+a0,\s*t6\s*$',
                    simd_lane_end=r'^\s*mv\s+a0,\s*t0\s*$',
                    result='a0', store={'sb'}, abi=True,
                    exclusive=re.compile(r'sc\.[wd](?:\.(?:aq|rl|aqrl))?$'),
                    other_store=re.compile(r's[hwd]$'),
                    reg=re.compile(r'\b(' + '|'.join(sorted(ABI, key=len, reverse=True)) + r')\b'),
                    zero={0},
                    flow={'mv', 'xor', 'xori', 'and', 'andi', 'or', 'ori', 'sll', 'slli',
                          'srl', 'srli', 'add', 'addi', 'addw', 'addiw', 'sub', 'not', 'neg',
                          'zext.b', 'sext.w', 'slliw', 'srliw'},
                    control={'beq', 'bne', 'beqz', 'bnez', 'blt', 'bge', 'bltu', 'bgeu',
                             'bgtu', 'bleu', 'bgt', 'ble'},
                    jump={'j'}, call={'call', 'jal', 'jalr'},
                    caller_saved={1, 5, 6, 7, *range(10, 18), *range(28, 32)}),
}
ASM_END = re.compile(r'(?:InlineAsm End|#NO_APP|;\s*0\s+\"\"\s+2)')
LABEL = re.compile(r'^([^\s:;#]+):')


def register_ids(cfg, text):
    if cfg.get('abi'):  # ABI register names (RISC-V)
        return {ABI[n] for n in cfg['reg'].findall(text)} - cfg['zero']
    return {int(n) for n in cfg['reg'].findall(text)}


def stored_value_depends_on_lane(cfg, assembly):
    """True when every copy of the lane feeds its result into the next byte store."""
    lines = assembly.splitlines()
    labels = {}
    for number, raw in enumerate(lines):
        label = LABEL.match(raw)
        if label:
            labels.setdefault(label.group(1), number)
    copies = [m.end() for m in re.finditer(cfg['lane_end'], assembly, re.M)]
    if not copies:
        raise AssertionError('cannot find the register lane output')
    for offset in copies:
        end = ASM_END.search(assembly, offset)
        if not end:
            raise AssertionError('cannot find inline-assembly boundary')
        if not lane_feeds_store(cfg, lines, labels, assembly.count('\n', 0, end.end()) + 1):
            return False
    return True


def lane_feeds_store(cfg, lines, labels, number):
    live = register_ids(cfg, cfg['result'])
    visited = set()
    while number < len(lines):
        line = lines[number].split('//', 1)[0].split(';', 1)[0].strip()
        number += 1
        if not line or line.startswith(('.', '#')) or line.endswith(':'):
            continue
        parts = line.split(None, 1)
        op, operands = parts[0], parts[1] if len(parts) > 1 else ''
        args = [s.strip() for s in operands.split(',')]
        if op == 'ret':
            raise AssertionError('reached a return before the byte store')
        if op in cfg['store']:
            value = register_ids(cfg, args[0])
            if not value:
                continue  # Constant (zero-register) store, e.g. an error flag.
            return bool(value & live)
        if op in cfg['jump']:
            if args[0] not in labels:
                raise AssertionError('cannot find branch target: ' + line)
            if args[0] in visited:
                raise AssertionError('branch loop before the byte store: ' + line)
            visited.add(args[0])
            number = labels[args[0]] + 1
            continue
        if op in cfg['call']:
            live -= cfg['caller_saved']  # The callee may overwrite them.
            continue
        if op in cfg['control'] or op.startswith('b.'):
            continue  # Control dependence is not data dependence.
        if cfg['exclusive'].match(op):
            live -= register_ids(cfg, args[0])  # Store-exclusive status result.
            continue
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
            for defines, lane_end in [([], 'lane_end'), (['-DBX_SIMD'], 'simd_lane_end')]:
                cfg = dict(CONFIG[ARCH], lane_end=CONFIG[ARCH][lane_end])
                for optimization in ['-O2', '-O3']:
                    with self.subTest(optimization=optimization, defines=defines):
                        target = Path(directory) / 'core.s'
                        subprocess.run([*compiler, '-std=c11', optimization, *defines, '-S',
                                        '-I' + str(ROOT), str(ROOT / 'bitoxin_core.c'),
                                        '-o', str(target)], check=True)
                        self.assertTrue(stored_value_depends_on_lane(cfg, target.read_text()),
                                        'byte store bypasses the checked chain result')


if __name__ == '__main__':
    unittest.main()
