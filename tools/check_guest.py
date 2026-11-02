#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Check one guest boot log from tools/verify-guest.sh.

Usage: check_guest.py ARCH MODE LOG. Prints BITOXIN_GUEST_<MODE>_PASS (or
BITOXIN_GUEST_S2IDLE_UNVERIFIED) and exits 0, or raises on the first failure.
"""
import json
import re
import sys

BACKEND = {'arm64': 'aarch64-gpr', 'riscv64': 'riscv64-gpr'}
FAULT_REG = {'arm64': 'x9', 'riscv64': 'a5'}   # lane position 5
TAINT_OOT, TAINT_UNSIGNED = 1 << 12, 1 << 13    # O, E: expected for a test module
# What a worker trap (process context) ends in. arm64 6.1: the worker dies
# and the module unloads. riscv64 6.12 handles every kernel ebreak inside
# irqentry_nmi_enter(), so die() sees in_interrupt() and panics after the
# BITOXIN_TRAP record ("Fatal exception in interrupt").
WORKER_TRAP_ENDS = {'arm64': 'unload', 'riscv64': 'panic'}
PANIC_IN_INTERRUPT = 'Kernel panic - not syncing: Fatal exception in interrupt'


def parse(text):
    status, runner, exits = {}, {}, {}
    for line in text.splitlines():
        line = line.strip('\r')
        for prefix, store in (('BITOXIN_GUEST_STATUS ', status),
                              ('BITOXIN_GUEST_RUNNER ', runner),
                              ('BITOXIN_GUEST_RUNNER_EXIT ', exits)):
            if line.startswith(prefix):
                label, payload = line[len(prefix):].split(' ', 1)
                assert label not in store, f'duplicate {label}'
                store[label] = json.loads(payload)
    return status, runner, exits


def consistent(label, data, arch):
    assert data['schema'] == 2 and data['backend'] == BACKEND[arch], label
    # Hook only (threads=0): no buffer and no workers.
    assert (data['mem_kib'] == 0) == (not data['workers']), (label, data['mem_kib'])
    size = data['mem_kib'] * 1024
    assert [w['id'] for w in data['workers']] == list(range(len(data['workers']))), label
    for w in data['workers']:
        assert w['operations'] == w['passes'] * size * 9 + w['walked'] + w['verified'], (label, w)
        if w['phase'] == 'walk':
            assert 0 <= w['walked'] < size * 8 and w['verified'] == 0, (label, w)
        else:
            assert w['phase'] == 'verify', (label, w)
            assert w['walked'] == size * 8 and 0 <= w['verified'] < size, (label, w)


def clean(label, data):
    assert data['failed'] is False and data['hook']['failed'] is False, label
    for w in data['workers']:
        assert w['state'] in ('running', 'complete'), (label, w)
        assert w['error'] == 'ok' and w['lane_reg'] == '', (label, w)


def check_runner(label, data, rc, arch):
    assert rc == 130, (label, 'runner exit', rc)
    assert data['status'] == 'interrupted' and data['backend'] == BACKEND[arch], (label, data)
    assert data['suspends'] >= 1, (label, data)
    assert len(data['workers']) == 2, (label, data)
    for w in data['workers']:
        assert w['error'] == 'ok' and w['audits'] >= 1 and w['operations'] > 0, (label, w)


def trap_line(text, who):
    pattern = re.compile(r'BITOXIN_TRAP kind=register ' + who + r' .*lane_reg=(\S+)')
    for line in text.splitlines():
        found = pattern.search(line)
        if found:
            return line, found
    raise AssertionError(f'no BITOXIN_TRAP for {who}')


def main_mode(arch, text):
    assert 'BITOXIN_GUEST_FAIL' not in text, 'guest reported a failure'
    assert 'BITOXIN_GUEST_INVALID_CONFIG_PASS' in text
    assert 'BITOXIN_GUEST_TAINT before_trap' in text, 'guest did not reach the worker trap'
    status, runner, exits = parse(text)
    for label, data in status.items():
        consistent(label, data, arch)
        if label not in ('fault_record', 'worker_trap'):
            clean(label, data)
    budget = status['auto_budget']
    assert budget['lane_rounds'] == 257 and budget['hook']['budget'] == 65536 // 257, budget
    fb, fa = status['finite_before'], status['finite_after']
    assert fb['freezable'] is True and fb['workers'] == fa['workers'], 'parked state changed'
    assert fb['pm_prepare'] == 0 and fa['pm_prepare'] == fa['pm_post'] == 1, (fb, fa)
    assert [w['seed'] for w in fb['workers']] == [16383, 1]
    assert all(w['state'] == 'complete' and w['operations'] == 36864 for w in fb['workers'])
    for name in ('active', 'nonfreezable'):
        before, after = status[f'{name}_before'], status[f'{name}_after']
        progress = status[f'{name}_progress']
        assert before['freezable'] is (name == 'active'), name
        assert before['pm_prepare'] == 0 and after['pm_prepare'] == after['pm_post'] == 1, name
        for old, new in zip(before['workers'], progress['workers']):
            assert old['state'] == new['state'] == 'running', (name, old, new)
            assert old['passes'] >= 1 and old['phase'] == 'walk' and old['walked'] > 0, old
            assert new['passes'] > old['passes'] and new['seed'] == old['seed'], (old, new)
            assert new['operations'] > old['operations'], (old, new)
            assert new['boottime_ns'] > old['boottime_ns'], (old, new)
            # Freezable workers audit on thaw (and may again for the PM_POST
            # generation); non-freezable ones at their next chunk after PM_POST.
            assert new['audits'] >= 1, ('no audit after thaw', name, new)
    pc = status['percpu_before']
    assert pc['per_cpu'] is True and [w['home_cpu'] for w in pc['workers']] == [0, 1], pc
    assert all(w['cpu'] == w['home_cpu'] for w in pc['workers']), pc
    off = status['percpu_offline']['workers'][1]
    assert off['cpu'] == 0 and off['cpu_changes'] >= 1, off
    back = status['percpu_online']['workers'][1]
    assert back['cpu'] == 1 and back['cpu_changes'] >= off['cpu_changes'] + 1, back
    for w in status['churn']['workers']:
        assert w['state'] == 'complete', w
        assert (w['passes'], w['churns'], w['churn_failures']) == (4, 3, 0), w
    kib = status['auto']['mem_kib']
    assert kib & (kib - 1) == 0 and 1 <= kib <= 131072 and len(status['auto']['workers']) == 2
    hook = status['hook']
    assert hook['workers'] == [] and hook['mem_kib'] == 0, hook
    assert hook['hook']['calls'] > 0 and hook['hook']['failed'] is False, hook
    assert hook['hook']['budget'] == 4096, hook
    fault = status['fault_record']
    assert fault['failed'] is True and fault['hook']['failed'] is False, fault
    w = fault['workers'][0]
    assert w['state'] == 'failed' and w['error'] == 'register_error', w
    assert w['lane_reg'] == FAULT_REG[arch], w
    assert int(w['lane_expected'], 16) ^ int(w['lane_observed'], 16) == 1, w
    check_runner('freezer', runner['freezer'], exits['freezer'], arch)
    taint = re.search(r'BITOXIN_GUEST_TAINT before_trap (\d+)', text)
    assert taint, 'no taint record before the trap'
    assert int(taint.group(1)) & ~(TAINT_OOT | TAINT_UNSIGNED) == 0, ('tainted', taint.group(1))
    # Worker trap: the first trapping worker prints the record; the other one
    # aborts (or traps too, unprinted, when both reach the fault at once).
    line, found = trap_line(text, r'worker=(\d+)')
    trapped, reg = int(found.group(1)), found.group(2)
    assert reg == FAULT_REG[arch], line
    lane = re.search(r'lane_expected=([0-9a-f]+) lane_observed=([0-9a-f]+)', line)
    assert int(lane.group(1), 16) ^ int(lane.group(2), 16) == 1, line
    assert text.index('BITOXIN_GUEST_TAINT before_trap') < text.index(line), 'trap before taint'
    if WORKER_TRAP_ENDS[arch] == 'panic':
        assert PANIC_IN_INTERRUPT in text[text.index(line):], 'no panic after the worker trap'
        assert 'BITOXIN_GUEST_WORKER_TRAP_UNLOADED' not in text, 'worker trap did not panic'
        print(f'BITOXIN_GUEST_MAIN_PASS arch={arch} worker_trap=panic')
        return
    assert 'BITOXIN_GUEST_ALL_PASS' in text, 'guest did not finish'
    assert text.index(line) < text.index('BITOXIN_GUEST_WORKER_TRAP_UNLOADED'), line
    after = status['worker_trap']
    assert after['failed'] is True and after['trap'] is True, after
    states = [w['state'] for w in after['workers']]
    assert states[trapped] == 'trapped', states
    assert all(s in ('trapped', 'aborted') for s in states), states
    assert all(w['error'] == 'ok' for w in after['workers']), after   # trap mode records nothing
    print(f'BITOXIN_GUEST_MAIN_PASS arch={arch} worker_trap=unload states={",".join(states)}')


def hook_trap_mode(arch, text):
    assert 'BITOXIN_GUEST_FAIL' not in text, 'guest reported a failure'
    line, found = trap_line(text, 'hook site=bx_test_timer')
    assert found.group(1) == FAULT_REG[arch], line
    assert 'Kernel panic' in text[text.index(line):], 'no panic after the trap'
    print(f'BITOXIN_GUEST_HOOK_TRAP_PASS arch={arch}')


def s2idle_mode(arch, text):
    # Unverified, not failed: no wake source, or no wake before the timeout.
    assert 'BITOXIN_GUEST_FAIL' not in text, 'guest reported a failure'
    skip = re.search(r'BITOXIN_GUEST_SKIP s2idle (\S+)', text)
    if skip:
        print(f'BITOXIN_GUEST_S2IDLE_UNVERIFIED arch={arch} reason={skip.group(1)}')
        return
    assert 'BITOXIN_GUEST_S2IDLE_ENTER' in text, 'guest did not reach suspend-to-idle'
    if 'BITOXIN_GUEST_S2IDLE_RESUMED' not in text:
        print(f'BITOXIN_GUEST_S2IDLE_UNVERIFIED arch={arch} reason=no_wake_before_timeout')
        return
    assert 'BITOXIN_GUEST_S2IDLE_DONE' in text, 'guest did not finish'
    wake = re.search(r'BITOXIN_GUEST_S2IDLE_RESUMED wake=(\w+) rc=(\d+) success=(\d+)', text)
    assert wake and wake.group(2) == '0' and int(wake.group(3)) >= 1, 'suspend-to-idle failed'
    status, runner, exits = parse(text)
    module = status['s2idle_module']
    consistent('s2idle_module', module, arch)
    clean('s2idle_module', module)
    assert module['pm_prepare'] >= 1 and module['pm_post'] >= 1, module
    assert all(w['audits'] >= 1 for w in module['workers']), module
    check_runner('s2idle', runner['s2idle'], exits['s2idle'], arch)
    # Suspend time shows only where timekeeping is suspended, i.e. through a
    # cpuidle driver's s2idle state. QEMU virt guests have none, so s2idle is
    # reached (suspend_stats, audits) but its duration reads 0 there.
    slept = runner['s2idle']['suspended_ms']
    assert slept == 0 or slept >= 1000, runner['s2idle']
    note = 'suspend_time=unobservable' if slept == 0 else f'suspended_ms={slept}'
    print(f'BITOXIN_GUEST_S2IDLE_PASS arch={arch} wake={wake.group(1)} {note}')


if __name__ == '__main__':
    arch, mode, path = sys.argv[1:4]
    with open(path, errors='replace') as log:
        content = log.read()
    {'main': main_mode, 'hook_trap': hook_trap_mode, 's2idle': s2idle_mode}[mode](arch, content)
