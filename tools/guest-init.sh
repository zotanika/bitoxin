#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
# Guest /init for tools/verify-guest.sh (BusyBox only). bitoxin_mode=main,
# hook_trap or s2idle on the kernel command line selects the scenarios; the
# host checks the console log with tools/check_guest.py.
export PATH=/bin
mount -t proc proc /proc
mount -t sysfs sysfs /sys
mount -t devtmpfs devtmpfs /dev
mount -t debugfs debugfs /sys/kernel/debug
STATUS=/sys/kernel/debug/bitoxin/status
# Status polls, 0.1 s apart plus process start-up: QEMU TCG (riscv64 above
# all) is slow, so the limits allow minutes rather than weaker assertions.
POLL=3000
fail() { echo "BITOXIN_GUEST_FAIL: $*"; poweroff -f; exit 1; }
snap() { last=$(cat $STATUS) || fail "status_$1"; echo "BITOXIN_GUEST_STATUS $1 $last"; }
count() { echo "$1" | grep -o "$2" | wc -l; }
values() { echo "$1" | grep -o "\"$2\":[0-9-]*" | cut -d: -f2; }
failed() {      # JSON true|false: the top-level flag (the hook object has its own)
    echo "$1" | grep -q "^{\"schema\":2,\"backend\":\"[a-z0-9-]*\",\"failed\":$2,"
}
load() { label=$1; shift; insmod "$@" || fail "${label}_load"; }
unload() { rmmod "$1" || fail "unload_$1"; }
refused() { label=$1; shift; if insmod "$@"; then fail "${label}_accepted"; fi; }
sleep_state() { if grep -qw mem /sys/power/state; then echo mem; else echo freeze; fi; }
# pm_test=freezer stops after the freezer stage (and waits 5 s there): user
# space and freezable kthreads freeze, no device or hardware sleep is exercised.
freeze_cycle() {
    echo freezer > /sys/power/pm_test || fail pm_test_unavailable
    sleep_state > /sys/power/state || fail "freeze_$1"
    echo none > /sys/power/pm_test || fail pm_test_reset
}
wait_for() {    # LABEL PATTERN COUNT
    tries=0
    while :; do
        s=$(cat $STATUS) || fail "status_$1"
        [ "$(count "$s" "$2")" -ge "$3" ] && break
        tries=$((tries + 1)); [ "$tries" -lt $POLL ] || fail "$1_timeout"
        sleep 0.1
    done
}
wait_active() { # LABEL: both workers running, past one pass, mid-walk
    tries=0
    while :; do
        s=$(cat $STATUS) || fail "status_$1"
        if [ "$(count "$s" '"state":"running"')" -eq 2 ] &&
           [ "$(count "$s" '"phase":"walk"')" -eq 2 ] &&
           ! echo "$s" | grep -q '"passes":0\|"walked":0'; then
            break
        fi
        tries=$((tries + 1)); [ "$tries" -lt $POLL ] || fail "$1_active_timeout"
        sleep 0.1
    done
}
wait_passes() { # LABEL BEFORE_JSON: each worker finishes one more pass
    label=$1
    set -- $(values "$2" passes)
    [ "$#" -eq 2 ] || fail "${label}_worker_count"
    t0=$(($1 + 1)); t1=$(($2 + 1))
    tries=0
    while :; do
        s=$(cat $STATUS) || fail "status_$label"
        failed "$s" false || fail "${label}_probe_failure"
        set -- $(values "$s" passes)
        [ "$1" -ge "$t0" ] && [ "$2" -ge "$t1" ] && break
        tries=$((tries + 1)); [ "$tries" -lt $POLL ] || fail "${label}_progress_timeout"
        sleep 0.1
    done
}
wait_home() {   # worker 1 back on CPU 1 (it re-pins itself after its next chunk)
    tries=0
    while :; do
        s=$(cat $STATUS) || fail status_percpu
        set -- $(values "$s" cpu)
        [ "$2" = 1 ] && break
        tries=$((tries + 1)); [ "$tries" -lt $POLL ] || fail percpu_return_timeout
        sleep 0.1
    done
}
run_runner() {  # LABEL ACTION: runner with live chain registers across ACTION
    /bitoxin-run --threads 2 --kib 64 --passes 0 --lane-rounds 256 > /tmp/run.json &
    pid=$!
    sleep 1
    $2
    sleep 1
    kill -TERM $pid
    wait $pid
    echo "BITOXIN_GUEST_RUNNER_EXIT $1 $?"
    echo "BITOXIN_GUEST_RUNNER $1 $(cat /tmp/run.json)"
}

main() {
    refused invalid_size /bitoxin_qa.ko mem_kib=3
    refused hook_budget_bound /bitoxin_qa.ko threads=0 lane_rounds=257 hook_budget=256
    refused chunk_bound /bitoxin_qa.ko threads=0 lane_rounds=4097
    load auto_budget /bitoxin_qa.ko threads=0 lane_rounds=257
    snap auto_budget
    unload bitoxin_qa
    echo BITOXIN_GUEST_INVALID_CONFIG_PASS

    load finite /bitoxin_qa.ko mem_kib=2 threads=2 passes=2 seed=16383 freezable=1
    wait_for finite '"state":"complete"' 2
    snap finite_before
    freeze_cycle finite
    snap finite_after
    unload bitoxin_qa

    load active /bitoxin_qa.ko mem_kib=1 threads=2 chunk=17 pause_ms=1 freezable=1
    wait_active active
    snap active_before; before=$last
    freeze_cycle active
    snap active_after
    wait_passes active "$before"
    snap active_progress
    unload bitoxin_qa

    load nonfreezable /bitoxin_qa.ko mem_kib=1 threads=2 chunk=17 pause_ms=1
    wait_active nonfreezable
    snap nonfreezable_before; before=$last
    freeze_cycle nonfreezable
    snap nonfreezable_after
    wait_passes nonfreezable "$before"
    snap nonfreezable_progress
    unload bitoxin_qa

    load percpu /bitoxin_qa.ko mem_kib=1 per_cpu=1 chunk=17 pause_ms=1
    wait_for percpu '"state":"running"' 2
    sleep 0.5
    snap percpu_before
    echo 0 > /sys/devices/system/cpu/cpu1/online || fail cpu1_offline
    sleep 1
    snap percpu_offline
    echo 1 > /sys/devices/system/cpu/cpu1/online || fail cpu1_online
    wait_home
    snap percpu_online
    unload bitoxin_qa

    load churn /bitoxin_qa.ko mem_kib=1 threads=2 passes=4 churn=1
    wait_for churn '"state":"complete"' 2
    snap churn
    unload bitoxin_qa

    load auto /bitoxin_qa.ko mem_kib=0 threads=2 pause_ms=1000
    snap auto
    unload bitoxin_qa

    load hook /bitoxin_qa.ko threads=0
    load hook_test /bitoxin_hook_test.ko
    sleep 1
    snap hook
    unload bitoxin_hook_test
    unload bitoxin_qa

    load fault /bitoxin_qa-fault5.ko threads=1 mem_kib=1
    wait_for fault '"state":"failed"' 1
    snap fault_record
    unload bitoxin_qa

    run_runner freezer "freeze_cycle runner"

    # Last: the worker oops taints the kernel (D; on arm64 also W from a
    # context-tracking warning) and on riscv64 6.12 panics it (kernel ebreak
    # runs in NMI context). Before it, only O and E (out-of-tree, unsigned).
    echo "BITOXIN_GUEST_TAINT before_trap $(cat /proc/sys/kernel/tainted)"
    load trap /bitoxin_qa-fault5.ko threads=2 mem_kib=1 trap=1
    tries=0
    while :; do     # every worker trapped or aborted
        s=$(cat $STATUS) || fail status_trap
        failed "$s" true &&
            [ "$(count "$s" '"state":"trapped"\|"state":"aborted"')" -eq 2 ] && break
        tries=$((tries + 1)); [ "$tries" -lt $POLL ] || fail trap_timeout
        sleep 0.1
    done
    dmesg -n 1      # the oops made the console verbose: keep status lines whole
    snap worker_trap
    unload bitoxin_qa
    echo BITOXIN_GUEST_WORKER_TRAP_UNLOADED
    echo BITOXIN_GUEST_ALL_PASS
    poweroff -f
}

hook_trap() {   # a timer-context trap must print BITOXIN_TRAP, then panic
    load hook_trap /bitoxin_qa-fault5.ko threads=0 trap=1
    load hook_trap_test /bitoxin_hook_test.ko timer_only=1
    sleep 30
    fail hook_trap_no_panic
}

s2idle() {      # real suspend-to-idle, woken by the RTC alarm or by console input
    for m in /rtc-pl031.ko /rtc-goldfish.ko; do [ -e "$m" ] && insmod "$m"; done
    skip() { echo "BITOXIN_GUEST_SKIP s2idle $1"; poweroff -f; exit 0; }
    grep -qw freeze /sys/power/state || skip no_freeze_state
    rtc=/sys/class/rtc/rtc0
    tty=$(tr ' ' '\n' < /proc/cmdline | grep '^console=' | cut -d= -f2)
    tty=/sys/class/tty/$tty/power/wakeup
    if [ -e $rtc/wakealarm ]; then
        wake=rtc
        [ -w $rtc/device/power/wakeup ] && echo enabled > $rtc/device/power/wakeup
    elif [ -e "$tty" ]; then
        # No RTC wake source (riscv64 virt: the goldfish RTC cannot wake). The
        # host sends console bytes once it sees S2IDLE_ENTER; with echo off
        # they never reach the log.
        wake=console
        echo enabled > "$tty" || fail console_wakeup
        stty -echo || fail console_echo
    else
        skip no_wake_source
    fi
    echo none > /sys/power/pm_test || fail pm_test_reset
    load s2idle /bitoxin_qa.ko mem_kib=1 threads=2 chunk=17 pause_ms=1
    run_runner s2idle s2idle_wake
    snap s2idle_module
    unload bitoxin_qa
    echo BITOXIN_GUEST_S2IDLE_DONE
    poweroff -f
}
s2idle_wake() { # BusyBox has no rtcwake everywhere: set the alarm through sysfs
    if [ $wake = rtc ]; then
        echo 0 > $rtc/wakealarm
        echo +3 > $rtc/wakealarm || fail s2idle_alarm
    fi
    echo "BITOXIN_GUEST_S2IDLE_ENTER wake=$wake"
    echo freeze > /sys/power/state
    rc=$?
    echo "BITOXIN_GUEST_S2IDLE_RESUMED wake=$wake rc=$rc success=$(cat /sys/power/suspend_stats/success) fail=$(cat /sys/power/suspend_stats/fail)"
}

case "$(cat /proc/cmdline)" in
*bitoxin_mode=hook_trap*) hook_trap ;;
*bitoxin_mode=s2idle*) s2idle ;;
*) main ;;
esac
