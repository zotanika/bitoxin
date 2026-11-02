#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
export PATH=/bin
mount -t proc proc /proc
mount -t sysfs sysfs /sys
mount -t devtmpfs devtmpfs /dev
mount -t debugfs debugfs /sys/kernel/debug
fail() { echo "BITOXIN_GUEST_FAIL: $*"; poweroff -f; exit 1; }
worker_values() { echo "$1" | grep -o "\"$2\":[0-9]*" | cut -d: -f2; }
if insmod /bitoxin_qa.ko mem_kib=3; then fail 'invalid size accepted'; fi
echo BITOXIN_GUEST_INVALID_CONFIG_PASS
insmod /bitoxin_qa.ko mem_kib=2 threads=2 passes=2 seed=16383 || fail load
tries=0
while :; do
    status=$(cat /sys/kernel/debug/bitoxin/status) || fail status
    complete=$(echo "$status" | grep -o '"state":"complete"' | wc -l)
    [ "$complete" -eq 2 ] && break
    tries=$((tries + 1))
    [ "$tries" -lt 100 ] || fail completion_timeout
    sleep 0.1
done
echo "BITOXIN_GUEST_STATUS finite_before $status"
echo "$status" | grep -q '"failed":false' || fail false_failure
# This stops after the freezer stage. It does not validate actual hardware sleep.
echo freezer > /sys/power/pm_test || fail pm_test_unavailable
echo mem > /sys/power/state || fail completed_worker_freeze
status=$(cat /sys/kernel/debug/bitoxin/status) || fail parked_status
echo "BITOXIN_GUEST_STATUS finite_after $status"
echo none > /sys/power/pm_test || fail pm_test_reset
rmmod bitoxin_qa || fail finite_unload
echo BITOXIN_GUEST_FINITE_AND_PARKED_FREEZER_PASS
insmod /bitoxin_qa.ko mem_kib=1 threads=2 chunk=17 pause_ms=1 || fail continuous_load
# Start with a completed pass and an in-flight walk for both workers, so a
# restart on thaw cannot look like normal progress from an almost-empty probe.
tries=0
while :; do
    status=$(cat /sys/kernel/debug/bitoxin/status) || fail active_status
    running=$(echo "$status" | grep -o '"state":"running"' | wc -l)
    walking=$(echo "$status" | grep -o '"phase":"walk"' | wc -l)
    if [ "$running" -eq 2 ] && [ "$walking" -eq 2 ] &&
       ! echo "$status" | grep -q '"passes":0\|"walked":0'; then
        break
    fi
    tries=$((tries + 1))
    [ "$tries" -lt 300 ] || fail active_progress_timeout
    sleep 0.1
done
echo "BITOXIN_GUEST_STATUS active_before $status"
set -- $(worker_values "$status" passes)
[ "$#" -eq 2 ] || fail active_worker_count
target0=$(($1 + 1))
target1=$(($2 + 1))
echo freezer > /sys/power/pm_test || fail pm_test_unavailable
echo mem > /sys/power/state || fail active_worker_freeze
echo none > /sys/power/pm_test || fail pm_test_reset
status=$(cat /sys/kernel/debug/bitoxin/status) || fail thawed_status
echo "BITOXIN_GUEST_STATUS active_after $status"
echo "$status" | grep -q '"failed":false' || fail probe_failure
echo "$status" | grep -q '"pm_prepare":1,"pm_post":1' || fail pm_notifications
set -- $(worker_values "$status" operations)
[ "$#" -eq 2 ] || fail thawed_worker_count
thawed0=$1
thawed1=$2
# Complete the retained walk and its byte scan after thaw, exercising the
# original buffer contents as well as proving that both workers resume.
tries=0
while :; do
    status=$(cat /sys/kernel/debug/bitoxin/status) || fail resumed_status
    echo "$status" | grep -q '"failed":false' || fail resumed_probe_failure
    set -- $(worker_values "$status" passes)
    [ "$#" -eq 2 ] || fail resumed_worker_count
    if [ "$1" -ge "$target0" ] && [ "$2" -ge "$target1" ]; then
        set -- $(worker_values "$status" operations)
        [ "$#" -eq 2 ] || fail resumed_worker_count
        [ "$1" -gt "$thawed0" ] && [ "$2" -gt "$thawed1" ] && break
    fi
    tries=$((tries + 1))
    [ "$tries" -lt 300 ] || fail resumed_progress_timeout
    sleep 0.1
done
echo "BITOXIN_GUEST_STATUS active_progress $status"
rmmod bitoxin_qa || fail continuous_unload
[ ! -d /sys/module/bitoxin_qa ] || fail module_still_present
echo BITOXIN_GUEST_ACTIVE_FREEZER_UNLOAD_PASS
# Repeated load/unload exercises worker lifetime and fresh allocation.
for i in 1 2 3 4 5; do
    insmod /bitoxin_qa.ko mem_kib=1 threads=4 freezable=0 || fail reload
    rmmod bitoxin_qa || fail reload_unload
done
echo BITOXIN_GUEST_ALL_PASS
poweroff -f
