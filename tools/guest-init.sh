#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
export PATH=/bin
mount -t proc proc /proc
mount -t sysfs sysfs /sys
mount -t devtmpfs devtmpfs /dev
mount -t debugfs debugfs /sys/kernel/debug
fail() { echo "BITOXIN_GUEST_FAIL: $*"; poweroff -f; }
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
echo "$status"
echo "$status" | grep -q '"failed":false' || fail false_failure
# This stops after the freezer stage. It does not validate actual hardware sleep.
echo freezer > /sys/power/pm_test || fail pm_test_unavailable
echo mem > /sys/power/state || fail completed_worker_freeze
cat /sys/kernel/debug/bitoxin/status
echo none > /sys/power/pm_test
rmmod bitoxin_qa || fail finite_unload
echo BITOXIN_GUEST_FINITE_AND_PARKED_FREEZER_PASS
insmod /bitoxin_qa.ko mem_kib=64 threads=2 chunk=17 pause_ms=1 || fail continuous_load
sleep 0.1
cat /sys/kernel/debug/bitoxin/status
echo freezer > /sys/power/pm_test
echo mem > /sys/power/state || fail active_worker_freeze
echo none > /sys/power/pm_test
status=$(cat /sys/kernel/debug/bitoxin/status)
echo "$status"
echo "$status" | grep -q '"failed":false' || fail probe_failure
echo "$status" | grep -q '"pm_prepare":1,"pm_post":1' || fail pm_notifications
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
