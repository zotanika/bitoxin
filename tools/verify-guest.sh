#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
set -eu
work=$(mktemp -d /tmp/bitoxin-guest.XXXXXX)
cp /src/*.c /src/*.h /src/Makefile /src/Kbuild "$work/"
headers=$(find /usr/src -maxdepth 1 -type d -name 'linux-headers-*-arm64' | sort | tail -n 1)
make -C "$work" module KDIR="$headers" W=1
mkdir -p "$work/root/bin" "$work/root/dev" "$work/root/proc" "$work/root/sys"
cp /bin/busybox "$work/root/bin/busybox"
for applet in sh mount insmod rmmod cat grep cut wc sleep poweroff; do
    ln -s busybox "$work/root/bin/$applet"
done
cp "$work/bitoxin_qa.ko" "$work/root/"
cp /src/tools/guest-init.sh "$work/root/init"
chmod +x "$work/root/init"
(cd "$work/root" && find . -print | cpio -o -H newc 2>/dev/null | gzip > "$work/initrd.gz")
kernel=$(find /boot -maxdepth 1 -name 'vmlinuz-*-arm64' | sort | tail -n 1)
timeout 120 qemu-system-aarch64 -machine virt -cpu cortex-a53 -smp 2 -m 256M \
    -nographic -nic none -no-reboot -kernel "$kernel" -initrd "$work/initrd.gz" \
    -append 'console=ttyAMA0 rdinit=/init panic=-1 loglevel=4' > "$work/guest.log" 2>&1 || {
    cat "$work/guest.log"; exit 1;
}
cat "$work/guest.log"
grep -q BITOXIN_GUEST_ALL_PASS "$work/guest.log"
! grep -q BITOXIN_GUEST_FAIL "$work/guest.log"
# Parse the actual debugfs JSON on the host; the initramfs needs only BusyBox.
python3 - "$work/guest.log" <<'PY'
import json
import sys

snapshots = {}
prefix = "BITOXIN_GUEST_STATUS "
with open(sys.argv[1]) as log:
    for line in log:
        if line.startswith(prefix):
            label, payload = line[len(prefix):].split(" ", 1)
            assert label not in snapshots, f"duplicate snapshot: {label}"
            snapshots[label] = json.loads(payload)

assert set(snapshots) == {
    "finite_before", "finite_after", "active_before", "active_after", "active_progress"
}, f"missing or unexpected snapshots: {set(snapshots)}"

for label, status in snapshots.items():
    assert status["schema"] == 1 and status["backend"] == "aarch64-gpr", label
    assert status["failed"] is False and status["freezable"] is True, label
    assert len(status["workers"]) == 2, label
    assert [worker["id"] for worker in status["workers"]] == [0, 1], label
    expected_pm = 0 if label.endswith("before") else 1
    assert status["pm_prepare"] == status["pm_post"] == expected_pm, label
    size = status["mem_kib"] * 1024
    for worker in status["workers"]:
        assert worker["error"] == "ok", (label, worker)
        assert worker["operations"] == (
            worker["passes"] * size * 9 + worker["walked"] + worker["verified"]
        ), (label, worker)
        if worker["phase"] == "walk":
            assert 0 <= worker["walked"] < size * 8 and worker["verified"] == 0, (label, worker)
        else:
            assert worker["phase"] == "verify", (label, worker)
            assert worker["walked"] == size * 8 and 0 <= worker["verified"] < size, (label, worker)

finite = snapshots["finite_before"]
assert finite["workers"] == snapshots["finite_after"]["workers"], "parked state changed across freeze"
assert [worker["seed"] for worker in finite["workers"]] == [16383, 1], "seed wrap"
for worker in finite["workers"]:
    assert worker["state"] == "complete" and worker["passes"] == 2, worker
    assert worker["operations"] == 36864, worker

before = snapshots["active_before"]["workers"]
after = snapshots["active_after"]["workers"]
progress = snapshots["active_progress"]["workers"]
for old, thawed, advanced in zip(before, after, progress):
    assert old["passes"] >= 1 and old["phase"] == "walk" and old["walked"] > 0, old
    assert old["state"] == thawed["state"] == advanced["state"] == "running", (old, thawed, advanced)
    assert old["seed"] == thawed["seed"] == advanced["seed"], (old, thawed, advanced)
    assert old["operations"] <= thawed["operations"] < advanced["operations"], "progress lost across freeze"
    assert old["boottime_ns"] <= thawed["boottime_ns"] <= advanced["boottime_ns"], "snapshot time regressed"
    assert advanced["passes"] > old["passes"], "retained pass did not finish after thaw"

print("BITOXIN_GUEST_STATE_RETENTION_PASS")
PY
