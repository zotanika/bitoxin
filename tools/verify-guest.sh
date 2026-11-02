#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
# Usage: verify-guest.sh ARCH [ARTIFACTS]. ARCH is arm64 (tools/Dockerfile.guest)
# or riscv64 (tools/Dockerfile.guest-riscv64), with the repository at /src.
# Without ARTIFACTS (arm64 only: the guest image is also a build image), the
# artifacts are built here first. Boots main, hook_trap and s2idle under QEMU
# TCG and checks each console log with tools/check_guest.py.
# BITOXIN_GUEST_MODES selects boots; BITOXIN_GUEST_TIMEOUT overrides the
# per-boot limit in seconds.
set -eu
arch=${1:?usage: verify-guest.sh arm64|riscv64 [ARTIFACTS]}
art=${2:-}
modes=${BITOXIN_GUEST_MODES:-main hook_trap s2idle}
if [ -z "$art" ] && [ "$arch" != arm64 ]; then
    echo "$arch needs ARTIFACTS from tools/build-artifacts.sh in its build container" >&2
    exit 2
fi
work=$(mktemp -d /tmp/bitoxin-guest.XXXXXX)
if [ -z "$art" ]; then
    art="$work/artifacts"
    /src/tools/build-artifacts.sh "$art"
fi
release=$(cat "$art/kernel-release")
case "$arch" in
arm64)
    sysroot=
    kernel=$(find /boot -maxdepth 1 -name 'vmlinuz-*-arm64' | sort | tail -n 1)
    console=ttyAMA0
    limit=600
    qemu="qemu-system-aarch64 -machine virt -cpu cortex-a53"
    ;;
riscv64)
    sysroot=/opt/riscv64
    kernel=$(find /opt/riscv64/boot -maxdepth 1 -name 'vmlinu*-riscv64' | sort | tail -n 1)
    console=ttyS0
    limit=2400
    fw=default
    for f in /usr/lib/riscv64-linux-gnu/opensbi/generic/fw_dynamic.bin \
             /usr/share/qemu/opensbi-riscv64-generic-fw_dynamic.bin; do
        if [ -e "$f" ]; then fw=$f; break; fi
    done
    qemu="qemu-system-riscv64 -machine virt -bios $fw"
    ;;
*) echo "unknown arch $arch" >&2; exit 2 ;;
esac
limit=${BITOXIN_GUEST_TIMEOUT:-$limit}
case "$kernel" in
*"-$release") ;;
*) echo "kernel '$kernel' does not match module release '$release'" >&2; exit 1 ;;
esac
busybox=
for b in "$sysroot/bin/busybox" "$sysroot/usr/bin/busybox"; do
    if [ -x "$b" ]; then busybox=$b; break; fi
done
test -n "$busybox"
root="$work/root"
mkdir -p "$root/bin" "$root/dev" "$root/proc" "$root/sys" "$root/tmp"
cp "$busybox" "$root/bin/busybox"
for applet in sh mount insmod rmmod cat grep cut wc sleep poweroff kill ls tr head dmesg stty; do
    ln -s busybox "$root/bin/$applet"
done
cp "$art/bitoxin_qa.ko" "$art/bitoxin_qa-fault5.ko" "$art/bitoxin_hook_test.ko" \
   "$art/bitoxin-run" "$root/"
# RTC drivers, where they are modules (BusyBox insmod takes no .ko.xz).
for rtc in rtc-pl031 rtc-goldfish; do
    module=$(find "$sysroot/lib/modules/$release" "$sysroot/usr/lib/modules/$release" \
             -name "$rtc.ko*" 2>/dev/null | head -n 1)
    [ -z "$module" ] && continue
    case "$module" in
    *.xz) xz -dc "$module" > "$root/$rtc.ko" ;;
    *) cp "$module" "$root/$rtc.ko" ;;
    esac
done
cp /src/tools/guest-init.sh "$root/init"
chmod +x "$root/init"
(cd "$root" && find . -print | cpio -o -H newc 2>/dev/null | gzip > "$work/initrd.gz")
echo "BITOXIN_GUEST_SETUP arch=$arch kernel=$kernel release=$release timeout=${limit}s"
# One boot. Console input goes only to an s2idle guest without an RTC wake
# source: a byte every 3 s from S2IDLE_ENTER until S2IDLE_RESUMED.
boot() {        # MODE LOG
    fifo="$work/console-in"
    rm -f "$fifo"
    mkfifo "$fifo"
    timeout "$limit" $qemu -smp 2 -m 512M -nographic -nic none -no-reboot \
        -kernel "$kernel" -initrd "$work/initrd.gz" \
        -append "console=$console rdinit=/init panic=-1 loglevel=4 bitoxin_mode=$1" \
        < "$fifo" > "$2" 2>&1 &
    pid=$!
    exec 3> "$fifo"
    while kill -0 "$pid" 2>/dev/null; do
        if grep -q 'BITOXIN_GUEST_S2IDLE_ENTER wake=console' "$2" &&
           ! grep -q 'BITOXIN_GUEST_S2IDLE_RESUMED' "$2"; then
            sleep 3
            (printf w >&3) 2>/dev/null || true
        fi
        sleep 1
    done
    rc=0
    wait "$pid" || rc=$?
    exec 3>&-
}
status=0
for mode in $modes; do
    log="$work/guest-$mode.log"
    start=$(date +%s)
    boot "$mode" "$log"
    cat "$log"
    echo "BITOXIN_GUEST_BOOT arch=$arch mode=$mode seconds=$(($(date +%s) - start)) qemu_rc=$rc"
    python3 /src/tools/check_guest.py "$arch" "$mode" "$log" || status=1
done
exit $status
