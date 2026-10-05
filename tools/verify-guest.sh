#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
set -eu
work=$(mktemp -d /tmp/bitoxin-guest.XXXXXX)
cp /src/bitoxin.c /src/bitoxin_core.c /src/bitoxin_core.h /src/bitoxin_lane.h /src/Makefile /src/Kbuild "$work/"
headers=$(find /usr/src -maxdepth 1 -type d -name 'linux-headers-*-arm64' | sort | tail -n 1)
make -C "$work" module KDIR="$headers" W=1
mkdir -p "$work/root/bin" "$work/root/dev" "$work/root/proc" "$work/root/sys"
cp /bin/busybox "$work/root/bin/busybox"
for applet in sh mount insmod rmmod cat grep wc sleep poweroff; do
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
