#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
# Usage: build-artifacts.sh OUTDIR. Runs in a build container of the target
# architecture with the repository at /src. Builds the module, a fault-injected
# module (lane position 5), the hook test module and a static runner.
set -eu
out=$1
mkdir -p "$out"
work=$(mktemp -d /tmp/bitoxin-artifacts.XXXXXX)
cp /src/*.c /src/*.h /src/Makefile /src/Kbuild "$work/"
cp -R /src/tests /src/tools "$work/"
headers=$(find /usr/src -maxdepth 1 -type d -name "linux-headers-*-$(dpkg --print-architecture)" | sort | tail -n 1)
test -n "$headers"
make -C "$headers" M="$work" W=1 ccflags-y=-DBX_LANE_FAULT=5 modules
cp "$work/bitoxin_qa.ko" "$out/bitoxin_qa-fault5.ko"
make -C "$headers" M="$work" clean
make -C "$headers" M="$work" W=1 modules
cp "$work/bitoxin_qa.ko" "$out/"
make -C "$headers" M="$work/tests/kmod" KBUILD_EXTRA_SYMBOLS="$work/Module.symvers" W=1 modules
cp "$work/tests/kmod/bitoxin_hook_test.ko" "$out/"
cc -O2 -std=c11 -Wall -Wextra -Wpedantic -Werror -static -DBX_SIMD -I"$work" -I"$work/tools" \
    "$work/tools/bitoxin-run.c" "$work/bitoxin_core.c" -pthread -o "$out/bitoxin-run"
basename "$headers" | sed 's/^linux-headers-//' > "$out/kernel-release"
rm -rf "$work"
echo "BITOXIN_ARTIFACTS $(cat "$out/kernel-release")"
