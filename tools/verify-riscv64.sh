#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
# Run in tools/Dockerfile.verify-riscv64 with the repository at /src (read-only).
set -eu
work=$(mktemp -d /tmp/bitoxin-verify.XXXXXX)
cp /src/*.c /src/*.h /src/Makefile /src/Kbuild "$work/"
cp -R /src/tests /src/tools "$work/"
cd "$work"
make test
headers=$(find /usr/src -maxdepth 1 -type d -name 'linux-headers-*-riscv64' | sort | tail -n 1)
test -n "$headers"
make module KDIR="$headers" W=1
printf '\nBITOXIN_RISCV64_PASS headers=%s\n' "$headers"
