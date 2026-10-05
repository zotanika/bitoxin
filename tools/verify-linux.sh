#!/bin/sh
set -eu
# Run in tools/Dockerfile.verify with this repository mounted read-only at /src.
mkdir -p /tmp/bitoxin-verify
cp /src/bitoxin.c /src/bitoxin_core.c /src/bitoxin_core.h /src/bitoxin_lane.h /src/Makefile /src/Kbuild /tmp/bitoxin-verify/
cp -R /src/tests /src/tools /tmp/bitoxin-verify/
cd /tmp/bitoxin-verify
make test
make sanitize
headers=$(find /usr/src -maxdepth 1 -type d -name 'linux-headers-*-arm64' | sort | tail -n 1)
test -n "$headers"
make module KDIR="$headers" W=1
printf '\nBITOXIN_LINUX_BUILD_PASS headers=%s\n' "$headers"
