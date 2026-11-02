# SPDX-License-Identifier: GPL-2.0-or-later
CC ?= cc
PYTHON ?= python3
BUILD ?= build
CFLAGS ?= -O2 -g
WARN = -std=c11 -Wall -Wextra -Wpedantic -Werror
KDIR ?= /lib/modules/$(shell uname -r)/build
LANE = bitoxin_core.h bitoxin_lane.h $(wildcard lane_*.h)
.PHONY: all test sanitize module clean
all: $(BUILD)/bitoxin-run
$(BUILD):
	mkdir -p $@
$(BUILD)/bitoxin-run: tools/bitoxin-run.c tools/bx_suspend.h bitoxin_core.c bitoxin_simd.h $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -DBX_SIMD -I. -Itools tools/bitoxin-run.c bitoxin_core.c -pthread -o $@
$(BUILD)/test-core: tests/test_core.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_core.c bitoxin_core.c -o $@
$(BUILD)/test-portable: tests/test_core.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -DBX_PORTABLE -I. tests/test_core.c bitoxin_core.c -o $@
$(BUILD)/test-lfsr: tests/test_lfsr.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_lfsr.c bitoxin_core.c -o $@
$(BUILD)/test-audit: tests/test_audit.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_audit.c bitoxin_core.c -o $@
$(BUILD)/test-midrun: tests/test_midrun.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_midrun.c -o $@
$(BUILD)/test-trap: tests/test_trap.c bitoxin_core.c $(LANE) | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_trap.c bitoxin_core.c -o $@
$(BUILD)/test-suspend: tests/test_suspend.c tools/bx_suspend.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) tests/test_suspend.c -o $@
test: $(BUILD)/test-core $(BUILD)/test-portable $(BUILD)/test-lfsr $(BUILD)/test-midrun $(BUILD)/test-audit $(BUILD)/test-trap $(BUILD)/test-suspend $(BUILD)/bitoxin-run
	$(BUILD)/test-core
	$(BUILD)/test-portable
	$(BUILD)/test-lfsr
	$(BUILD)/test-midrun
	$(BUILD)/test-audit
	$(BUILD)/test-trap
	$(BUILD)/test-suspend
	BITOXIN_RUNNER=$(abspath $(BUILD)/bitoxin-run) $(PYTHON) tests/test_runner.py
	CC="$(CC)" $(PYTHON) tests/test_codegen.py
	CC="$(CC)" CFLAGS="$(CFLAGS)" $(PYTHON) tests/test_lane_decode.py
	CC="$(CC)" CFLAGS="$(CFLAGS)" $(PYTHON) tests/test_trap.py
sanitize:
	$(MAKE) BUILD=$(BUILD)/sanitize CFLAGS='-O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer' test
module:
	$(MAKE) -C $(KDIR) M=$(CURDIR) modules
clean:
	rm -rf $(BUILD)
