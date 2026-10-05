# SPDX-License-Identifier: GPL-2.0-or-later
CC ?= cc
PYTHON ?= python3
BUILD ?= build
CFLAGS ?= -O2 -g
WARN = -std=c11 -Wall -Wextra -Wpedantic -Werror
KDIR ?= /lib/modules/$(shell uname -r)/build
.PHONY: all test sanitize module clean
all: $(BUILD)/bitoxin-run
$(BUILD):
	mkdir -p $@
$(BUILD)/bitoxin-run: tools/bitoxin-run.c bitoxin_core.c bitoxin_core.h bitoxin_lane.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tools/bitoxin-run.c bitoxin_core.c -pthread -o $@
$(BUILD)/test-core: tests/test_core.c bitoxin_core.c bitoxin_core.h bitoxin_lane.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_core.c bitoxin_core.c -o $@
$(BUILD)/test-portable: tests/test_core.c bitoxin_core.c bitoxin_core.h bitoxin_lane.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -DBX_PORTABLE -I. tests/test_core.c bitoxin_core.c -o $@
$(BUILD)/test-lfsr: tests/test_lfsr.c bitoxin_core.c bitoxin_core.h bitoxin_lane.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_lfsr.c bitoxin_core.c -o $@
$(BUILD)/test-lane-fault: tests/test_lane_fault.c bitoxin_core.c bitoxin_core.h | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -I. tests/test_lane_fault.c -o $@
test: $(BUILD)/test-core $(BUILD)/test-portable $(BUILD)/test-lfsr $(BUILD)/test-lane-fault $(BUILD)/bitoxin-run
	$(BUILD)/test-core
	$(BUILD)/test-portable
	$(BUILD)/test-lfsr
	$(BUILD)/test-lane-fault
	BITOXIN_RUNNER=$(abspath $(BUILD)/bitoxin-run) $(PYTHON) tests/test_runner.py
sanitize:
	$(MAKE) BUILD=$(BUILD)/sanitize CFLAGS='-O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer' test
module:
	$(MAKE) -C $(KDIR) M=$(CURDIR) modules
clean:
	rm -rf $(BUILD)
