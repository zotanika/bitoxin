# SPDX-License-Identifier: GPL-2.0-or-later
ifneq ($(KBUILD_EXTMOD),)
obj-m += bitoxin_qa.o
else
obj-$(CONFIG_BITOXIN_QA) += bitoxin_qa.o
endif
bitoxin_qa-y := bitoxin.o bitoxin_core.o
