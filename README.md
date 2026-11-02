BITOXIN module
==============

A preemptible state-integrity probe for Linux. Kernel threads keep a known
computation and its memory alive while QA workloads or sleep/wakeup scenarios
run alongside, and report the first corruption they observe.

```sh
make && make test                        # host runner and tests
make module KDIR=/path/to/kernel/build   # bitoxin_qa.ko

sudo insmod bitoxin_qa.ko threads=2 mem_kib=1024
sudo cat /sys/kernel/debug/bitoxin/status
sudo rmmod bitoxin_qa
```

`modinfo bitoxin_qa.ko` lists the module parameters, and
`build/bitoxin-run --help` describes the user-space runner.

License: GPL-2.0-or-later
