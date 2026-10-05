# BITOXIN QA rewrite design

## Intent and scope
The user ran a loadable Linux module as independent kernel threads alongside QA
sleep/wakeup and stress scenarios. Preserve preemptible data-dependent computation
and persistent test state. Do not convert this into a PM hook or protect the probe
with preemption/IRQ disabling. The reported vendor BSP paging/PM reproduction
is an author recollection without archived measurements in this repository.

Deliver a tested shared probe, a Linux module, a portable user-space runner, QA
application instructions, and a Korean white paper PDF with editable source.
Other repositories are read-only references. No board deployment or PM operation
is performed in this task. `../compuon-dev` is absent; `../compuon` is provisional.

## Design
- Independent buffer per worker; power-of-two 64 B..128 MiB, bounded allocation.
- Maximum-length LFSR visits nonzero bit indices; explicitly visit bit zero last.
- Read expected bit, carry a varied 64-bit token through a GPR dependency chain,
  compare it, then write the opposite bit using its result. No deliberate bad pointer.
- Fixed-count walks; verify LFSR closure and every byte before inverting direction.
- Chunking preserves buffer and cursor; preemption remains possible inside ARM64
  asm when the caller/kernel permit it. Cooperative rescheduling between chunks
  is distinct from asynchronous preemption inside the chain.
- Failures latch: stop, capture type/offset/expected/observed/pass, optional module
  panic after a kernel log. A checker is fallible; no exhaustive coverage claim.
- Kernel workers cooperate with the freezer by default; a documented load-time
  option supports deliberate non-freezable experiments. PM notifications are
  observations, not proof that a requested low-power state was reached.
- Portable C backend validates algorithmic semantics; ARM64 uses correctly
  constrained inline GPR asm, avoiding reserved x18 and floating-point state.
- Immutable module configuration; debugfs snapshots; safe startup/stop/unload.

## Validation and white paper
Host tests and ASan/UBSan cover full cycle, bit zero, inverse pass, chunk resume,
early/late corruption, bad configuration, state errors and latched failures.
Run ARM64 Linux user tests under QEMU and compile the module against real Linux
headers if available. Build success is not board runtime evidence.
White paper separates mathematical properties, measured local checks, historical
recollection, proposed QA experiments and untested target integration. Include
limitations of PM coverage, cache/DRAM reach, swap, security and failure masking.

## Execution decisions
The user's explicit rewrite instruction follows the in-chat design and authorizes
implementation. Work in the clean current checkout on codex/bitoxin-qa-rewrite;
no unnecessary worktree or repeated design approval. Keep changes reviewable.

## Clarification: product applications (2026-10-05)
The user clarified that Compuon/HESM should borrow the concept, not deploy a Linux
module. The application guide and white paper now describe dependent product-state
sequences, independent models and checkpoints at contract-valid lifecycle boundaries.
The existing system probe remains a reference realization; product integration is
proposed, not implemented or validated by the probe's tests. Other repositories
remain read-only.
