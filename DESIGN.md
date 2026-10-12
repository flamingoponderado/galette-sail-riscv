# Design

## Two models

- **L3 (Galette).** `Galette.HOL.examples.l3_machine_code.riscv.model.riscv`
  is a port of HOL4's L3 RISC-V model. Its step is `riscv_step.NextRISCV`.
  `riscv_target` (in `cakeml/compiler/encoders/riscv`) packages it as an
  `asmProps.target`. Galette's machine semantics `targetSem.machine_sem`, and
  hence the Pancake theorem `pan_to_targetProof.pan_to_target_compile_semantics`,
  are stated over `machine_config`s built from such a target.
- **Sail.** `sail/rv64d.v` and `sail/rv64d_types.v` are generated from
  sail-riscv `6136f843` (master) by Sail at git `2ba32128` (master). That
  Sail commit includes rems-project/sail#1757, the fix for "Unsupported
  register type", which is not yet in the 0.20.3 release. In
  this model every function lives in `M = Defs.monad exception`, a free monad
  (`iMon`) over the concurrency-interface-V2 outcomes `RegRead`, `RegWrite`,
  `MemRead`, `MemWrite`, the announce events, `Choose`, `GenericFail`, and so
  on. The top-level step is `try_step : Z -> bool -> M bool`.

## Layers

1. **`Interp.v`: sequential interpreter.** `SailState` is a register file
   (`forall r : register, reg_type r`) plus a byte memory. `run : iMon A ->
   SailState -> option (A * SailState)` handles the outcomes as follows:
   - `RegRead` and `RegWrite` act on the register file.
   - `MemRead` and `MemWrite` act on the byte memory, one byte at a time,
     with tags ignored (no tag memory).
   - The announce events, `Barrier`, `CacheOp`, `TlbOp`, `TakeException`,
     `ReturnException`, `TranslationStart`/`End`, `CycleCount` and `Message`
     are no-ops.
   - `GetCycleCount` returns the `mcycle` register.
   - `Choose`, `Discard`, `ExtraOutcome` and `GenericFail` make `run` return
     `None`; this is a "stuck" step, like L3's exception.

   Recursion is structural, because `iMon` is an inductive type. The
   interpreter is ours: it fixes a *sequential* reading of the concurrency
   interface. That choice is part of the trusted base and is documented in
   the README.
2. **`SailTarget.v`.** `sail_step s := run (try_step 0 false) s`, packaged as
   an `asmProps.target` (`next`, `get_pc`, `get_reg`, `get_byte`,
   `state_ok`, ...) over `option`-free states (with an `ok` flag, as in
   riscv-im-compare), so that Galette's `machine_sem` can run on Sail.
3. **`Relation.v`.** `Rel ms s` relates an L3 state to a Sail state:
   - the PCs are equal;
   - the integer registers `x1`..`x31` are equal;
   - the memories agree on the program's memory domain;
   - the L3 `ok` flag matches the Sail `ok` flag.

   Sail-only invariants (`SailInv s`):
   - `cur_privilege = Machine` and `hart_state = HART_ACTIVE`;
   - interrupts globally disabled (`mstatus.MIE = 0`), so `try_step` never
     takes an interrupt;
   - `mstatus.MPRV = 0`;
   - PMP entries off, so M-mode accesses are allowed;
   - accessed addresses lie in the baked-in PMA memory regions.

   The invariants are preserved by the steps we simulate.
4. **`StepSim.v`.** One lemma per instruction kind emitted by Galette's
   encoder, covering 37 kinds:
   - ALU and immediate: `ADDI ANDI ORI XORI LUI AUIPC ADD SUB AND OR XOR SLTU`
   - shifts: `SLL SRL SRA SLLI SRLI SRAI`
   - multiply and divide: `MUL MULHU DIV`
   - loads and stores: `LD LWU LHU LBU SD SW SH SB`
   - branches: `BEQ BNE BLT BGE BLTU BGEU`
   - jumps: `JAL JALR`

   Each lemma says: if `Rel ms s`, `SailInv s`, the bytes at the PC encode
   that instruction, and the memory access is safe, then `NextRISCV ms` and
   `sail_step s` are related again. Proof shape:
   - decode: Sail's `encdec_backwards` on the encoded word gives the expected AST;
   - execute: symbolic evaluation of `run` through `execute_*`;
   - the `try_step` prologue and epilogue: `update_mip` changes nothing,
     because of `SailInv`; `minstret` and `mcycle` are not in `Rel`.
5. **`Simulation.v`.** A generic theorem: two `machine_config`s whose
   targets are related by a relation that is preserved by `next` on guarded
   steps, and by the FFI/interference oracles, have the same `machine_sem`
   behaviours. This is the Rocq counterpart of riscv-im-compare's
   `machineSem_sim`.
6. **`Main.v`.** Transfer of `pan_to_target_compile_semantics` to the Sail
   machine configuration, with the side conditions as explicit premises.

## Axioms of the generated model

sail-riscv `6136f843` includes #1994, which binds truncating division and
remainder to `tdiv_int`/`tmod_int`. So `DIV`, and the alignment checks
(`is_aligned_vaddr` and friends), are fully defined. At older commits they
were uninterpreted `Axiom`s: concrete evaluation got stuck and proofs were
impossible.

The model still declares 88 `Axiom`s: the floating-point primitives, the
reservation primitives, `read_mem_`/`write_mem_` (unused; memory goes
through `sail_mem_read`/`sail_mem_write`), random bits and the initramfs
location. None of them is reached by the simulated instructions.
`Print Assumptions` on the final theorem must list only Rocq's standard
axioms and Galette's Base axioms.

## Build

- A separate opam switch `galette-sail` with Rocq 9.2, needed because
  `rocq-sail-stdpp` requires Rocq < 9.3. `rocq-core` and `rocq-runtime` are
  pinned to 9.2.0.
- Galette is built from `deps/galette` with that switch. Galette's
  `dune-project` needs dune >= 3.24, so the dune 3.24 binary from the default
  switch is used against the `galette-sail` Rocq.
- The generated Sail files are committed in `sail/` (theory `Riscv`); Sail
  is pinned in the switch to git `2ba32128`.
  `scripts/gen-sail.sh` regenerates them from `deps/sail-riscv` and checks
  that they are unchanged.
