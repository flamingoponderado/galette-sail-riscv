# galette-sail-riscv

A Rocq comparison of two RISC-V semantics:

| | Model | Where |
|---|---|---|
| **L3** | Galette's L3-derived RV64 model (`Galette.HOL.examples.l3_machine_code.riscv.model.riscv`, step `riscv_step.NextRISCV`), which Galette's Pancake compiler-correctness theorem `pan_to_target_compile_semantics` is stated over | `deps/galette` |
| **Sail** | The official Sail RISC-V model, translated to Rocq by Sail's Rocq backend (`rocq-sail-riscv`, RV64) | `deps/sail-riscv` |

**Goal.** Formal equivalence for what matters to compiled Pancake programs: the
observable behaviour defined by Galette's `machine_sem` (a port of CakeML's).
The plan follows the Lean development
[riscv-im-compare](https://github.com/flamingoponderado/riscv-im-compare):

1. a state relation between L3 states and Sail states;
2. single-step simulation for every instruction that Galette's RISC-V encoder
   emits (37 instruction kinds), under explicit side conditions (privilege
   mode, address translation off, alignment, PMP, interrupts...);
3. a generic `machine_sem` simulation theorem;
4. transfer of `pan_to_target_compile_semantics` to a machine configuration
   whose processor is the Sail model.

Status: work in progress. See "Building" for the toolchain.

## Building

The Rocq output of sail-riscv needs `rocq-sail-stdpp`, which currently requires
Rocq < 9.3, so this project uses a dedicated opam switch with Rocq 9.2:

    opam switch create galette-sail ocaml-base-compiler.5.2.1
    opam install --switch=galette-sail "rocq-core<9.3" rocq-stdlib rocq-sail-stdpp \
      sail sail_coq_backend ...   # see rocq-sail-riscv.opam.in in sail-riscv

    git submodule update --init

## License

The comparison development is MIT-licensed (see `LICENSE`); the submodules
keep their own licenses (Galette: BSD-3-Clause, sail-riscv: BSD-2-Clause).
