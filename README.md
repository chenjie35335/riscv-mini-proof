# riscv-mini-proof
This is a coq proof of riscv-mini, a RISC-V processor implemented by Chisel.

Clone with submodules:

```sh
git clone --recurse-submodules https://github.com/chenjie35335/riscv-mini-proof.git
```

For an existing checkout, run `git submodule update --init --recursive`.
`firrtl2coq` uses https://github.com/wky17/firrtl2coq, branch `lyc-fix-prop`,
pinned to the commit recorded by this repository.
