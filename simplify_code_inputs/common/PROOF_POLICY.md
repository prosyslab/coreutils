## File structure

* `spec.rs`: readable executable specification.
* `dafny_spec.rs`: reference specification translated from Dafnyutils.
* `equivalence.rs`: input/output equivalence statement and verification entry point.
* `proof.rs`: helper lemmas and their proofs.
* `trusted.rs`: contracts and wrappers for permitted trusted operations.

Share proofs and trusted contracts in `proof_common.rs` and `trusted_common.rs`:

* `AbstractUutils/`: shared across utilities.
* `AbstractUutils/{utility}/`: shared across cases of one utility.

Keep helper modules inside the corresponding proof or trusted file.
Keep contracts, loop invariants, and necessary proof annotations beside verified code.

Do not create additional proof or trusted files outside this structure.

## Trust

* Filesystem and I/O operations
* Rust standard library
* External crates needed by the implementation or verification
    * Examples: Rayon, BigDecimal, foldhash, memchr, self_cell, itertools, tempfile, rlimit, rustix, and ctrlc
* All functions within uucore
* Verus, SMT solvers, and compilers
    * Trait delegation contracts describe only a direct call to a verified helper.

Trust is limited to each function's stated contract.
Record added trusted contracts and their source crates in experiment results.
Utility-specific logic must be proved, even when it calls trusted libraries.
Equivalence between the implementation and its executable specification must be proved.
