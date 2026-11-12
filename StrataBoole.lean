/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
public import StrataBoole.Verify
public import StrataBoole.HoareLogic.HoareLift

/-! ## Strata Boole Public Interface

Parsing, translation to Core, verification, and pretty-printing for the Boole
dialect of Strata.

### `import StrataBoole`

- **Types**: `Strata.Boole.Type`, `Strata.Boole.Expr`, `Strata.Boole.Program`
- **Parsing**: `Strata.Boole.getProgram`
- **Translation**: `Strata.Boole.toCoreProgram`
- **Type checking**: `Strata.Boole.typeCheck`
- **Verification**: `Strata.Boole.verify`
- **VC generation**: `Strata.Boole.genVCs`
- **Pretty-printing**: `Strata.Boole.formatProgram`

### `import StrataBoole.Nat` (specification only)

- **Binary nat library as a Core-syntax spec**: `Strata.BooleNat.natLibrary`,
  `Strata.BooleNat.prepend`.  The implementation is `natCorePreamble` in
  `StrataBoole/Verify.lean`; nothing imports this module.  `lake build StrataBoole.Nat`.

### `import StrataBoole.HoareLogic.Shallow.Layer`

A shallow-embedding prototype on `Std.Do`: the `ND` monad with `havoc`,
`assume`, `assert` and `whileInv`, each with its `@[spec]` rule for `mvcgen`.
The Hoare-logic route in `docs/HoareLogic.md` does not build on it.

### `import StrataBoole.HoareLogic.Pipeline`

`boole_prove pgm proc` proves in Lean the contract of the procedure `proc` of the Boole program
`pgm`: it binds the program's Core AST (`shallow_reflect`), then states and proves
`proc_contract : Core.Logic.Hoare.Procedure.contractTriple pgm_ast params "proc"` and
`proc_correct : Strata.Deep.Procedure.Correct proc_ast`, closing each verification condition
with `omega`, then `grind`. `boole_prove pgm proc strata` or `… deep` proves one of the two, and
`… with tac` closes the conditions with `tac`.

### `import StrataBoole.HoareLogic.Hoare.Tactic`

The Hoare-logic route of `docs/HoareLogic.md`, on Strata's `Core.Logic.Hoare`:
weakest-precondition rules proved from Strata's (`Hoare/Rules.lean`, `Proj.lean`, `WP.lean`,
`Contract.lean`), lifting lemmas for the evaluator and the denotation (`Hoare/Lift/`), and the
tactics `hoare_contract`, `hoare_vcs` and `hoare_lift`, which turn `Procedure.contractTriple`
into verification conditions over `Int` and `Bool`, named after the program's clauses.

### `import StrataBoole.HoareLogic.Deep.Tactic`

A deep embedding of Core's structured statements with a big-step semantics of its own
(`Deep/Exec.lean`), rules proved about it, and the tactics `core_vcgen` and `core_lift`. It leaves
the same conditions as the Hoare-logic route and serves as a cross-check; nothing connects it to
Core's semantics.

### `import StrataBoole.HoareLogic.Reflect.Boole`

`shallow_reflect p` binds the type-checked Core program of the Boole program `p` to
`<p>_ast : Core.Program` and each of its procedures to `<name>_ast : Core.Procedure`, as terms
the kernel can reduce. `#core_reflect` (`StrataBoole.HoareLogic.Reflect.Core`) does the same
for a program written in Core syntax.

### `import StrataBoole.MetaVerifier`

The `gen_smt_vcs_boole` tactic and `Strata.smtVCsCorrectBoole` are available
by importing `StrataBoole.MetaVerifier` directly.
-/
