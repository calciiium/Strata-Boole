/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Verify

/-! # From Boole source to a type-checked Core program, at elaboration time

`shallow_reflect` (`Boole.lean`) starts from the Core program obtained by
`Strata.Boole.typeCheck`, that is `getProgram → toCoreProgram → Core.typeCheck`, before any Core
transform phase: the program Core's verifier works on. This file computes it. The computation
runs compiled code (`Term.evalTerm`): its result is a value in the elaborator, not a term the
kernel can reduce. -/

open Lean Elab Term Meta

namespace Strata.Reflect

/-- Lower and type-check; render the error as a string so the result can be evaluated at
elaboration time without naming Strata's message type. -/
def typeCheckStr (p : StrataDDM.Program) : Except String Core.Program :=
  match Strata.Boole.typeCheck p Core.VerifyOptions.quiet with
  | .ok cp => .ok cp
  | .error m => .error (toString (m.format none))

unsafe def evalProgramUnsafe (t : Term) : TermElabM Core.Program := do
  let ty := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String) (mkConst ``Core.Program)
  let r ← Term.evalTerm (Except String Core.Program) ty
    (← `(Strata.Reflect.typeCheckStr $t))
  match r with
  | .ok p => pure p
  | .error m => throwError m!"Core type checking failed: {m}"

/-- The type-checked Core program denoted by the term `t : StrataDDM.Program`. -/
@[implemented_by evalProgramUnsafe]
opaque evalProgram (t : Term) : TermElabM Core.Program

end Strata.Reflect
