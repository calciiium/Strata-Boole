/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Deep.Tactic

/-! # Example: the maximum of two integers, through the deep embedding

1. Write the procedure in Core syntax.
2. `#core_reflect` translates and type checks it with Strata's Core front end, and
   defines `max2 : Core.Procedure`, the AST as a Lean term.
3. `Procedure.Correct max2` is the procedure's contract read as a Hoare triple:
   `{requires} body {ensures}` over the big-step semantics `Exec`.
4. `core_vcgen` applies one rule per statement and leaves verification conditions;
   `core_lift` names them and evaluates the embedding away; `omega` closes the arithmetic.

`#print max2` shows the procedure in Core notation (`Deep/Delab.lean`). After
`core_vcgen`, the VC of the then branch reads
```
case ifTrue.rest
σ : State
hguard : evalBool σ ⟪x >= y⟫ = some true
v : Val
hv : some v = eval σ ⟪x⟫
⊢ Labeled "max2_ensures_0" (σ.update "m" v ⊨ ⟪m >= x⟫) ∧
    Labeled "max2_ensures_1" (σ.update "m" v ⊨ ⟪m >= y⟫) ∧
      Labeled "max2_ensures_2" (σ.update "m" v ⊨ ⟪m == x || m == y⟫)
```
and `core_lift` closes all but one of the six conditions, leaving
```
case else.max2_ensures_0
x y : Int
hguard : x < y
⊢ x ≤ y
```
-/

open StrataDDM (Program)
open Strata.Deep

-- `max2` below is defined by `#core_reflect`; if that failed, an auto-bound implicit would
-- silently stand in for it.
set_option autoImplicit false

namespace Strata.DeepExamples

def max2Pgm :=
#strata
program Core;

procedure max2(x : int, y : int, out m : int)
spec {
  ensures (int.ge(m, x));
  ensures (int.ge(m, y));
  ensures (m == x || m == y);
}
{
  if (int.ge(x, y)) {
    m := x;
  } else {
    m := y;
  }
};
#end

#core_reflect max2Pgm

theorem max2_correct : Procedure.Correct max2 := by
  unfold max2
  simp only [Procedure.Correct]
  core_vcgen <;> core_lift <;> omega

/-! ## A wrong contract is refuted

The triple is not vacuous: with `ensures (m == x)`, the VC of the else branch is false,
and a concrete run shows the contract itself is false. From `x = 0`, `y = 1` the guard
is false, the body sets `m := y = 1`, and `m == x` fails. -/

def max2WrongPgm :=
#strata
program Core;

procedure max2Wrong(x : int, y : int, out m : int)
spec {
  ensures (m == x);
}
{
  if (int.ge(x, y)) {
    m := x;
  } else {
    m := y;
  }
};
#end

#core_reflect max2WrongPgm

theorem max2Wrong_refuted : ¬ Procedure.Correct max2Wrong := by
  unfold max2Wrong
  simp only [Procedure.Correct, Procedure.pre, Procedure.post, Triple]
  intro h
  let σ : State := fun v => if v = "y" then .int 1 else .int 0
  -- The run `ite_false` → `m := y` → end, from `σ`.
  have := h σ (by simp [σ, OldSnapshot, PresHold, Core.Procedure.Header.getInoutParams,
      Core.getInoutParams, ListMap.keys]) _
    (.ite_false (by simp [σ, evalBool, eval, evalIn, binop])
      (.set (v := .int 1) (by simp [σ, eval, evalIn]) .nil) .nil)
  simp [σ, Outcome.Sat, PostsHold, Labeled, Holds, SatT, evalBoolIn, evalIn, eqAt, typeOf,
    State.update] at this

end Strata.DeepExamples
