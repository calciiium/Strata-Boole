/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Hoare.Tactic

/-! # Why the value of a `havoc` is not lifted

`havoc x` and `var x : int;` give `x` a value `v` about which the semantics says only
`HasVal.valueOfTy Core.Factory v int`: `v` is a value (`isValue`) and the syntactic type checker
assigns it `int`. Neither check looks at the type annotation an operator carries, so a partially
applied operator whose annotation lies is such a value, and it is not a numeral. The lifting
reads integer variables as numerals, so it cannot read `x` after a `havoc`; a `choose` lowers to
`assert ∃; havoc; assume` and stops there. Making `valueOfTy` canonical for the base types (as
`Procedure.valueHasType`, which types a procedure's inputs, already is) would close the gap; the
facts below are what such a change has to refute. -/

open Strata Core Lambda

namespace Strata.HoareTest

/-- `Int.Neg`, annotated as an integer: a value of type `int` that is not a numeral. -/
def junk : Core.Expression.Expr := .op () ⟨"Int.Neg", ()⟩ (some .int)

theorem junk_typeCheck : LExpr.typeCheck [] junk = some .int := rfl

theorem junk_isValue : LExpr.isValue Core.Factory junk = true := by
  rw [LExpr.isValue.eq_def]
  simp only [junk, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
  rw [Strata.Hoare.Eval.coreFactory_intNeg]
  simp [Lambda.intNegFunc, Lambda.unaryOp]

/-- The value a `havoc x` or an uninitialized `var x : int` may store. -/
theorem junk_valueOfTy :
    Imperative.HasVal.valueOfTy (P := Core.Expression) Core.Factory junk (.forAll [] .int) :=
  ⟨.int, junk_isValue, rfl, rfl⟩

/-- A clause reading `x` stays well typed, so its denotation is a real, model-dependent
proposition rather than a vacuous one. -/
theorem junk_hasTypeA : LExpr.HasTypeA (T := Core.CoreLParams) [] junk .int := .op

theorem junk_not_numeral (i : Int) : junk ≠ .const () (.intConst i) := by
  simp [junk]

end Strata.HoareTest
