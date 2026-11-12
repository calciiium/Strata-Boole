/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.Languages.Core.IntEvalProps
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.Denote.LExprDenote
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import StrataBoole.HoareLogic.Hoare.Lift.Eval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.IntBoolFactory

/-! # Denoting closed Core conditions in every model

A contract clause or an `assert` is checked under `DenoteBasedInterp model`: the store is
substituted into the condition (`capturedExpr`) and the closed expression is read by
`LExpr.denote` at type `bool`. After the substitution the expression is built from literals,
the built-in operators and `eq`, so its denotation is the Lean value of the same shape:
`int.ge(a, b)` denotes `decide (a ≥ b)`, `p || q` denotes `p || q`, `a == b` denotes
`decide (a = b)`.

What makes this hold in *every* model is `Lambda.Interp.interpConsistent`: the model agrees
with each operator's `concreteEval` on literals, so its interpretation of `Int.Ge` at
`int, int → bool` is `≥`. Strata proves this for `Int.Ge`, `Int.Add` and `Int.Mul`
(`Core.intGe_opInterp` and companions); the same argument gives `Int.Lt`, `Int.Le`, `Int.Gt`,
`Int.Sub`, `Bool.And` and `Bool.Or` here, and `Int.Div` and `Int.Mod` for a non-zero divisor,
the only case their `concreteEval` covers.

The denotation lemmas are stated for arbitrary sub-expressions, with their typing witnesses as
hypotheses, so that `simp` can rewrite a closed condition from the outside in; the `hasTypeA`
tactic discharges the witnesses. -/

public section

namespace Strata.Hoare.Denote

open Core Lambda

/-! ## Operators in the concrete factory -/

set_option maxRecDepth 8000 in
theorem coreFactory_boolOr :
    (Core.Factory)["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  have hmem : (Lambda.boolOrFunc (T := CoreLParams)).func ∈ Core.WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolOrFunc (T := CoreLParams), ?_, rfl⟩
    unfold Core.WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  show (Core.Factory)[(Lambda.boolOrFunc (T := CoreLParams)).func.name.name]? = _
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

set_option maxRecDepth 8000 in
theorem coreFactory_boolAnd :
    (Core.Factory)["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  have hmem : (Lambda.boolAndFunc (T := CoreLParams)).func ∈ Core.WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolAndFunc (T := CoreLParams), ?_, rfl⟩
    unfold Core.WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  show (Core.Factory)[(Lambda.boolAndFunc (T := CoreLParams)).func.name.name]? = _
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

/-! ## Interpretations forced by consistency -/

/-- `Int.Lt` at `int, int → bool` is `<` in every consistent model. -/
theorem intLt_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Lt" (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool)
      = decide (a < b) := by
  have hmem : "Int.Lt" ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem Core.coreFactory_intLt
  have hget : Core.Factory["Int.Lt"]'hmem = (Lambda.intLtFunc (T := Core.CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem Core.coreFactory_intLt
  have hsome : (Core.Factory["Int.Lt"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Lt" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b]
      = some (.boolConst () (decide (a < b))) := by
    have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) Core.CoreLParams
        = @Lambda.LExpr.boolConst Core.CoreLParams.mono := rfl
    have key : (Lambda.intLtFunc (T := Core.CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b])
        = some (.boolConst () (decide (a < b))) := by
      simp only [Lambda.intLtFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, ite_true]
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.boolConst () (decide (a < b))) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (decide (a < b))) .bool := .const
  have h_eq := h_inst h_args h_result
  change decide (a < b) = model.opInterp "Int.Lt"
    (Lambda.LSort.mkArrow .bool [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Le` at `int, int → bool` is `≤` in every consistent model. -/
theorem intLe_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Le" (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool)
      = decide (a ≤ b) := by
  have hmem : "Int.Le" ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem Core.coreFactory_intLe
  have hget : Core.Factory["Int.Le"]'hmem = (Lambda.intLeFunc (T := Core.CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem Core.coreFactory_intLe
  have hsome : (Core.Factory["Int.Le"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Le" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b]
      = some (.boolConst () (decide (a ≤ b))) := by
    have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) Core.CoreLParams
        = @Lambda.LExpr.boolConst Core.CoreLParams.mono := rfl
    have key : (Lambda.intLeFunc (T := Core.CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b])
        = some (.boolConst () (decide (a ≤ b))) := by
      simp only [Lambda.intLeFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, ite_true]
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.boolConst () (decide (a ≤ b))) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (decide (a ≤ b))) .bool := .const
  have h_eq := h_inst h_args h_result
  change decide (a ≤ b) = model.opInterp "Int.Le"
    (Lambda.LSort.mkArrow .bool [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- A short-circuit boolean operator: its interpretation at `bool, bool → bool` is the Lean
operation `f`, given that its `concreteEval` computes `f` on literals. -/
theorem boolBinOp_opInterp (model : Lambda.Interp Core.Factory) (name : String)
    (wf : Lambda.WFLFunc CoreLParams) (f : Bool → Bool → Bool)
    (hlookup : (Core.Factory)[name]? = some wf.func)
    (hname : wf.func.name.name = name)
    (hin : wf.func.inputs.map Prod.snd = [.bool, .bool]) (hout : wf.func.output = .bool)
    (hceval : ∀ p q : Bool, wf.func.concreteEval.bind
      (fun ce => ce () [.boolConst () p, .boolConst () q]) = some (.boolConst () (f p q)))
    (p q : Bool) :
    (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) = f p q := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : Core.Factory[name]'hmem = wf.func := Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (Core.Factory[name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    have := hceval p q
    cases h : wf.func.concreteEval with
    | none => rw [h] at this; simp at this
    | some _ => rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  rw [hin, hout, hname] at h_ic
  have h_eval : ceval () [.boolConst () p, .boolConst () q] = some (.boolConst () (f p q)) := by
    have key := hceval p q
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.boolConst () p, .boolConst () q] (.boolConst () (f p q)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.boolConst () p, .boolConst () q] [Lambda.LMonoTy.bool, Lambda.LMonoTy.bool] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (f p q)) .bool := .const
  have h_eq := h_inst h_args h_result
  change f p q = model.opInterp name (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q at h_eq
  exact h_eq.symm

theorem boolOr_opInterp (model : Lambda.Interp Core.Factory) (p q : Bool) :
    (model.opInterp "Bool.Or" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) = (p || q) :=
  boolBinOp_opInterp model "Bool.Or" (Lambda.boolOrFunc (T := CoreLParams)) (· || ·)
    coreFactory_boolOr rfl rfl rfl (fun p q => by cases p <;> cases q <;> rfl) p q

theorem boolAnd_opInterp (model : Lambda.Interp Core.Factory) (p q : Bool) :
    (model.opInterp "Bool.And" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) = (p && q) :=
  boolBinOp_opInterp model "Bool.And" (Lambda.boolAndFunc (T := CoreLParams)) (· && ·)
    coreFactory_boolAnd rfl rfl rfl (fun p q => by cases p <;> cases q <;> rfl) p q


/-! ## Integer operators, generically

`boolBinOp_opInterp` for the integer operators: the concrete evaluation on two numerals, under
a side condition `P` on the operands (trivial for most operators, a non-zero divisor for
`Int.Div` and `Int.Mod`), forces the interpretation. -/

/-- The concrete evaluation of a `binaryOp` over `Int` on two numerals. -/
theorem binaryOp_concreteEval_int {OutValTy : Type} {outTy : Lambda.LMonoTy} [ToString OutValTy]
    [Lambda.LambdaLeanType outTy OutValTy] (name : CoreLParams.Identifier)
    (op : Int → Int → OutValTy) (guard : Int → Bool) (hOutTy : outTy.freeVars = [])
    (a b : Int) (hg : guard b = true) :
    (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
        (hOutTy := hOutTy) (h_precond := by simp)).func.concreteEval.bind
      (fun ce => ce () [.intConst () a, .intConst () b])
      = some (Lambda.LambdaLeanType.mkConst (ValTy := OutValTy) CoreLParams () (op a b)) := by
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
      = Lambda.LExpr.denoteInt := rfl
  have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
  have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
  simp only [Lambda.binaryOp, Option.bind_some, hcev, hda, hdb, hg, ite_true]

/-- An integer operator with an integer result: its interpretation at `int, int → int` is `f`
wherever `P` holds, given that its `concreteEval` computes `f` there. -/
theorem intBinOp_opInterp (model : Lambda.Interp Core.Factory) (name : String)
    (wf : Lambda.WFLFunc CoreLParams) (f : Int → Int → Int) (P : Int → Int → Prop)
    (hlookup : (Core.Factory)[name]? = some wf.func)
    (hname : wf.func.name.name = name)
    (hin : wf.func.inputs.map Prod.snd = [.int, .int]) (hout : wf.func.output = .int)
    (hceval : ∀ a b : Int, P a b → wf.func.concreteEval.bind
      (fun ce => ce () [.intConst () a, .intConst () b]) = some (.intConst () (f a b)))
    (a b : Int) (hP : P a b) :
    (model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = f a b := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : Core.Factory[name]'hmem = wf.func := Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (Core.Factory[name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    have := hceval a b hP
    cases h : wf.func.concreteEval with
    | none => rw [h] at this; simp at this
    | some _ => rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  rw [hin, hout, hname] at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] = some (.intConst () (f a b)) := by
    have key := hceval a b hP
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.intConst () (f a b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.intConst () (f a b)) .int := .const
  have h_eq := h_inst h_args h_result
  change f a b = model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- An integer relation: its interpretation at `int, int → bool` is `f` wherever `P` holds. -/
theorem intRelOp_opInterp (model : Lambda.Interp Core.Factory) (name : String)
    (wf : Lambda.WFLFunc CoreLParams) (f : Int → Int → Bool) (P : Int → Int → Prop)
    (hlookup : (Core.Factory)[name]? = some wf.func)
    (hname : wf.func.name.name = name)
    (hin : wf.func.inputs.map Prod.snd = [.int, .int]) (hout : wf.func.output = .bool)
    (hceval : ∀ a b : Int, P a b → wf.func.concreteEval.bind
      (fun ce => ce () [.intConst () a, .intConst () b]) = some (.boolConst () (f a b)))
    (a b : Int) (hP : P a b) :
    (model.opInterp name (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = f a b := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : Core.Factory[name]'hmem = wf.func := Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (Core.Factory[name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    have := hceval a b hP
    cases h : wf.func.concreteEval with
    | none => rw [h] at this; simp at this
    | some _ => rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  rw [hin, hout, hname] at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] = some (.boolConst () (f a b)) := by
    have key := hceval a b hP
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.boolConst () (f a b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (f a b)) .bool := .const
  have h_eq := h_inst h_args h_result
  change f a b = model.opInterp name (Lambda.LSort.mkArrow .bool [.int, .int]) a b at h_eq
  exact h_eq.symm

theorem intSub_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Sub" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a - b :=
  intBinOp_opInterp model "Int.Sub" (Lambda.intSubFunc (T := CoreLParams)) (· - ·) (fun _ _ => True)
    Eval.coreFactory_intSub rfl rfl rfl
    (fun a b _ => binaryOp_concreteEval_int "Int.Sub" Int.sub (fun _ => true) (by decide) a b rfl)
    a b trivial

theorem intGt_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Gt" (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool)
      = decide (a > b) :=
  intRelOp_opInterp model "Int.Gt" (Lambda.intGtFunc (T := CoreLParams)) (fun a b => decide (a > b))
    (fun _ _ => True) Eval.coreFactory_intGt rfl rfl rfl
    (fun a b _ => binaryOp_concreteEval_int (OutValTy := Bool) "Int.Gt" (· > ·) (fun _ => true)
      (by decide) a b rfl)
    a b trivial

/-- `Int.Div` is `/` wherever the divisor is non-zero; at zero the factory does not evaluate
it, and the model is free. -/
theorem intDiv_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) (hb : b ≠ 0) :
    (model.opInterp "Int.Div" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a / b :=
  intBinOp_opInterp model "Int.Div" (Lambda.intDivFunc (T := CoreLParams)) (· / ·) (fun _ b => b ≠ 0)
    Eval.coreFactory_intDiv rfl rfl rfl
    (fun a b hb => binaryOp_concreteEval_int "Int.Div" (· / ·) (· != 0) (by decide) a b
      (by simpa using hb))
    a b hb

theorem intMod_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) (hb : b ≠ 0) :
    (model.opInterp "Int.Mod" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a % b :=
  intBinOp_opInterp model "Int.Mod" (Lambda.intModFunc (T := CoreLParams)) (· % ·) (fun _ b => b ≠ 0)
    Eval.coreFactory_intMod rfl rfl rfl
    (fun a b hb => binaryOp_concreteEval_int "Int.Mod" (· % ·) (· != 0) (by decide) a b
      (by simpa using hb))
    a b hb

/-! ## Unary operators and the remaining boolean connectives -/

/-- `boolBinOp_opInterp` for a unary integer operator. -/
theorem intUnOp_opInterp (model : Lambda.Interp Core.Factory) (name : String)
    (wf : Lambda.WFLFunc CoreLParams) (f : Int → Int)
    (hlookup : (Core.Factory)[name]? = some wf.func)
    (hname : wf.func.name.name = name)
    (hin : wf.func.inputs.map Prod.snd = [.int]) (hout : wf.func.output = .int)
    (hceval : ∀ a : Int, wf.func.concreteEval.bind
      (fun ce => ce () [.intConst () a]) = some (.intConst () (f a)))
    (a : Int) :
    (model.opInterp name (Lambda.LSort.mkArrow .int [.int]) a : Int) = f a := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : Core.Factory[name]'hmem = wf.func := Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (Core.Factory[name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    have := hceval a
    cases h : wf.func.concreteEval with
    | none => rw [h] at this; simp at this
    | some _ => rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  rw [hin, hout, hname] at h_ic
  have h_eval : ceval () [.intConst () a] = some (.intConst () (f a)) := by
    have key := hceval a
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty [.intConst () a] (.intConst () (f a)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a] [Lambda.LMonoTy.int] :=
    .cons .const .nil
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.intConst () (f a)) .int := .const
  have h_eq := h_inst h_args h_result
  change f a = model.opInterp name (Lambda.LSort.mkArrow .int [.int]) a at h_eq
  exact h_eq.symm

/-- `boolBinOp_opInterp` for a unary boolean operator. -/
theorem boolUnOp_opInterp (model : Lambda.Interp Core.Factory) (name : String)
    (wf : Lambda.WFLFunc CoreLParams) (f : Bool → Bool)
    (hlookup : (Core.Factory)[name]? = some wf.func)
    (hname : wf.func.name.name = name)
    (hin : wf.func.inputs.map Prod.snd = [.bool]) (hout : wf.func.output = .bool)
    (hceval : ∀ p : Bool, wf.func.concreteEval.bind
      (fun ce => ce () [.boolConst () p]) = some (.boolConst () (f p)))
    (p : Bool) :
    (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool]) p : Bool) = f p := by
  have hmem : name ∈ Core.Factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : Core.Factory[name]'hmem = wf.func := Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (Core.Factory[name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    have := hceval p
    cases h : wf.func.concreteEval with
    | none => rw [h] at this; simp at this
    | some _ => rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  rw [hin, hout, hname] at h_ic
  have h_eval : ceval () [.boolConst () p] = some (.boolConst () (f p)) := by
    have key := hceval p
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty [.boolConst () p] (.boolConst () (f p)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.boolConst () p] [Lambda.LMonoTy.bool] :=
    .cons .const .nil
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.boolConst () (f p)) .bool := .const
  have h_eq := h_inst h_args h_result
  change f p = model.opInterp name (Lambda.LSort.mkArrow .bool [.bool]) p at h_eq
  exact h_eq.symm

theorem intNeg_opInterp (model : Lambda.Interp Core.Factory) (a : Int) :
    (model.opInterp "Int.Neg" (Lambda.LSort.mkArrow .int [.int]) a : Int) = -a :=
  intUnOp_opInterp model "Int.Neg" (Lambda.intNegFunc (T := CoreLParams)) (-·)
    Eval.coreFactory_intNeg rfl rfl rfl (fun _ => rfl) a

theorem boolNot_opInterp (model : Lambda.Interp Core.Factory) (p : Bool) :
    (model.opInterp "Bool.Not" (Lambda.LSort.mkArrow .bool [.bool]) p : Bool) = !p :=
  boolUnOp_opInterp model "Bool.Not" (Lambda.boolNotFunc (T := CoreLParams)) (!·)
    Core.coreFactory_boolNot rfl rfl rfl (fun p => by cases p <;> rfl) p

theorem boolImplies_opInterp (model : Lambda.Interp Core.Factory) (p q : Bool) :
    (model.opInterp "Bool.Implies" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool)
      = (!p || q) :=
  boolBinOp_opInterp model "Bool.Implies" (Lambda.boolImpliesFunc (T := CoreLParams))
    (fun p q => !p || q) Eval.coreFactory_boolImplies rfl rfl rfl
    (fun p q => by cases p <;> cases q <;> rfl) p q

theorem boolEquiv_opInterp (model : Lambda.Interp Core.Factory) (p q : Bool) :
    (model.opInterp "Bool.Equiv" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool)
      = decide (p = q) :=
  boolBinOp_opInterp model "Bool.Equiv" (Lambda.boolEquivFunc (T := CoreLParams))
    (fun p q => decide (p = q)) Eval.coreFactory_boolEquiv rfl rfl rfl
    (fun p q => by cases p <;> cases q <;> rfl) p q

/-! ## Denotations of closed conditions

Each lemma reads one node from the outside: the operator's interpretation applied to the
denotations of the operands, whose typing witnesses are hypotheses. -/

variable (model : Lambda.Interp Core.Factory)
variable (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
variable {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)

theorem denote_intConst_raw {i : Int}
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const () (.intConst i)) .int) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.const () (.intConst i)) .int h : Int) = i :=
  Lambda.denote_intConst _ _ _ _ _ h

theorem denote_boolConst_raw {b : Bool}
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const () (.boolConst b)) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.const () (.boolConst b)) .bool h : Bool) = b :=
  Lambda.denote_boolConst _ _ _ _ _ h

/-- An integer relation (`Int.Ge`, `Int.Lt`, …) on two integer operands. -/
theorem denote_int_rel_raw {name : String} {f : Int → Int → Bool}
    (hop : ∀ a b : Int,
      (model.opInterp name (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = f a b)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool h : Bool)
      = f (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁)
          (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .bool)))) (.arrow .int (.arrow .int .bool)) :=
    .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.app () (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .bool)))) e₁) (.arrow .int .bool) :=
    .app hop' h₁
  rw [Lambda.denote_app bv happ1 h₂ h, Lambda.denote_app bv hop' h₁ happ1, Lambda.denote_op]
  exact hop _ _

/-- An integer operation (`Int.Add`, `Int.Mul`, …) on two integer operands. -/
theorem denote_int_op_raw {name : String} {f : Int → Int → Int}
    (hop : ∀ a b : Int,
      (model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = f a b)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int h : Int)
      = f (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁)
          (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .int)))) (.arrow .int (.arrow .int .int)) :=
    .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.app () (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .int)))) e₁) (.arrow .int .int) :=
    .app hop' h₁
  rw [Lambda.denote_app bv happ1 h₂ h, Lambda.denote_app bv hop' h₁ happ1, Lambda.denote_op]
  exact hop _ _

/-- A boolean operation (`Bool.And`, `Bool.Or`, …) on two boolean operands. -/
theorem denote_bool_op_raw {name : String} {f : Bool → Bool → Bool}
    (hop : ∀ p q : Bool,
      (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) = f p q)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .bool) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool h : Bool)
      = f (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .bool h₁)
          (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .bool h₂) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) (.arrow .bool (.arrow .bool .bool)) :=
    .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.app () (.op () ⟨name, ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) e₁) (.arrow .bool .bool) :=
    .app hop' h₁
  rw [Lambda.denote_app bv happ1 h₂ h, Lambda.denote_app bv hop' h₁ happ1, Lambda.denote_op]
  exact hop _ _

/-- Equality of two integer operands holds exactly when their denotations agree. -/
theorem denote_eq_int_iff_raw {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h : Bool)
        = true
      ↔ (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ : Int)
        = Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ := by
  constructor
  · intro htrue
    exact Classical.byContradiction fun hne => by
      rw [Lambda.denote_eq_false bv h₁ h₂ h hne] at htrue
      exact Bool.false_ne_true htrue
  · intro heq
    exact Lambda.denote_eq_true bv h₁ h₂ h heq

/-- A unary integer operator (`Int.Neg`) on an integer operand. -/
theorem denote_int_un_raw {name : String} {f : Int → Int}
    (hop : ∀ a : Int, (model.opInterp name (Lambda.LSort.mkArrow .int [.int]) a : Int) = f a)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int .int)
    {e : Core.Expression.Expr} (h₁ : Lambda.LExpr.HasTypeA Δ e .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.op () ⟨name, ()⟩ (some ty)) e) .int) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.op () ⟨name, ()⟩ (some ty)) e) .int h : Int)
      = f (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .int h₁) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .int .int))) (.arrow .int .int) := .op
  rw [Lambda.denote_app bv hop' h₁ h, Lambda.denote_op]
  exact hop _

/-- A unary boolean operator (`Bool.Not`) on a boolean operand. -/
theorem denote_bool_un_raw {name : String} {f : Bool → Bool}
    (hop : ∀ p : Bool, (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool]) p : Bool) = f p)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .bool .bool)
    {e : Core.Expression.Expr} (h₁ : Lambda.LExpr.HasTypeA Δ e .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.op () ⟨name, ()⟩ (some ty)) e) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.op () ⟨name, ()⟩ (some ty)) e) .bool h : Bool)
      = f (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .bool h₁) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .bool .bool))) (.arrow .bool .bool) := .op
  rw [Lambda.denote_app bv hop' h₁ h, Lambda.denote_op]
  exact hop _

/-- `denote_eq_int_iff_raw` for two boolean operands. -/
theorem denote_eq_bool_iff_raw {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .bool) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h : Bool)
        = true
      ↔ (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .bool h₁ : Bool)
        = Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .bool h₂ := by
  constructor
  · intro htrue
    exact Classical.byContradiction fun hne => by
      rw [Lambda.denote_eq_false bv h₁ h₂ h hne] at htrue
      exact Bool.false_ne_true htrue
  · intro heq
    exact Lambda.denote_eq_true bv h₁ h₂ h heq

/-! ## The same, through explicit conversions

`TyDenote tcInterp vt .bool` is `Bool` by computation, not by a reducible unfolding, so an
equation stated between a denotation and a `Bool` does not type check at the transparency
`simp` works at. `toBool` and `toInt` make the conversion a term, and the lemmas below are the
ones above restated through them. -/

/-- A denotation at `bool`, as a `Bool`. -/
@[expose] def toBool {tcInterp : Lambda.TyConstrInterp} {vt : Lambda.TyVarVal}
    (x : Lambda.TyDenote tcInterp vt .bool) : Bool := x

/-- A denotation at `int`, as an `Int`. -/
@[expose] def toInt {tcInterp : Lambda.TyConstrInterp} {vt : Lambda.TyVarVal}
    (x : Lambda.TyDenote tcInterp vt .int) : Int := x

theorem denote_intConst' {i : Int}
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const () (.intConst i)) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.const () (.intConst i)) .int h) = i :=
  denote_intConst_raw model fv vt bv h

theorem denote_boolConst' {b : Bool}
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const () (.boolConst b)) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.const () (.boolConst b)) .bool h) = b :=
  denote_boolConst_raw model fv vt bv h

theorem denote_int_rel {name : String} {f : Int → Int → Bool}
    (hop : ∀ a b : Int,
      (model.opInterp name (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = f a b)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool h)
      = f (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁))
          (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂)) :=
  denote_int_rel_raw model fv vt bv hop hty h₁ h₂ h

theorem denote_int_op {name : String} {f : Int → Int → Int}
    (hop : ∀ a b : Int,
      (model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = f a b)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int h)
      = f (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁))
          (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂)) :=
  denote_int_op_raw model fv vt bv hop hty h₁ h₂ h

/-- `denote_int_op` for an operator whose interpretation is forced only under a side condition
on the operands (`Int.Div`, `Int.Mod`): the condition is asked of the operands' denotations. -/
theorem denote_int_op_guarded {name : String} {f : Int → Int → Int} {P : Int → Int → Prop}
    (hop : ∀ a b : Int, P a b →
      (model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = f a b)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int)
    (hP : P (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁))
      (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂))) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .int h)
      = f (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁))
          (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂)) := by
  subst hty
  have hop' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .int)))) (.arrow .int (.arrow .int .int)) :=
    .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ
      (.app () (.op () ⟨name, ()⟩ (some (.arrow .int (.arrow .int .int)))) e₁) (.arrow .int .int) :=
    .app hop' h₁
  unfold toInt
  rw [Lambda.denote_app bv happ1 h₂ h, Lambda.denote_app bv hop' h₁ happ1, Lambda.denote_op]
  exact hop _ _ hP

theorem denote_bool_op {name : String} {f : Bool → Bool → Bool}
    (hop : ∀ p q : Bool,
      (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) = f p q)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .bool) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.app () (.op () ⟨name, ()⟩ (some ty)) e₁) e₂) .bool h)
      = f (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .bool h₁))
          (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .bool h₂)) :=
  denote_bool_op_raw model fv vt bv hop hty h₁ h₂ h

theorem denote_eq_int_iff {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h)
        = true
      ↔ toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁)
        = toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂) :=
  denote_eq_int_iff_raw model fv vt bv h₁ h₂ h

theorem denote_int_un {name : String} {f : Int → Int}
    (hop : ∀ a : Int, (model.opInterp name (Lambda.LSort.mkArrow .int [.int]) a : Int) = f a)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .int .int)
    {e : Core.Expression.Expr} (h₁ : Lambda.LExpr.HasTypeA Δ e .int)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.op () ⟨name, ()⟩ (some ty)) e) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.op () ⟨name, ()⟩ (some ty)) e) .int h)
      = f (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .int h₁)) :=
  denote_int_un_raw model fv vt bv hop hty h₁ h

theorem denote_bool_un {name : String} {f : Bool → Bool}
    (hop : ∀ p : Bool, (model.opInterp name (Lambda.LSort.mkArrow .bool [.bool]) p : Bool) = f p)
    {ty : Lambda.LMonoTy} (hty : ty = .arrow .bool .bool)
    {e : Core.Expression.Expr} (h₁ : Lambda.LExpr.HasTypeA Δ e .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.op () ⟨name, ()⟩ (some ty)) e) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.app () (.op () ⟨name, ()⟩ (some ty)) e) .bool h)
      = f (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .bool h₁)) :=
  denote_bool_un_raw model fv vt bv hop hty h₁ h

theorem denote_eq_bool_iff {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .bool) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h)
        = true
      ↔ toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .bool h₁)
        = toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .bool h₂) :=
  denote_eq_bool_iff_raw model fv vt bv h₁ h₂ h

/-- The equalities as the boolean they denote, for an `==` below another connective. -/
theorem denote_eq_int {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h)
      = decide (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁)
        = toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact denote_eq_int_iff model fv vt bv h₁ h₂ h

theorem denote_eq_bool {e₁ e₂ : Core.Expression.Expr}
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .bool) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.eq () e₁ e₂) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.eq () e₁ e₂) .bool h)
      = decide (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .bool h₁)
        = toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .bool h₂)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact denote_eq_bool_iff model fv vt bv h₁ h₂ h

theorem toInt_cond (b : Bool) (x y : Lambda.TyDenote model.tcInterp vt .int) :
    toInt (cond b x y) = cond b (toInt x) (toInt y) := by
  cases b <;> rfl

theorem toBool_cond (b : Bool) (x y : Lambda.TyDenote model.tcInterp vt .bool) :
    toBool (cond b x y) = cond b (toBool x) (toBool y) := by
  cases b <;> rfl

/-- A conditional expression at `int` is the conditional of its branches. -/
theorem denote_ite_int {c t e : Core.Expression.Expr}
    (hc : Lambda.LExpr.HasTypeA Δ c .bool)
    (ht : Lambda.LExpr.HasTypeA Δ t .int) (he : Lambda.LExpr.HasTypeA Δ e .int)
    (h : Lambda.LExpr.HasTypeA Δ (.ite () c t e) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.ite () c t e) .int h)
      = cond (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv c .bool hc))
          (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv t .int ht))
          (toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .int he)) :=
  (congrArg toInt (Lambda.denote_ite (bvarVal := bv) hc ht he h)).trans
    (toInt_cond model vt _ _ _)

theorem denote_ite_bool {c t e : Core.Expression.Expr}
    (hc : Lambda.LExpr.HasTypeA Δ c .bool)
    (ht : Lambda.LExpr.HasTypeA Δ t .bool) (he : Lambda.LExpr.HasTypeA Δ e .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.ite () c t e) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.ite () c t e) .bool h)
      = cond (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv c .bool hc))
          (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv t .bool ht))
          (toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e .bool he)) :=
  (congrArg toBool (Lambda.denote_ite (bvarVal := bv) hc ht he h)).trans
    (toBool_cond model vt _ _ _)

/-! ## Bound variables and quantifiers

A quantifier in a clause binds a variable its body reads as `bvar 0` (an enclosing binder's
variable as `bvar 1`, and so on). Its denotation at `bool` is the Lean quantifier over the
values of the bound type, with the body read at the valuation extended by the value. Only
integer bound variables are lifted. -/

/-- An `Int` as a value of the sort `int`, the form a bound integer takes in a valuation. -/
@[expose] def ofInt {tcInterp : Lambda.TyConstrInterp} {vt : Lambda.TyVarVal} (v : Int) :
    Lambda.TyDenote tcInterp vt .int := v

theorem denote_bvar_zero_int {τs : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt τs)
    (v : Int) (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) (.int :: τs) (.bvar () 0) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt (.cons (ofInt v) bv)
      (.bvar () 0) .int h) = v := by
  unfold toInt
  rw [Lambda.denote_bvar]
  rfl

theorem denote_bvar_succ_int {τ : Lambda.LMonoTy} {τs : List Lambda.LMonoTy}
    (bv : Lambda.BVarVal model.tcInterp vt τs) (x : Lambda.TyDenote model.tcInterp vt τ) (i : Nat)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) (τ :: τs) (.bvar () (i + 1)) .int)
    (h' : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) τs (.bvar () i) .int) :
    toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt (.cons x bv)
        (.bvar () (i + 1)) .int h)
      = toInt (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv (.bvar () i) .int h') := by
  unfold toInt
  rw [Lambda.denote_bvar, Lambda.denote_bvar]
  rfl

theorem denote_forall_int {name : String} {tr body : Core.Expression.Expr}
    {qty : Lambda.LMonoTy} (hq : qty = .int)
    (hb : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) (.int :: Δ) body .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.quant () .all name (some qty) tr body) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.quant () .all name (some qty) tr body) .bool h) = true
      ↔ ∀ v : Int, toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt
          (.cons (ofInt v) bv) body .bool hb) = true := by
  subst hq
  constructor
  · intro hall v
    refine Classical.byContradiction fun hv => ?_
    have hf := Lambda.denote_quant_all_false bv hb h (ofInt v) (Bool.eq_false_iff.mpr hv)
    rw [hf] at hall
    exact Bool.false_ne_true hall
  · intro hall
    exact Lambda.denote_quant_all_true bv hb h (fun x => hall x)

theorem denote_exists_int {name : String} {tr body : Core.Expression.Expr}
    {qty : Lambda.LMonoTy} (hq : qty = .int)
    (hb : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) (.int :: Δ) body .bool)
    (h : Lambda.LExpr.HasTypeA Δ (.quant () .exist name (some qty) tr body) .bool) :
    toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
        (.quant () .exist name (some qty) tr body) .bool h) = true
      ↔ ∃ v : Int, toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt
          (.cons (ofInt v) bv) body .bool hb) = true := by
  subst hq
  constructor
  · intro hex
    refine Classical.byContradiction fun hnone => ?_
    have hall : ∀ x : Lambda.TyDenote model.tcInterp vt .int,
        (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt (.cons x bv) body .bool hb : Bool)
          = false :=
      fun x => Bool.eq_false_iff.mpr (fun hx => hnone ⟨x, hx⟩)
    rw [Lambda.denote_quant_exist_false bv hb h hall] at hex
    exact Bool.false_ne_true hex
  · rintro ⟨v, hv⟩
    exact Lambda.denote_quant_exist_true bv hb h (ofInt v) hv

/-! ## Typing witnesses -/

/-- Literals, with their types spelled as the lemmas above expect them, so that a witness
built from these has exactly the type `simp` asks for. -/
theorem HasTypeA_intConst (Δ : List Lambda.LMonoTy) (m : Unit) (i : Int) :
    Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const m (.intConst i)) .int := .const

theorem HasTypeA_boolConst (Δ : List Lambda.LMonoTy) (m : Unit) (b : Bool) :
    Lambda.LExpr.HasTypeA (T := Core.CoreLParams) Δ (.const m (.boolConst b)) .bool := .const

/-- Build a `HasTypeA` witness for a closed condition made of literals, operators,
applications and equalities. -/
syntax "hasTypeA" : tactic
macro_rules
  | `(tactic| hasTypeA) => `(tactic| repeat' first
      | exact Strata.Hoare.Denote.HasTypeA_intConst _ _ _
      | exact Strata.Hoare.Denote.HasTypeA_boolConst _ _ _
      | exact Lambda.LExpr.HasTypeA.const
      | exact Lambda.LExpr.HasTypeA.op
      | apply Lambda.LExpr.HasTypeA.eq
      | apply Lambda.LExpr.HasTypeA.ite
      | apply Lambda.LExpr.HasTypeA.app
      | apply Lambda.LExpr.HasTypeA.quant
      | (apply Lambda.LExpr.HasTypeA.bvar; rfl))

end Strata.Hoare.Denote

end -- public section
