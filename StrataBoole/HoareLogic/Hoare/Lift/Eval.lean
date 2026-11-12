/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprEvalProps
public import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr

/-! # Evaluating Core expressions over a store of literals

Statements evaluate their expressions with `Core.Expression.eval` (`Lambda.LExpr.evalFully`
over `Core.Factory`). A verification condition therefore reads `eval ρ.factory ρ.store e = some v`
for the guard or right-hand side `e`, with the store known slot by slot: `ρ.store x = some (intConst a)`.
The lemmas here compute such evaluations: a variable yields its stored literal, a constant
itself, and a built-in integer operation on two sub-expressions that evaluate to numerals yields
the numeral or boolean of the Lean operation. The last is one generic argument over fuel-level
step lemmas, instantiated per operator: Strata's (`Core.eval_intGe_value_of_numerals` and
companions) where they exist, and `eval_intBinOp_value_of_numerals` here for the operators
Strata has none for, `Int.Sub`, `Int.Div`, `Int.Mod` and `Int.Gt`. Division and remainder
evaluate only for a non-zero divisor, which is the guard of their factory entries.

A guard read by the `ite` and `while` rules is compared with `HasBool.tt`; `tt_of_decide` and
`ff_of_decide` turn that comparison into the proposition the guard decides. -/

public section

namespace Strata.Hoare.Eval

open Core Lambda

/-- Statements evaluate with `Core.Expression.eval`, which is `evalFully` by definition. -/
theorem eval_def (f : Expression.Factory) (σ : CoreStore) (e : Expression.Expr) :
    Core.Expression.eval f σ e = LExpr.evalFully f σ e := rfl

/-! ## Leaves -/

theorem evalFully_fvar_const {σ : CoreStore} {x : Expression.Ident} {κ : LConst}
    (m : Unit) (ty : Option LMonoTy) (hx : σ x = some (.const () κ)) :
    LExpr.evalFully Core.Factory σ (.fvar m x ty) = some (.const () κ) :=
  Lambda.evalFully_fvar_of_value (F := Core.Factory) (env := σ) (m := m) (x := x) (ty := ty)
    (hx := hx) (hv := Lambda.isValue_const_true Core.Factory () κ)

theorem evalFully_intConst (σ : CoreStore) (n : Int) :
    LExpr.evalFully Core.Factory σ (.const () (.intConst n)) = some (.const () (.intConst n)) :=
  Lambda.evalFully_const Core.Factory σ () (LConst.intConst n)

theorem evalFully_boolConst (σ : CoreStore) (b : Bool) :
    LExpr.evalFully Core.Factory σ (.const () (.boolConst b)) = some (.const () (.boolConst b)) :=
  Lambda.evalFully_const Core.Factory σ () (LConst.boolConst b)

/-! ## Binary integer operations -/

/-- The operator nodes the type checker writes, as Strata's factory entries spell them. -/
theorem intGe_opExpr :
    (Lambda.intGeFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Ge", ()⟩ (some (.arrow .int (.arrow .int .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem intLt_opExpr :
    (Lambda.intLtFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Lt", ()⟩ (some (.arrow .int (.arrow .int .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem intLe_opExpr :
    (Lambda.intLeFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Le", ()⟩ (some (.arrow .int (.arrow .int .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem intAdd_opExpr :
    (Lambda.intAddFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Add", ()⟩ (some (.arrow .int (.arrow .int .int))) : Expression.Expr) := by
  first | rfl | decide

theorem intMul_opExpr :
    (Lambda.intMulFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Mul", ()⟩ (some (.arrow .int (.arrow .int .int))) : Expression.Expr) := by
  first | rfl | decide

/-- From a fuel-level step lemma for an operator to its `evalFully` statement: evaluate both
operands to numerals, lift them to a common fuel, step, and read the result back. -/
theorem evalFully_binop_of_step {σ : CoreStore} {opE x y res : Expression.Expr} {a b : Int}
    (step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.intConst () a, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.intConst () b, .value true) →
      LExpr.eval (n + 1) Core.Factory σ (.app () (.app () opE x) y) = (res, .value true))
    (hx : LExpr.evalFully Core.Factory σ x = some (LExpr.intConst () a))
    (hy : LExpr.evalFully Core.Factory σ y = some (LExpr.intConst () b)) :
    LExpr.evalFully Core.Factory σ (.app () (.app () opE x) y) = some res := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx' := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy' := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ (step (max nx ny) hx' hy')

theorem evalFully_intGe {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Ge", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (decide (a ≥ b)))) := by
  subst hty
  have step := fun n => Core.eval_intGe_value_of_numerals Core.Factory σ x y n a b Core.coreFactory_intGe
  rw [intGe_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intLt {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Lt", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (decide (a < b)))) := by
  subst hty
  have step := fun n => Core.eval_intLt_value_of_numerals Core.Factory σ x y n a b Core.coreFactory_intLt
  rw [intLt_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intLe {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Le", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (decide (a ≤ b)))) := by
  subst hty
  have step := fun n => Core.eval_intLe_value_of_numerals Core.Factory σ x y n a b Core.coreFactory_intLe
  rw [intLe_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intAdd {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Add", ()⟩ (some ty)) x) y)
      = some (.const () (.intConst (a + b))) := by
  subst hty
  have step := fun n => Core.eval_intAdd_value_of_numerals Core.Factory σ x y n a b Core.coreFactory_intAdd
  rw [intAdd_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intMul {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Mul", ()⟩ (some ty)) x) y)
      = some (.const () (.intConst (a * b))) := by
  subst hty
  have step := fun n => Core.eval_intMul_value_of_numerals Core.Factory σ x y n a b Core.coreFactory_intMul
  rw [intMul_opExpr] at step
  exact evalFully_binop_of_step step hx hy

/-! ## The operators Strata has no step lemma for

`Core.eval_intGe_value_of_numerals` and its companions all come from one argument about
`binaryOp`, which Strata keeps private and instantiates without the guard `binaryOp` admits.
The argument is repeated here with the guard: when both operands evaluate to numerals and the
guard accepts the second, the application steps to the constant of the Lean operation. -/

theorem eval_intBinOp_value_of_numerals
    {OutValTy : Type} {outTy : LMonoTy} [ToString OutValTy] [LambdaLeanType outTy OutValTy]
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr) (n : Nat) (a b : Int)
    (name : CoreLParams.Identifier) (op : Int → Int → OutValTy) (guard : Int → Bool)
    (hOutTy : outTy.freeVars = [])
    (hI : f[name.name]? = some (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
      (hOutTy := hOutTy) (h_precond := by simp)).func)
    (hg : guard b = true)
    (hval : LExpr.isValue f (LambdaLeanType.mkConst (ValTy := OutValTy) CoreLParams () (op a b)) = true)
    (hx : LExpr.eval n f σ x = (LExpr.intConst () a, .value true))
    (hy : LExpr.eval n f σ y = (LExpr.intConst () b, .value true)) :
    LExpr.eval (n + 1) f σ
        (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
          (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y)
      = (LambdaLeanType.mkConst (ValTy := OutValTy) CoreLParams () (op a b), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
        (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y)
      = some ((Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
                (hOutTy := hOutTy) (h_precond := by simp)).opExpr,
              [x, y],
              (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
                (hOutTy := hOutTy) (h_precond := by simp)).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr, Lambda.binaryOp]
    rw [hI]
    simp [Lambda.binaryOp]
  have hcan : LExpr.isValue f
      (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) name op guard
        (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y) = false := by
    simp only [LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.binaryOp]
    rw [hI]
    simp [Lambda.binaryOp]
  have hcani : ∀ (a : Int), LExpr.isValue f (LExpr.intConst () a : Expression.Expr) = true := by
    intro a; simp [LExpr.isValue, LExpr.intConst]
  simp only [LExpr.eval]
  rw [ite_eq_right (by simp [hcan]), hcall]
  dsimp only
  rw [LExpr.shortCircuitCall?_of_not_attr _
    (by simp [Strata.DL.Util.FuncAttr.hasShortCircuit, Lambda.binaryOp])]
  dsimp only
  simp only [Lambda.binaryOp]
  rw [dite_eq_right (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfValue #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : LambdaLeanType.cevalTy (ty := LMonoTy.int) (ValTy := Int) CoreLParams
      = LExpr.denoteInt := rfl
  simp only [hcev]
  have hdenote : LExpr.denoteInt (LExpr.intConst () a : Expression.Expr) = some a := rfl
  have hdenote' : LExpr.denoteInt (LExpr.intConst () b : Expression.Expr) = some b := rfl
  rw [ite_eq_left (by simp [hcani])]
  simp only [hdenote, hdenote', hg, ite_true]
  rw [Lambda.eval_value_identity n f σ _ hval]
  simp [LExpr.combineEvalResValueFlag_eq_pair, LExpr.EvalResult.combineValueFlag]

/-- A function of `WFFactoryArray` resolves in `Core.Factory` under its own name. -/
theorem coreFactory_get?_of_mem {wf : Lambda.WFLFunc CoreLParams}
    (hmem : wf.func ∈ Core.WFFactoryArray.map (·.func)) :
    (Core.Factory)[wf.func.name.name]? = some wf.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

/-- Membership of a factory function in `WFFactoryArray`, by walking the array. -/
syntax "wf_factory_mem" : tactic
macro_rules
  | `(tactic| wf_factory_mem) => `(tactic| (
      rw [Array.mem_def]
      unfold Core.WFFactoryArray
      simp only [Array.toList_appendList]
      repeat (first | exact List.Mem.head _ | apply List.Mem.tail)))

set_option maxRecDepth 8000 in
theorem coreFactory_intSub :
    (Core.Factory)["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intSubFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.intSubFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

set_option maxRecDepth 8000 in
theorem coreFactory_intDiv :
    (Core.Factory)["Int.Div"]? = some (Lambda.intDivFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intDivFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.intDivFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

set_option maxRecDepth 8000 in
theorem coreFactory_intMod :
    (Core.Factory)["Int.Mod"]? = some (Lambda.intModFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intModFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.intModFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

set_option maxRecDepth 8000 in
theorem coreFactory_intGt :
    (Core.Factory)["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intGtFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.intGtFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

theorem intSub_opExpr :
    (Lambda.intSubFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Sub", ()⟩ (some (.arrow .int (.arrow .int .int))) : Expression.Expr) := by
  first | rfl | decide

theorem intDiv_opExpr :
    (Lambda.intDivFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Div", ()⟩ (some (.arrow .int (.arrow .int .int))) : Expression.Expr) := by
  first | rfl | decide

theorem intMod_opExpr :
    (Lambda.intModFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Mod", ()⟩ (some (.arrow .int (.arrow .int .int))) : Expression.Expr) := by
  first | rfl | decide

theorem intGt_opExpr :
    (Lambda.intGtFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Gt", ()⟩ (some (.arrow .int (.arrow .int .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem evalFully_intSub {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .int))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Sub", ()⟩ (some ty)) x) y)
      = some (.const () (.intConst (a - b))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.intConst () a, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.intConst () b, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.intSubFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.intConst () (a - b), .value true) :=
    fun n => eval_intBinOp_value_of_numerals Core.Factory σ x y n a b "Int.Sub" Int.sub
      (fun _ => true) (by decide) coreFactory_intSub rfl
      (Lambda.isValue_const_true Core.Factory () (.intConst (a - b)))
  rw [intSub_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intDiv {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .int)) (hb : b ≠ 0)
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Div", ()⟩ (some ty)) x) y)
      = some (.const () (.intConst (a / b))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.intConst () a, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.intConst () b, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.intDivFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.intConst () (a / b), .value true) :=
    fun n => eval_intBinOp_value_of_numerals Core.Factory σ x y n a b "Int.Div" (· / ·)
      (· != 0) (by decide) coreFactory_intDiv (by simpa using hb)
      (Lambda.isValue_const_true Core.Factory () (.intConst (a / b)))
  rw [intDiv_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intMod {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .int)) (hb : b ≠ 0)
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Mod", ()⟩ (some ty)) x) y)
      = some (.const () (.intConst (a % b))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.intConst () a, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.intConst () b, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.intModFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.intConst () (a % b), .value true) :=
    fun n => eval_intBinOp_value_of_numerals Core.Factory σ x y n a b "Int.Mod" (· % ·)
      (· != 0) (by decide) coreFactory_intMod (by simpa using hb)
      (Lambda.isValue_const_true Core.Factory () (.intConst (a % b)))
  rw [intMod_opExpr] at step
  exact evalFully_binop_of_step step hx hy

theorem evalFully_intGt {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int (.arrow .int .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Int.Gt", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (decide (a > b)))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.intConst () a, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.intConst () b, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.intGtFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (decide (a > b)), .value true) :=
    fun n => eval_intBinOp_value_of_numerals (OutValTy := Bool) Core.Factory σ x y n a b "Int.Gt" (· > ·)
      (fun _ => true) (by decide) coreFactory_intGt rfl
      (Lambda.isValue_const_true Core.Factory () (.boolConst (decide (a > b))))
  rw [intGt_opExpr] at step
  exact evalFully_binop_of_step step hx hy

/-! ## Equality and conditionals

`==` evaluates through `eql`, which decides two literals, and `if … then … else …` through the
literal its condition evaluates to. -/

/-- Metadata-insensitive equality of two literals is their structural equality. -/
theorem eqModuloMeta_const (c1 c2 : LConst) :
    LExpr.eqModuloMeta (.const () c1 : Expression.Expr) (.const () c2) = (c1 == c2) := by
  simp [LExpr.eqModuloMeta, LExpr.eraseMetadata, LExpr.replaceMetadata, BEq.beq, LExpr.beq]

theorem eql_const (c1 c2 : LConst) :
    LExpr.eql Core.Factory (.const () c1 : Expression.Expr) (.const () c2) = some (c1 == c2) := by
  simp only [LExpr.eql]
  rw [eqModuloMeta_const]
  cases hc : (c1 == c2) <;> simp

theorem eql_intConst (a b : Int) :
    LExpr.eql Core.Factory (.const () (.intConst a) : Expression.Expr) (.const () (.intConst b))
      = some (decide (a = b)) := by
  rw [eql_const]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

theorem eql_boolConst (p q : Bool) :
    LExpr.eql Core.Factory (.const () (.boolConst p) : Expression.Expr) (.const () (.boolConst q))
      = some (decide (p = q)) := by
  rw [eql_const]
  cases p <;> cases q <;> first | rfl | decide

theorem evalFully_eq_int {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.eq () x y) = some (.const () (.boolConst (decide (a = b)))) :=
  Lambda.evalFully_eq_of_evalFully Core.Factory σ () x y _ _ _ hx hy (eql_intConst a b)

theorem evalFully_eq_bool {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.boolConst q))) :
    LExpr.evalFully Core.Factory σ (.eq () x y) = some (.const () (.boolConst (decide (p = q)))) :=
  Lambda.evalFully_eq_of_evalFully Core.Factory σ () x y _ _ _ hx hy (eql_boolConst p q)

theorem evalFully_ite {σ : CoreStore} {c t e : Expression.Expr} {p : Bool} {vt vf : Expression.Expr}
    (hc : LExpr.evalFully Core.Factory σ c = some (.const () (.boolConst p)))
    (ht : LExpr.evalFully Core.Factory σ t = some vt)
    (he : LExpr.evalFully Core.Factory σ e = some vf) :
    LExpr.evalFully Core.Factory σ (.ite () c t e) = some (cond p vt vf) := by
  obtain ⟨nc, hnc, _⟩ := Lambda.evalFully_some_exists Core.Factory σ c _ hc
  obtain ⟨nt, hnt, _⟩ := Lambda.evalFully_some_exists Core.Factory σ t _ ht
  obtain ⟨ne, hne, _⟩ := Lambda.evalFully_some_exists Core.Factory σ e _ he
  have hc' := Lambda.eval_value_true_mono_le Core.Factory σ nc (max nc (max nt ne))
    (Nat.le_max_left _ _) c _ hnc
  have ht' := Lambda.eval_value_true_mono_le Core.Factory σ nt (max nc (max nt ne))
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) t _ hnt
  have he' := Lambda.eval_value_true_mono_le Core.Factory σ ne (max nc (max nt ne))
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) e _ hne
  refine Lambda.evalFully_of_value_true Core.Factory σ _ (max nc (max nt ne) + 1) _ ?_
  rw [Lambda.eval_succ_ite (max nc (max nt ne)) Core.Factory σ () c t e]
  cases p <;> simp [LExpr.evalIte, hc', ht', he', LExpr.EvalResult.combineValueFlag,
    LExpr.EvalResult.isValueTrue]

/-- A conditional whose branches are integer literals is the literal of a conditional. -/
theorem cond_intConst (p : Bool) (a b : Int) :
    (cond p (.const () (.intConst a) : Expression.Expr) (.const () (.intConst b)))
      = .const () (.intConst (cond p a b)) := by
  cases p <;> rfl

theorem cond_boolConst (p q r : Bool) :
    (cond p (.const () (.boolConst q) : Expression.Expr) (.const () (.boolConst r)))
      = .const () (.boolConst (cond p q r)) := by
  cases p <;> rfl

/-- `evalFully_ite` with literal branches, folded into one literal so that the condition's
normalization never reaches the expression level. -/
theorem evalFully_ite_int {σ : CoreStore} {c t e : Expression.Expr} {p : Bool} {a b : Int}
    (hc : LExpr.evalFully Core.Factory σ c = some (.const () (.boolConst p)))
    (ht : LExpr.evalFully Core.Factory σ t = some (.const () (.intConst a)))
    (he : LExpr.evalFully Core.Factory σ e = some (.const () (.intConst b))) :
    LExpr.evalFully Core.Factory σ (.ite () c t e) = some (.const () (.intConst (cond p a b))) := by
  rw [evalFully_ite hc ht he, cond_intConst]

theorem evalFully_ite_bool {σ : CoreStore} {c t e : Expression.Expr} {p q r : Bool}
    (hc : LExpr.evalFully Core.Factory σ c = some (.const () (.boolConst p)))
    (ht : LExpr.evalFully Core.Factory σ t = some (.const () (.boolConst q)))
    (he : LExpr.evalFully Core.Factory σ e = some (.const () (.boolConst r))) :
    LExpr.evalFully Core.Factory σ (.ite () c t e) = some (.const () (.boolConst (cond p q r))) := by
  rw [evalFully_ite hc ht he, cond_boolConst]

/-! ## Unary operators -/

set_option maxRecDepth 8000 in
theorem coreFactory_intNeg :
    (Core.Factory)["Int.Neg"]? = some (Lambda.intNegFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intNegFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.intNegFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

theorem intNeg_opExpr :
    (Lambda.intNegFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Int.Neg", ()⟩ (some (.arrow .int .int)) : Expression.Expr) := by
  first | rfl | decide

theorem boolNot_opExpr :
    (Lambda.boolNotFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool)) : Expression.Expr) := by
  first | rfl | decide

/-- The step of `Int.Neg` on a numeral, after `Core.eval_boolNot_value_iff`. -/
theorem eval_intNeg_value_of_numeral (f : Expression.Factory) (σ : CoreStore) (x : Expression.Expr)
    (n : Nat) (a : Int)
    (hI : f["Int.Neg"]? = some (Lambda.intNegFunc (T := CoreLParams)).func)
    (hx : LExpr.eval n f σ x = (LExpr.intConst () a, .value true)) :
    LExpr.eval (n + 1) f σ (.app () (Lambda.intNegFunc (T := CoreLParams)).opExpr x)
      = (LExpr.intConst () (-a), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (LExpr.app () (Lambda.intNegFunc (T := CoreLParams)).opExpr x)
      = some ((Lambda.intNegFunc (T := CoreLParams)).opExpr, [x],
              (Lambda.intNegFunc (T := CoreLParams)).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.intNegFunc, Lambda.unaryOp]
    rw [hI]
    simp [Lambda.intNegFunc, Lambda.unaryOp]
  have hcan : LExpr.isValue f
      (LExpr.app () (Lambda.intNegFunc (T := CoreLParams)).opExpr x) = false := by
    simp only [LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.intNegFunc, Lambda.unaryOp]
    rw [hI]
    simp [Lambda.intNegFunc, Lambda.unaryOp]
  simp only [LExpr.eval]
  rw [ite_eq_right (by simp [hcan]), hcall]
  dsimp only
  rw [LExpr.shortCircuitCall?_of_not_attr _
    (by simp [Strata.DL.Util.FuncAttr.hasShortCircuit, Lambda.intNegFunc, Lambda.unaryOp])]
  dsimp only
  simp only [Lambda.intNegFunc, Lambda.unaryOp, Option.isSome_none, Bool.false_and,
    Bool.false_eq_true, ↓reduceDIte]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfValue #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.or_false, Bool.and_true]
  rw [hx]
  simp only [LExpr.EvalResult.isValueTrue]
  have hcev : LambdaLeanType.cevalTy (ty := LMonoTy.int) (ValTy := Int) CoreLParams
      = LExpr.denoteInt := rfl
  have hmk : LambdaLeanType.mkConst (ty := LMonoTy.int) (ValTy := Int) CoreLParams
      = @LExpr.intConst CoreLParams.mono := rfl
  have hcani : ∀ (m : Unit) (i : Int), LExpr.isValue f (LExpr.intConst m i : Expression.Expr) = true := by
    intro m i; simp [LExpr.isValue, LExpr.intConst]
  have hdenote : LExpr.denoteInt (LExpr.intConst () a : Expression.Expr) = some a := rfl
  rw [ite_eq_left (by simp [hcani])]
  simp only [hcev, hmk, hdenote]
  rw [Lambda.eval_value_identity n f σ _ (hcani _ _)]
  simp only [LExpr.combineEvalResValueFlag_eq_pair, LExpr.EvalResult.combineValueFlag, Bool.and_self]
  rfl

theorem evalFully_intNeg {σ : CoreStore} {x : Expression.Expr} {a : Int}
    {ty : LMonoTy} (hty : ty = .arrow .int .int)
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.intConst a))) :
    LExpr.evalFully Core.Factory σ (.app () (.op () ⟨"Int.Neg", ()⟩ (some ty)) x)
      = some (.const () (.intConst (-a))) := by
  subst hty
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  have step := eval_intNeg_value_of_numeral Core.Factory σ x nx a coreFactory_intNeg hnx
  rw [intNeg_opExpr] at step
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ step

theorem evalFully_boolNot {σ : CoreStore} {x : Expression.Expr} {p : Bool}
    {ty : LMonoTy} (hty : ty = .arrow .bool .bool)
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p))) :
    LExpr.evalFully Core.Factory σ (.app () (.op () ⟨"Bool.Not", ()⟩ (some ty)) x)
      = some (.const () (.boolConst (!p))) := by
  subst hty
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  have step := (Core.eval_boolNot_value_iff Core.Factory σ x nx _ Core.coreFactory_boolNot).mpr
    ⟨p, hnx, rfl⟩
  rw [boolNot_opExpr] at step
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ step

/-! ## Short-circuit boolean operators

`Bool.And`, `Bool.Or` and `Bool.Implies` are `shortCircuitOp`s: the evaluator evaluates the
first operand alone and asks the operator's `concreteEval` whether that decides the result,
otherwise it continues with the second operand. On two boolean literals the result is the
Lean operation either way. -/

theorem eval_shortCircuitOp_value_of_bools (f : Expression.Factory) (σ : CoreStore)
    (x y : Expression.Expr) (n : Nat) (p q : Bool) (name : CoreLParams.Identifier)
    (absorb decided : Bool)
    (hI : f[name.name]? = some (Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).func)
    (hx : LExpr.eval n f σ x = (LExpr.boolConst () p, .value true))
    (hy : LExpr.eval n f σ y = (LExpr.boolConst () q, .value true)) :
    LExpr.eval (n + 1) f σ
        (.app () (.app () (Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).opExpr x) y)
      = (LExpr.boolConst () (if p == absorb then decided else q), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).opExpr x) y)
      = some ((Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).opExpr, [x, y],
              (Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr, Lambda.shortCircuitOp]
    rw [hI]
    simp [Lambda.shortCircuitOp]
  have hcan : LExpr.isValue f
      (.app () (.app () (Lambda.shortCircuitOp (T := CoreLParams) name absorb decided).opExpr x) y)
        = false := by
    simp only [LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.shortCircuitOp]
    rw [hI]
    simp [Lambda.shortCircuitOp]
  have hcev : LambdaLeanType.cevalTy (ty := LMonoTy.bool) (ValTy := Bool) CoreLParams
      = LExpr.denoteBool := rfl
  have hmk : LambdaLeanType.mkConst (ty := LMonoTy.bool) (ValTy := Bool) CoreLParams
      = @LExpr.boolConst CoreLParams.mono := rfl
  have hcanb : ∀ b : Bool, LExpr.isValue f (LExpr.boolConst () b : Expression.Expr) = true := by
    intro b; simp [LExpr.isValue, LExpr.boolConst]
  have hdb : LExpr.denoteBool (LExpr.boolConst () p : Expression.Expr) = some p := rfl
  have hsc : Strata.DL.Util.FuncAttr.hasShortCircuit #[Strata.DL.Util.FuncAttr.shortCircuit] = true := by
    first | rfl | decide
  simp only [LExpr.eval]
  rw [ite_eq_right (by simp [hcan]), hcall]
  dsimp only
  simp only [LExpr.shortCircuitCall?, Lambda.shortCircuitOp, hsc, ite_true]
  simp only [LExpr.evalShortCircuit, hx, hcanb, hcev, hmk, hdb, ite_true, LExpr.metadata]
  cases hpa : (p == absorb)
  · simp only [Bool.false_eq_true, ite_false, hy, LExpr.EvalResult.isValueTrue,
      LExpr.combineEvalResValueFlag_eq_pair, LExpr.EvalResult.combineValueFlag, Bool.and_true]
  · simp only [ite_true]
    rw [Lambda.eval_value_identity n f σ _ (hcanb _)]
    simp [LExpr.EvalResult.isValueTrue, LExpr.combineEvalResValueFlag_eq_pair,
      LExpr.EvalResult.combineValueFlag]

set_option maxRecDepth 8000 in
theorem coreFactory_boolImplies :
    (Core.Factory)["Bool.Implies"]? = some (Lambda.boolImpliesFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.boolImpliesFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.boolImpliesFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

set_option maxRecDepth 8000 in
theorem coreFactory_boolAnd' :
    (Core.Factory)["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.boolAndFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.boolAndFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

set_option maxRecDepth 8000 in
theorem coreFactory_boolOr' :
    (Core.Factory)["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.boolOrFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.boolOrFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

theorem boolAnd_opExpr :
    (Lambda.boolAndFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem boolOr_opExpr :
    (Lambda.boolOrFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Bool.Or", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : Expression.Expr) := by
  first | rfl | decide

theorem boolImplies_opExpr :
    (Lambda.boolImpliesFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Bool.Implies", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : Expression.Expr) := by
  first | rfl | decide

/-- `evalFully_binop_of_step` for operands that evaluate to boolean literals. -/
theorem evalFully_boolBinop_of_step {σ : CoreStore} {opE x y res : Expression.Expr} {p q : Bool}
    (step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.boolConst () p, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.boolConst () q, .value true) →
      LExpr.eval (n + 1) Core.Factory σ (.app () (.app () opE x) y) = (res, .value true))
    (hx : LExpr.evalFully Core.Factory σ x = some (LExpr.boolConst () p))
    (hy : LExpr.evalFully Core.Factory σ y = some (LExpr.boolConst () q)) :
    LExpr.evalFully Core.Factory σ (.app () (.app () opE x) y) = some res := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx' := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy' := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ (step (max nx ny) hx' hy')

theorem evalFully_boolAnd {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    {ty : LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.boolConst q))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (p && q))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.boolConst () p, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.boolConst () q, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolAndFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (p && q), .value true) := by
    intro n hx hy
    have h : LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolAndFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (if p == false then false else q), .value true) :=
      eval_shortCircuitOp_value_of_bools Core.Factory σ x y n p q "Bool.And" false false
        coreFactory_boolAnd' hx hy
    cases p <;> cases q <;> simpa using h
  rw [boolAnd_opExpr] at step
  exact evalFully_boolBinop_of_step step hx hy

theorem evalFully_boolOr {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    {ty : LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.boolConst q))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Bool.Or", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (p || q))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.boolConst () p, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.boolConst () q, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolOrFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (p || q), .value true) := by
    intro n hx hy
    have h : LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolOrFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (if p == true then true else q), .value true) :=
      eval_shortCircuitOp_value_of_bools Core.Factory σ x y n p q "Bool.Or" true true
        coreFactory_boolOr' hx hy
    cases p <;> cases q <;> simpa using h
  rw [boolOr_opExpr] at step
  exact evalFully_boolBinop_of_step step hx hy

theorem evalFully_boolImplies {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    {ty : LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.boolConst q))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Bool.Implies", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (!p || q))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.boolConst () p, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.boolConst () q, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolImpliesFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (!p || q), .value true) := by
    intro n hx hy
    have h : LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolImpliesFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (if p == false then true else q), .value true) :=
      eval_shortCircuitOp_value_of_bools Core.Factory σ x y n p q "Bool.Implies" false true
        coreFactory_boolImplies hx hy
    cases p <;> cases q <;> simpa using h
  rw [boolImplies_opExpr] at step
  exact evalFully_boolBinop_of_step step hx hy

/-! ## `Bool.Equiv`

`Bool.Equiv` is an ordinary `binaryOp` on booleans, evaluated like the integer operators. -/

set_option maxRecDepth 8000 in
theorem coreFactory_boolEquiv :
    (Core.Factory)["Bool.Equiv"]? = some (Lambda.boolEquivFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.boolEquivFunc (T := CoreLParams))
    (Array.mem_map.mpr ⟨Lambda.boolEquivFunc (T := CoreLParams), by wf_factory_mem, rfl⟩)

theorem boolEquiv_opExpr :
    (Lambda.boolEquivFunc (T := CoreLParams)).opExpr
      = (.op () ⟨"Bool.Equiv", ()⟩ (some (.arrow .bool (.arrow .bool .bool))) : Expression.Expr) := by
  first | rfl | decide

/-- `eval_intBinOp_value_of_numerals` for a `binaryOp` whose operands are boolean literals. -/
theorem eval_boolBinOp_value_of_bools
    {OutValTy : Type} {outTy : LMonoTy} [ToString OutValTy] [LambdaLeanType outTy OutValTy]
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr) (n : Nat) (p q : Bool)
    (name : CoreLParams.Identifier) (op : Bool → Bool → OutValTy) (guard : Bool → Bool)
    (hOutTy : outTy.freeVars = [])
    (hI : f[name.name]? = some (Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
      (hOutTy := hOutTy) (h_precond := by simp)).func)
    (hg : guard q = true)
    (hval : LExpr.isValue f (LambdaLeanType.mkConst (ValTy := OutValTy) CoreLParams () (op p q)) = true)
    (hx : LExpr.eval n f σ x = (LExpr.boolConst () p, .value true))
    (hy : LExpr.eval n f σ y = (LExpr.boolConst () q, .value true)) :
    LExpr.eval (n + 1) f σ
        (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
          (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y)
      = (LambdaLeanType.mkConst (ValTy := OutValTy) CoreLParams () (op p q), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
        (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y)
      = some ((Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
                (hOutTy := hOutTy) (h_precond := by simp)).opExpr,
              [x, y],
              (Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
                (hOutTy := hOutTy) (h_precond := by simp)).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr, Lambda.binaryOp]
    rw [hI]
    simp [Lambda.binaryOp]
  have hcan : LExpr.isValue f
      (.app () (.app () (Lambda.binaryOp (T := CoreLParams) (InValTy := Bool) name op guard
        (hOutTy := hOutTy) (h_precond := by simp)).opExpr x) y) = false := by
    simp only [LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.binaryOp]
    rw [hI]
    simp [Lambda.binaryOp]
  have hcanb : ∀ (b : Bool), LExpr.isValue f (LExpr.boolConst () b : Expression.Expr) = true := by
    intro b; simp [LExpr.isValue, LExpr.boolConst]
  simp only [LExpr.eval]
  rw [ite_eq_right (by simp [hcan]), hcall]
  dsimp only
  rw [LExpr.shortCircuitCall?_of_not_attr _
    (by simp [Strata.DL.Util.FuncAttr.hasShortCircuit, Lambda.binaryOp])]
  dsimp only
  simp only [Lambda.binaryOp]
  rw [dite_eq_right (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfValue #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : LambdaLeanType.cevalTy (ty := LMonoTy.bool) (ValTy := Bool) CoreLParams
      = LExpr.denoteBool := rfl
  simp only [hcev]
  have hdenote : LExpr.denoteBool (LExpr.boolConst () p : Expression.Expr) = some p := rfl
  have hdenote' : LExpr.denoteBool (LExpr.boolConst () q : Expression.Expr) = some q := rfl
  rw [ite_eq_left (by simp [hcanb])]
  simp only [hdenote, hdenote', hg, ite_true]
  rw [Lambda.eval_value_identity n f σ _ hval]
  simp [LExpr.combineEvalResValueFlag_eq_pair, LExpr.EvalResult.combineValueFlag]

theorem evalFully_boolEquiv {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    {ty : LMonoTy} (hty : ty = .arrow .bool (.arrow .bool .bool))
    (hx : LExpr.evalFully Core.Factory σ x = some (.const () (.boolConst p)))
    (hy : LExpr.evalFully Core.Factory σ y = some (.const () (.boolConst q))) :
    LExpr.evalFully Core.Factory σ (.app () (.app () (.op () ⟨"Bool.Equiv", ()⟩ (some ty)) x) y)
      = some (.const () (.boolConst (decide (p = q)))) := by
  subst hty
  have step : ∀ n, LExpr.eval n Core.Factory σ x = (LExpr.boolConst () p, .value true) →
      LExpr.eval n Core.Factory σ y = (LExpr.boolConst () q, .value true) →
      LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolEquivFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (decide (p = q)), .value true) := by
    intro n hx hy
    have h : LExpr.eval (n + 1) Core.Factory σ
          (.app () (.app () (Lambda.boolEquivFunc (T := CoreLParams)).opExpr x) y)
        = (LExpr.boolConst () (p == q), .value true) :=
      eval_boolBinOp_value_of_bools (OutValTy := Bool) Core.Factory σ x y n p q "Bool.Equiv"
        (· == ·) (fun _ => true) (by decide) coreFactory_boolEquiv rfl
        (Lambda.isValue_const_true Core.Factory () (.boolConst (p == q))) hx hy
    cases p <;> cases q <;> simpa using h
  rw [boolEquiv_opExpr] at step
  exact evalFully_boolBinop_of_step step hx hy

/-! ## Boolean normal forms

`&&`, `||` and `!` of decided propositions are the decision of the connective, so that a guard or
a clause built from them is read as one proposition. -/

theorem and_decide_eq {p q : Prop} [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := (Bool.decide_and p q).symm

theorem or_decide_eq {p q : Prop} [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := (Bool.decide_or p q).symm

theorem not_decide_eq {p : Prop} [Decidable p] : (!decide p) = decide (¬ p) := decide_not.symm

/-- `==>` lifts to an implication, not to the disjunction its encoding is. -/
theorem not_or_eq_imp (p q : Prop) : (¬ p ∨ q) = (p → q) :=
  propext ⟨fun h hp => h.elim (fun hn => absurd hp hn) id,
    fun h => (Classical.em p).elim (fun hp => .inr (h hp)) .inl⟩

/-! ## Guards -/

/-- A guard that evaluates to `boolConst (decide P)` and is reported `tt` decides `P`. -/
theorem tt_of_decide {σ : CoreStore} {cond : Expression.Expr} {P : Prop} [Decidable P]
    (hev : LExpr.evalFully Core.Factory σ cond = some (.const () (.boolConst (decide P))))
    (htt : LExpr.evalFully Core.Factory σ cond = some (Imperative.HasBool.tt : Expression.Expr)) : P := by
  have h := Option.some.inj (hev.symm.trans htt)
  simpa [LExpr.boolConst, Imperative.HasBool.tt, Core.true] using h

theorem ff_of_decide {σ : CoreStore} {cond : Expression.Expr} {P : Prop} [Decidable P]
    (hev : LExpr.evalFully Core.Factory σ cond = some (.const () (.boolConst (decide P))))
    (hff : LExpr.evalFully Core.Factory σ cond = some (Imperative.HasBool.ff : Expression.Expr)) : ¬ P := by
  have h := Option.some.inj (hev.symm.trans hff)
  simpa [LExpr.boolConst, Imperative.HasBool.ff, Core.false] using h

/-- The guard comparison the rules state, as the proposition it decides. -/
theorem some_boolConst_eq_tt_iff {P : Prop} [Decidable P] :
    (some (LExpr.const () (.boolConst (decide P))) = some (Imperative.HasBool.tt : Expression.Expr)) ↔ P := by
  simp [LExpr.boolConst, Imperative.HasBool.tt, Core.true]

theorem some_boolConst_eq_ff_iff {P : Prop} [Decidable P] :
    (some (LExpr.const () (.boolConst (decide P))) = some (Imperative.HasBool.ff : Expression.Expr)) ↔ ¬ P := by
  simp [LExpr.boolConst, Imperative.HasBool.ff, Core.false]

/-- The same comparison once `some` has been stripped from both sides. -/
theorem boolConst_eq_tt_iff {P : Prop} [Decidable P] :
    ((LExpr.const () (.boolConst (decide P)) : Expression.Expr) = (Imperative.HasBool.tt : Expression.Expr)) ↔ P := by
  simp [Imperative.HasBool.tt, Core.true, LExpr.boolConst]

theorem boolConst_eq_ff_iff {P : Prop} [Decidable P] :
    ((LExpr.const () (.boolConst (decide P)) : Expression.Expr) = (Imperative.HasBool.ff : Expression.Expr)) ↔ ¬ P := by
  simp [Imperative.HasBool.ff, Core.false, LExpr.boolConst]

/-- The same comparisons for an arbitrary boolean, as a guard built from `&&`, `||` or `!`
evaluates to. -/
theorem some_boolConst_eq_tt_iff' {b : Bool} :
    (some (LExpr.const () (.boolConst b)) = some (Imperative.HasBool.tt : Expression.Expr)) ↔ b = true := by
  cases b <;> simp [LExpr.boolConst, Imperative.HasBool.tt, Core.true]

theorem some_boolConst_eq_ff_iff' {b : Bool} :
    (some (LExpr.const () (.boolConst b)) = some (Imperative.HasBool.ff : Expression.Expr)) ↔ b = false := by
  cases b <;> simp [LExpr.boolConst, Imperative.HasBool.ff, Core.false]

theorem boolConst_eq_tt_iff' {b : Bool} :
    ((LExpr.const () (.boolConst b) : Expression.Expr) = (Imperative.HasBool.tt : Expression.Expr)) ↔ b = true := by
  cases b <;> simp [Imperative.HasBool.tt, Core.true, LExpr.boolConst]

theorem boolConst_eq_ff_iff' {b : Bool} :
    ((LExpr.const () (.boolConst b) : Expression.Expr) = (Imperative.HasBool.ff : Expression.Expr)) ↔ b = false := by
  cases b <;> simp [Imperative.HasBool.ff, Core.false, LExpr.boolConst]

/-! ## Store updates and projections -/

/-- A slot a block's exit did not drop reads as before the exit. -/
theorem dropVars_of_not_mem {D : List Expression.Ident} {σ : CoreStore} {x : Expression.Ident}
    (h : x ∉ D) : Imperative.dropVars D σ x = σ x := by
  simp [Imperative.dropVars, h]


theorem UpdateState.at_self {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    (h : Imperative.UpdateState Expression σ x v σ') : σ' x = some v := by
  cases h with | update _ hnew _ => exact hnew

theorem UpdateState.at_other {σ σ' : CoreStore} {x y : Expression.Ident} {v : Expression.Expr}
    (h : Imperative.UpdateState Expression σ x v σ') (hne : x ≠ y) : σ' y = σ y := by
  cases h with | update _ _ hrest => exact hrest y hne

/-- A slot the update did not touch, read through to its binding before the update. Unlike
`at_other`, the right-hand side is the binding itself, so `simp` does not take the lemma for
a permutation and can rewrite with it whenever the binding is known. -/
theorem UpdateState.at_other_lit {σ σ' : CoreStore} {x y : Expression.Ident} {v w : Expression.Expr}
    (h : Imperative.UpdateState Expression σ x v σ') (hne : x ≠ y) (hy : σ y = some w) :
    σ' y = some w := by
  rw [UpdateState.at_other h hne, hy]

theorem InitState.at_self {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    (h : Imperative.InitState Expression σ x v σ') : σ' x = some v := by
  cases h with | init _ hnew _ => exact hnew

theorem InitState.at_other {σ σ' : CoreStore} {x y : Expression.Ident} {v : Expression.Expr}
    (h : Imperative.InitState Expression σ x v σ') (hne : x ≠ y) : σ' y = σ y := by
  cases h with | init _ _ hrest => exact hrest y hne

theorem InitState.at_other_lit {σ σ' : CoreStore} {x y : Expression.Ident} {v w : Expression.Expr}
    (h : Imperative.InitState Expression σ x v σ') (hne : x ≠ y) (hy : σ y = some w) :
    σ' y = some w := by
  rw [InitState.at_other h hne, hy]

end Strata.Hoare.Eval

end -- public section
