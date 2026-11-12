/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.HoareLogic.Hoare.WP
public import StrataBoole.HoareLogic.Hoare.Lift.Eval
public import StrataBoole.HoareLogic.Hoare.Lift.Denote
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import all Strata.DL.Lambda.LState

/-! # From a procedure's contract to the rules and back

`Procedure.contractTriple` is the statement a user proves. Its entry,
`Procedure.contractTriple_of_core_typed`, asks for one triple per model from `contractPre` to
`contractPost` around the procedure body wrapped in a block. The lemmas here read both ends:

* `contractPre` gives the ambient factory, a literal for every integer input (`input_int`) and
  the `requires` clauses in a chosen valuation (`requires_denote`);
* `contractPost` is one `checkAsPredicate` per non-free `ensures`, which `checkAsPredicate_iff`
  turns into the denotation of the clause with the store substituted, in every valuation.

Both go through `holds_iff`, the reading of `DenoteBasedInterp` when the condition's factory
is the ambient one; `clause_intro` and `clause_denote` are the same reading for any captured
condition, which covers `assert` and the loop invariants.

`loopInv` is the invariant `while_wp` is given: besides the program's `invariant` clauses it
carries what the rules after the loop rely on and `while_rule` would otherwise forget, the
ambient factory and the typed bindings of the variables the loop mentions. -/

public section

namespace Strata.Hoare

open Core.Logic Core.Logic.Hoare

/-! ## Entry -/

theorem contract_intro (p : Core.Program) (params : InitEnvWFParams) (procName : String)
    (proc : Core.Procedure) (bss : Core.Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : ∀ model : Lambda.Interp Core.Factory,
      Model.TripleM p.findProcByString? params (model := model)
        (Procedure.contractPre model proc) [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost model proc)) :
    Procedure.contractTriple p params procName :=
  Procedure.contractTriple_of_core_typed p params procName proc bss hproc hbody hchecksTyped h

/-! ## Reading conditions -/

/-- An arbitrary valuation, to read a `requires` clause in. -/
def someValuation (model : Lambda.Interp Core.Factory) : DenoteValuation model where
  tyVarVal := fun _ => .bool
  freeVarVal := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  offFactoryHolds := fun _ => False

/-- Under the ambient factory, a condition holds in a valuation when its captured expression
denotes `true` there. -/
theorem holds_iff (model : Lambda.Interp Core.Factory) (world : DenoteValuation model)
    (c : Imperative.EventArg Core.Expression) (hfac : c.factory = Core.Factory) :
    (DenoteBasedInterp model).holds world c ↔
      ∃ h : Lambda.LExpr.HasTypeA [] (capturedExpr c) .bool,
        Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp
          world.freeVarVal world.tyVarVal .nil (capturedExpr c) .bool h) = true := by
  simp only [DenoteBasedInterp, hfac, true_and, ne_eq, not_true_eq_false, false_and, or_false]
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨h, hd⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, hd⟩

/-- The event argument a contract clause is checked as. -/
abbrev clauseArg (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) : Imperative.EventArg Core.Expression :=
  { factory := ρ.factory, store := ρ.store, label := label, expr := check.expr, metadata := check.md }

theorem checkAsPredicate_iff (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Core.Expression) (hfac : ρ.factory = Core.Factory)
    (label : Core.CoreLabel) (check : Core.Procedure.Check) :
    Procedure.checkAsPredicate model ρ label check ↔
      ∀ (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp) (vt : Lambda.TyVarVal),
        ∃ h : Lambda.LExpr.HasTypeA [] (capturedExpr (clauseArg ρ label check)) .bool,
          Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
            (capturedExpr (clauseArg ρ label check)) .bool h) = true := by
  constructor
  · intro hall fv vt
    exact (holds_iff model ⟨vt, fv, fun _ => False⟩ _ hfac).mp (hall ⟨vt, fv, fun _ => False⟩)
  · intro hden world
    exact (holds_iff model world _ hfac).mpr (hden world.freeVarVal world.tyVarVal)

/-! ## The precondition -/

/-- Quantification over the members of a signature, one binding at a time. -/
theorem forall_mem_cons_pair {α β : Type _} {P : α → β → Prop} {x : α} {τ : β}
    {rest : List (α × β)} :
    (∀ id ty, (id, ty) ∈ (x, τ) :: rest → P id ty) ↔
      P x τ ∧ ∀ id ty, (id, ty) ∈ rest → P id ty := by
  constructor
  · intro h
    exact ⟨h x τ (List.mem_cons_self ..), fun id ty hm => h id ty (List.mem_cons_of_mem _ hm)⟩
  · rintro ⟨hx, hrest⟩ id ty hm
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq
      exact hx
    · exact hrest id ty hm

theorem forall_mem_nil_pair {α β : Type _} {P : α → β → Prop} :
    (∀ id ty, (id, ty) ∈ ([] : List (α × β)) → P id ty) ↔ True := by
  simp

/-- Quantification over the members of a list, one element at a time. -/
theorem forall_mem_cons_elem {α : Type _} {P : α → Prop} {x : α} {rest : List α} :
    (∀ a ∈ x :: rest, P a) ↔ P x ∧ ∀ a ∈ rest, P a := by
  constructor
  · intro h
    exact ⟨h x (List.mem_cons_self ..), fun a hm => h a (List.mem_cons_of_mem _ hm)⟩
  · rintro ⟨hx, hrest⟩ a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hx
    · exact hrest a hm

theorem forall_mem_nil_elem {α : Type _} {P : α → Prop} :
    (∀ a ∈ ([] : List α), P a) ↔ True := by
  simp

/-- `valueHasType` at `int`, with the type written as the type checker annotates it and the
literal in the constructor form the evaluation lemmas use. -/
theorem valueHasType_int_iff (v : Core.Expression.Expr) :
    Procedure.valueHasType (.tcons "int" []) v ↔ ∃ i : Int, v = .const () (.intConst i) :=
  Iff.rfl

/-- The binding of an integer input, with the literal in place of the bound value. -/
theorem exists_store_intConst (ρ : Imperative.Env Core.Expression) (x : Core.Expression.Ident) :
    (∃ v, ρ.store x = some v ∧ ∃ i : Int, v = .const () (.intConst i)) ↔
      ∃ i : Int, ρ.store x = some (.const () (.intConst i)) := by
  constructor
  · rintro ⟨v, hv, i, rfl⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, hi, i, rfl⟩

/-- `exists_store_intConst` over a bare store, for a slot read after an update. -/
theorem exists_store_intConst' (σ : Core.CoreStore) (x : Core.Expression.Ident) :
    (∃ v, σ x = some v ∧ ∃ i : Int, v = .const () (.intConst i)) ↔
      ∃ i : Int, σ x = some (.const () (.intConst i)) := by
  constructor
  · rintro ⟨v, hv, i, rfl⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, hi, i, rfl⟩

/-- The forward direction of `exists_store_intConst'`, for destructuring a binding. -/
theorem store_intConst_of {σ : Core.CoreStore} {x : Core.Expression.Ident}
    (h : ∃ v, σ x = some v ∧ ∃ i : Int, v = .const () (.intConst i)) :
    ∃ i : Int, σ x = some (.const () (.intConst i)) :=
  (exists_store_intConst' σ x).mp h

/-- A typed integer input is bound to an integer literal. -/
theorem input_int {proc : Core.Procedure} {ρ : Imperative.Env Core.Expression}
    (hin : Procedure.inputAsPredicate proc ρ) {x : Core.Expression.Ident}
    (hmem : (x, Lambda.LMonoTy.int) ∈ proc.header.inputs.toList) :
    ∃ a : Int, ρ.store x = some (.const () (.intConst a)) := by
  obtain ⟨v, hv, a, rfl⟩ := hin x .int hmem
  exact ⟨a, hv⟩

/-- A `requires` clause, read in the valuation `someValuation`. -/
theorem requires_denote {model : Lambda.Interp Core.Factory} {proc : Core.Procedure}
    {ρ : Imperative.Env Core.Expression}
    (hpre : Procedure.preAsPredicate model proc ρ) (hfac : ρ.factory = Core.Factory)
    {label : Core.CoreLabel} {check : Core.Procedure.Check}
    (hmem : (label, check) ∈ proc.spec.preconditions.toList) :
    ∃ h : Lambda.LExpr.HasTypeA [] (capturedExpr (clauseArg ρ label check)) .bool,
      Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp
        (someValuation model).freeVarVal (someValuation model).tyVarVal .nil
        (capturedExpr (clauseArg ρ label check)) .bool h) = true :=
  (checkAsPredicate_iff model ρ hfac label check).mp (hpre label check hmem) _ _


/-! ## Captured conditions -/

theorem capturedExpr_condArg (ρ : Imperative.Env Core.Expression) (label : String)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) :
    capturedExpr (condArg ρ label e md)
      = Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk ρ.store) e :=
  rfl

theorem condArg_factory (ρ : Imperative.Env Core.Expression) (label : String)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) :
    (condArg ρ label e md).factory = ρ.factory :=
  rfl

/-- A captured condition holds in every valuation once its expression denotes `true` in each. -/
theorem clause_intro {model : Lambda.Interp Core.Factory} {c : Imperative.EventArg Core.Expression}
    (hfac : c.factory = Core.Factory)
    (h : ∀ (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp) (vt : Lambda.TyVarVal),
      ∃ hty : Lambda.LExpr.HasTypeA [] (capturedExpr c) .bool,
        Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
          (capturedExpr c) .bool hty) = true) :
    ClauseHolds model c :=
  fun world => (holds_iff model world c hfac).mpr (h _ _)

/-- A captured condition that holds, read in `someValuation`. -/
theorem clause_denote {model : Lambda.Interp Core.Factory} {c : Imperative.EventArg Core.Expression}
    (h : ClauseHolds model c) (hfac : c.factory = Core.Factory) :
    ∃ hty : Lambda.LExpr.HasTypeA [] (capturedExpr c) .bool,
      Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp
        (someValuation model).freeVarVal (someValuation model).tyVarVal .nil
        (capturedExpr c) .bool hty) = true :=
  (holds_iff model _ c hfac).mp (h _)

/-! ## Reading a store through a frame

A loop obligation knows the store it runs on agrees with the entry store outside the body's
write set `M`. A statement of the body preserves that agreement, and a variable outside `M`
is read at the entry store. -/

theorem agreeExcept_update {M : List Core.Expression.Ident} {σ σ' : Core.CoreStore}
    {y : Core.Expression.Ident} {v : Core.Expression.Expr}
    (hup : Imperative.UpdateState Core.Expression σ y v σ') (hy : y ∈ M) :
    agreeExcept M σ' σ :=
  fun _ hx => Eval.UpdateState.at_other hup (fun h => hx (h ▸ hy))

theorem agreeExcept_init {M : List Core.Expression.Ident} {σ σ' : Core.CoreStore}
    {y : Core.Expression.Ident} {v : Core.Expression.Expr}
    (hini : Imperative.InitState Core.Expression σ y v σ') (hy : y ∈ M) :
    agreeExcept M σ' σ :=
  fun _ hx => Eval.InitState.at_other hini (fun h => hx (h ▸ hy))

theorem agreeExcept_read {M : List Core.Expression.Ident} {σ σ₀ : Core.CoreStore}
    {x : Core.Expression.Ident} (h : agreeExcept M σ σ₀) (hx : x ∉ M) : σ x = σ₀ x :=
  h x hx

/-! ## Loop invariants -/

/-- The variables of `Γ` are bound to values of their types. -/
@[expose] def typedVars (Γ : List (Core.Expression.Ident × Lambda.LMonoTy)) : Pred :=
  fun ρ => ∀ id ty, (id, ty) ∈ Γ → ∃ v, ρ.store id = some v ∧ Procedure.valueHasType ty v

/-- The invariant of a loop: the ambient factory, the typed bindings of the variables in `Γ`,
and each `invariant` clause holding in every valuation. -/
@[expose] def loopInv (model : Lambda.Interp Core.Factory)
    (Γ : List (Core.Expression.Ident × Lambda.LMonoTy))
    (inv : List (String × Core.Expression.Expr)) : Pred :=
  fun ρ => ρ.factory = Core.Factory ∧ typedVars Γ ρ ∧
    ∀ lc ∈ inv, ClauseHolds model (condArg ρ lc.1 lc.2 #[])

theorem loopInv_intro {model : Lambda.Interp Core.Factory}
    {Γ : List (Core.Expression.Ident × Lambda.LMonoTy)}
    {inv : List (String × Core.Expression.Expr)} {ρ : Imperative.Env Core.Expression}
    (hfac : ρ.factory = Core.Factory) (hΓ : typedVars Γ ρ)
    (hinv : ∀ lc ∈ inv, ClauseHolds model (condArg ρ lc.1 lc.2 #[])) :
    loopInv model Γ inv ρ :=
  ⟨hfac, hΓ, hinv⟩

/-! ## The postcondition -/

/-- `contractPost` clause by clause, over the list of `ensures`. -/
theorem contractPost_intro {model : Lambda.Interp Core.Factory} {proc : Core.Procedure}
    {ρ : Imperative.Env Core.Expression} (hfac : ρ.factory = Core.Factory)
    (h : ∀ lc ∈ proc.spec.postconditions.toList,
      lc.2.attr = Core.Procedure.CheckAttr.Default →
      ∀ (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp) (vt : Lambda.TyVarVal),
        ∃ hty : Lambda.LExpr.HasTypeA [] (capturedExpr (clauseArg ρ lc.1 lc.2)) .bool,
          Denote.toBool (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
            (capturedExpr (clauseArg ρ lc.1 lc.2)) .bool hty) = true) :
    Procedure.contractPost model proc ρ := by
  intro label check hmem hattr
  exact (checkAsPredicate_iff model ρ hfac label check).mpr (h (label, check) hmem hattr)

/-- The captured expression of a clause, unfolded to the substitution it is. -/
theorem capturedExpr_clause (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) :
    capturedExpr (clauseArg ρ label check)
      = Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk ρ.store) check.expr :=
  rfl

/-! ## The substitution, node by node

`substFvarsFromEnv` replaces each variable by its binding in the store. Its equations are
restated here so that they can drive `simp` from any file. -/

section Subst

variable (σ : Core.CoreStore)

theorem substFvars_const (m : Unit) (κ : Lambda.LConst) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.const m κ)
      = .const m κ := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_op (m : Unit) (o : Core.Expression.Ident) (ty : Option Lambda.LMonoTy) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.op m o ty)
      = .op m o ty := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_bvar (m : Unit) (i : Nat) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.bvar m i)
      = .bvar m i := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_fvar {x : Core.Expression.Ident} {v : Core.Expression.Expr}
    (m : Unit) (ty : Option Lambda.LMonoTy) (hx : σ x = some v) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.fvar m x ty) = v := by
  simp [Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hx]

theorem substFvars_app (m : Unit) (f a : Core.Expression.Expr) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.app m f a)
      = .app m (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) f)
          (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) a) := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_eq (m : Unit) (a b : Core.Expression.Expr) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.eq m a b)
      = .eq m (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) a)
          (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) b) := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_ite (m : Unit) (c t e : Core.Expression.Expr) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.ite m c t e)
      = .ite m (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) c)
          (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) t)
          (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) e) := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_abs (m : Unit) (nm : String) (ty : Option Lambda.LMonoTy)
    (e : Core.Expression.Expr) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.abs m nm ty e)
      = .abs m nm ty (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) e) := by
  simp [Lambda.LExpr.substFvarsFromEnv]

theorem substFvars_quant (m : Unit) (qk : Lambda.QuantifierKind) (nm : String)
    (ty : Option Lambda.LMonoTy) (tr e : Core.Expression.Expr) :
    Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams) (Lambda.Env.mk σ) (.quant m qk nm ty tr e)
      = .quant m qk nm ty (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) tr)
          (Lambda.LExpr.substFvarsFromEnv (Lambda.Env.mk σ) e) := by
  simp [Lambda.LExpr.substFvarsFromEnv]

end Subst

end Strata.Hoare

end -- public section
