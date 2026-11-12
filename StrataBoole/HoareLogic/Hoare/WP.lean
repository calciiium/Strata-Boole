/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.HoareLogic.Hoare.Rules
import all Strata.DL.Imperative.Logic.HoareTemplate

/-! # The rules in weakest-precondition form

Each rule here has the shape `TripleM (wp Q) [s] Q`: the postcondition is a parameter, the
precondition is a named predicate computed from it. Applied to a goal whose precondition is a
metavariable, `apply` fills that metavariable by unification, so a driver that walks a statement
list with these rules never writes a predicate itself. The named predicates (`wpSet`, `wpIte`, …)
are also what a verification-condition function would produce, which keeps the two drivers'
goals identical.

The glue the Core rules lack: `exists_pre` introduces a value the precondition fixes (the
literal behind a typed input), `frame_const` carries a closed fact past a statement list, and
`vc_entry` splits a goal into the rule-driven part and one implication at the entry.

`Core.Logic.Hoare` has no rule for `assert`, `assume`, `havoc` or an uninitialized `var`; theirs
come from the generic command rule and the command semantics. The `while` rule takes the
invariant as a predicate, left to the caller: `Contract.lean` builds it from the program's
`invariant` clauses.

A block, a branch or a loop body that declares variables drops them on exit. The rules
`block_wp`, `ite_wp` and `while_wp` ask for `PostWF`, which a driver discharges only when nothing
is declared. Their primed versions carry the projection in the postcondition instead (`wpProj`):
the verification conditions then read the store through `dropVars`, which the lifting handles
like an update, and no stability of a synthesized predicate is ever asked. -/

public section

namespace Strata.Hoare

open Core.Logic

variable (π : String → Option Core.Procedure) (params : Core.Logic.InitEnvWFParams)
variable {model : Lambda.Interp Core.Factory}

/-- Assertions over Core environments. -/
abbrev Pred := Imperative.Env Core.Expression → Prop

/-! ## Entry -/

/-- The precondition the rules synthesize is implied by the given one. -/
theorem vc_entry {P Pre Q : Pred} {ss : Core.Statements}
    (h : Model.TripleM π params (model := model) P ss Q) (himp : ∀ ρ, Pre ρ → P ρ) :
    Model.TripleM π params (model := model) Pre ss Q :=
  Model.consequence π params h himp (fun _ h => h)

/-- A value the precondition fixes can be introduced before any rule runs. -/
theorem exists_pre {α : Sort _} {P : α → Pred} {ss : Core.Statements} {Q : Pred}
    (h : ∀ a, Model.TripleM π params (model := model) (P a) ss Q) :
    Model.TripleM π params (model := model) (fun ρ => ∃ a, P a ρ) ss Q := by
  intro ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨a, ha⟩ := hpre
  exact h a ρ₀ ρ' trace ha hinit hrun

/-- A closed fact survives any statement list. -/
theorem frame_const {Pre Post : Pred} {ss : Core.Statements} (C : Prop)
    (h : Model.TripleM π params (model := model) Pre ss Post) :
    Model.TripleM π params (model := model) (fun ρ => Pre ρ ∧ C) ss (fun ρ => Post ρ ∧ C) := by
  by_cases hC : C
  · exact Model.consequence π params h (fun _ hp => hp.1) (fun _ hp => ⟨hp, hC⟩)
  · exact Model.consequence π params (Model.false_pre π params ss (fun ρ => Post ρ ∧ C))
      (fun _ hp => hC hp.2) (fun _ hp => hp)

/-! ## Statements -/

/-- The empty statement list. -/
theorem nil_wp (Q : Pred) : Model.TripleM π params (model := model) Q [] Q :=
  Model.nil π params Q

/-- Peel one statement off the front; `Mid` is left to unification. Stated for two or more
statements, so that a single unsupported statement stops a driver instead of looping. -/
theorem seq_cons {s s' : Core.Statement} {ss : Core.Statements} {Pre Mid Post : Pred}
    (h₁ : Model.TripleM π params (model := model) Pre [s] Mid)
    (h₂ : Model.TripleM π params (model := model) Mid (s' :: ss) Post)
    (hnoesc : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] [s]) :
    Model.TripleM π params (model := model) Pre (s :: s' :: ss) Post :=
  Model.seq π params h₁ h₂ hnoesc

/-- Weakest precondition of `x := e`, read off the premise of the `set` rule. -/
@[expose] def wpSet (Q : Pred) (x : Core.Expression.Ident) (e : Core.Expression.Expr) : Pred :=
  fun ρ => ∀ σ' v, Core.Expression.eval ρ.factory ρ.store e = some v →
    Imperative.UpdateState Core.Expression ρ.store x v σ' → Q { ρ with store := σ' }

theorem set_wp (Q : Pred) (x : Core.Expression.Ident) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpSet Q x e) [Core.Statement.set x e md] Q := by
  apply Model.set
  intro ρ₀ σ' v h hev hup
  exact h σ' v hev hup

/-- Weakest precondition of `var x : ty := e`. -/
@[expose] def wpInit (Q : Pred) (x : Core.Expression.Ident) (e : Core.Expression.Expr) : Pred :=
  fun ρ => ∀ σ' v, Core.Expression.eval ρ.factory ρ.store e = some v →
    Imperative.InitState Core.Expression ρ.store x v σ' → Q { ρ with store := σ' }

theorem init_wp (Q : Pred) (x : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpInit Q x e)
      [Core.Statement.init x ty (.det e) md] Q := by
  apply Model.init
  intro ρ₀ σ' v h hev hup
  exact h σ' v hev hup

/-- Weakest precondition of `if cond then … else …`, given those of the two branches. -/
@[expose] def wpIte (cond : Core.Expression.Expr) (T E : Pred) : Pred :=
  fun ρ => (Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.tt → T ρ) ∧
           (Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.ff → E ρ)

theorem ite_wp {cond : Core.Expression.Expr} {tss ess : Core.Statements}
    {md : Imperative.MetaData Core.Expression} {T E Q : Pred}
    (ht : Model.TripleM π params (model := model) T tss Q)
    (he : Model.TripleM π params (model := model) E ess Q)
    (hwt : Imperative.Logic.Hoare.PostWF tss Q) (hwe : Imperative.Logic.Hoare.PostWF ess Q) :
    Model.TripleM π params (model := model) (wpIte cond T E) [.ite (.det cond) tss ess md] Q :=
  Model.ite π params
    (Model.consequence π params ht (fun _ h => h.1.1 h.2) (fun _ h => h))
    (Model.consequence π params he (fun _ h => h.1.2 h.2) (fun _ h => h))
    hwt hwe

/-- A block: the precondition is the body's. -/
theorem block_wp {ss : Core.Statements} {l : String} {md : Imperative.MetaData Core.Expression}
    {P Q : Pred}
    (h : Model.TripleM π params (model := model) P ss Q)
    (hwf : Imperative.Logic.Hoare.PostWF ss Q) :
    Model.TripleM π params (model := model) P [.block l ss md] Q :=
  Model.block π params h hwf

/-! ## Declarations that go out of scope -/

/-- `Q` at the environment that leaves a block which declared the names `D`. -/
@[expose] def wpProj (D : List Core.Expression.Ident) (Q : Pred) : Pred :=
  fun ρ => Q { ρ with store := Imperative.dropVars D ρ.store }

theorem dropVars_idem (D : List Core.Expression.Ident) (σ : Core.CoreStore) :
    Imperative.dropVars D (Imperative.dropVars D σ) = Imperative.dropVars D σ := by
  funext x
  simp only [Imperative.dropVars]
  split <;> simp_all

/-- A projected postcondition is stable under the projection: dropping twice is dropping once. -/
theorem postWF_proj {ss : Core.Statements} {D : List Core.Expression.Ident}
    (hD : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ss true = D)
    (Q : Pred) : Imperative.Logic.Hoare.PostWF ss (wpProj D Q) := by
  intro ρ h
  simp only [wpProj, hD, dropVars_idem]
  exact h

/-- A block that declares `D`: the body ends in `Q` with `D` dropped. -/
theorem block_wp' {ss : Core.Statements} {l : String} {md : Imperative.MetaData Core.Expression}
    (D : List Core.Expression.Ident)
    (hD : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ss true = D)
    {P Q : Pred}
    (h : Model.TripleM π params (model := model) P ss (wpProj D Q)) :
    Model.TripleM π params (model := model) P [.block l ss md] Q := by
  subst hD
  exact Model.block_proj π params h

/-- `if` with branches that declare `Dt` and `De`. -/
theorem ite_wp' {cond : Core.Expression.Expr} {tss ess : Core.Statements}
    {md : Imperative.MetaData Core.Expression}
    (Dt De : List Core.Expression.Ident)
    (hDt : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) tss true = Dt)
    (hDe : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ess true = De)
    {T E Q : Pred}
    (ht : Model.TripleM π params (model := model) T tss (wpProj Dt Q))
    (he : Model.TripleM π params (model := model) E ess (wpProj De Q)) :
    Model.TripleM π params (model := model) (wpIte cond T E) [.ite (.det cond) tss ess md] Q := by
  subst hDt hDe
  exact Model.ite_proj π params
    (Model.consequence π params ht (fun _ h => h.1.1 h.2) (fun _ h => h))
    (Model.consequence π params he (fun _ h => h.1.2 h.2) (fun _ h => h))

/-! ## Conditions checked against the model

An `assert`, a loop invariant and an `ensures` clause are checked alike: the condition is
captured with the current store and must hold in every valuation of the model. -/

/-- The condition a statement or clause captures at `ρ`. -/
@[expose] def condArg (ρ : Imperative.Env Core.Expression) (label : String)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) :
    Imperative.EventArg Core.Expression :=
  { factory := ρ.factory, store := ρ.store, label := label, expr := e, metadata := md }

/-- The captured condition holds in every valuation of the model. -/
@[expose] def ClauseHolds (model : Lambda.Interp Core.Factory)
    (c : Imperative.EventArg Core.Expression) : Prop :=
  ∀ world, (DenoteBasedInterp model).holds world c

/-- Weakest precondition of `assert`: the condition holds, and the rest. -/
@[expose] def wpAssert (model : Lambda.Interp Core.Factory) (Q : Pred) (label : String)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) : Pred :=
  fun ρ => ClauseHolds model (condArg ρ label e md) ∧ Q ρ

theorem assert_wp (Q : Pred) (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpAssert model Q label e md)
      [Core.Statement.assert label e md] Q := by
  apply Model.cmd
  intro ρ₀ σ' emitted hpre _ hstep
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assert => exact ⟨⟨fun _ world _ => hpre.1 world, trivial⟩, fun _ => hpre.2⟩

/-- Weakest precondition of `assume`: the rest, under the condition in some valuation. -/
@[expose] def wpAssume (model : Lambda.Interp Core.Factory) (Q : Pred) (label : String)
    (e : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) : Pred :=
  fun ρ => (∃ world, (DenoteBasedInterp model).holds world (condArg ρ label e md)) → Q ρ

theorem assume_wp (Q : Pred) (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpAssume model Q label e md)
      [Core.Statement.assume label e md] Q := by
  apply Model.cmd
  intro ρ₀ σ' emitted hpre _ hstep
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assume =>
      refine ⟨trivial, fun hreach => hpre ?_⟩
      obtain ⟨world, hw⟩ := hreach
      exact ⟨world, hw _ (List.Mem.head _)⟩

/-- Weakest precondition of `havoc x`: the rest, for every value of the stored type. -/
@[expose] def wpHavoc (Q : Pred) (x : Core.Expression.Ident) : Pred :=
  fun ρ => ∀ σ' v, Imperative.UpdateState Core.Expression ρ.store x v σ' →
    Imperative.HasVal.valueOfStoredTy (P := Core.Expression) ρ.factory ρ.store x v →
    Q { ρ with store := σ' }

theorem havoc_wp (Q : Pred) (x : Core.Expression.Ident) (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpHavoc Q x) [Core.Statement.havoc x md] Q := by
  apply Model.cmd
  intro ρ₀ σ' emitted hpre _ hstep
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_set_nondet hup hty _ => exact ⟨trivial, fun _ => hpre σ' _ hup hty⟩

/-- Weakest precondition of `var x : ty` without an initializer: the rest, for every value of
the type. -/
@[expose] def wpInitNondet (Q : Pred) (x : Core.Expression.Ident) (ty : Core.Expression.Ty) : Pred :=
  fun ρ => ∀ σ' v, Imperative.InitState Core.Expression ρ.store x v σ' →
    Imperative.HasVal.valueOfTy (P := Core.Expression) ρ.factory v ty →
    Q { ρ with store := σ' }

theorem init_nondet_wp (Q : Pred) (x : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) (wpInitNondet Q x ty)
      [Core.Statement.init x ty .nondet md] Q := by
  apply Model.cmd
  intro ρ₀ σ' emitted hpre _ hstep
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_init_unconstrained hini hty _ => exact ⟨trivial, fun _ => hpre σ' _ hini hty⟩

/-! ## Loops -/

/-- `while` with the invariant `I`: the loop is entered with `I`, and leaves `Q` provided the
body re-establishes `I` from `I` and the guard (`step`) and `Q` follows from `I` and the
negated guard (`exit`). `B` is the precondition the rules synthesize for the body, so `step`
is the preservation obligation and `exit` the exit obligation. -/
theorem while_wp (I : Pred) {guard : Core.Expression.Expr} {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} {B Q : Pred}
    (hbody : Model.TripleM π params (model := model) B body I)
    (step : ∀ ρ, I ρ →
      Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.tt → B ρ)
    (exit : ∀ ρ, I ρ →
      Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.ff → Q ρ)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body)
    (hwf : Imperative.Logic.Hoare.PostWF body I) :
    Model.TripleM π params (model := model) I [.loop (.det guard) measure inv body md] Q :=
  Model.consequence π params
    (Model.while_rule π params
      (Model.consequence π params hbody (fun ρ h => step ρ h.1 h.2) (fun _ h => h)) hcov hwf)
    (fun _ h => h) (fun ρ h => exit ρ h.1 h.2)

/-- `while` whose body declares `D`: the invariant is read at the environment with `D` dropped,
which makes it stable by construction, so no `PostWF` is asked. -/
theorem while_wp' (I : Pred) {guard : Core.Expression.Expr} {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} (D : List Core.Expression.Ident)
    (hD : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) body true = D)
    {B Q : Pred}
    (hbody : Model.TripleM π params (model := model) B body (wpProj D I))
    (step : ∀ ρ, wpProj D I ρ →
      Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.tt → B ρ)
    (exit : ∀ ρ, wpProj D I ρ →
      Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.ff → Q ρ)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body) :
    Model.TripleM π params (model := model) (wpProj D I) [.loop (.det guard) measure inv body md] Q :=
  while_wp π params (wpProj D I) hbody step exit hcov (postWF_proj hD I)

/-! ## Framing a loop

`while_wp` knows nothing after the loop about a variable the body never assigns: its value is
whatever the invariant allows, and what was known about it at the entry is lost. The loop only
changes the variables its body writes, so the step and exit obligations can be stated at an
environment that agrees with the entry environment outside that write set, as the loop rule of
a verification-condition generator does. `while_wp_frame` is that rule: its precondition is the
invariant at the entry together with the two obligations, each quantified over the environments
that agree with the entry one outside `M`. -/

/-- `σ` agrees with `σ₀` on every variable outside `M`. -/
@[expose] def agreeExcept (M : List Core.Expression.Ident) (σ σ₀ : Core.CoreStore) : Prop :=
  ∀ x, x ∉ M → σ x = σ₀ x

theorem agreeExcept_refl (M : List Core.Expression.Ident) (σ : Core.CoreStore) :
    agreeExcept M σ σ := fun _ _ => rfl

theorem agreeExcept_symm {M : List Core.Expression.Ident} {σ σ' : Core.CoreStore}
    (h : agreeExcept M σ σ') : agreeExcept M σ' σ :=
  fun x hx => (h x hx).symm

theorem agreeExcept_trans {M : List Core.Expression.Ident} {σ₂ σ₁ σ₀ : Core.CoreStore}
    (h₂ : agreeExcept M σ₂ σ₁) (h₁ : agreeExcept M σ₁ σ₀) : agreeExcept M σ₂ σ₀ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- Agreement outside a smaller set is agreement outside a larger one. -/
theorem agreeExcept_mono {M' M : List Core.Expression.Ident} {σ σ' : Core.CoreStore}
    (h : agreeExcept M' σ σ') (hsub : ∀ x, x ∈ M' → x ∈ M) : agreeExcept M σ σ' :=
  fun x hx => h x (fun h' => hx (hsub x h'))

/-- Dropping names inside `M` changes nothing outside it. -/
theorem agreeExcept_dropVars {M D : List Core.Expression.Ident} (hDM : ∀ x, x ∈ D → x ∈ M)
    (σ : Core.CoreStore) : agreeExcept M (Imperative.dropVars D σ) σ := by
  intro x hx
  have hxD : x ∉ D := fun h => hx (hDM x h)
  simp [Imperative.dropVars, hxD]

/-- The step obligation at the entry environment `ρ₀`: the body's precondition `B ρ₀.store`
holds at every environment that agrees with `ρ₀` outside `M` and satisfies the invariant and
the guard. -/
@[expose] def stepObligation (M : List Core.Expression.Ident) (I : Pred)
    (guard : Core.Expression.Expr) (B : Core.CoreStore → Pred) : Pred :=
  fun ρ₀ => ∀ ρ, agreeExcept M ρ.store ρ₀.store → I ρ →
    Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.tt → B ρ₀.store ρ

/-- The exit obligation at the entry environment `ρ₀`: `Q` holds at every environment that
agrees with `ρ₀` outside `M` and satisfies the invariant and the negated guard. -/
@[expose] def exitObligation (M : List Core.Expression.Ident) (I : Pred)
    (guard : Core.Expression.Expr) (Q : Pred) : Pred :=
  fun ρ₀ => ∀ ρ, agreeExcept M ρ.store ρ₀.store → I ρ →
    Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.ff → Q ρ

/-- Weakest precondition of a loop whose body declares `D` and writes at most `M`: the
invariant at the entry, and the two obligations at the entry. -/
@[expose] def wpLoop (D M : List Core.Expression.Ident) (I : Pred) (guard : Core.Expression.Expr)
    (B : Core.CoreStore → Pred) (Q : Pred) : Pred :=
  fun ρ₀ => wpProj D I ρ₀ ∧ stepObligation M (wpProj D I) guard B ρ₀ ∧
    exitObligation M (wpProj D I) guard Q ρ₀

/-- The framed `while` rule. The body is verified once for every entry store `σ₀`, against the
invariant together with agreement with `σ₀` outside `M`; the soundness of the frame is what the
body's verification condition proves, so `M` need only contain the names the body declares. -/
theorem while_wp_frame (I : Pred) {guard : Core.Expression.Expr}
    {measure : Option Core.Expression.Expr} {inv : List (String × Core.Expression.Expr)}
    {body : Core.Statements} {md : Imperative.MetaData Core.Expression}
    (D M : List Core.Expression.Ident)
    (hD : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) body true = D)
    (hDM : ∀ x, x ∈ D → x ∈ M)
    {B : Core.CoreStore → Pred} {Q : Pred}
    (hbody : ∀ σ₀, Model.TripleM π params (model := model) (B σ₀) body
      (wpProj D (fun ρ => I ρ ∧ agreeExcept M ρ.store σ₀)))
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body) :
    Model.TripleM π params (model := model) (wpLoop D M I guard B Q)
      [.loop (.det guard) measure inv body md] Q := by
  intro ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨hI, hstep, hexit⟩ := hpre
  have hJ : ∀ ρ : Imperative.Env Core.Expression,
      wpProj D (fun ρ => I ρ ∧ agreeExcept M ρ.store ρ₀.store) ρ →
      wpProj D I ρ ∧ agreeExcept M ρ.store ρ₀.store := by
    intro ρ h
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨h₁, agreeExcept_trans (agreeExcept_symm (agreeExcept_dropVars hDM ρ.store)) h₂⟩
  have h := while_wp' (measure := measure) (inv := inv) (md := md) π params
    (fun ρ => I ρ ∧ agreeExcept M ρ.store ρ₀.store) D hD (hbody ρ₀.store)
    (fun ρ hρ hg => hstep ρ (hJ ρ hρ).2 (hJ ρ hρ).1 hg)
    (fun ρ hρ hg => hexit ρ (hJ ρ hρ).2 (hJ ρ hρ).1 hg) hcov
  exact h ρ₀ ρ' trace (And.intro hI (agreeExcept_dropVars hDM ρ₀.store)) hinit hrun

/-! ## Nondeterministic branches and loops, and `cover`

`if (*)` requires both branches, `while (*)` is the framed loop rule with nothing learned from
a guard, and `cover` is a skip: its event is never an obligation of a triple. -/

/-- Weakest precondition of `if (*)`: both branches'. -/
@[expose] def wpIteNondet (T E : Pred) : Pred := fun ρ => T ρ ∧ E ρ

theorem ite_nondet_wp' {tss ess : Core.Statements} {md : Imperative.MetaData Core.Expression}
    (Dt De : List Core.Expression.Ident)
    (hDt : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) tss true = Dt)
    (hDe : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ess true = De)
    {T E Q : Pred}
    (ht : Model.TripleM π params (model := model) T tss (wpProj Dt Q))
    (he : Model.TripleM π params (model := model) E ess (wpProj De Q)) :
    Model.TripleM π params (model := model) (wpIteNondet T E) [.ite .nondet tss ess md] Q := by
  subst hDt hDe
  exact Model.ite_nondet_proj π params
    (Model.consequence π params ht (fun _ h => h.1) (fun _ h => h))
    (Model.consequence π params he (fun _ h => h.2) (fun _ h => h))

theorem cover_wp (Q : Pred) (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Model.TripleM π params (model := model) Q [Core.Statement.cover label e md] Q := by
  apply Model.cmd
  intro ρ₀ σ' emitted hpre _ hstep
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_cover => exact ⟨trivial, fun _ => hpre⟩

/-- The step obligation of `while (*)`: no guard. -/
@[expose] def stepObligationN (M : List Core.Expression.Ident) (I : Pred)
    (B : Core.CoreStore → Pred) : Pred :=
  fun ρ₀ => ∀ ρ, agreeExcept M ρ.store ρ₀.store → I ρ → B ρ₀.store ρ

/-- The exit obligation of `while (*)`: no guard. -/
@[expose] def exitObligationN (M : List Core.Expression.Ident) (I : Pred) (Q : Pred) : Pred :=
  fun ρ₀ => ∀ ρ, agreeExcept M ρ.store ρ₀.store → I ρ → Q ρ

/-- Weakest precondition of a framed `while (*)`. -/
@[expose] def wpLoopN (D M : List Core.Expression.Ident) (I : Pred)
    (B : Core.CoreStore → Pred) (Q : Pred) : Pred :=
  fun ρ₀ => wpProj D I ρ₀ ∧ stepObligationN M (wpProj D I) B ρ₀ ∧
    exitObligationN M (wpProj D I) Q ρ₀

theorem while_nondet_wp (I : Pred) {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} {B Q : Pred}
    (hbody : Model.TripleM π params (model := model) B body I)
    (step : ∀ ρ, I ρ → B ρ) (exit : ∀ ρ, I ρ → Q ρ)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body)
    (hwf : Imperative.Logic.Hoare.PostWF body I) :
    Model.TripleM π params (model := model) I [.loop .nondet measure inv body md] Q :=
  Model.consequence π params
    (Model.while_nondet π params (Model.consequence π params hbody step (fun _ h => h)) hcov hwf)
    (fun _ h => h) exit

theorem while_nondet_wp_frame (I : Pred) {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} (D M : List Core.Expression.Ident)
    (hD : Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) body true = D)
    (hDM : ∀ x, x ∈ D → x ∈ M)
    {B : Core.CoreStore → Pred} {Q : Pred}
    (hbody : ∀ σ₀, Model.TripleM π params (model := model) (B σ₀) body
      (wpProj D (fun ρ => I ρ ∧ agreeExcept M ρ.store σ₀)))
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body) :
    Model.TripleM π params (model := model) (wpLoopN D M I B Q)
      [.loop .nondet measure inv body md] Q := by
  intro ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨hI, hstep, hexit⟩ := hpre
  have hJ : ∀ ρ : Imperative.Env Core.Expression,
      wpProj D (fun ρ => I ρ ∧ agreeExcept M ρ.store ρ₀.store) ρ →
      wpProj D I ρ ∧ agreeExcept M ρ.store ρ₀.store := by
    intro ρ h
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨h₁, agreeExcept_trans (agreeExcept_symm (agreeExcept_dropVars hDM ρ.store)) h₂⟩
  have h := while_nondet_wp (measure := measure) (inv := inv) (md := md) π params
    (wpProj D (fun ρ => I ρ ∧ agreeExcept M ρ.store ρ₀.store)) (hbody ρ₀.store)
    (fun ρ hρ => hstep ρ (hJ ρ hρ).2 (hJ ρ hρ).1)
    (fun ρ hρ => hexit ρ (hJ ρ hρ).2 (hJ ρ hρ).1) hcov (postWF_proj hD _)
  exact h ρ₀ ρ' trace (And.intro hI (agreeExcept_dropVars hDM ρ₀.store)) hinit hrun

end Strata.Hoare

end -- public section
