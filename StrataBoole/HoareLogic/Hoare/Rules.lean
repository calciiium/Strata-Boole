/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.LangDefProps
public import StrataBoole.HoareLogic.Hoare.Proj

/-! # The Core Hoare rules at one model

`Procedure.contractTriple` fixes a `model : Lambda.Interp Core.Factory` and states the
contract as `TripleWithModel π model params (contractPre model proc) … (contractPost model proc)`.
Both ends mention the model, and so does every intermediate assertion a verification
condition generator writes down (an `assert` holds under `DenoteBasedInterp model`).

The rules of `Core.Logic.Hoare` are stated for `Triple`, which quantifies over every model, so
they cannot be fed premises that hold at one model only. Their proofs, however, go through the
generic per-interpretation rules of `Imperative.Logic.Hoare`; the rules below are those proofs
with the model held fixed. Names and premises follow `Core.Logic.Hoare` one to one, plus `nil`
for the empty statement list, which the structural rules there do not cover, and `block_proj`
and `ite_proj`, the block rules of `StrataBoole/HoareLogic/Hoare/Proj.lean` that carry the store projection
in the postcondition instead of asking for `PostWF`. -/

public section

namespace Strata.Hoare.Model

open Core.Logic

variable (π : String → Option Core.Procedure) (params : Core.Logic.InitEnvWFParams)
variable {model : Lambda.Interp Core.Factory}

/-- The judgement every rule here is about. -/
abbrev TripleM (Pre : Imperative.Env Core.Expression → Prop) (ss : Core.Statements)
    (Post : Imperative.Env Core.Expression → Prop) : Prop :=
  Core.Logic.Hoare.TripleWithModel π model params Pre ss Post

/-! ## Rules that do not inspect the statement -/

theorem false_pre (ss : Core.Statements) (Post : Imperative.Env Core.Expression → Prop) :
    TripleM π params (model := model) (fun _ => False) ss Post :=
  Strata.Logic.Hoare.false_pre (EventLang.coreBlock π) params ss Post

theorem consequence {Pre Pre' Post Post' : Imperative.Env Core.Expression → Prop}
    {ss : Core.Statements}
    (h : TripleM π params (model := model) Pre ss Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    TripleM π params (model := model) Pre' ss Post' :=
  Strata.Logic.Hoare.consequence (EventLang.coreBlock π) params h hpre hpost

/-! ## Rules for a single command -/

/-- A generic single command. Unlike `Core.Logic.Hoare.cmd`, the premise speaks about the
one model the conclusion is about. -/
theorem cmd (c : Core.Command) (Pre Post : Imperative.Env Core.Expression → Prop)
    (h : ∀ ρ₀ σ' emitted,
      Pre ρ₀ → Core.Logic.InitEnvWF params (.cmd c) ρ₀ →
      Core.EvalCommandE π ρ₀.factory ρ₀.store c σ' emitted →
      Imperative.Trace.AssertionsValid Core.Expression (DenoteBasedInterp model) emitted ∧
        (Imperative.Trace.Reachable Core.Expression (DenoteBasedInterp model) emitted →
          Post { ρ₀ with store := σ' })) :
    TripleM π params (model := model) Pre [.cmd c] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.cmd (Core.EvalCommandE π) Core.Logic.InitEnvWF params c Pre Post h)

/-- Assignment: the premise of `Core.Logic.Hoare.set` is model-free, so the rule specializes. -/
theorem set (x : Core.Expression.Ident) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore) (v : Core.Expression.Expr),
      Pre ρ₀ → Core.Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.UpdateState Core.Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    TripleM π params (model := model) Pre [Core.Statement.set x e md] Post :=
  Core.Logic.Hoare.set π params x e md Pre Post hpost model

/-- Declaration with an initializer; as `set`, a specialization. -/
theorem init (x : Core.Expression.Ident) (ty : Core.Expression.Ty) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore) (v : Core.Expression.Expr),
      Pre ρ₀ → Core.Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.InitState Core.Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    TripleM π params (model := model) Pre [Core.Statement.init x ty (.det e) md] Post :=
  Core.Logic.Hoare.init π params x ty e md Pre Post hpost model

/-! ## Structural rules -/

/-- The empty statement list leaves the environment alone. -/
theorem nil (Pre : Imperative.Env Core.Expression → Prop) :
    TripleM π params (model := model) Pre [] Pre :=
  Imperative.Logic.Hoare.skip_block (Core.EvalCommandE π) Core.Logic.BlockInitEnvWF params Pre

theorem seq {ss₁ ss₂ : Core.Statements} {Pre Mid Post : Imperative.Env Core.Expression → Prop}
    (h₁ : TripleM π params (model := model) Pre ss₁ Mid)
    (h₂ : TripleM π params (model := model) Mid ss₂ Post)
    (hnoesc : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] ss₁) :
    TripleM π params (model := model) Pre (ss₁ ++ ss₂) Post :=
  Imperative.Logic.Hoare.seq_append (Core.EvalCommandE π)
    Core.Logic.BlockInitEnvWF params
    (fun _ hb => blockInitEnvWF_append_head hb)
    (fun _ _ _ hb hr => blockInitEnvWF_append_tailE π hb hr)
    h₁ h₂ hnoesc

theorem exit_cons {lbl : String} {md : Imperative.MetaData Core.Expression}
    {ss : Core.Statements} (Pre : Imperative.Env Core.Expression → Prop) :
    TripleM π params (model := model) Pre (.exit lbl md :: ss) Pre :=
  Imperative.Logic.Hoare.exit_cons (Core.EvalCommandE π) Core.Logic.BlockInitEnvWF params

theorem block {ss : Core.Statements} {l : String} {md : Imperative.MetaData Core.Expression}
    {Pre Post : Imperative.Env Core.Expression → Prop}
    (h : TripleM π params (model := model) Pre ss Post)
    (hpost_proj : Imperative.Logic.Hoare.PostWF ss Post) :
    TripleM π params (model := model) Pre [.block l ss md] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.block (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      h hpost_proj)

/-- `block` with the projection in the body's postcondition: `Post` is checked at the environment
with the body's declarations dropped, which is the one leaving the block. -/
theorem block_proj {ss : Core.Statements} {l : String} {md : Imperative.MetaData Core.Expression}
    {Pre Post : Imperative.Env Core.Expression → Prop}
    (h : TripleM π params (model := model) Pre ss
      (Proj.projected (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ss true)
        Post)) :
    TripleM π params (model := model) Pre [.block l ss md] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Proj.block_proj (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      h)

theorem skip (l : String) (md : Imperative.MetaData Core.Expression)
    (Pre : Imperative.Env Core.Expression → Prop) :
    TripleM π params (model := model) Pre [.block l [] md] Pre :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.skip (Core.EvalCommandE π)
      Core.Logic.InitEnvWF params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd) l md Pre)

theorem ite {cond : Core.Expression.Expr} {tss ess : Core.Statements}
    {md : Imperative.MetaData Core.Expression}
    {Pre Post : Imperative.Env Core.Expression → Prop}
    (ht : TripleM π params (model := model)
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.tt)
      tss Post)
    (he : TripleM π params (model := model)
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.ff)
      ess Post)
    (hthen_proj : Imperative.Logic.Hoare.PostWF tss Post)
    (helse_proj : Imperative.Logic.Hoare.PostWF ess Post) :
    TripleM π params (model := model) Pre [.ite (.det cond) tss ess md] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.ite (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_ite_then hb)
      (fun _ hb => blockInitEnvWF_of_ite_else hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_then hb))
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_else hb))
      ht he hthen_proj helse_proj)

/-- `ite` with the projection in each branch's postcondition. -/
theorem ite_proj {cond : Core.Expression.Expr} {tss ess : Core.Statements}
    {md : Imperative.MetaData Core.Expression}
    {Pre Post : Imperative.Env Core.Expression → Prop}
    (ht : TripleM π params (model := model)
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.tt)
      tss (Proj.projected
        (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) tss true) Post))
    (he : TripleM π params (model := model)
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store cond = some Imperative.HasBool.ff)
      ess (Proj.projected
        (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ess true) Post)) :
    TripleM π params (model := model) Pre [.ite (.det cond) tss ess md] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Proj.ite_proj (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_ite_then hb)
      (fun _ hb => blockInitEnvWF_of_ite_else hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_then hb))
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_else hb))
      ht he)

theorem while_rule {guard : Core.Expression.Expr} {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} {Inv : Imperative.Env Core.Expression → Prop}
    (hbody : TripleM π params (model := model)
      (fun ρ => Inv ρ ∧ Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.tt)
      body Inv)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body)
    (hInv_proj : Imperative.Logic.Hoare.PostWF body Inv) :
    TripleM π params (model := model) Inv [.loop (.det guard) measure inv body md]
      (fun ρ => Inv ρ ∧ Core.Expression.eval ρ.factory ρ.store guard = some Imperative.HasBool.ff) :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.while_rule (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hl => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_loop_body hl))
      (fun _ hl => blockInitEnvWF_of_loop_body hl)
      (fun _ _ _ hl hr => initEnvWF_loop_iterateE π hl hr)
      hbody hcov hInv_proj)

/-! ## Nondeterministic branches and loops

The well-formedness lemmas of `Core.Logic` are stated for a deterministic guard. A
nondeterministic guard puts no variable and no operator into the def-use check, so the same
proofs go through at `.nondet`. -/

theorem blockInitEnvWF_of_ite_then_nondet {params : InitEnvWFParams}
    {tss ess : Core.Statements} {md : Imperative.MetaData Core.Expression}
    {ρ : Imperative.Env Core.Expression}
    (h : InitEnvWF params (.ite .nondet tss ess md) ρ) : BlockInitEnvWF params tss ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Imperative.Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Imperative.Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inl hn)))
    h.reservedFresh hdu.1.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by simp only [Imperative.Stmt.initTypes]; exact List.mem_append.mpr (Or.inl hty)))

theorem blockInitEnvWF_of_ite_else_nondet {params : InitEnvWFParams}
    {tss ess : Core.Statements} {md : Imperative.MetaData Core.Expression}
    {ρ : Imperative.Env Core.Expression}
    (h : InitEnvWF params (.ite .nondet tss ess md) ρ) : BlockInitEnvWF params ess ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Imperative.Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Imperative.Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inr hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inr hn)))
    h.reservedFresh hdu.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by simp only [Imperative.Stmt.initTypes]; exact List.mem_append.mpr (Or.inr hty)))

theorem blockInitEnvWF_of_loop_body_nondet {params : InitEnvWFParams}
    {m : Option Core.Expression.Expr} {inv : List (String × Core.Expression.Expr)}
    {body : Core.Statements} {md : Imperative.MetaData Core.Expression}
    {ρ : Imperative.Env Core.Expression}
    (h : InitEnvWF params (.loop .nondet m inv body md) ρ) : BlockInitEnvWF params body ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Imperative.Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Imperative.Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined hdefs hdnr
    h.reservedFresh hdu.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty (by simp only [Imperative.Stmt.initTypes]; exact hty))

theorem initEnvWF_loop_iterateE_nondet {params : InitEnvWFParams}
    {m : Option Core.Expression.Expr} {inv : List (String × Core.Expression.Expr)}
    {body : Core.Statements} {md : Imperative.MetaData Core.Expression}
    {ρ ρ_inner : Imperative.Env Core.Expression} {tr : Imperative.Trace Core.Expression}
    (h : InitEnvWF params (.loop .nondet m inv body md) ρ)
    (hrun : Imperative.StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts body ρ) tr (.terminal ρ_inner)) :
    InitEnvWF params (.loop .nondet m inv body md)
      { ρ_inner with store := Imperative.projectStore ρ.store ρ_inner.store } := by
  have hstore : ∀ n, ((Imperative.projectStore ρ.store ρ_inner.store) n).isSome
      = (ρ.store n).isSome := by
    intro n
    by_cases hn : (ρ.store n).isSome = Bool.true
    · simp only [Imperative.projectStore, hn, ite_true]
      exact Core.core_stmts_preserves_isSomeE π hrun hn
    · have hnone : ρ.store n = none := by
        cases hq : ρ.store n with
        | none => rfl
        | some v => rw [hq] at hn; simp at hn
      simp [Imperative.projectStore, hnone]
  have hfun : (fun n => ((Imperative.projectStore ρ.store ρ_inner.store) n).isSome)
      = (fun n => (ρ.store n).isSome) := funext hstore
  have hfac : ρ.factory = ρ_inner.factory := Imperative.starE_preserves_factory hrun
  have hproj : Imperative.WellFormedStore (Imperative.projectStore ρ.store ρ_inner.store)
      ρ_inner.factory := by
    have hpres : ∀ {f : Core.Expression.Factory} {σ σ' : Core.CoreStore} {c : Core.Command}
        {emitted : Imperative.Trace Core.Expression},
        Core.EvalCommandE π f σ c σ' emitted →
        Imperative.WellFormedStore σ f → Imperative.WellFormedStore σ' f :=
      fun hc hs => Core.evalCommandE_storeWellDefined π hc hs
    have hinner : Imperative.WellFormedStore ρ_inner.store ρ_inner.factory :=
      Imperative.Config.storeWellDefined_star_ofE (EvalCmd := Core.EvalCommandE π) hpres
        hrun h.storeWellDefined
    intro x w hx
    simp only [Imperative.projectStore] at hx
    split at hx
    · exact hinner x w hx
    · exact absurd hx (by simp)
  refine InitEnvWF.of_defUseOk (hfac ▸ h.toWellFormedSemanticEval) hproj (fun n hn => ?_)
    h.definedVarsNotReserved (fun n hn => ?_) ?_ h.factoryDeclared
    (hfac ▸ h.initTypesInhabited)
  · have hdef := h.defsUndefined n hn
    show (Imperative.projectStore ρ.store ρ_inner.store n).isNone
    rw [Option.isNone_iff_eq_none] at hdef ⊢
    simp [Imperative.projectStore, hdef]
  · exact h.reservedFresh n (by rw [← hstore n]; exact hn)
  · show Imperative.Stmt.defUseWellFormed
      (fun n => ((Imperative.projectStore ρ.store ρ_inner.store) n).isSome) params.declaredFuncs _
        = Bool.true
    rw [hfun]; exact h.defUseOk

theorem ite_nondet_proj {tss ess : Core.Statements} {md : Imperative.MetaData Core.Expression}
    {Pre Post : Imperative.Env Core.Expression → Prop}
    (ht : TripleM π params (model := model) Pre tss (Proj.projected
      (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) tss true) Post))
    (he : TripleM π params (model := model) Pre ess (Proj.projected
      (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command) ess true) Post)) :
    TripleM π params (model := model) Pre [.ite .nondet tss ess md] Post :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Proj.ite_nondet_proj (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_ite_then_nondet hb)
      (fun _ hb => blockInitEnvWF_of_ite_else_nondet hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_then_nondet hb))
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_else_nondet hb))
      ht he)

theorem while_nondet {measure : Option Core.Expression.Expr}
    {inv : List (String × Core.Expression.Expr)} {body : Core.Statements}
    {md : Imperative.MetaData Core.Expression} {Inv : Imperative.Env Core.Expression → Prop}
    (hbody : TripleM π params (model := model) Inv body Inv)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] body)
    (hInv_proj : Imperative.Logic.Hoare.PostWF body Inv) :
    TripleM π params (model := model) Inv [.loop .nondet measure inv body md] Inv :=
  Imperative.Logic.Hoare.singleton (Core.EvalCommandE π)
    Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Proj.while_nondet (Core.EvalCommandE π)
      Core.Logic.InitEnvWF Core.Logic.BlockInitEnvWF params params
      (fun he hn hnd => Core.evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hl => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_loop_body_nondet hl))
      (fun _ hl => blockInitEnvWF_of_loop_body_nondet hl)
      (fun _ _ _ hl hr => initEnvWF_loop_iterateE_nondet π hl hr)
      hbody hcov hInv_proj)

end Strata.Hoare.Model

end -- public section
