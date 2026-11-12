/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.DL.Imperative.Logic.HoareTemplate

/-! # Block rules with the projection in the postcondition

`Imperative.Logic.Hoare.block` and `ite` ask for `PostWF`: the postcondition must be stable
under dropping the names the body declares from the store, since leaving the block drops them.
For a postcondition a verification-condition generator synthesizes, that stability is a real
proof obligation about an arbitrary predicate.

The rules here ask for nothing. The body's postcondition is stated at the projected
environment, `Post { ρ with store := dropVars (Block.definedVars ss true) ρ.store }`, which is
exactly the environment that leaves the block, so no stability is needed. `PostWF` is traded for
a store transformer inside the verification conditions, which a lifting reads through as it
reads through an update. The proofs are those of `block` and `ite` with the stability step
removed. -/

public section

namespace Strata.Hoare.Proj

open Imperative Imperative.Logic Strata.Logic.Hoare Imperative.Logic.Hoare

variable {P : Imperative.PureExpr}
variable {conditionInterp : Imperative.ConditionInterp P}
variable [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P]
    [HasSubstFvar P] [HasInt P] [HasIntOps P]
variable {CmdT : Type}
variable (evalCmd : EvalCmdParamE P CmdT (Event P))
variable {ParamsTy : Type}
variable (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop)
variable {BParamsTy : Type}
variable (blockInitEnvWF : BParamsTy → List (Stmt P CmdT) → Env P → Prop)
variable (bparams : BParamsTy)
variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- `Post` at the environment that leaves a block whose body declared the names `D`. -/
abbrev projected (D : List P.Ident) (Post : Env P → Prop) : Env P → Prop :=
  fun ρ => Post { ρ with store := dropVars D ρ.store }

/-- `block` with the projection in the body's postcondition instead of `PostWF`. -/
theorem block_proj (params : ParamsTy)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyWF : ∀ ρ, initEnvWF params (.block l ss md) ρ → blockInitEnvWF bparams ss ρ)
    (hbodyDefs : ∀ ρ, initEnvWF params (.block l ss md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ.store x = none)
    (h : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams Pre ss
      (projected (Block.definedVars (P := P) (C := CmdT) ss true) Post)) :
    TripleWith (EventLang.imperativeE P CmdT evalCmd ParamsTy initEnvWF) conditionInterp params
      Pre (.block l ss md) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨ρ_inner, hrun_inner, heq⟩ := stmt_block_reaches_doneE hrun
  have ⟨hvalid, hpost⟩ := h ρ₀ ρ_inner trace hpre (hbodyWF ρ₀ hinit) hrun_inner
  have hproj : projectStore ρ₀.store ρ_inner.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store :=
    projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ₀ hinit) hrun_inner
  subst heq
  refine ⟨hvalid, fun hf => ?_⟩
  have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P)
      = { ρ_inner with
            store := dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store } := by
    rw [hproj]
  rw [hrec]
  exact hpost hf

/-- `ite` with the projection in each branch's postcondition instead of `PostWF`. -/
theorem ite_proj (params : ParamsTy)
    {cond : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hthenWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (ht : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.tt) tss
      (projected (Block.definedVars (P := P) (C := CmdT) tss true) Post))
    (he : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.ff) ess
      (projected (Block.definedVars (P := P) (C := CmdT) ess true) Post)) :
    TripleWith (EventLang.imperativeE P CmdT evalCmd ParamsTy initEnvWF) conditionInterp params
      Pre (.ite (.det cond) tss ess md) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hbranch : ∀ (bss : List (Stmt P CmdT)) (Pre' : Env P → Prop) (tr : Trace P),
      Pre' ρ₀ → blockInitEnvWF bparams bss ρ₀ →
      (∀ x ∈ Block.definedVars (P := P) (C := CmdT) bss true, ρ₀.store x = none) →
      TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
        conditionInterp bparams Pre' bss
        (projected (Block.definedVars (P := P) (C := CmdT) bss true) Post) →
      (StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.terminal ρ') ∨
       ∃ lbl, StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.exiting lbl ρ')) →
      Trace.AssertionsValid P conditionInterp tr ∧
        (Trace.Reachable P conditionInterp tr → Post ρ') := by
    intro bss Pre' tr hpre' hbwf hbdefs hb hdone_b
    obtain ⟨ρ_inner, hrun_inner, heq⟩ := block_reaches_doneE hdone_b
    have ⟨hvalid, hpost⟩ := hb ρ₀ ρ_inner tr hpre' hbwf hrun_inner
    have hproj : projectStore ρ₀.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store :=
      projectStore_eq_dropVarsE h_cmd hbdefs hrun_inner
    subst heq
    refine ⟨hvalid, fun hf => ?_⟩
    have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P)
        = { ρ_inner with
              store := dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store } := by
      rw [hproj]
    rw [hrec]
    exact hpost hf
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc =>
          exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)
            (hthenDefs ρ₀ hinit) ht (.inl (by simpa using hrest))
        | step_ite_false hc =>
          exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)
            (helseDefs ρ₀ hinit) he (.inl (by simpa using hrest))
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc =>
          exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)
            (hthenDefs ρ₀ hinit) ht (.inr ⟨lbl, by simpa using hrest⟩)
        | step_ite_false hc =>
          exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)
            (helseDefs ρ₀ hinit) he (.inr ⟨lbl, by simpa using hrest⟩)

/-! ## Nondeterministic branches and loops

`if (*)` takes either branch and `while (*)` runs any number of iterations; neither has a guard
to learn from. The rules are `ite_proj` and `Imperative.Logic.Hoare.while_rule` with the guard
hypotheses removed, following the nondeterministic steps of the semantics. -/

theorem ite_nondet_proj (params : ParamsTy)
    {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hthenWF : ∀ ρ, initEnvWF params (.ite .nondet tss ess md) ρ →
      blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite .nondet tss ess md) ρ →
      blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite .nondet tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite .nondet tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (ht : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams Pre tss
      (projected (Block.definedVars (P := P) (C := CmdT) tss true) Post))
    (he : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams Pre ess
      (projected (Block.definedVars (P := P) (C := CmdT) ess true) Post)) :
    TripleWith (EventLang.imperativeE P CmdT evalCmd ParamsTy initEnvWF) conditionInterp params
      Pre (.ite .nondet tss ess md) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hbranch : ∀ (bss : List (Stmt P CmdT)) (Pre' : Env P → Prop) (tr : Trace P),
      Pre' ρ₀ → blockInitEnvWF bparams bss ρ₀ →
      (∀ x ∈ Block.definedVars (P := P) (C := CmdT) bss true, ρ₀.store x = none) →
      TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
        conditionInterp bparams Pre' bss
        (projected (Block.definedVars (P := P) (C := CmdT) bss true) Post) →
      (StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.terminal ρ') ∨
       ∃ lbl, StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.exiting lbl ρ')) →
      Trace.AssertionsValid P conditionInterp tr ∧
        (Trace.Reachable P conditionInterp tr → Post ρ') := by
    intro bss Pre' tr hpre' hbwf hbdefs hb hdone_b
    obtain ⟨ρ_inner, hrun_inner, heq⟩ := block_reaches_doneE hdone_b
    have ⟨hvalid, hpost⟩ := hb ρ₀ ρ_inner tr hpre' hbwf hrun_inner
    have hproj : projectStore ρ₀.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store :=
      projectStore_eq_dropVarsE h_cmd hbdefs hrun_inner
    subst heq
    refine ⟨hvalid, fun hf => ?_⟩
    have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P)
        = { ρ_inner with
              store := dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store } := by
      rw [hproj]
    rw [hrec]
    exact hpost hf
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_nondet_true =>
          exact hbranch tss _ _ hpre (hthenWF ρ₀ hinit)
            (hthenDefs ρ₀ hinit) ht (.inl (by simpa using hrest))
        | step_ite_nondet_false =>
          exact hbranch ess _ _ hpre (helseWF ρ₀ hinit)
            (helseDefs ρ₀ hinit) he (.inl (by simpa using hrest))
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_nondet_true =>
          exact hbranch tss _ _ hpre (hthenWF ρ₀ hinit)
            (hthenDefs ρ₀ hinit) ht (.inr ⟨lbl, by simpa using hrest⟩)
        | step_ite_nondet_false =>
          exact hbranch ess _ _ hpre (helseWF ρ₀ hinit)
            (helseDefs ρ₀ hinit) he (.inr ⟨lbl, by simpa using hrest⟩)

/-- Helper for `while_nondet`: the invariant survives arbitrarily many iterations, and the
completed trace is assertion-valid. By strong induction on the length of the derivation. -/
theorem while_nondet_genE
    {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : ParamsTy)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop .nondet measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop .nondet measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop .nondet measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop .nondet measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams Inv body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv)
    (ρ₀ ρ' : Env P) (trace : Trace P) (n : Nat)
    (hInv : Inv ρ₀)
    (hwf : initEnvWF params (.loop .nondet measure inv body md) ρ₀)
    (hrunT : ReflTransTraceT (StepStmtE P evalCmd)
      (.stmt (.loop .nondet measure inv body md) ρ₀) trace (.terminal ρ'))
    (hlen : hrunT.len ≤ n) :
    Trace.AssertionsValid P conditionInterp trace ∧
      (Trace.Reachable P conditionInterp trace → Inv ρ') := by
  induction n generalizing ρ₀ ρ' trace with
  | zero =>
    match hrunT, hlen with
    | .step _ _ _ _ _ _ _, hlen => simp only [ReflTransTraceT.len] at hlen; omega
  | succ n ih =>
    match hrunT, hlen with
    | .step _ _ _ restTr _ (.step_admin .step_loop_nondet_exit) hrest, hlen =>
      obtain ⟨hc, hnil⟩ := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
      subst hnil
      injection hc with hρ
      subst hρ
      exact ⟨True.intro, fun _ => hInv⟩
    | .step _ _ _ restTr _ (.step_admin .step_loop_nondet_enter) hrest, hlen =>
      simp only [List.nil_append]
      obtain ⟨ρ_mid, tr₁, tr₂, htr, h_block_term, h_loop_rest, hlen_seq⟩ :=
        seqT_reaches_terminalE hrest
      obtain ⟨ρ_inner, hbody_disj, heq_ρ_mid⟩ :=
        block_reaches_doneE (.inl (reflTransTraceT_to_prop h_block_term))
      have hbody_run : StepStmtStarE P evalCmd (.stmts body ρ₀) tr₁ (.terminal ρ_inner) := by
        rcases hbody_disj with hterm | ⟨lbl, hexit⟩
        · exact hterm
        · exact absurd hexit (stmts_exitsCoveredByBlocks_noEscapeE evalCmd
            body hcov ρ₀ lbl ρ_inner)
      obtain ⟨ρ_x, tr_l, tr_nil, htr2, h_loop_head, h_nil, hlen_cons⟩ :=
        stmtsT_cons_terminalE h_loop_rest
      obtain ⟨htail_nil, htail_cfg⟩ := stmts_nil_runE evalCmd
        (reflTransTraceT_to_prop h_nil)
      subst htail_nil
      have hρx : ρ_x = ρ' := by
        rcases htail_cfg with hcfg | hcfg
        · exact absurd hcfg (by simp)
        · injection hcfg with hρ; exact hρ.symm
      subst ρ_x
      simp only [List.append_nil] at htr2
      rw [htr2] at htr
      rw [htr]
      have hbodyTriple := hbody ρ₀ ρ_inner tr₁ hInv (hloopBodyWF ρ₀ hwf) (.inl hbody_run)
      have hproj : projectStore ρ₀.store ρ_inner.store
          = dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store :=
        projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ₀ hwf) (.inl hbody_run)
      have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P)
          = { ρ_inner with
                store := dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store } := by
        rw [hproj]
      have hwf_mid : initEnvWF params (.loop .nondet measure inv body md) ρ_mid := by
        rw [heq_ρ_mid]; exact hloopWF ρ₀ ρ_inner tr₁ hwf hbody_run
      have hIH : Trace.Reachable P conditionInterp tr₁ →
          Trace.AssertionsValid P conditionInterp tr_l ∧
            (Trace.Reachable P conditionInterp tr_l → Inv ρ') := by
        intro hs
        have hInv_mid : Inv ρ_mid := by
          rw [heq_ρ_mid, hrec]; exact hInv_proj ρ_inner (hbodyTriple.2 hs)
        exact ih ρ_mid ρ' tr_l hInv_mid hwf_mid h_loop_head
          (by simp only [ReflTransTraceT.len] at hlen; omega)
      refine ⟨Trace.AssertionsValid.append_of_reachable_left conditionInterp hbodyTriple.1
        (fun hs => (hIH hs).1), fun hfull => ?_⟩
      exact (hIH (Trace.Reachable.left_of_append conditionInterp hfull)).2
        (Trace.Reachable.right_of_append conditionInterp hfull)

/-- `while (*)`: an invariant the body re-establishes holds when the loop finishes, after any
number of iterations, with nothing learned from a guard. -/
theorem while_nondet (params : ParamsTy)
    {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P} {Inv : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop .nondet measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop .nondet measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop .nondet measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop .nondet measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : TripleWith (EventLang.imperativeBlockE P CmdT evalCmd ⟨BParamsTy, blockInitEnvWF⟩)
      conditionInterp bparams Inv body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv) :
    TripleWith (EventLang.imperativeE P CmdT evalCmd ParamsTy initEnvWF) conditionInterp params
      Inv (.loop .nondet measure inv body md) Inv := by
  intro ρ₀ ρ' trace hInv hinit hrun
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · exact while_nondet_genE evalCmd initEnvWF blockInitEnvWF bparams params
      h_cmd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj
      ρ₀ ρ' trace _ hInv hinit (reflTransTrace_to_T hterm) (Nat.le_refl _)
  · exact absurd hexit (exitsCoveredByBlocks_noEscapeE evalCmd
      (.loop .nondet measure inv body md) hcov ρ₀ lbl ρ')

end Strata.Hoare.Proj

end -- public section
