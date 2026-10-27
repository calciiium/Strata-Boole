/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Deep.Spec

/-! # Deep embedding of Core: tactics

* `core_vcgen` turns a goal `Procedure.Correct p` (or `Triple P ss Q`) into verification
  conditions. It applies the rules of `Deep/Spec.lean` backwards, statement by statement,
  as `vcgen` applies `@[spec]` lemmas in the `lean-vcgen-tutorial`. `vcgen` itself needs
  Lean 4.33. The 4.31 `mvcgen` does not split the conditional rule's precondition, and
  stated with premises instead, its `if` rule loses an assignment made before the `if`.
* `core_lift` evaluates the embedding away in every hypothesis and the goal (`eval`,
  `State.update`, the loop and contract predicates), leaving propositions about `Int`
  and `Bool`, like the tutorial's `imp_lift`.

Typical use, after unfolding the procedure: `core_vcgen <;> core_lift <;> omega`.

The VCs `core_vcgen` leaves still mention the program: they say which Core formulas
must hold in which states, as in `σ.update "m" v ⊨ ⟪m >= x⟫` (with the notation of
`Deep/Delab.lean`). The binders it introduces have names: `σ` for the initial state and
`pre` for the precondition, `v`/`hv` for an assigned value, `hguard` for a branch
condition, `hassume` for an `assume`, and `τ`/`hhead`/`hguard` for a loop head state.
-/

public section

namespace Strata.Deep

/-- Apply the rule for the statement at the head of a `semWP` goal. -/
syntax "core_wp_step" : tactic
macro_rules
  | `(tactic| core_wp_step) => `(tactic| first
    | apply wp_nil
    | apply wp_set
    | apply wp_havoc
    | apply wp_init
    | apply wp_init_havoc
    | apply wp_assert
    | apply wp_assume
    | apply wp_ite
    | apply wp_block
    | apply wp_loop)

/-- Tidy the VCs left by the rules. Compute the variables a loop body assigns, unfold the
contract and loop-head predicates into one `σ ⊨ e` per formula, simplify the
precondition, and close the definedness VCs `(eval σ e).isSome` of expressions in the
fragment. None of this evaluates a Core formula, so the VCs keep their Core reading. -/
syntax "core_vc_tidy" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| core_vc_tidy) => `(tactic| (
    try simp only [Strata.Deep.Block.mods, Strata.Deep.Stmt.mods, List.cons_append,
      List.nil_append, List.append_nil, Strata.Deep.PostsHold, Strata.Deep.LoopHead,
      Strata.Deep.InvsHold, eq_self_iff_true, true_implies, reduceCtorEq, false_implies,
      and_true, true_and] at *
    try simp [Strata.Deep.OldSnapshot, Strata.Deep.PresHold, Core.CoreIdent.mkOld,
      Core.CoreIdent.oldStr, Core.Procedure.Header.getInoutParams, Core.getInoutParams,
      ListMap.keys] at pre
    try (guard_hyp pre : True; clear pre)
    try (simp [Strata.Deep.eval, Strata.Deep.evalBool, Strata.Deep.binop, Strata.Deep.unop,
      Strata.Deep.typeOf, Strata.Deep.eqAt]; done)))

/-- Generate the verification conditions of `Procedure.Correct p` or `Triple P ss Q`.
A rule's continuation premise sits under up to three binders (a fresh value, a guard
hypothesis, a loop head state). The step introduces them, by name, only when a rule
applies underneath, so VC goals are left as they are. -/
syntax "core_vcgen" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| core_vcgen) => `(tactic| (
    try simp only [Strata.Deep.Procedure.Correct, Strata.Deep.Procedure.pre,
      Strata.Deep.Procedure.post, Strata.Deep.Triple]
    intro σ pre
    repeat' (first
      | core_wp_step
      | (intro (v : Strata.Deep.Val); core_wp_step)
      | (intro (hassume : Strata.Deep.MayHold _ _); core_wp_step)
      | (intro hguard; core_wp_step)
      | (intro (v : Strata.Deep.Val) hv; core_wp_step)
      | (intro (τ : Strata.Deep.State) hhead hguard; core_wp_step))
    all_goals core_vc_tidy))

/-- Evaluate the embedding away in every hypothesis and the goal. Extra simp lemmas
can be passed as `core_lift [h₁, h₂]`. -/
syntax "core_lift" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| core_lift $[[$extra,*]]?) => do
    let extra := extra.map (·.getElems) |>.getD #[]
    `(tactic|
      simp_all [eval, evalBool, evalInt, typeOf, eqAt, binop, unop, Holds, MayHold,
        State.update, State.havoc, LoopHead, InvsHold, MeasureNonneg, MeasureDecreased,
        PresHold, PostsHold, OldSnapshot, Stmt.mods, Block.mods,
        Core.Procedure.Header.getInoutParams, Core.getInoutParams, ListMap.keys, $extra,*])

end Strata.Deep

end
