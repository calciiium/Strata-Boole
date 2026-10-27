/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Deep.Triple

/-! # Deep embedding of Core: proof rules

One rule per statement form, each a theorem about `Exec`. A rule concludes
`semWP (s :: ss) Q σ` for a statement `s` and reduces it to premises about the rest of
the list: either smaller `semWP` goals, or *verification conditions* (VCs) that mention
no program. `core_vcgen` (`Deep/Tactic.lean`) applies the rules backwards until only VCs
are left, the way `vcgen` applies `@[spec]` lemmas in the `lean-vcgen-tutorial`.

The premises of a rule are ordered so that a VC comes first and the continuation last.
Their names (`defined`, `assertion`, `entry`, `step`, `ifTrue`, `rest`, …) become the
case tags of the goals `core_vcgen` leaves, so a tag such as `rest.step.rest` reads as
the path to the obligation:
* a definedness VC `(eval σ e).isSome`: the expression is in the fragment;
* a check VC: an assertion, or a loop invariant or measure obligation;
* a continuation: `semWP` of what runs next, possibly under binders (a fresh value, a
  guard hypothesis, a loop head state).

`Exec.unsupported` gives every list one extra run, which fails unless the head statement
is supported. Each proof dismisses that run with `absurd trivial`: `Supported s` reduces
to `True` for the statement forms that have a rule.
-/

@[expose] public section

namespace Strata.Deep

open Imperative

variable {Q : State → Prop} {σ : State} {ss : List Core.Statement}
  {e c g : Expr} {x : Core.CoreIdent} {l : String} {md : MetaData Core.Expression}

/-- The empty list: the postcondition must hold now. -/
theorem wp_nil (h : Q σ) : semWP [] Q σ := by
  intro o ho
  cases ho with
  | nil => exact h

/-- `x := e`: Hoare's assignment rule. The new value is a fresh `v`, with the hypothesis
`some v = eval σ e`, so the VCs stay readable until `core_lift` evaluates `e`. The
variable is on the left so that `simp_all` substitutes it once `e` is evaluated. -/
theorem wp_set (defined : (eval σ e).isSome)
    (rest : ∀ v, some v = eval σ e → semWP ss Q (σ.update x.name v)) :
    semWP (.cmd (.cmd (.set x (.det e) md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | set he k => exact rest _ he.symm _ k
  | set_fail he => simp [he] at defined
  | unsupported hs => exact absurd trivial hs

/-- `havoc x`: the rest must work for every value of `x`. -/
theorem wp_havoc (rest : ∀ v, semWP ss Q (σ.update x.name v)) :
    semWP (.cmd (.cmd (.set x .nondet md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | havoc k => exact rest _ _ k
  | unsupported hs => exact absurd trivial hs

/-- `var x : T := e`: as `x := e`. -/
theorem wp_init {ty : Core.Expression.Ty} (defined : (eval σ e).isSome)
    (rest : ∀ v, some v = eval σ e → semWP ss Q (σ.update x.name v)) :
    semWP (.cmd (.cmd (.init x ty (.det e) md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | init he k => exact rest _ he.symm _ k
  | init_fail he => simp [he] at defined
  | unsupported hs => exact absurd trivial hs

/-- `var x : T`: as `havoc x`. -/
theorem wp_init_havoc {ty : Core.Expression.Ty} (rest : ∀ v, semWP ss Q (σ.update x.name v)) :
    semWP (.cmd (.cmd (.init x ty .nondet md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | init_havoc k => exact rest _ _ k
  | unsupported hs => exact absurd trivial hs

/-- `assert e`: a VC that `e` holds, then the rest. -/
theorem wp_assert (assertion : Holds σ e) (rest : semWP ss Q σ) :
    semWP (.cmd (.cmd (.assert l e md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | assert _ k => exact rest _ k
  | assert_fail hne => exact absurd assertion hne
  | unsupported hs => exact absurd trivial hs

/-- `assume e`: the rest, under the hypothesis that `e` may hold. -/
theorem wp_assume (rest : MayHold σ e → semWP ss Q σ) :
    semWP (.cmd (.cmd (.assume l e md)) :: ss) Q σ := by
  intro o ho
  cases ho with
  | assume he k => exact rest he _ k
  | unsupported hs => exact absurd trivial hs

/-- `if (c) { t } else { f }`: each branch, under its value of the guard, followed by
the rest. -/
theorem wp_ite {t f : List Core.Statement} (defined : (evalBool σ c).isSome)
    (ifTrue : evalBool σ c = some true → semWP t (semWP ss Q) σ)
    (ifFalse : evalBool σ c = some false → semWP f (semWP ss Q) σ) :
    semWP (.ite (.det c) t f md :: ss) Q σ := by
  intro o ho
  cases ho with
  | ite_true hc h k => exact ifTrue hc _ h _ k
  | ite_true_fail hc h => exact False.elim (ifTrue hc _ h)
  | ite_false hc h k => exact ifFalse hc _ h _ k
  | ite_false_fail hc h => exact False.elim (ifFalse hc _ h)
  | ite_fail hc => simp [hc] at defined
  | unsupported hs => exact absurd trivial hs

/-- `{ b }`: the block, followed by the rest. -/
theorem wp_block {b : List Core.Statement} (hb : semWP b (semWP ss Q) σ) :
    semWP (.block l b md :: ss) Q σ := by
  intro o ho
  cases ho with
  | block h k => exact hb _ h _ k
  | block_fail h => exact False.elim (hb _ h)
  | unsupported hs => exact absurd trivial hs

/-- `while (g) decreases m invariant invs { b }`, with the annotations the program
carries. The head states are `σ.havoc (Block.mods b) τ` for an arbitrary `τ`: the body
can change only the variables it assigns, so every other variable keeps its value from
`σ`. This is the frame Core's verifier gets by havocking just the modified variables.
* `entry`: the invariants and the measure bound hold on entry.
* `guardDefined`: the guard is defined at every head state.
* `step`: an iteration from a head state, with the guard true, re-establishes the
  invariants and the bound, and decreases the measure.
* `exit`: from a head state with the guard false, the rest of the list runs.

The proof inducts on the runs of the loop. -/
theorem wp_loop {m : Option Expr} {invs : List (String × Expr)} {b : List Core.Statement}
    (entry : LoopHead invs m σ)
    (guardDefined : ∀ τ, LoopHead invs m (σ.havoc (Block.mods b) τ) →
      (evalBool (σ.havoc (Block.mods b) τ) g).isSome)
    (step : ∀ τ, LoopHead invs m (σ.havoc (Block.mods b) τ) →
      evalBool (σ.havoc (Block.mods b) τ) g = some true →
      semWP b (fun σ' => LoopHead invs m σ' ∧
        MeasureDecreased m (σ.havoc (Block.mods b) τ) σ') (σ.havoc (Block.mods b) τ))
    (exit : ∀ τ, LoopHead invs m (σ.havoc (Block.mods b) τ) →
      evalBool (σ.havoc (Block.mods b) τ) g = some false →
      semWP ss Q (σ.havoc (Block.mods b) τ)) :
    semWP (.loop (.det g) m invs b md :: ss) Q σ := by
  -- Strengthen to an arbitrary head state `σ₁`: one that agrees with `σ` outside the
  -- body's variables and passes the head checks.
  suffices key : ∀ l σ₁ o, Exec l σ₁ o → l = .loop (.det g) m invs b md :: ss →
      (∀ y, y ∉ Block.mods b → σ₁ y = σ y) → LoopHead invs m σ₁ → o.Sat Q from
    fun o ho => key _ _ _ ho rfl (fun _ _ => rfl) entry
  intro l σ₁ o h
  induction h with
  | loop_head_fail hh => intro hl _ hh₁; cases hl; exact absurd hh₁ hh
  | loop_guard_fail hh hg =>
    intro hl hfr _
    cases hl
    have := guardDefined _ (by rwa [State.havoc_self hfr]); rw [State.havoc_self hfr] at this
    simp [hg] at this
  | loop_exit hh hg k _ =>
    intro hl hfr _
    cases hl
    have := exit _ (by rwa [State.havoc_self hfr]) (by rwa [State.havoc_self hfr])
    rw [State.havoc_self hfr] at this
    exact this _ k
  | loop_body_fail hh hg hb =>
    intro hl hfr _
    cases hl
    have := step _ (by rwa [State.havoc_self hfr]) (by rwa [State.havoc_self hfr])
    rw [State.havoc_self hfr] at this
    exact False.elim (this _ hb)
  | loop_measure_fail hh hg hb hd =>
    intro hl hfr _
    cases hl
    have := step _ (by rwa [State.havoc_self hfr]) (by rwa [State.havoc_self hfr])
    rw [State.havoc_self hfr] at this
    exact absurd (this _ hb).2 hd
  | loop_iter hh hg hb hd k _ ih =>
    intro hl hfr _
    cases hl
    have := step _ (by rwa [State.havoc_self hfr]) (by rwa [State.havoc_self hfr])
    rw [State.havoc_self hfr] at this
    refine ih rfl (fun y hy => ?_) (this _ hb).1
    rw [hb.frame _ rfl y hy, hfr y hy]
  | unsupported hs => intro hl _ _; cases hl; exact absurd trivial hs
  | _ => intro hl; cases hl

end Strata.Deep

end
