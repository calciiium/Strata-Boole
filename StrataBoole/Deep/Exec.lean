/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Deep.Lang

/-! # Deep embedding of Core: big-step semantics

`Exec ss σ o` says that running the statement list `ss` from `σ` can end with outcome
`o`. It is the ground truth of the deep embedding: the triple (`Deep/Triple.lean`) is
defined from it, and every proof rule (`Deep/Spec.lean`) is a theorem about it.

* **Failure is an outcome.** A run ends in `.failure` when a check fails: an `assert`,
  a loop invariant, or a `decreases` obligation. It also fails when it meets an
  expression or a statement outside the fragment. A triple rules out failure, so it
  covers every assertion in the program.
* **`assume` discards runs.** `assume e` has no outcome when `e` is false.
* **Loops are checked the way Core checks them.** Each time control reaches the loop
  head, every invariant must hold and the measure must be a non-negative integer.
  After each iteration of the body, the measure must have decreased.
* **Only terminating runs are described**, so the triple is partial correctness. The
  `decreases` checks are still enforced on every iteration a run makes.
-/

@[expose] public section

namespace Strata.Deep

open Imperative

/-! ## Outcomes -/

/-- How a run ends: normally in a state, or with a failed check. -/
inductive Outcome where
  | normal (σ : State)
  | failure

/-- `Q` holds of a normal outcome. A failure satisfies no postcondition. -/
def Outcome.Sat (Q : State → Prop) : Outcome → Prop
  | .normal σ => Q σ
  | .failure => False

/-! ## The fragment -/

/-- The statement forms the semantics covers. Every other form (calls, `cover`, `exit`,
nondeterministic guards, type declarations) fails, so a triple about a program that
uses one cannot be proved. -/
def Supported : Core.Statement → Prop
  | .cmd (.cmd (.init _ _ _ _)) => True
  | .cmd (.cmd (.set _ _ _)) => True
  | .cmd (.cmd (.assert _ _ _)) => True
  | .cmd (.cmd (.assume _ _ _)) => True
  | .ite (.det _) _ _ _ => True
  | .block _ _ _ => True
  | .loop (.det _) _ _ _ _ => True
  | _ => False

mutual
/-- The variables a statement may assign: the targets of `var`, `:=` and `havoc`,
including those in nested blocks. -/
def Stmt.mods : Core.Statement → List String
  | .cmd (.cmd (.init x _ _ _)) => [x.name]
  | .cmd (.cmd (.set x _ _)) => [x.name]
  | .ite _ t f _ => Block.mods t ++ Block.mods f
  | .block _ b _ => Block.mods b
  | .loop _ _ _ b _ => Block.mods b
  | _ => []

/-- The variables a statement list may assign. -/
def Block.mods : List Core.Statement → List String
  | [] => []
  | s :: ss => Stmt.mods s ++ Block.mods ss
end

/-- `σ` with each variable of `xs` replaced by its value in `τ`. A loop's head states are
of this form, with `xs` the variables its body may assign. -/
def State.havoc (σ : State) (xs : List String) (τ : State) : State :=
  fun y => if y ∈ xs then τ y else σ y

/-! ## Loop checks -/

/-- Every invariant holds. -/
def InvsHold : List (String × Expr) → State → Prop
  | [], _ => True
  | (_, e) :: invs, σ => Holds σ e ∧ InvsHold invs σ

/-- The measure, if there is one, is a non-negative integer. -/
def MeasureNonneg : Option Expr → State → Prop
  | none, _ => True
  | some e, σ =>
    match evalInt σ e with
    | some k => 0 ≤ k
    | none => False

/-- The measure, if there is one, is smaller in `σ'` (after an iteration) than in `σ`
(before it). -/
def MeasureDecreased : Option Expr → State → State → Prop
  | none, _, _ => True
  | some e, σ, σ' =>
    match evalInt σ e, evalInt σ' e with
    | some k, some k' => k' < k
    | _, _ => False

/-- What Core checks whenever control reaches a loop head (`loop_entry` in the CFG Core
lowers loops to): the invariants, then the lower bound of the measure. -/
def LoopHead (invs : List (String × Expr)) (m : Option Expr) (σ : State) : Prop :=
  InvsHold invs σ ∧ MeasureNonneg m σ

/-! ## Execution -/

/-- `Exec ss σ o`: running `ss` from `σ` can end with outcome `o`. Each compound
statement has one constructor for a normal run of its body, followed by the rest of the
list, and one for a body that fails. -/
inductive Exec : List Core.Statement → State → Outcome → Prop where
  | nil : Exec [] σ (.normal σ)
  -- `x := e`
  | set (he : eval σ e = some v) (k : Exec ss (σ.update x.name v) o) :
      Exec (.cmd (.cmd (.set x (.det e) md)) :: ss) σ o
  | set_fail (he : eval σ e = none) :
      Exec (.cmd (.cmd (.set x (.det e) md)) :: ss) σ .failure
  -- `havoc x`
  | havoc (k : Exec ss (σ.update x.name v) o) :
      Exec (.cmd (.cmd (.set x .nondet md)) :: ss) σ o
  -- `var x : T := e`
  | init (he : eval σ e = some v) (k : Exec ss (σ.update x.name v) o) :
      Exec (.cmd (.cmd (.init x ty (.det e) md)) :: ss) σ o
  | init_fail (he : eval σ e = none) :
      Exec (.cmd (.cmd (.init x ty (.det e) md)) :: ss) σ .failure
  -- `var x : T`
  | init_havoc (k : Exec ss (σ.update x.name v) o) :
      Exec (.cmd (.cmd (.init x ty .nondet md)) :: ss) σ o
  -- `assert e`
  | assert (he : Holds σ e) (k : Exec ss σ o) :
      Exec (.cmd (.cmd (.assert l e md)) :: ss) σ o
  | assert_fail (he : ¬ Holds σ e) :
      Exec (.cmd (.cmd (.assert l e md)) :: ss) σ .failure
  -- `assume e`
  | assume (he : MayHold σ e) (k : Exec ss σ o) :
      Exec (.cmd (.cmd (.assume l e md)) :: ss) σ o
  -- `if (c) { t } else { f }`
  | ite_true (hc : evalBool σ c = some true) (ht : Exec t σ (.normal σ')) (k : Exec ss σ' o) :
      Exec (.ite (.det c) t f md :: ss) σ o
  | ite_true_fail (hc : evalBool σ c = some true) (ht : Exec t σ .failure) :
      Exec (.ite (.det c) t f md :: ss) σ .failure
  | ite_false (hc : evalBool σ c = some false) (hf : Exec f σ (.normal σ')) (k : Exec ss σ' o) :
      Exec (.ite (.det c) t f md :: ss) σ o
  | ite_false_fail (hc : evalBool σ c = some false) (hf : Exec f σ .failure) :
      Exec (.ite (.det c) t f md :: ss) σ .failure
  | ite_fail (hc : evalBool σ c = none) :
      Exec (.ite (.det c) t f md :: ss) σ .failure
  -- `{ b }`; variables declared in `b` stay visible after it
  | block (hb : Exec b σ (.normal σ')) (k : Exec ss σ' o) :
      Exec (.block l b md :: ss) σ o
  | block_fail (hb : Exec b σ .failure) :
      Exec (.block l b md :: ss) σ .failure
  -- `while (g) decreases m invariant invs { b }`
  | loop_head_fail (hh : ¬ LoopHead invs m σ) :
      Exec (.loop (.det g) m invs b md :: ss) σ .failure
  | loop_guard_fail (hh : LoopHead invs m σ) (hg : evalBool σ g = none) :
      Exec (.loop (.det g) m invs b md :: ss) σ .failure
  | loop_exit (hh : LoopHead invs m σ) (hg : evalBool σ g = some false)
      (k : Exec ss σ o) :
      Exec (.loop (.det g) m invs b md :: ss) σ o
  | loop_body_fail (hh : LoopHead invs m σ) (hg : evalBool σ g = some true)
      (hb : Exec b σ .failure) :
      Exec (.loop (.det g) m invs b md :: ss) σ .failure
  | loop_measure_fail (hh : LoopHead invs m σ) (hg : evalBool σ g = some true)
      (hb : Exec b σ (.normal σ')) (hd : ¬ MeasureDecreased m σ σ') :
      Exec (.loop (.det g) m invs b md :: ss) σ .failure
  | loop_iter (hh : LoopHead invs m σ) (hg : evalBool σ g = some true)
      (hb : Exec b σ (.normal σ')) (hd : MeasureDecreased m σ σ')
      (k : Exec (.loop (.det g) m invs b md :: ss) σ' o) :
      Exec (.loop (.det g) m invs b md :: ss) σ o
  -- everything outside the fragment
  | unsupported (hs : ¬ Supported s) : Exec (s :: ss) σ .failure

/-- The weakest liberal precondition read off `Exec`: no run of `ss` from `σ` fails,
and every run that ends normally ends in `Q`. -/
def semWP (ss : List Core.Statement) (Q : State → Prop) (σ : State) : Prop :=
  ∀ o, Exec ss σ o → o.Sat Q

/-! ## Framing -/

/-- A run changes only the variables the statements may assign. -/
theorem Exec.frame {ss : List Core.Statement} {σ : State} {o : Outcome} (h : Exec ss σ o) :
    ∀ σ', o = .normal σ' → ∀ y, y ∉ Block.mods ss → σ' y = σ y := by
  induction h with
  | nil => intro _ h _ _; cases h; rfl
  | set _ _ ih | havoc _ ih | init _ _ ih | init_havoc _ ih =>
    intro σ' h y hy
    simp only [Block.mods, Stmt.mods, List.cons_append, List.nil_append, List.mem_cons,
      not_or] at hy
    rw [ih σ' h y hy.2]
    simp [State.update, hy.1]
  | assert _ _ ih | assume _ _ ih =>
    intro σ' h y hy
    exact ih σ' h y (by simpa [Block.mods, Stmt.mods] using hy)
  | ite_true _ _ _ iht ihk | ite_false _ _ _ iht ihk | block _ _ iht ihk =>
    intro σ' h y hy
    simp only [Block.mods, Stmt.mods, List.mem_append, not_or] at hy
    rw [ihk σ' h y (by simp_all), iht _ rfl y (by simp_all)]
  | loop_exit _ _ _ ih =>
    intro σ' h y hy
    exact ih σ' h y (by simp_all [Block.mods, Stmt.mods])
  | loop_iter _ _ _ _ _ ihb ihk =>
    intro σ' h y hy
    rw [ihk σ' h y hy, ihb _ rfl y (by simp_all [Block.mods, Stmt.mods])]
  | _ => intro _ h; cases h

/-- A state that agrees with `σ` outside `xs` is `σ` havocked at `xs`. -/
theorem State.havoc_self {σ σ' : State} {xs : List String}
    (h : ∀ y, y ∉ xs → σ' y = σ y) : σ.havoc xs σ' = σ' := by
  funext y
  by_cases hy : y ∈ xs <;> simp [State.havoc, hy, h]

end Strata.Deep

end
