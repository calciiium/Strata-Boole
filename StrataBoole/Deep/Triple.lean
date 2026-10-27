/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Deep.Exec
public import Strata.Languages.Core.Procedure

/-! # Deep embedding of Core: Hoare triples and procedure contracts

`Triple P ss Q` is the partial-correctness triple `{P} ss {Q}` over `Exec`. Since a
failed check is an outcome (`Deep/Exec.lean`), the triple also says that every `assert`,
loop invariant and `decreases` check in `ss` holds whenever a run reaches it.

`Procedure.Correct p` reads the contract of a Core procedure as a triple: the
`requires` clauses become the precondition and the checked `ensures` clauses the
postcondition.
-/

@[expose] public section

namespace Strata.Deep

open Imperative

/-- `{P} ss {Q}`: every run of `ss` from a `P`-state passes all its checks, and every
run that ends ends in a `Q`-state. -/
def Triple (P : State → Prop) (ss : List Core.Statement) (Q : State → Prop) : Prop :=
  ∀ σ, P σ → semWP ss Q σ

/-- `Triple` unfolds to the textbook reading over `Exec`. Both directions are the
identity: the triple is defined from the semantics, so no separate soundness proof is
needed. -/
theorem Triple.iff_exec {P Q : State → Prop} {ss : List Core.Statement} :
    Triple P ss Q ↔
      ∀ σ, P σ → (¬ Exec ss σ .failure) ∧ ∀ σ', Exec ss σ (.normal σ') → Q σ' := by
  constructor
  · intro h σ hP
    exact ⟨fun hf => h σ hP _ hf, fun σ' he => h σ hP _ he⟩
  · intro h σ hP o he
    cases o with
    | normal σ' => exact (h σ hP).2 σ' he
    | failure => exact (h σ hP).1 he

/-! ## Procedure contracts -/

/-- Each precondition may hold. The body assumes every `requires` clause, `free` or not. -/
def PresHold : List (String × Check Core.Expression) → State → Prop
  | [], _ => True
  | (_, c) :: cs, σ => MayHold σ c.expr ∧ PresHold cs σ

/-- Each checked postcondition holds. A `free ensures` is assumed by callers and never
checked against the body. Each case returns a function of the state, so that the
predicate also unfolds where it is passed unapplied, as a postcondition. -/
def PostsHold : List (String × Check Core.Expression) → State → Prop
  | [] => fun _ => True
  | (_, c) :: cs => fun σ => (c.attr = .Default → Holds σ c.expr) ∧ PostsHold cs σ

/-- The translator turns `old g` into the variable `"old g"`. On entry it equals `g`,
and no statement assigns it, so it keeps the entry value of the `inout` parameter `g`. -/
def OldSnapshot : List (Core.CoreIdent × Lambda.LMonoTy) → State → Prop
  | [], _ => True
  | (g, _) :: gs, σ => σ (Core.CoreIdent.mkOld g.name).name = σ g.name ∧ OldSnapshot gs σ

namespace Procedure

/-- The precondition of a procedure's triple. -/
def pre (p : Core.Procedure) : State → Prop :=
  fun σ => OldSnapshot p.header.getInoutParams σ ∧ PresHold p.spec.preconditions σ

/-- The postcondition of a procedure's triple. It is stated without the state argument
so that it unfolds where the triple passes it unapplied, as `semWP ss (post p)`. -/
def post (p : Core.Procedure) : State → Prop :=
  PostsHold p.spec.postconditions

/-- `p` meets its contract: `{pre p} body {post p}`. A body given as a CFG is outside
the fragment. -/
def Correct (p : Core.Procedure) : Prop :=
  match p.body with
  | .structured ss => Triple (pre p) ss (post p)
  | .cfg _ => False

end Procedure

end Strata.Deep

end
