/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import StrataBoole.HoareLogic.Deep.Spec
import StrataBoole.HoareLogic.Lift.Names

/-! # Deep embedding of Core: tactics

* `core_vcgen` turns a goal `Procedure.Correct p` (or `Triple P ss Q`) into verification
  conditions. It applies the rules of `Deep/Spec.lean` backwards, statement by statement,
  as `vcgen` applies `@[spec]` lemmas in the `lean-vcgen-tutorial`.
* `core_lift` names the conditions and evaluates the embedding away in every hypothesis and
  the goal (`eval`, `State.update`, the loop and contract predicates), leaving propositions
  about `Int` and `Bool`, like the tutorial's `imp_lift`.

Typical use, after unfolding the procedure: `core_vcgen <;> core_lift <;> omega`.

The VCs `core_vcgen` leaves still mention the program: they say which Core formulas
must hold in which states, as in `σ.update "m" v ⊨ ⟪m >= x⟫` (with the notation of
`Deep/Delab.lean`), each under the label of its clause (`Labeled "max2_ensures_0" …`).
The binders it introduces have names: `σ` for the initial state and `pre` for the
precondition, `v`/`hv` for an assigned value, `hguard` for a branch condition,
`hassume` for an `assume`, and `τ`/`hhead`/`hguard` for a loop head state.

`core_lift` then reads like the Strata route's goals: one goal per condition, named
`then.<label>`, `else.<label>`, `step.<label>`, `exit.<label>` or `<label>` (an unlabeled
invariant is `inv_1`, `inv_2`, … in the order written; a loop measure gives `bound` at a head
and `decreases` over an iteration); the `requires` and the invariants as hypotheses
`h<label>`; and every variable read from a state as an `Int` named like the variable (`x` for
its value in the newest state, `x₀` for the value in an older one, such as the entry state of
a loop). This file is not a `module`, so its elaborators need no `meta` phase annotations. -/

namespace Strata.Deep

open Lean Elab Tactic Meta Strata.Lift

/-! ## Verification conditions -/

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
    | apply wp_cover
    | apply wp_ite
    | apply wp_ite_nondet
    | apply wp_block
    | apply wp_loop
    | apply wp_loop_nondet)

/-- Fail with the statement at the head of a `semWP` goal that no rule applied to: after
`core_wp_step` has run to a fixpoint, such a goal is a statement outside the fragment (`call`,
`exit`, …), whose run `Exec` counts as a failure. -/
elab "core_check_supported" : tactic => do
  for g in ← getGoals do
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``Strata.Deep.semWP then
        let ss ← whnf (ty.getArg! 0)
        if ss.isAppOfArity ``List.cons 3 then
          throwError "core: no rule for the statement{indentExpr (ss.getArg! 1)}\n\
            Supported: var, :=, havoc, assert, assume, cover, if, if *, \{ }, while, while *."

/-- Tidy the VCs left by the rules. Compute the variables a loop body assigns, unfold the
contract and loop-head predicates into one `σ ⊨ e` per formula (each under its label),
simplify the precondition, and close the definedness VCs `(eval σ e).isSome` of expressions
in the fragment. None of this evaluates a Core formula, so the VCs keep their Core reading. -/
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
    try (simp [Strata.Deep.eval, Strata.Deep.evalIn, Strata.Deep.evalBool, Strata.Deep.binop,
      Strata.Deep.unop, Strata.Deep.typeOf, Strata.Deep.eqAt]; done)))

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
      | (intro (hassume : Strata.Deep.Labeled _ (Strata.Deep.MayHold _ _)); core_wp_step)
      | (intro hguard; core_wp_step)
      | (intro (v : Strata.Deep.Val) hv; core_wp_step)
      | (intro (τ : Strata.Deep.State) hhead hguard; core_wp_step)
      | (intro (τ : Strata.Deep.State) hhead; core_wp_step))
    core_check_supported
    all_goals core_vc_tidy))

/-! ## Naming the conditions -/

/-- The label a condition carries: the string of `Labeled` (empty for an unlabeled
invariant), `bound` for the lower bound of a loop measure at a head, `decreases` for its
decrease over an iteration. Leading implications (the attribute of an `ensures`, a guard) are
looked through. -/
partial def clauseLabel? (ty : Lean.Expr) : Option String :=
  let ty := ty.consumeMData
  if ty.isArrow then clauseLabel? ty.bindingBody!
  else if ty.isAppOf ``Strata.Deep.Labeled then firstStrLit? (ty.getArg! 0)
  else if ty.isAppOf ``Strata.Deep.MeasureNonneg then some "bound"
  else if ty.isAppOf ``Strata.Deep.MeasureDecreased then some "decreases"
  else none

/-- The name of the `i`-th (from 1) unlabeled invariant, or the label itself. -/
def conditionName (label : String) (i : Nat) : String × Nat :=
  if label.isEmpty then (s!"inv_{i + 1}", i + 1) else (label, i)

/-- Split the goal `g` into one goal per condition and name each after its path and label,
dropping the labels; an unlabeled invariant is `inv_1`, `inv_2`, … in the order written,
counting from `i`. Returns the goals and the next count. -/
partial def tagConditions (g : MVarId) (i : Nat) : TacticM (List MVarId × Nat) := g.withContext do
  let t := (← whnfR (← instantiateMVars (← g.getType))).consumeMData
  if t.isAppOf ``And then
    let tag ← g.getTag
    match ← g.constructor with
    | [g₁, g₂] =>
      g₁.setTag tag
      g₂.setTag tag
      let (l₁, i₁) ← tagConditions g₁ i
      let (l₂, i₂) ← tagConditions g₂ i₁
      return (l₁ ++ l₂, i₂)
    | gs => return (gs, i)
  else
    let (label, i') := match clauseLabel? t with
      | some l => let (n, i') := conditionName l i; (some n, i')
      | none => (none, i)
    let base := pathTag (← g.getTag)
    g.setTag (match label with | some s => base ++ Name.mkSimple s | none => base)
    setGoals [g]
    evalTactic (← `(tactic| try simp only [Strata.Deep.Labeled]))
    return (← getGoals, i')

/-- One goal per condition, each named after its path and label. -/
elab "core_tag" : tactic => do
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  let (gs, _) ← tagConditions g 0
  setGoals (gs ++ rest)

/-- Split the hypothesis `h` along its conjunctions and name each condition in it `h<label>`
(`hinv_1`, `hinv_2`, … for unlabeled invariants, counting from `i`; `hbound` for the lower
bound of a measure); drop the labels. Returns the next count. -/
partial def splitLabeled (h : Name) (i : Nat) : TacticM Nat := withMainContext do
  let some decl := (← getLCtx).findFromUserName? h | return i
  let ty := (← instantiateMVars decl.type).consumeMData
  if ty.isAppOf ``And then
    let hId := mkIdent h
    let left := mkIdent (Name.mkSimple (h.toString ++ "_left"))
    evalTactic (← `(tactic| obtain ⟨$left:ident, $hId:ident⟩ := $hId:ident))
    let i ← splitLabeled left.getId i
    splitLabeled h i
  else
    match clauseLabel? ty with
    | some l =>
      let (n, i') := conditionName l i
      let name := Name.mkSimple ("h" ++ n)
      let g ← getMainGoal
      replaceMainGoal [← g.rename decl.fvarId name]
      evalTactic (← `(tactic| try simp only [Strata.Deep.Labeled] at $(mkIdent name):ident))
      return i'
    | none => return i

/-- Name the hypotheses that carry labels: the precondition `pre` as one hypothesis per
`requires`, a loop head `hhead` as one per `invariant` (and `hbound`), an `assume` after its
label. -/
elab "core_hyps" : tactic => do
  for h in [`pre, `hhead, `hassume] do
    discard <| splitLabeled h 0

/-- The reads of state variables in an expression, `(σ "x").toInt` or `(σ "x").toBool`, as
(state, variable, read) triples. -/
partial def stateReads : Lean.Expr → Array (FVarId × String × Name) → Array (FVarId × String × Name)
  | e@(.app f a), acc =>
    let acc := match e with
      | .app (.const c _) (.app (.fvar σ) (.lit (.strVal x))) =>
        if c == ``Strata.Deep.Val.toInt || c == ``Strata.Deep.Val.toBool then acc.push (σ, x, c)
        else acc
      | _ => acc
    stateReads a (stateReads f acc)
  | .lam _ t b _, acc | .forallE _ t b _, acc => stateReads b (stateReads t acc)
  | .letE _ t v b _, acc => stateReads b (stateReads v (stateReads t acc))
  | .mdata _ e, acc | .proj _ _ e, acc => stateReads e acc
  | _, acc => acc

/-- `n` as a subscript, for the value of a variable in an older state. -/
def subscript (n : Nat) : String :=
  String.ofList ((toString n).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat))

/-- Name the variables the goal and the hypotheses read: `(σ "x").toInt` becomes an `Int`
named `x`, read from the newest state that mentions `x`; the same variable read from an older
state (its value at the entry of a loop) is `x₀`, then `x₁`. -/
elab "core_vars" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut reads := stateReads (← instantiateMVars (← getMainTarget)) #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    reads := stateReads (← instantiateMVars d.type) reads
  let mut keys : Array (FVarId × String × Name) := #[]
  for r in reads do
    unless keys.contains r do keys := keys.push r
  let vars := (keys.map (·.2.1)).toList.eraseDups
  for x in vars do
    let states := ((keys.filter (·.2.1 == x)).map (·.1)).toList.eraseDups.toArray
    let states := states.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index
    let n := states.size
    for σ in states, i in List.range n do
      let name := if i + 1 == n then x else x ++ subscript i
      for (σ', x', c) in keys do
        unless σ' == σ && x' == x do continue
        let term := mkApp (mkConst c) (mkApp (.fvar σ) (mkStrLit x))
        let tStx ← withMainContext (Term.exprToSyntax term)
        let xId := mkIdent (Name.mkSimple name)
        let hId := mkIdent (Name.mkSimple ("h" ++ name ++ "_read"))
        evalTactic (← `(tactic| generalize $hId:ident : $tStx:term = $xId:ident at *))
        evalTactic (← `(tactic| try clear $hId:ident))

/-- Drop what the lifting has consumed: the states, the values, and trivial hypotheses. -/
elab "core_clear" : tactic => do
  clearNoise fun d => do
    let ty ← instantiateMVars d.type
    if ty.isConstOf ``True then return true
    if ty.isConstOf ``Strata.Deep.Val || ty.isConstOf ``Strata.Deep.State then return true
    if ty.isArrow && ty.bindingDomain!.isConstOf ``String &&
        ty.bindingBody!.isConstOf ``Strata.Deep.Val then
      return true
    return false

/-! ## Lifting -/

/-- Name the conditions, then evaluate the embedding away in every hypothesis and the goal,
and name the variables. Extra simp lemmas can be passed as `core_lift [h₁, h₂]`. Ground
terms are evaluated by unfolding: `simp` does not retrieve the equations of `typeOf` on an
operator application through its index, and `typeOf` of the closed left operand of a `==`
is what decides how the equality is read. -/
syntax "core_lift" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| core_lift $[[$extra,*]]?) => do
    let extra := extra.map (·.getElems) |>.getD #[]
    `(tactic| (
      core_tag
      all_goals core_hyps
      all_goals try simp_all (config := { ground := true })
        [eval, evalIn, evalBool, evalBoolIn, evalInt, typeOf, eqAt, binop, unop, SatT, SatF,
         Holds, MayHold, Labeled, Val.ty,
         State.update, State.havoc, LoopHead, InvsHold, MeasureNonneg, MeasureDecreased,
         PresHold, PostsHold, OldSnapshot, Stmt.mods, Block.mods,
         Core.Procedure.Header.getInoutParams, Core.getInoutParams, ListMap.keys,
         Val.toInt_int, Val.toBool_bool, decide_eq_true_eq, decide_eq_false_iff_not,
         Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Classical.not_not,
         $extra,*]
      all_goals try subst_vars
      all_goals core_vars
      all_goals core_clear))

end Strata.Deep
