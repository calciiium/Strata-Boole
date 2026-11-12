/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import Strata.Languages.Core.Statement

/-! # Reading the program from a goal, naming the goals

Helpers shared by the tactics of `StrataBoole/HoareLogic/Hoare` and `StrataBoole/HoareLogic/Deep`: reading list, pair,
string and identifier literals off a reduced AST, naming a goal after the path to it and the
label of the clause it checks, splitting a conjunction while keeping that name, and clearing the
hypotheses a lifting has consumed. This file is not a `module`, so its elaborators need no `meta`
phase annotations. -/

namespace Strata.Lift

open Lean Elab Tactic Meta

/-! ## Literals of the AST -/

/-- The elements of a list literal, after reduction. -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.cons, #[_, hd, tl]) => return hd :: (← listElems tl)
  | (``List.nil, _) => return []
  | _ => throwError "not a list literal{indentExpr e}"

/-- The two components of a pair, after reduction. -/
def pairElems (e : Expr) : MetaM (Expr × Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Prod.mk, #[_, _, a, b]) => return (a, b)
  | _ => throwError "not a pair{indentExpr e}"

/-- The string of a string literal, after reduction. -/
def strLit (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => return s
  | _ => throwError "not a string literal{indentExpr e}"

/-- The name of a Core identifier `⟨name, ()⟩`. -/
def identName (e : Expr) : MetaM String := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Lambda.Identifier.mk, #[_, n, _]) => strLit n
  | _ => throwError "not an identifier{indentExpr e}"

/-- Whether a monomorphic type is `int`. -/
def isIntTy (e : Expr) : MetaM Bool := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Lambda.LMonoTy.tcons, #[n, _]) => return (← strLit n) == "int"
  | _ => return false

/-- The expression of a deterministic operand, if it is one. -/
def detExpr? (e : Expr) : MetaM (Option Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Imperative.ExprOrNondet.det, #[_, e]) => return some e
  | _ => return none

/-- A proof that the `i`-th element of a list literal is a member of it. -/
def memProof : Nat → TermElabM (TSyntax `term)
  | 0 => `(List.mem_cons_self ..)
  | n + 1 => do
    let s ← memProof n
    `(List.mem_cons_of_mem _ $s)

/-- The `argIdx`-th argument of the type of the hypothesis `h`. -/
def argOf (h : Name) (argIdx : Nat) : TacticM Expr := do
  let some decl := (← getLCtx).findFromUserName? h
    | throwError "no hypothesis `{h}`"
  let ty ← instantiateMVars decl.type
  let args := ty.getAppArgs
  unless argIdx < args.size do throwError "unexpected shape of `{h}`{indentExpr ty}"
  return args[argIdx]!

/-- The first string literal in an expression. -/
def firstStrLit? (e : Expr) : Option String :=
  match e.find? (fun e => e matches .lit (.strVal _)) with
  | some (.lit (.strVal s)) => some s
  | _ => none

/-! ## Goal names

A goal is named after the path to it and the clause it checks: `then.<label>`, `else.<label>`
for the branches of an `if`, `step.<label>` for an invariant the body of a loop re-establishes,
`exit.<label>` for a condition after a loop, `<label>` alone for a condition on the straight path
from the entry. -/

/-- The components of a goal's tag that describe the path to it: the branch of an `if` (`then`
and `else`, also as the rule premises `ifTrue` and `ifFalse`) and the obligation of a loop
(`step`, `exit`). -/
def pathTag (tag : Name) : Name :=
  tag.components.filterMap (fun c =>
    if c == `then || c == `ifTrue then some `then
    else if c == `else || c == `ifFalse then some `else
    else if c == `step || c == `exit then some c else none)
  |>.foldl (fun n c => n ++ c) Name.anonymous

/-- Rename the main goal after the path to it. -/
def tagPath : TacticM Unit := do
  let g ← getMainGoal
  g.setTag (pathTag (← g.getTag))

/-- Rename the main goal after the path to it and the label `label`, if any. -/
def tagClause (label : Option String) : TacticM Unit := do
  let g ← getMainGoal
  let base := pathTag (← g.getTag)
  g.setTag (match label with | some s => base ++ Name.mkSimple s | none => base)

/-- Split a conjunction that is one on the surface, leaving the named predicates folded; both
halves keep the goal's name. Fails on anything but a conjunction. -/
def splitAnd : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tag ← g.getTag
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.consumeMData.isAppOf ``And do throwError "not a conjunction{indentExpr t}"
  evalTactic (← `(tactic| constructor))
  for g in (← getGoals).take 2 do g.setTag tag

/-! ## Clearing -/

/-- A hypothesis whose type is `True`, an application of a constant in `heads`, or an equation
whose left-hand side is an application of a constant in `eqHeads`. -/
def noiseByHead (heads eqHeads : List Name) (d : LocalDecl) : MetaM Bool := do
  let ty ← instantiateMVars d.type
  if ty.isConstOf ``True then return true
  if let .const n _ := ty.getAppFn then
    if heads.contains n then return true
    if n == ``Eq then
      if let #[_, lhs, _] := ty.getAppArgs then
        if let .const m _ := lhs.getAppFn then return eqHeads.contains m
  return false

/-- Clear, in two passes, every hypothesis `isNoise` accepts that nothing depends on. The
predicate runs in the goal's context, so it may look up other hypotheses. -/
def clearNoise (isNoise : LocalDecl → MetaM Bool) : TacticM Unit := do
  for _ in [0, 1] do
    let g ← getMainGoal
    let decls := (← g.getDecl).lctx.decls.toList.filterMap id
    for d in decls.reverse do
      if d.isImplementationDetail then continue
      if ← g.withContext (isNoise d) then
        try
          let g ← getMainGoal
          replaceMainGoal [← g.clear d.fvarId]
        catch _ => pure ()

end Strata.Lift
