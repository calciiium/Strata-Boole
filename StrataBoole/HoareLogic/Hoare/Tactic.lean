/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import StrataBoole.HoareLogic.Hoare.Contract
import StrataBoole.HoareLogic.Lift.Names

/-! # The tactics

* `hoare_wp` walks a statement list with the `wp`-form rules, synthesizing every intermediate
  assertion by unification and discharging the structural side conditions (the declared names,
  the write set, `exitsCoveredByBlocks`) on the concrete AST. At a `while` it builds the
  invariant predicate from the program's `invariant` clauses and reads the body's write set
  (`hoare_loop`); the body is verified under its entry store. It stops at a statement no rule
  covers, leaving that goal open.
* `hoare_contract` opens `Procedure.contractTriple`: one model, the two blocks around the body,
  the check that the evaluator runs every statement (`hoare_refuse_unevaluated`), then
  `hoare_wp`, so that what is left is the implication from `contractPre` to the synthesized
  precondition, which contains the preservation and exit obligations of each loop at the
  loop's entry.
* `hoare_vcs` introduces that implication statement by statement, opens each loop obligation it
  meets (`hoare_open_loop`) and splits the conjunctions the rules leave, so that each
  verification condition is its own goal with the run's store facts as hypotheses; a variable
  the loop does not write is read through the agreement with the entry store (`hagree`).
* `hoare_lift` evaluates the stores and reads the conditions, leaving goals over `Int` and
  `Bool`.

Typical use: `hoare_contract <;> hoare_vcs <;> hoare_lift <;> omega`.

The names in the goals come from the program: `hoare_inputs` and `hoare_typed` introduce each
integer variable as an `Int` named like the variable, `hoare_requires` and `hoare_invariants`
lift each clause into a hypothesis named after its label, and the goal tags read
`then.<label>`, `else.<label>`, `step.<label>` (an invariant preserved by the body) and
`exit.<label>` (a condition after a loop), as `StrataBoole/HoareLogic/Lift/Names.lean` defines them. This
file is not a `module`, so its elaborators need no `meta` phase annotations. -/

namespace Strata.Hoare

open Lean Elab Tactic Meta Strata.Lift

/-! ## Reading the goal -/

/-- The statement list and the model of a goal `TripleM π params Pre ss Post`. -/
def tripleParts : TacticM (Expr × Expr) := do
  let ty ← instantiateMVars (← getMainTarget)
  let args := ty.getAppArgs
  unless args.size == 6 do throwError "hoare: not a triple{indentExpr ty}"
  let model := if ty.isAppOf ``Strata.Hoare.Model.TripleM then args[2]! else args[1]!
  return (args[4]!, model)

/-! ## Refusing statements the evaluator cannot run -/

/-- Whether `Core.Factory` evaluates full applications of the operator `name`: it has an entry
for it with a concrete evaluation. `select`, `update`, the `Sequence` and `String` operators,
and every function a program declares itself have none. -/
def evaluatedOp (name : String) : Bool :=
  match Core.Factory[name]? with
  | some f => f.concreteEval.isSome
  | none => false

/-- The operators an expression applies, after reduction of the AST. -/
partial def opsOf (e : Expr) : MetaM (List String) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Lambda.LExpr.const, _) | (``Lambda.LExpr.bvar, _) | (``Lambda.LExpr.fvar, _) => return []
  | (``Lambda.LExpr.op, #[_, _, o, _]) => return [← identName o]
  | (``Lambda.LExpr.app, #[_, _, f, a]) => return (← opsOf f) ++ (← opsOf a)
  | (``Lambda.LExpr.eq, #[_, _, a, b]) => return (← opsOf a) ++ (← opsOf b)
  | (``Lambda.LExpr.ite, #[_, _, c, t, f]) => return (← opsOf c) ++ (← opsOf t) ++ (← opsOf f)
  | (``Lambda.LExpr.abs, #[_, _, _, _, b]) => opsOf b
  | (``Lambda.LExpr.quant, #[_, _, _, _, _, tr, b]) => return (← opsOf tr) ++ (← opsOf b)
  | _ => throwError "hoare: unexpected expression form{indentExpr e}"

/-- The expressions a statement list evaluates, each with the statement it belongs to: the
right-hand sides of `set` and `init` and the deterministic guards of `if` and `while`, through
blocks, branches and loop bodies. -/
partial def evaluatedExprs (ss : Expr) : MetaM (List (String × Expr)) := do
  let mut acc := []
  for s in ← listElems ss do
    let s ← whnf s
    match s.getAppFnArgs with
    | (``Imperative.Stmt.cmd, #[_, _, c]) =>
      let c ← whnf c
      if let (``Imperative.CmdExt.cmd, #[_, c]) := c.getAppFnArgs then
        let c ← whnf c
        match c.getAppFnArgs with
        | (``Imperative.Cmd.set, #[_, x, e, _]) =>
          if let some e ← detExpr? e then acc := acc ++ [(s!"`{← identName x} := …`", e)]
        | (``Imperative.Cmd.init, #[_, x, _, e, _]) =>
          if let some e ← detExpr? e then acc := acc ++ [(s!"`var {← identName x} := …`", e)]
        | _ => pure ()
    | (``Imperative.Stmt.block, #[_, _, _, b, _]) => acc := acc ++ (← evaluatedExprs b)
    | (``Imperative.Stmt.ite, #[_, _, c, t, f, _]) =>
      if let some e ← detExpr? c then acc := acc ++ [("the guard of an `if`", e)]
      acc := acc ++ (← evaluatedExprs t) ++ (← evaluatedExprs f)
    | (``Imperative.Stmt.loop, #[_, _, g, _, _, b, _]) =>
      if let some e ← detExpr? g then acc := acc ++ [("the guard of a `while`", e)]
      acc := acc ++ (← evaluatedExprs b)
    | _ => pure ()
  return acc

/-- Fail if a statement evaluates an expression `Core.Factory` cannot run. `set` and `init` need
`Expression.eval` to return a value, and a deterministic guard needs it to return a boolean; an
operator without a concrete evaluation (`select`, `update`, the `Sequence` and `String`
operators, a function the program declares) leaves the expression unevaluated, so the statement
has no execution and every triple about it holds vacuously. The rules would prove such a
contract; this check refuses it instead. Works on a goal `TripleM π params Pre ss Post`. -/
elab "hoare_refuse_unevaluated" : tactic => withMainContext do
  let (ss, _) ← tripleParts
  for (what, e) in ← evaluatedExprs ss do
    for op in ← opsOf e do
      unless evaluatedOp op do
        throwError "hoare: {what} applies `{op}`, which `Core.Factory` does not evaluate: the statement has no execution, so its triple would hold vacuously"

/-! ## Loops

`while_wp_frame` takes the invariant as a predicate and the body's write set. `hoare_loop` reads
both off the loop statement in the goal: the invariant is `loopInv`, the program's `invariant`
clauses together with a typed binding for every integer variable the body writes and the loop
reads; the write set is what the body assigns, havocs or declares at any depth. A variable
outside the write set keeps its entry value through the loop, so the obligations after and
inside the loop know everything the entry knew about it. -/

/-- The free variables of an expression with their type annotations, after reduction. -/
partial def fvarsOf (e : Expr) : MetaM (List (Expr × Expr)) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Lambda.LExpr.const, _) | (``Lambda.LExpr.bvar, _) | (``Lambda.LExpr.op, _) => return []
  | (``Lambda.LExpr.fvar, #[_, _, x, ty]) =>
    let ty ← whnf ty
    match ty.getAppFnArgs with
    | (``Option.some, #[_, ty]) => return [(x, ty)]
    | _ => return []
  | (``Lambda.LExpr.app, #[_, _, f, a]) => return (← fvarsOf f) ++ (← fvarsOf a)
  | (``Lambda.LExpr.eq, #[_, _, a, b]) => return (← fvarsOf a) ++ (← fvarsOf b)
  | (``Lambda.LExpr.ite, #[_, _, c, t, f]) =>
    return (← fvarsOf c) ++ (← fvarsOf t) ++ (← fvarsOf f)
  | (``Lambda.LExpr.abs, #[_, _, _, _, b]) => fvarsOf b
  | (``Lambda.LExpr.quant, #[_, _, _, _, _, tr, b]) => return (← fvarsOf tr) ++ (← fvarsOf b)
  | _ => throwError "hoare: unexpected expression form{indentExpr e}"

/-- The variables a statement list mentions, with their annotations, and the names it
declares. -/
partial def stmtsVars (ss : Expr) : MetaM (List (Expr × Expr) × List String) := do
  let mut vars := []
  let mut decls := []
  for s in ← listElems ss do
    let s ← whnf s
    match s.getAppFnArgs with
    | (``Imperative.Stmt.cmd, #[_, _, c]) =>
      let c ← whnf c
      if let (``Imperative.CmdExt.cmd, #[_, c]) := c.getAppFnArgs then
        let c ← whnf c
        match c.getAppFnArgs with
        | (``Imperative.Cmd.set, #[_, _, e, _]) =>
          if let some e ← detExpr? e then vars := vars ++ (← fvarsOf e)
        | (``Imperative.Cmd.init, #[_, x, _, e, _]) =>
          decls := decls ++ [← identName x]
          if let some e ← detExpr? e then vars := vars ++ (← fvarsOf e)
        | (``Imperative.Cmd.assert, #[_, _, e, _]) | (``Imperative.Cmd.assume, #[_, _, e, _])
        | (``Imperative.Cmd.cover, #[_, _, e, _]) => vars := vars ++ (← fvarsOf e)
        | _ => pure ()
    | (``Imperative.Stmt.block, #[_, _, _, b, _]) =>
      let (v, d) ← stmtsVars b
      vars := vars ++ v
      decls := decls ++ d
    | (``Imperative.Stmt.ite, #[_, _, c, t, f, _]) =>
      if let some e ← detExpr? c then vars := vars ++ (← fvarsOf e)
      let (v₁, d₁) ← stmtsVars t
      let (v₂, d₂) ← stmtsVars f
      vars := vars ++ v₁ ++ v₂
      decls := decls ++ d₁ ++ d₂
    | (``Imperative.Stmt.loop, #[_, _, g, _, invs, b, _]) =>
      if let some e ← detExpr? g then vars := vars ++ (← fvarsOf e)
      for lc in ← listElems invs do
        let (_, e) ← pairElems lc
        vars := vars ++ (← fvarsOf e)
      let (v, d) ← stmtsVars b
      vars := vars ++ v
      decls := decls ++ d
    | _ => pure ()
  return (vars, decls)

/-- The names a statement list declares, `Block.definedVars ss true`, as a list literal. -/
def declaredNames (ss : Expr) : TacticM (List Expr) := do
  listElems (← mkAppM ``Imperative.Block.definedVars #[ss, mkConst ``true])

/-- A list of Core identifiers as a term. -/
def identListStx (xs : List Expr) : TacticM (TSyntax `term) := do
  let identTy ← Term.elabType (← `(Core.Expression.Ident))
  Term.exprToSyntax (← mkListLit identTy xs)

/-- The names a loop body may write: the variables it assigns or havocs, and the ones it
declares at any depth, each once. -/
def writtenNames (body : Expr) : TacticM (List Expr) := do
  let modified ← listElems (← mkAppM ``Imperative.Block.modifiedVars #[body])
  let declared ← listElems (← mkAppM ``Imperative.Block.definedVars #[body, mkConst ``false])
  let mut seen : List String := []
  let mut out : List Expr := []
  for x in modified ++ declared do
    let name ← identName x
    unless seen.contains name do
      seen := seen ++ [name]
      out := out ++ [x]
  return out

/-- The typed variables of a loop statement, as the list `loopInv` takes: the integer variables
among `written` that the loop mentions and does not declare, each once, in order of first
occurrence. A variable the body does not write needs no binding: the frame keeps its entry
value. -/
def loopGamma (loop : Expr) (written : List String) : TacticM Expr := do
  let (vars, decls) ← stmtsVars (← mkListLit (← inferType loop) [loop])
  let identTy ← Term.elabType (← `(Core.Expression.Ident))
  let monoTy := mkConst ``Lambda.LMonoTy
  let mut seen : List String := []
  let mut elems : List Expr := []
  for (x, ty) in vars do
    let name ← identName x
    if seen.contains name || decls.contains name || !written.contains name then continue
    unless ← isIntTy ty do continue
    seen := seen ++ [name]
    elems := elems ++ [mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) identTy monoTy x ty]
  mkListLit (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) identTy monoTy) elems

/-- Apply `while_wp_frame` to a goal `TripleM π params Pre [while …] Post`, with the invariant
`loopInv model Γ inv`, the declared names and the write set read off the statement. The body's
triple is left for the driver, under its entry store `σ₀`. -/
elab "hoare_loop" : tactic => withMainContext do
  let (ss, model) ← tripleParts
  let [s] ← listElems ss | throwError "hoare: not a single statement"
  let s ← whnf s
  let (``Imperative.Stmt.loop, #[_, _, g, _, invs, body, _]) := s.getAppFnArgs
    | throwError "hoare: not a loop"
  let nondet := (← whnf g).isAppOf ``Imperative.ExprOrNondet.nondet
  let D ← declaredNames body
  let M ← writtenNames body
  let Γ ← loopGamma s (← M.mapM fun x => (identName x : MetaM String))
  let I ← mkAppM ``Strata.Hoare.loopInv #[model, Γ, invs]
  let IStx ← Term.exprToSyntax I
  let DStx ← identListStx D
  let MStx ← identListStx M
  if nondet then
    evalTactic (← `(tactic| (
      apply Strata.Hoare.while_nondet_wp_frame _ _ $IStx $DStx $MStx
      case hD => rfl
      case hDM => decide)))
  else
    evalTactic (← `(tactic| (
      apply Strata.Hoare.while_wp_frame _ _ $IStx $DStx $MStx
      case hD => rfl
      case hDM => decide)))

/-- Apply the block rule to a goal `TripleM π params Pre [block …] Post`: `block_wp` when the
body declares nothing, `block_wp'` with the declared names otherwise. -/
elab "hoare_block" : tactic => withMainContext do
  let (ss, _) ← tripleParts
  let [s] ← listElems ss | throwError "hoare: not a single statement"
  let s ← whnf s
  let (``Imperative.Stmt.block, #[_, _, _, body, _]) := s.getAppFnArgs
    | throwError "hoare: not a block"
  match ← declaredNames body with
  | [] => evalTactic (← `(tactic| (
      apply Strata.Hoare.block_wp _ _
      case hwf => (apply Imperative.Logic.Hoare.postWF_of_definedVars_nil; rfl))))
  | ds =>
    let D ← identListStx ds
    evalTactic (← `(tactic| (
      apply Strata.Hoare.block_wp' _ _ $D
      case hD => rfl)))

/-- Apply the `if` rule to a goal `TripleM π params Pre [if …] Post`: `ite_wp` when neither
branch declares anything, `ite_wp'` with the declared names otherwise. -/
elab "hoare_ite" : tactic => withMainContext do
  let (ss, _) ← tripleParts
  let [s] ← listElems ss | throwError "hoare: not a single statement"
  let s ← whnf s
  let (``Imperative.Stmt.ite, #[_, _, c, tss, ess, _]) := s.getAppFnArgs
    | throwError "hoare: not an if"
  if (← whnf c).isAppOf ``Imperative.ExprOrNondet.nondet then
    let Dt ← identListStx (← declaredNames tss)
    let De ← identListStx (← declaredNames ess)
    evalTactic (← `(tactic| (
      apply Strata.Hoare.ite_nondet_wp' _ _ $Dt $De
      case hDt => rfl
      case hDe => rfl)))
    return
  match ← declaredNames tss, ← declaredNames ess with
  | [], [] => evalTactic (← `(tactic| (
      apply Strata.Hoare.ite_wp _ _
      case hwt => (apply Imperative.Logic.Hoare.postWF_of_definedVars_nil; rfl)
      case hwe => (apply Imperative.Logic.Hoare.postWF_of_definedVars_nil; rfl))))
  | dt, de =>
    let Dt ← identListStx dt
    let De ← identListStx de
    evalTactic (← `(tactic| (
      apply Strata.Hoare.ite_wp' _ _ $Dt $De
      case hDt => rfl
      case hDe => rfl)))

/-! ## The driver -/

/-- Fail with the statement at the head of a `TripleM` goal that no rule applied to. After the
driver has run to a fixpoint, such a goal is a statement outside the fragment (`call`, `exit`,
…): say so, instead of leaving a goal the user would read as a failed condition. -/
elab "hoare_check_supported" : tactic => do
  for g in ← getGoals do
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``Strata.Hoare.Model.TripleM || ty.isAppOf ``Core.Logic.Hoare.TripleWithModel then
        let args := ty.getAppArgs
        if args.size == 6 then
          let ss ← whnf args[4]!
          if ss.isAppOfArity ``List.cons 3 then
            throwError "hoare: no rule for the statement{indentExpr (ss.getArg! 1)}\n\
              Supported: var, :=, havoc, assert, assume, cover, if, if *, \{ }, while, while *."

/-- Apply the `wp`-form rules until only the entry implication and the loop obligations are
left. A block, a branch or a loop body that declares variables gets the projected form of its
rule, so no `PostWF` side condition is left behind. -/
syntax "hoare_wp" : tactic
macro_rules
  | `(tactic| hoare_wp) => `(tactic| repeat' first
      | apply Strata.Hoare.nil_wp
      | apply Strata.Hoare.set_wp
      | apply Strata.Hoare.havoc_wp
      | apply Strata.Hoare.init_wp
      | apply Strata.Hoare.init_nondet_wp
      | apply Strata.Hoare.assert_wp
      | apply Strata.Hoare.assume_wp
      | apply Strata.Hoare.cover_wp
      | hoare_ite
      | hoare_block
      | hoare_loop
      | apply Strata.Hoare.seq_cons
      | intro (σ₀ : Core.CoreStore)
      | (simp only [Imperative.Block.exitsCoveredByBlocks, Imperative.Stmt.exitsCoveredByBlocks,
          and_self]; done))

/-! ## Lifting -/

/-- Discharge a side condition of an evaluation lemma: a store fact in the context, read
through updates, declarations and the projection at a block's exit; a decidable inequality of
identifiers or integers; or the evaluation of a sub-expression. -/
syntax "hoare_disch" : tactic
macro_rules
  | `(tactic| hoare_disch) => `(tactic| first
      | assumption
      | rfl
      | decide
      | (simp (config := { index := false }) (disch := hoare_disch) only
          [Strata.Hoare.Eval.evalFully_fvar_const, Strata.Hoare.Eval.evalFully_intConst,
           Strata.Hoare.Eval.evalFully_boolConst,
           Strata.Hoare.Eval.evalFully_intGe, Strata.Hoare.Eval.evalFully_intLt,
           Strata.Hoare.Eval.evalFully_intLe, Strata.Hoare.Eval.evalFully_intGt,
           Strata.Hoare.Eval.evalFully_intAdd, Strata.Hoare.Eval.evalFully_intSub,
           Strata.Hoare.Eval.evalFully_intMul, Strata.Hoare.Eval.evalFully_intDiv,
           Strata.Hoare.Eval.evalFully_intMod,
           Strata.Hoare.Eval.evalFully_intNeg, Strata.Hoare.Eval.evalFully_boolNot,
           Strata.Hoare.Eval.evalFully_boolAnd, Strata.Hoare.Eval.evalFully_boolOr,
           Strata.Hoare.Eval.evalFully_boolImplies, Strata.Hoare.Eval.evalFully_boolEquiv,
           Strata.Hoare.Eval.evalFully_eq_int, Strata.Hoare.Eval.evalFully_eq_bool,
           Strata.Hoare.Eval.evalFully_ite_int, Strata.Hoare.Eval.evalFully_ite_bool,
           Strata.Hoare.Eval.UpdateState.at_self, Strata.Hoare.Eval.UpdateState.at_other_lit,
           Strata.Hoare.Eval.InitState.at_self, Strata.Hoare.Eval.InitState.at_other_lit,
           Strata.Hoare.Eval.dropVars_of_not_mem, Strata.Hoare.agreeExcept_read]
         first | done | assumption | rfl))

/-- Evaluate the run: every `Expression.eval` on a known store and every guard comparison. A
store slot after an update or a declaration is read by `hoare_disch`, where the evaluation of a
variable asks for it. -/
syntax "hoare_eval" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| hoare_eval $[$loc:location]?) => `(tactic|
      simp (config := { index := false }) (disch := hoare_disch) only
        [Strata.Hoare.Eval.eval_def,
         Strata.Hoare.Eval.evalFully_fvar_const, Strata.Hoare.Eval.evalFully_intConst,
         Strata.Hoare.Eval.evalFully_boolConst,
         Strata.Hoare.Eval.evalFully_intGe, Strata.Hoare.Eval.evalFully_intLt,
         Strata.Hoare.Eval.evalFully_intLe, Strata.Hoare.Eval.evalFully_intGt,
         Strata.Hoare.Eval.evalFully_intAdd, Strata.Hoare.Eval.evalFully_intSub,
         Strata.Hoare.Eval.evalFully_intMul, Strata.Hoare.Eval.evalFully_intDiv,
         Strata.Hoare.Eval.evalFully_intMod,
         Strata.Hoare.Eval.evalFully_intNeg, Strata.Hoare.Eval.evalFully_boolNot,
         Strata.Hoare.Eval.evalFully_boolAnd, Strata.Hoare.Eval.evalFully_boolOr,
         Strata.Hoare.Eval.evalFully_boolImplies, Strata.Hoare.Eval.evalFully_boolEquiv,
         Strata.Hoare.Eval.evalFully_eq_int, Strata.Hoare.Eval.evalFully_eq_bool,
         Strata.Hoare.Eval.evalFully_ite_int, Strata.Hoare.Eval.evalFully_ite_bool,
         Strata.Hoare.Eval.some_boolConst_eq_tt_iff, Strata.Hoare.Eval.some_boolConst_eq_ff_iff,
         Strata.Hoare.Eval.boolConst_eq_tt_iff, Strata.Hoare.Eval.boolConst_eq_ff_iff,
         Strata.Hoare.Eval.some_boolConst_eq_tt_iff', Strata.Hoare.Eval.some_boolConst_eq_ff_iff',
         Strata.Hoare.Eval.boolConst_eq_tt_iff', Strata.Hoare.Eval.boolConst_eq_ff_iff',
         Strata.Hoare.Eval.and_decide_eq, Strata.Hoare.Eval.or_decide_eq,
         Strata.Hoare.Eval.not_decide_eq,
         Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
         Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false',
         decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide, Bool.cond_decide,
         Classical.not_not, Strata.Hoare.Eval.not_or_eq_imp,
         Option.some.injEq] $[$loc:location]?)

/-- Substitute the store into a captured condition. -/
syntax "hoare_subst_clause" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| hoare_subst_clause $[$loc:location]?) => `(tactic|
      simp (config := { index := false }) (disch := hoare_disch) only
        [Strata.Hoare.capturedExpr_clause, Strata.Hoare.capturedExpr_condArg,
         Strata.Hoare.substFvars_const, Strata.Hoare.substFvars_op, Strata.Hoare.substFvars_bvar,
         Strata.Hoare.substFvars_fvar, Strata.Hoare.substFvars_app, Strata.Hoare.substFvars_eq,
         Strata.Hoare.substFvars_ite, Strata.Hoare.substFvars_abs,
         Strata.Hoare.substFvars_quant] $[$loc:location]?)

/-- Denote a closed condition, leaving a proposition over `Int` and `Bool`. A division or
remainder is read only when its divisor is a non-zero literal. -/
syntax "hoare_denote_clause" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| hoare_denote_clause $[$loc:location]?) => `(tactic|
      try simp (config := { index := false })
        (disch := first
          | (with_unfolding_all hasTypeA; done)
          | rfl
          | decide
          | (simp only [Strata.Hoare.Denote.denote_intConst']; decide)) only
        [Strata.Hoare.Denote.denote_int_rel _ _ _ _ (Core.intGe_opInterp _),
         Strata.Hoare.Denote.denote_int_rel _ _ _ _ (Strata.Hoare.Denote.intLt_opInterp _),
         Strata.Hoare.Denote.denote_int_rel _ _ _ _ (Strata.Hoare.Denote.intLe_opInterp _),
         Strata.Hoare.Denote.denote_int_rel _ _ _ _ (Strata.Hoare.Denote.intGt_opInterp _),
         Strata.Hoare.Denote.denote_int_op _ _ _ _ (Core.intAdd_opInterp _),
         Strata.Hoare.Denote.denote_int_op _ _ _ _ (Strata.Hoare.Denote.intSub_opInterp _),
         Strata.Hoare.Denote.denote_int_op _ _ _ _ (Core.intMul_opInterp _),
         Strata.Hoare.Denote.denote_int_op_guarded _ _ _ _ (Strata.Hoare.Denote.intDiv_opInterp _),
         Strata.Hoare.Denote.denote_int_op_guarded _ _ _ _ (Strata.Hoare.Denote.intMod_opInterp _),
         Strata.Hoare.Denote.denote_bool_op _ _ _ _ (Strata.Hoare.Denote.boolOr_opInterp _),
         Strata.Hoare.Denote.denote_bool_op _ _ _ _ (Strata.Hoare.Denote.boolAnd_opInterp _),
         Strata.Hoare.Denote.denote_bool_op _ _ _ _ (Strata.Hoare.Denote.boolImplies_opInterp _),
         Strata.Hoare.Denote.denote_bool_op _ _ _ _ (Strata.Hoare.Denote.boolEquiv_opInterp _),
         Strata.Hoare.Denote.denote_int_un _ _ _ _ (Strata.Hoare.Denote.intNeg_opInterp _),
         Strata.Hoare.Denote.denote_bool_un _ _ _ _ (Strata.Hoare.Denote.boolNot_opInterp _),
         Strata.Hoare.Denote.denote_eq_int_iff, Strata.Hoare.Denote.denote_eq_bool_iff,
         Strata.Hoare.Denote.denote_eq_int, Strata.Hoare.Denote.denote_eq_bool,
         Strata.Hoare.Denote.denote_ite_int, Strata.Hoare.Denote.denote_ite_bool,
         Strata.Hoare.Denote.denote_forall_int, Strata.Hoare.Denote.denote_exists_int,
         Strata.Hoare.Denote.denote_bvar_zero_int, Strata.Hoare.Denote.denote_bvar_succ_int,
         Strata.Hoare.Denote.denote_intConst', Strata.Hoare.Denote.denote_boolConst',
         Strata.Hoare.Eval.and_decide_eq, Strata.Hoare.Eval.or_decide_eq,
         Strata.Hoare.Eval.not_decide_eq,
         Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
         Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false',
         decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide, Bool.cond_decide,
         Classical.not_not, Strata.Hoare.Eval.not_or_eq_imp,
         true_or, or_true, true_and, and_true] $[$loc:location]?)

/-- Read one captured condition in a hypothesis: substitute, then denote. -/
syntax "hoare_lift_clause" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| hoare_lift_clause $[$loc:location]?) => `(tactic| (
      hoare_subst_clause $[$loc:location]?
      hoare_denote_clause $[$loc:location]?))

/-! ## Opening a verification condition -/

/-- Destructure the hypothesis `h`, the conjunction left by unfolding a typed-binding predicate
over the bindings `elems`, into one `Int` and one store fact per integer variable, named after
the variable; another variable keeps its value under its name. -/
def bindTyped (h : Ident) (elems : List Expr) : TacticM Unit := do
  let n := elems.length
  for e in elems, i in List.range n do
    let (x, ty) ← withMainContext (pairElems e)
    let name ← identName x
    let xId := mkIdent (Name.mkSimple name)
    let hId := mkIdent (Name.mkSimple ("h" ++ name))
    let last := i + 1 == n
    let cur ← if last then `($h:ident) else `(($h:ident).1)
    if ← isIntTy ty then
      evalTactic (← `(tactic| obtain ⟨$xId:ident, $hId:ident⟩ := Strata.Hoare.store_intConst_of $cur))
    else
      evalTactic (← `(tactic| obtain ⟨$xId:ident, $hId:ident, _⟩ := $cur))
    unless last do evalTactic (← `(tactic| replace $h:ident := ($h:ident).2))
  evalTactic (← `(tactic| try clear $h:ident))

/-- Introduce the integer inputs of the procedure as `Int`s named like the parameters, with the
store facts `h<name>`. Works on `hin : inputAsPredicate proc ρ`. -/
elab "hoare_inputs" : tactic => withMainContext do
  let hin := mkIdent `hin
  let proc ← argOf `hin 0
  let procStx ← Term.exprToSyntax proc
  let inputs ← Term.elabTerm (← `(($procStx).header.inputs.toList)) none
  let elems ← listElems inputs
  evalTactic (← `(tactic| simp only [Core.Logic.Hoare.Procedure.inputAsPredicate, ListMap.toList,
    Strata.Hoare.forall_mem_cons_pair, Strata.Hoare.forall_mem_nil_pair, and_true,
    Strata.Hoare.valueHasType_int_iff] at $hin:ident))
  bindTyped hin elems

/-- Introduce the typed variables of a loop invariant as `Int`s named like the variables, with
the store facts `h<name>`. Works on `hΓ : typedVars Γ ρ`; a store `ρ` projects with `dropVars`
is read through the projection, so that the facts are about the store itself. -/
elab "hoare_typed" : tactic => withMainContext do
  let hΓ := mkIdent `hΓ
  let elems ← listElems (← argOf `hΓ 0)
  evalTactic (← `(tactic| simp only [Strata.Hoare.typedVars,
    Strata.Hoare.forall_mem_cons_pair, Strata.Hoare.forall_mem_nil_pair, and_true,
    Strata.Hoare.valueHasType_int_iff] at $hΓ:ident))
  evalTactic (← `(tactic| try simp (disch := decide) only [Strata.Hoare.Eval.dropVars_of_not_mem]
    at $hΓ:ident))
  bindTyped hΓ elems

/-- Introduce the entry snapshot of each `inout` parameter `x`: the store fact `hold_x` that the
variable `old x`, which a contract's `old(x)` reads, holds the parameter's entry value. Works on
`hold : oldInoutAsPredicate proc ρ` with the store facts of the inputs in context and the store
named `σ₀`. -/
elab "hoare_old" : tactic => withMainContext do
  let hold := mkIdent `hold
  let σ₀ := mkIdent `σ₀
  let proc ← argOf `hold 0
  let procStx ← Term.exprToSyntax proc
  let inouts ← Term.elabTerm (← `(ListMap.keys ($procStx).header.getInoutParams)) none
  let elems ← listElems inouts
  for e in elems, i in List.range elems.length do
    let name ← identName e
    let hId := mkIdent (Name.mkSimple ("hold_" ++ name))
    let hx := mkIdent (Name.mkSimple ("h" ++ name))
    let mem ← memProof i
    let oldLit := Syntax.mkStrLit (Core.CoreIdent.oldStr ++ name)
    evalTactic (← `(tactic| have $hId:ident : $σ₀:ident (⟨$oldLit, ()⟩ : Core.Expression.Ident) = some _ :=
      ($hold:ident _ $mem).trans $hx:ident))
  evalTactic (← `(tactic| try clear $hold:ident))

/-- Lift each `requires` clause into a hypothesis `h<label>` over Lean values. Works on
`hreq : preAsPredicate model proc ρ`, with `ρ.factory` reducing to `Core.Factory` and the store
facts of the inputs in context. -/
elab "hoare_requires" : tactic => withMainContext do
  let hreq := mkIdent `hreq
  let proc ← argOf `hreq 1
  let procStx ← Term.exprToSyntax proc
  let pres ← Term.elabTerm (← `(($procStx).spec.preconditions.toList)) none
  let elems ← listElems pres
  for e in elems, i in List.range elems.length do
    let (label, _) ← withMainContext (pairElems e)
    let hId := mkIdent (Name.mkSimple ("h" ++ (← strLit label)))
    let mem ← memProof i
    evalTactic (← `(tactic| obtain ⟨_, $hId:ident⟩ :=
      Strata.Hoare.requires_denote $hreq:ident rfl $mem))
    evalTactic (← `(tactic| try simp only [Lambda.LExpr.intConst, Lambda.LExpr.boolConst] at $hId:ident))
    evalTactic (← `(tactic| hoare_lift_clause at $hId:ident))
  evalTactic (← `(tactic| try clear $hreq:ident))

/-- Lift each `invariant` clause into a hypothesis `h<label>` over Lean values. Works on
`hinvs : ∀ lc ∈ inv, ClauseHolds model (condArg ρ lc.1 lc.2 #[])`, with `ρ.factory` reducing to
`Core.Factory` and the store facts of the typed variables in context. -/
elab "hoare_invariants" : tactic => withMainContext do
  let hinvs := mkIdent `hinvs
  let some decl := (← getLCtx).findFromUserName? `hinvs
    | throwError "hoare: no hypothesis `hinvs`"
  let ty ← instantiateMVars decl.type
  let .forallE _ _ (.forallE _ memTy _ _) _ := ty
    | throwError "hoare: unexpected shape of `hinvs`{indentExpr ty}"
  let some inv ← memTy.getAppArgs.findM? (fun a => do pure ((← inferType a).isAppOf ``List))
    | throwError "hoare: unexpected shape of `hinvs`{indentExpr ty}"
  let elems ← listElems inv
  for e in elems, i in List.range elems.length do
    let (label, _) ← withMainContext (pairElems e)
    let label ← strLit label
    let hId := mkIdent (Name.mkSimple (if label.isEmpty then s!"hinv_{i + 1}" else "h" ++ label))
    let mem ← memProof i
    evalTactic (← `(tactic| obtain ⟨_, $hId:ident⟩ :=
      Strata.Hoare.clause_denote ($hinvs:ident _ $mem) rfl))
    evalTactic (← `(tactic| try simp only [Lambda.LExpr.intConst, Lambda.LExpr.boolConst] at $hId:ident))
    evalTactic (← `(tactic| hoare_lift_clause at $hId:ident))
  evalTactic (← `(tactic| try clear $hinvs:ident))

/-- Lift every `assume` the run passed: a hypothesis `∃ world, holds world (condArg ρ label e md)`
becomes `h<label>` over Lean values, read in the valuation the hypothesis provides. An `assume`
without a label is `hassume_1`, `hassume_2`, … in order. Works once the stores the conditions
capture are known, so after the run is evaluated. -/
elab "hoare_assume" : tactic => do
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut hs : List (FVarId × Option String) := []
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``Exists 2 do continue
      let some arg := ty.find? (fun t => t.isAppOf ``Strata.Hoare.condArg && t.getAppNumArgs == 4)
        | continue
      hs := hs ++ [(d.fvarId, firstStrLit? (arg.getArg! 1))]
    return hs
  let mut k := 0
  for (fv, label) in hs do
    let name ← match label with
      | some l =>
        if l.isEmpty then
          k := k + 1
          pure s!"hassume_{k}"
        else
          pure ("h" ++ l)
      | none =>
        k := k + 1
        pure s!"hassume_{k}"
    let hStx ← withMainContext (Term.exprToSyntax (mkFVar fv))
    let hId := mkIdent (Name.mkSimple name)
    let hw := mkIdent `hw
    let world := mkIdent `world
    evalTactic (← `(tactic| (
      obtain ⟨$world:ident, $hw:ident⟩ := $hStx
      try clear $hStx
      obtain ⟨_, $hId:ident⟩ := (Strata.Hoare.holds_iff _ $world:ident _ rfl).mp $hw:ident
      clear $hw:ident
      try simp only [Lambda.LExpr.intConst, Lambda.LExpr.boolConst] at $hId:ident
      hoare_lift_clause at $hId:ident
      try clear $world:ident)))

/-- Open the hypothesis `hpre` of a verification condition: the contract's precondition at the
entry, or a loop invariant together with the guard. The environment `ρ` is taken apart and its
factory, which both fix to `Core.Factory`, is substituted away, so that every evaluation in the
goal is at `Core.Factory` and no hypothesis about the factory is left for the lifting to
consume. -/
elab "hoare_open_pre" : tactic => withMainContext do
  let hpre := mkIdent `hpre
  evalTactic (← `(tactic| try simp only [Strata.Hoare.wpProj] at $hpre:ident))
  let some decl := (← getLCtx).findFromUserName? `hpre | throwError "hoare: no hypothesis `hpre`"
  let ty ← instantiateMVars decl.type
  let ρ := mkIdent `ρ
  let σ₀ := mkIdent `σ₀
  let f := mkIdent `f
  let hfail := mkIdent `hfail
  let hfac := mkIdent `hfac
  if ty.isAppOf ``Core.Logic.Hoare.Procedure.contractPre then
    let hreq := mkIdent `hreq
    let hold := mkIdent `hold
    let hin := mkIdent `hin
    evalTactic (← `(tactic| (
      obtain ⟨$hreq:ident, $hfac:ident, $hold:ident, $hin:ident⟩ := $hpre:ident
      rcases $ρ:ident with ⟨$σ₀:ident, $f:ident, $hfail:ident⟩
      try dsimp only at $hfac:ident
      subst $hfac:ident
      hoare_inputs
      hoare_old
      hoare_requires)))
  else if ty.isAppOf ``Strata.Hoare.loopInv then
    let hΓ := mkIdent `hΓ
    let hinvs := mkIdent `hinvs
    let hguard := mkIdent `hguard
    evalTactic (← `(tactic| (
      obtain ⟨$hfac:ident, $hΓ:ident, $hinvs:ident⟩ := $hpre:ident
      rcases $ρ:ident with ⟨$σ₀:ident, $f:ident, $hfail:ident⟩
      try dsimp only at $hfac:ident
      subst $hfac:ident
      intro $hguard:ident
      hoare_typed
      hoare_invariants)))
  else
    throwError "hoare: unexpected precondition{indentExpr ty}"

/-- Open a loop obligation, a goal `stepObligation …` or `exitObligation …` at the entry
environment: the environment the obligation quantifies over is taken apart, its factory
substituted away, its agreement with the entry store kept as `hagree`, the typed variables and
the invariants introduced as for an entry, and the body's precondition unfolded. -/
elab "hoare_open_loop" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let det := t.isAppOf ``Strata.Hoare.stepObligation || t.isAppOf ``Strata.Hoare.exitObligation
  let nondet := t.isAppOf ``Strata.Hoare.stepObligationN || t.isAppOf ``Strata.Hoare.exitObligationN
  unless det || nondet do
    throwError "hoare: not a loop obligation{indentExpr t}"
  let ρ := mkIdent `ρ
  let σ := mkIdent `σ
  let f := mkIdent `f
  let hfail := mkIdent `hfail
  let hagree := mkIdent `hagree
  let hpre := mkIdent `hpre
  let hfac := mkIdent `hfac
  let hΓ := mkIdent `hΓ
  let hinvs := mkIdent `hinvs
  let hguard := mkIdent `hguard
  evalTactic (← `(tactic| simp only [Strata.Hoare.stepObligation, Strata.Hoare.exitObligation,
    Strata.Hoare.stepObligationN, Strata.Hoare.exitObligationN, Strata.Hoare.wpProj]))
  if det then
    evalTactic (← `(tactic| intro $ρ:ident $hagree:ident $hpre:ident $hguard:ident))
  else
    evalTactic (← `(tactic| intro $ρ:ident $hagree:ident $hpre:ident))
  evalTactic (← `(tactic| (
    obtain ⟨$hfac:ident, $hΓ:ident, $hinvs:ident⟩ := $hpre:ident
    rcases $ρ:ident with ⟨$σ:ident, $f:ident, $hfail:ident⟩
    try dsimp only at $hfac:ident $hΓ:ident $hinvs:ident $hagree:ident
    try dsimp only at $hguard:ident
    subst $hfac:ident
    hoare_typed
    hoare_invariants
    try simp only [Strata.Hoare.wpSet, Strata.Hoare.wpInit, Strata.Hoare.wpIte,
      Strata.Hoare.wpAssert, Strata.Hoare.wpAssume, Strata.Hoare.wpHavoc,
      Strata.Hoare.wpInitNondet, Strata.Hoare.wpProj, Strata.Hoare.wpLoop,
      Strata.Hoare.wpLoopN])))

/-- Whether a proposition is the branch of an `if`: an implication from a guard evaluation,
written `Expression.eval` by the rule or `evalFully` once the rule's predicate is unfolded. -/
def isGuardBranch (e : Expr) : Bool :=
  e.isArrow && e.bindingDomain!.isAppOf ``Eq &&
    (let lhs := e.bindingDomain!.getAppArgs.getD 1 default
     lhs.isAppOf ``Imperative.PureExpr.eval || lhs.isAppOf ``Lambda.LExpr.evalFully)

/-- Split a conjunction that is one on the surface, leaving the named predicates folded. The two
branches of an `if` are tagged `then` and `else`, the obligations of a loop `step` and `exit`;
any other split keeps the goal's tag. -/
elab "hoare_split_and" : tactic => withMainContext do
  let g ← getMainGoal
  let tag ← g.getTag
  let t₀ := (← instantiateMVars (← getMainTarget)).consumeMData
  -- `if (*)`: both branches, named like those of an `if`
  let nondetIte := t₀.isAppOf ``Strata.Hoare.wpIteNondet
  if nondetIte then evalTactic (← `(tactic| simp only [Strata.Hoare.wpIteNondet]))
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let t := t.consumeMData
  unless t.isAppOf ``And do throwError "hoare: not a conjunction{indentExpr t}"
  let ite := nondetIte || isGuardBranch (t.getAppArgs.getD 0 default)
  splitAnd
  match ← getGoals with
  | g₁ :: g₂ :: _ =>
    if ite then
      g₁.setTag (tag ++ `then)
      g₂.setTag (tag ++ `else)
    for g in [g₁, g₂] do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOf ``Strata.Hoare.stepObligation || ty.isAppOf ``Strata.Hoare.stepObligationN then
        g.setTag (tag ++ `step)
      else if ty.isAppOf ``Strata.Hoare.exitObligation || ty.isAppOf ``Strata.Hoare.exitObligationN then
        g.setTag (tag ++ `exit)
  | _ => pure ()

/-! ## Naming and cleaning the goals -/

/-- Rename the goal after the path to it. -/
elab "hoare_tag_branch" : tactic => tagPath

/-- The label of the condition a goal checks: the label argument of the captured condition
(`clauseArg`, `condArg`, or the event argument written out), else the first string literal in
the goal. -/
def goalLabel? (ty : Expr) : Option String :=
  let arg? := ty.find? fun t =>
    (t.isAppOf ``Strata.Hoare.clauseArg && t.getAppNumArgs == 3) ||
    (t.isAppOf ``Strata.Hoare.condArg && t.getAppNumArgs == 4) ||
    (t.isAppOf ``Imperative.EventArg.mk && t.getAppNumArgs == 6)
  match arg? with
  | some t =>
    if t.isAppOf ``Imperative.EventArg.mk then firstStrLit? (t.getArg! 3)
    else firstStrLit? (t.getArg! 1)
  | none => firstStrLit? ty

/-- Name every goal after its path and the label of its condition; an unlabeled invariant is
`inv_1`, `inv_2`, … in the order written. -/
elab "hoare_tag_clauses" : tactic => do
  let gs ← getGoals
  let mut k := 0
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    let label ← match goalLabel? ty with
      | some "" => k := k + 1; pure (some s!"inv_{k}")
      | l => pure l
    setGoals [g]
    tagClause label
  setGoals gs

/-- Drop what the lifting has consumed: store facts, evaluations, state updates, typing of
arbitrary values and typing witnesses of conditions, trivial hypotheses, the environment's
failure flag, and the semantic objects nothing refers to any more. -/
elab "hoare_clear" : tactic => do
  let heads : List Name := [``Imperative.UpdateState, ``Imperative.InitState,
    ``Imperative.HasVal.valueOfTy, ``Imperative.HasVal.valueOfStoredTy,
    ``Core.Logic.Hoare.Procedure.preAsPredicate, ``Core.Logic.Hoare.Procedure.oldInoutAsPredicate,
    ``Core.Logic.Hoare.Procedure.inputAsPredicate, ``Strata.Hoare.typedVars,
    ``Strata.Hoare.loopInv, ``Strata.Hoare.ClauseHolds, ``Strata.Hoare.agreeExcept,
    ``Lambda.FreeVarVal, ``Lambda.TyVarVal,
    ``Imperative.SemanticStore, ``Core.CoreStore, ``Imperative.Env, ``Lambda.Interp,
    ``Core.Logic.InitEnvWFParams, ``Imperative.PureExpr.Expr, ``Core.Logic.DenoteValuation]
  let eqHeads : List Name := [``Imperative.Env.store, ``Lambda.LExpr.evalFully,
    ``Imperative.Env.factory]
  clearNoise fun d => do
    if d.userName == `hfail then return true
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Lambda.LExpr.HasTypeA then return true
    -- a store fact `σ x = some v` about a store variable
    if let some (_, lhs, _) := ty.eq? then
      if let .fvar f := lhs.getAppFn then
        let fty ← instantiateMVars (← f.getDecl).type
        if fty.isConstOf ``Core.CoreStore || fty.isAppOf ``Imperative.SemanticStore then
          return true
    noiseByHead heads eqHeads d

/-! ## The final goals

After the run is evaluated, a goal is one of three things: the contract's postcondition, a loop
invariant to re-establish, or one captured condition (an `assert`). Each ends in condition
goals, read by `hoare_clause_goal`. -/

/-- Read one named condition goal: substitute the store, type it, denote it. -/
syntax "hoare_clause_goal" : tactic
macro_rules
  | `(tactic| hoare_clause_goal) => `(tactic| (
      try refine Strata.Hoare.clause_intro (by first | assumption | rfl) ?_
      try intro (_ : _ = Core.Procedure.CheckAttr.Default)
      intro fv vt
      hoare_subst_clause
      refine ⟨by hasTypeA, ?_⟩
      hoare_denote_clause
      try hoare_clear))

/-- The contract's postcondition: one goal per non-free `ensures`. -/
syntax "hoare_post_contract" : tactic
macro_rules
  | `(tactic| hoare_post_contract) => `(tactic| (
      refine Strata.Hoare.contractPost_intro (by first | assumption | rfl) ?_
      simp only [ListMap.toList, List.forall_mem_cons, Strata.Hoare.forall_mem_cons_elem,
        Strata.Hoare.forall_mem_nil_elem, List.not_mem_nil, false_implies, implies_true,
        true_implies, and_true]
      repeat' constructor
      hoare_tag_clauses
      all_goals hoare_clause_goal))

/-- The typed variables of a loop invariant, from the store facts of the run: one binding per
variable, read through the updates by `hoare_disch`. A variable whose binding the run does not
determine is left as a goal. -/
syntax "hoare_post_typed" : tactic
macro_rules
  | `(tactic| hoare_post_typed) => `(tactic| (
      simp only [Strata.Hoare.typedVars, Strata.Hoare.forall_mem_cons_pair,
        Strata.Hoare.forall_mem_nil_pair, and_true, Strata.Hoare.valueHasType_int_iff]
      repeat' first
        | hoare_split_and
        | exact ⟨_, by hoare_disch, _, rfl⟩))

/-- The clauses of a loop invariant: one goal per `invariant`. -/
syntax "hoare_post_clauses" : tactic
macro_rules
  | `(tactic| hoare_post_clauses) => `(tactic| (
      simp only [Strata.Hoare.forall_mem_cons_elem, Strata.Hoare.forall_mem_nil_elem,
        List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      repeat' constructor
      hoare_tag_clauses
      all_goals hoare_clause_goal))

/-- A loop invariant to re-establish: the factory, the typed variables, the clauses. The two
goals `loopInv_intro` leaves are handled by position, the clauses first so that the typed goal is
the last one when its turn comes. -/
syntax "hoare_post_inv" : tactic
macro_rules
  | `(tactic| hoare_post_inv) => `(tactic| (
      refine Strata.Hoare.loopInv_intro (by first | assumption | rfl) ?_ ?_
      rotate_left 1
      focus hoare_post_clauses
      rotate_right 1
      focus hoare_post_typed))

/-- The frame of a loop body: the store it ends in agrees with the store it started from
outside the write set. Each update, declaration or projection of the run is on a name of the
write set, read backwards to the agreement the body started with; an inner loop's agreement
is on a smaller write set. -/
syntax "hoare_post_frame" : tactic
macro_rules
  | `(tactic| hoare_post_frame) => `(tactic| (
      repeat' first
        | assumption
        | exact Strata.Hoare.agreeExcept_refl _ _
        | (apply Strata.Hoare.agreeExcept_trans (Strata.Hoare.agreeExcept_dropVars ?hDM _)
           case hDM => decide)
        | (apply Strata.Hoare.agreeExcept_trans (Strata.Hoare.agreeExcept_update ?hup ?hy)
           case hup => assumption
           case hy => decide)
        | (apply Strata.Hoare.agreeExcept_trans (Strata.Hoare.agreeExcept_init ?hini ?hy)
           case hini => assumption
           case hy => decide)
        | (apply Strata.Hoare.agreeExcept_trans (Strata.Hoare.agreeExcept_mono ?hin ?hsub)
           case hin => assumption
           case hsub => decide)))

/-- Dispatch a final goal on its shape. -/
syntax "hoare_post" : tactic
macro_rules
  | `(tactic| hoare_post) => `(tactic| first
      | hoare_post_contract
      | hoare_post_inv
      | (hoare_post_frame; done)
      | (hoare_tag_clauses; hoare_clause_goal)
      | skip)

/-! ## The pipeline -/

/-- Open a `Procedure.contractTriple` goal, refuse a body the evaluator cannot run, and run
`hoare_wp` on it. -/
syntax "hoare_contract" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| hoare_contract) => `(tactic| (
      refine Strata.Hoare.contract_intro _ _ _ _ _ (by rfl) (by rfl) (by decide) (fun model => ?_)
      hoare_refuse_unevaluated
      apply Strata.Hoare.vc_entry
      hoare_wp
      hoare_check_supported))

/-- Introduce a verification condition, the entry implication or a loop obligation, and split it
into one goal per condition. -/
syntax "hoare_vcs" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| hoare_vcs) => `(tactic| (
      intro ρ hpre
      hoare_open_pre
      try simp only [Strata.Hoare.wpSet, Strata.Hoare.wpInit, Strata.Hoare.wpIte,
        Strata.Hoare.wpAssert, Strata.Hoare.wpAssume, Strata.Hoare.wpHavoc,
        Strata.Hoare.wpInitNondet, Strata.Hoare.wpProj, Strata.Hoare.wpLoop,
        Strata.Hoare.wpLoopN]
      repeat' first
        | (intro (σ' : Core.CoreStore) (v : Core.Expression.Expr)
            (hev : Core.Expression.eval _ _ _ = some _)
            (hup : Imperative.UpdateState Core.Expression _ _ _ _))
        | (intro (σ' : Core.CoreStore) (v : Core.Expression.Expr)
            (hev : Core.Expression.eval _ _ _ = some _)
            (hini : Imperative.InitState Core.Expression _ _ _ _))
        | (intro (σ' : Core.CoreStore) (v : Core.Expression.Expr)
            (hup : Imperative.UpdateState Core.Expression _ _ _ _)
            (hty : Imperative.HasVal.valueOfStoredTy _ _ _ _))
        | (intro (σ' : Core.CoreStore) (v : Core.Expression.Expr)
            (hini : Imperative.InitState Core.Expression _ _ _ _)
            (hty : Imperative.HasVal.valueOfTy _ _ _))
        | (intro (hguard : Core.Expression.eval _ _ _ = some _))
        | (intro (hassume : ∃ _, _))
        | hoare_open_loop
        | hoare_split_and))

/-- Evaluate the run's stores and read the conditions, leaving goals over Lean values. The
evaluation is repeated to a fixpoint: a value one statement assigns is a variable until it is
evaluated and substituted, and only then can the next statement's reading of it evaluate. -/
syntax "hoare_lift" : tactic
macro_rules
  | `(tactic| hoare_lift) => `(tactic| (
      hoare_tag_branch
      try subst_vars
      try simp only [Lambda.LExpr.intConst, Lambda.LExpr.boolConst] at *
      repeat (hoare_eval at *; try subst_vars)
      hoare_assume
      hoare_post))

end Strata.Hoare
