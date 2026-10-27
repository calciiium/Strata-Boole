/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.Verifier
import StrataBoole.Deep.Triple
import StrataBoole.Deep.Delab

/-! # Deep embedding of Core: Core programs as Lean terms

`#core_reflect prog` takes a program `prog` written in Core syntax
(`def prog := #strata program Core; … #end`). At elaboration time it runs Strata's Core
translator and type checker on it, and defines `<name> : Core.Procedure` in the current
namespace for each procedure `<name>`. The value of that definition is the translated AST, written
out as a term, so that `Procedure.Correct <name>` unfolds to concrete statements and
expressions for `core_vcgen` and `core_lift` to work on.

The definitions are not placed under `prog`. On Lean 4.31, resolving a name `prog.x`
while `prog`'s value is still being elaborated trips a `PANIC` in the reserved-name
check (`PartialFixpoint.isOptionFixpoint`).

The AST is the *type-checked* program, the one Core's verifier works on. Type checking
also rules out what the semantics takes for granted: operands of the right type (the
value projections of `Deep/Lang.lean` are then never read at a wrong type) and no
redeclared variables (so leaving a block need not restore the variables it declared).

Metadata (source locations) is replaced by `MetaData.empty`: the semantics never reads
it. Type declarations and CFG bodies are rejected, since the semantics has no meaning
for them either.

This file is not a `module`, so its elaborator needs no `meta` phase annotations. A
file that uses `#core_reflect` imports it as an ordinary file.
-/

namespace Strata.Deep.Reflect

open Lean Elab Command Meta

/-- Run Strata's Core translator and type checker, reporting their errors. -/
def translateCore (p : StrataDDM.Program) : Except String Core.Program :=
  let (prog, errs) := TransM.run Inhabited.default (translateProgram p)
  if errs.isEmpty then
    match Core.typeCheck { Core.VerifyOptions.default with verbose := .quiet } prog with
    | .ok prog => .ok prog
    | .error msg => .error s!"type checking failed: {msg}"
  else .error (String.intercalate "\n" errs.toList)

/-! ## Building terms -/

/-- The implicit arguments every AST constructor takes. -/
structure Ctx where
  /-- The `LExprParamsT` of `Core.Expression.Expr`. -/
  T : Lean.Expr
  /-- `Core.Expression`. -/
  P : Lean.Expr
  /-- `Core.Command`. -/
  C : Lean.Expr

def mkCtx : MetaM Ctx := do
  let P := mkConst ``Core.Expression
  let exprTy ← whnfR (mkApp (mkConst ``Imperative.PureExpr.Expr) P)
  let some T := exprTy.app1? ``Lambda.LExpr
    | throwError "#core_reflect: unexpected shape of Core.Expression.Expr: {exprTy}"
  return { T, P, C := mkConst ``Core.Command }

def mkList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)

def mkOption (ty : Lean.Expr) : Option Lean.Expr → Lean.Expr
  | none => mkApp (mkConst ``Option.none [0]) ty
  | some e => mkApp2 (mkConst ``Option.some [0]) ty e

def mkPair (α β a b : Lean.Expr) : Lean.Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) α β a b

def mkProd (α β : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Prod [0, 0]) α β

def unitE : Lean.Expr := mkConst ``Unit.unit
def stringTy : Lean.Expr := mkConst ``String
def monoTyTy : Lean.Expr := mkConst ``Lambda.LMonoTy
def identTy : Lean.Expr := mkApp (mkConst ``Lambda.Identifier) (mkConst ``Unit)

def identE (x : Lambda.Identifier Unit) : Lean.Expr :=
  mkApp3 (mkConst ``Lambda.Identifier.mk) (mkConst ``Unit) (toExpr x.name) unitE

partial def monoTyE : Lambda.LMonoTy → Lean.Expr
  | .ftvar n => mkApp (mkConst ``Lambda.LMonoTy.ftvar) (toExpr n)
  | .tcons n args =>
    mkApp2 (mkConst ``Lambda.LMonoTy.tcons) (toExpr n) (mkList monoTyTy (args.map monoTyE))
  | .bitvec n => mkApp (mkConst ``Lambda.LMonoTy.bitvec) (toExpr n)

def lTyE : Lambda.LTy → Lean.Expr
  | .forAll vs ty =>
    mkApp2 (mkConst ``Lambda.LTy.forAll) (mkList stringTy (vs.map toExpr)) (monoTyE ty)

def constE : Lambda.LConst → Lean.Expr
  | .intConst i => mkApp (mkConst ``Lambda.LConst.intConst) (toExpr i)
  | .strConst s => mkApp (mkConst ``Lambda.LConst.strConst) (toExpr s)
  | .realConst r => mkApp (mkConst ``Lambda.LConst.realConst) (toExpr r)
  | .bitvecConst n b => mkApp2 (mkConst ``Lambda.LConst.bitvecConst) (toExpr n) (toExpr b)
  | .boolConst b => mkApp (mkConst ``Lambda.LConst.boolConst) (toExpr b)

def quantE : Lambda.QuantifierKind → Lean.Expr
  | .all => mkConst ``Lambda.QuantifierKind.all
  | .exist => mkConst ``Lambda.QuantifierKind.exist

def optTyE (ty : Option Lambda.LMonoTy) : Lean.Expr := mkOption monoTyTy (ty.map monoTyE)

partial def exprE (c : Ctx) : Core.Expression.Expr → Lean.Expr
  | .const _ k => mkApp3 (mkConst ``Lambda.LExpr.const) c.T unitE (constE k)
  | .op _ o ty => mkApp4 (mkConst ``Lambda.LExpr.op) c.T unitE (identE o) (optTyE ty)
  | .bvar _ i => mkApp3 (mkConst ``Lambda.LExpr.bvar) c.T unitE (toExpr i)
  | .fvar _ x ty => mkApp4 (mkConst ``Lambda.LExpr.fvar) c.T unitE (identE x) (optTyE ty)
  | .abs _ n ty e =>
    mkApp5 (mkConst ``Lambda.LExpr.abs) c.T unitE (toExpr n) (optTyE ty) (exprE c e)
  | .quant _ k n ty tr e =>
    mkAppN (mkConst ``Lambda.LExpr.quant)
      #[c.T, unitE, quantE k, toExpr n, optTyE ty, exprE c tr, exprE c e]
  | .app _ f a => mkApp4 (mkConst ``Lambda.LExpr.app) c.T unitE (exprE c f) (exprE c a)
  | .ite _ x y z =>
    mkApp5 (mkConst ``Lambda.LExpr.ite) c.T unitE (exprE c x) (exprE c y) (exprE c z)
  | .eq _ a b => mkApp4 (mkConst ``Lambda.LExpr.eq) c.T unitE (exprE c a) (exprE c b)

def exprTy (c : Ctx) : Lean.Expr := mkApp (mkConst ``Imperative.PureExpr.Expr) c.P

def mdE (c : Ctx) : Lean.Expr := mkApp (mkConst ``Imperative.MetaData.empty) c.P

def eonE (c : Ctx) : Imperative.ExprOrNondet Core.Expression → Lean.Expr
  | .det e => mkApp2 (mkConst ``Imperative.ExprOrNondet.det) c.P (exprE c e)
  | .nondet => mkApp (mkConst ``Imperative.ExprOrNondet.nondet) c.P

def cmdE (c : Ctx) : Imperative.Cmd Core.Expression → Lean.Expr
  | .init x ty e _ =>
    mkApp5 (mkConst ``Imperative.Cmd.init) c.P (identE x) (lTyE ty) (eonE c e) (mdE c)
  | .set x e _ => mkApp4 (mkConst ``Imperative.Cmd.set) c.P (identE x) (eonE c e) (mdE c)
  | .assert l e _ =>
    mkApp4 (mkConst ``Imperative.Cmd.assert) c.P (toExpr l) (exprE c e) (mdE c)
  | .assume l e _ =>
    mkApp4 (mkConst ``Imperative.Cmd.assume) c.P (toExpr l) (exprE c e) (mdE c)
  | .cover l e _ =>
    mkApp4 (mkConst ``Imperative.Cmd.cover) c.P (toExpr l) (exprE c e) (mdE c)

def callArgE (c : Ctx) : Imperative.CallArg Core.Expression → Lean.Expr
  | .inArg e => mkApp2 (mkConst ``Imperative.CallArg.inArg) c.P (exprE c e)
  | .inoutArg x => mkApp2 (mkConst ``Imperative.CallArg.inoutArg) c.P (identE x)
  | .outArg x => mkApp2 (mkConst ``Imperative.CallArg.outArg) c.P (identE x)

def commandE (c : Ctx) : Core.Command → Lean.Expr
  | .cmd k => mkApp2 (mkConst ``Imperative.CmdExt.cmd) c.P (cmdE c k)
  | .call p args _ =>
    mkApp4 (mkConst ``Imperative.CmdExt.call) c.P (toExpr p)
      (mkList (mkApp (mkConst ``Imperative.CallArg) c.P) (args.map (callArgE c))) (mdE c)

mutual
partial def stmtE (c : Ctx) : Core.Statement → Except String Lean.Expr
  | .cmd k => pure <| mkApp3 (mkConst ``Imperative.Stmt.cmd) c.P c.C (commandE c k)
  | .block l b _ => do
    pure <| mkApp5 (mkConst ``Imperative.Stmt.block) c.P c.C (toExpr l) (← stmtsE c b) (mdE c)
  | .ite g t f _ => do
    pure <| mkAppN (mkConst ``Imperative.Stmt.ite)
      #[c.P, c.C, eonE c g, ← stmtsE c t, ← stmtsE c f, mdE c]
  | .loop g m invs b _ => do
    let invTy := mkProd stringTy (exprTy c)
    let invsE := mkList invTy (invs.map fun (l, e) => mkPair stringTy (exprTy c) (toExpr l) (exprE c e))
    pure <| mkAppN (mkConst ``Imperative.Stmt.loop)
      #[c.P, c.C, eonE c g, mkOption (exprTy c) (m.map (exprE c)), invsE, ← stmtsE c b, mdE c]
  | .exit l _ => pure <| mkApp4 (mkConst ``Imperative.Stmt.exit) c.P c.C (toExpr l) (mdE c)
  | .typeDecl _ _ => throw "type declarations are not supported"

partial def stmtsE (c : Ctx) (ss : List Core.Statement) : Except String Lean.Expr := do
  return mkList (mkApp2 (mkConst ``Imperative.Stmt) c.P c.C) (← ss.mapM (stmtE c))
end

def checkE (c : Ctx) (ch : Imperative.Check Core.Expression) : Lean.Expr :=
  let attr := match ch.attr with
    | .Free => mkConst ``Imperative.CheckAttr.Free
    | .Default => mkConst ``Imperative.CheckAttr.Default
  mkApp4 (mkConst ``Imperative.Check.mk) c.P (exprE c ch.expr) attr (mdE c)

def specE (c : Ctx) (s : Imperative.Spec Core.Expression) : Lean.Expr :=
  let checkTy := mkApp (mkConst ``Imperative.Check) c.P
  let clauses (cs : ListMap String (Imperative.Check Core.Expression)) :=
    mkList (mkProd stringTy checkTy)
      (cs.toList.map fun (l, ch) => mkPair stringTy checkTy (toExpr l) (checkE c ch))
  mkApp3 (mkConst ``Imperative.Spec.mk) c.P (clauses s.preconditions) (clauses s.postconditions)

def sigE (sig : @Lambda.LMonoTySignature Unit) : Lean.Expr :=
  mkList (mkProd identTy monoTyTy)
    (sig.toList.map fun (x, ty) => mkPair identTy monoTyTy (identE x) (monoTyE ty))

def headerE (h : Core.Procedure.Header) : Lean.Expr :=
  mkApp5 (mkConst ``Core.Procedure.Header.mk) (identE h.name)
    (mkList stringTy (h.typeArgs.map toExpr)) (sigE h.inputs) (sigE h.outputs)
    (mkList stringTy (h.lemmas.map toExpr))

def procedureE (c : Ctx) (p : Core.Procedure) : MetaM Lean.Expr := do
  let ss ← match p.body with
    | .structured ss => pure ss
    | .cfg _ => throwError "#core_reflect: procedure {p.header.name.name} has a CFG body"
  let body ← match stmtsE c ss with
    | .ok e => pure e
    | .error msg => throwError "#core_reflect: procedure {p.header.name.name}: {msg}"
  mkAppM ``Imperative.Procedure.mk
    #[headerE p.header, specE c p.spec, mkApp3 (mkConst ``Imperative.Body.structured) c.P c.C body]

/-! ## The command -/

/-- Translate `prog`. The call is elaborated from syntax, so that `#strata`'s
`SourcedProgram` is coerced to the `Program` the translator expects. -/
unsafe def evalTranslateUnsafe (prog : Name) : TermElabM (Except String Core.Program) := do
  let ty := mkApp2 (mkConst ``Except [0, 0]) stringTy (mkConst ``Core.Program)
  let e ← Term.elabTermEnsuringType (← `(translateCore $(mkIdent prog))) ty
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.evalExpr (Except String Core.Program) ty (← instantiateMVars e)

@[implemented_by evalTranslateUnsafe]
opaque evalTranslate (prog : Name) : TermElabM (Except String Core.Program)

/-- `#core_reflect prog` defines `<name> : Core.Procedure` in the current namespace for
each procedure `<name>` of the Core program `prog`, with the translated AST as its
value. -/
syntax (name := coreReflect) "#core_reflect " ident : command

@[command_elab coreReflect] def elabCoreReflect : CommandElab := fun stx => do
  let prog ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let pgm ← match ← liftTermElabM (evalTranslate prog) with
    | .ok pgm => pure pgm
    | .error msg => throwError "#core_reflect: {msg}"
  let ctx ← liftTermElabM mkCtx
  for d in pgm.decls do
    let .proc p _ := d | continue
    let value ← liftTermElabM (procedureE ctx p)
    let name := (← getCurrNamespace) ++ .mkSimple p.header.name.name
    liftTermElabM <| do
      let type := mkConst ``Core.Procedure
      check value
      unless ← isDefEq (← inferType value) type do
        throwError "#core_reflect: the term for {name} does not have type Core.Procedure"
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Core.Procedure, value,
      hints := .regular 0, safety := .safe }
    logInfo m!"defined {name} : Core.Procedure"

end Strata.Deep.Reflect
