/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Verify

/-! # Reflection: a type-checked Core procedure as a Lean term

`shallow_reflect` obtains the Core program by *running* `Strata.Boole.typeCheck` at elaboration
time. That result is a value in the elaborator's memory, not a term the kernel can compute
with: the lowering is built from `partial` definitions, so `typeCheck p` never reduces. To
state and prove anything about the program, each procedure is turned back into a closed term
made of constructors and literals (`ToExpr`) and bound to a definition
`<name>_ast : Core.Procedure`, on which `rfl`, `simp` and `decide` work by structural
reduction.

Leaf types derive `ToExpr`. The types parametrised by `PureExpr` or `LExprParamsT` cannot be
derived (the parameter is a bundle of `Type`s, not a `Type`), so their instances are written
for the Core instantiation `Core.Expression`. -/

open Lean Meta
open Lambda Imperative

namespace Strata.Shallow.Reflect

/-! ## Leaves -/

deriving instance ToExpr for Lambda.QuantifierKind
deriving instance ToExpr for Lambda.LMonoTy
deriving instance ToExpr for Lambda.LTy
deriving instance ToExpr for Lambda.LConst
deriving instance ToExpr for Lambda.Identifier
deriving instance ToExpr for Imperative.CheckAttr
deriving instance ToExpr for Boundedness
deriving instance ToExpr for TypeConstructor
deriving instance ToExpr for Strata.SynthesizedOrigin
deriving instance ToExpr for Strata.Uri
deriving instance ToExpr for StrataDDM.SourceRange
deriving instance ToExpr for Strata.Provenance

/-- `ListMap` is a definition, not an abbreviation, so the `List` instance is not found
through it. -/
instance {α β : Type} [ToExpr α] [ToExpr β] : ToExpr (ListMap α β) :=
  inferInstanceAs (ToExpr (List (α × β)))

deriving instance ToExpr for Core.Procedure.Header

/-! ## The Core instantiation

The implicit parameters every constructor takes, as terms. -/

/-- `Core.Expression : PureExpr`. -/
def pureExprE : Expr := mkConst ``Core.Expression
/-- `Core.Command`, the command type of Core statements. -/
def cmdE : Expr := mkConst ``Core.Command
/-- `Core.CoreLParams.mono : LExprParamsT`, the parameters of Core's `LExpr`. -/
def lparamsE : Expr := mkApp (mkConst ``Lambda.LExprParams.mono) (mkConst ``Core.CoreLParams)

/-- Metadata on Core expressions is `Unit`. -/
def unitE (u : Unit) : Expr := toExpr u

/-- Core identifiers (`Lambda.Identifier Unit`). -/
def identE (x : Core.CoreIdent) : Expr := toExpr x

/-- Expressions. -/
def exprE : Core.Expression.Expr → Expr
  | .const m c => mkApp3 (mkConst ``LExpr.const) lparamsE (unitE m) (toExpr c)
  | .op m o ty => mkApp4 (mkConst ``LExpr.op) lparamsE (unitE m) (identE o) (toExpr ty)
  | .bvar m i => mkApp3 (mkConst ``LExpr.bvar) lparamsE (unitE m) (toExpr i)
  | .fvar m x ty => mkApp4 (mkConst ``LExpr.fvar) lparamsE (unitE m) (identE x) (toExpr ty)
  | .abs m n ty e => mkApp5 (mkConst ``LExpr.abs) lparamsE (unitE m) (toExpr n) (toExpr ty) (exprE e)
  | .quant m k n ty tr e =>
    mkApp7 (mkConst ``LExpr.quant) lparamsE (unitE m) (toExpr k) (toExpr n) (toExpr ty) (exprE tr)
      (exprE e)
  | .app m f a => mkApp4 (mkConst ``LExpr.app) lparamsE (unitE m) (exprE f) (exprE a)
  | .ite m c t e => mkApp5 (mkConst ``LExpr.ite) lparamsE (unitE m) (exprE c) (exprE t) (exprE e)
  | .eq m a b => mkApp4 (mkConst ``LExpr.eq) lparamsE (unitE m) (exprE a) (exprE b)

instance : ToExpr Core.Expression.Expr where
  toExpr := exprE
  toTypeExpr := mkApp (mkConst ``Lambda.LExpr) lparamsE

instance : ToExpr (ExprOrNondet Core.Expression) where
  toExpr
    | .det e => mkApp2 (mkConst ``ExprOrNondet.det) pureExprE (toExpr e)
    | .nondet => mkApp (mkConst ``ExprOrNondet.nondet) pureExprE
  toTypeExpr := mkApp (mkConst ``ExprOrNondet) pureExprE

instance : ToExpr (MetaDataElem.Field Core.Expression) where
  toExpr
    | .var v => mkApp2 (mkConst ``MetaDataElem.Field.var) pureExprE (identE v)
    | .label l => mkApp2 (mkConst ``MetaDataElem.Field.label) pureExprE (toExpr l)
  toTypeExpr := mkApp (mkConst ``MetaDataElem.Field) pureExprE

instance : ToExpr (MetaDataElem.Value Core.Expression) where
  toExpr
    | .expr e => mkApp2 (mkConst ``MetaDataElem.Value.expr) pureExprE (toExpr e)
    | .msg s => mkApp2 (mkConst ``MetaDataElem.Value.msg) pureExprE (toExpr s)
    | .switch b => mkApp2 (mkConst ``MetaDataElem.Value.switch) pureExprE (toExpr b)
    | .provenance p => mkApp2 (mkConst ``MetaDataElem.Value.provenance) pureExprE (toExpr p)
  toTypeExpr := mkApp (mkConst ``MetaDataElem.Value) pureExprE

instance : ToExpr (MetaDataElem Core.Expression) where
  toExpr e := mkApp3 (mkConst ``MetaDataElem.mk) pureExprE (toExpr e.fld) (toExpr e.value)
  toTypeExpr := mkApp (mkConst ``MetaDataElem) pureExprE

/-- Statement metadata. -/
def mdE (md : Imperative.MetaData Core.Expression) : Expr := toExpr md

instance : ToExpr (Cmd Core.Expression) where
  toExpr
    | .init x ty e md =>
      mkApp5 (mkConst ``Cmd.init) pureExprE (identE x) (toExpr ty) (toExpr e) (mdE md)
    | .set x e md => mkApp4 (mkConst ``Cmd.set) pureExprE (identE x) (toExpr e) (mdE md)
    | .assert l b md => mkApp4 (mkConst ``Cmd.assert) pureExprE (toExpr l) (toExpr b) (mdE md)
    | .assume l b md => mkApp4 (mkConst ``Cmd.assume) pureExprE (toExpr l) (toExpr b) (mdE md)
    | .cover l b md => mkApp4 (mkConst ``Cmd.cover) pureExprE (toExpr l) (toExpr b) (mdE md)
  toTypeExpr := mkApp (mkConst ``Cmd) pureExprE

instance : ToExpr (CallArg Core.Expression) where
  toExpr
    | .inArg e => mkApp2 (mkConst ``CallArg.inArg) pureExprE (toExpr e)
    | .inoutArg x => mkApp2 (mkConst ``CallArg.inoutArg) pureExprE (identE x)
    | .outArg x => mkApp2 (mkConst ``CallArg.outArg) pureExprE (identE x)
  toTypeExpr := mkApp (mkConst ``CallArg) pureExprE

instance : ToExpr Core.Command where
  toExpr
    | .cmd c => mkApp2 (mkConst ``CmdExt.cmd) pureExprE (toExpr c)
    | .call n args md => mkApp4 (mkConst ``CmdExt.call) pureExprE (toExpr n) (toExpr args) (mdE md)
  toTypeExpr := cmdE

mutual

/-- Statements. -/
partial def stmtE : Core.Statement → Expr
  | .cmd c => mkApp3 (mkConst ``Stmt.cmd) pureExprE cmdE (toExpr c)
  | .block l b md => mkApp5 (mkConst ``Stmt.block) pureExprE cmdE (toExpr l) (stmtsE b) (mdE md)
  | .ite c t e md =>
    mkApp6 (mkConst ``Stmt.ite) pureExprE cmdE (toExpr c) (stmtsE t) (stmtsE e) (mdE md)
  | .loop g m invs b md =>
    mkApp7 (mkConst ``Stmt.loop) pureExprE cmdE (toExpr g) (toExpr m) (toExpr invs) (stmtsE b)
      (mdE md)
  | .exit l md => mkApp4 (mkConst ``Stmt.exit) pureExprE cmdE (toExpr l) (mdE md)
  | .typeDecl tc md => mkApp4 (mkConst ``Stmt.typeDecl) pureExprE cmdE (toExpr tc) (mdE md)

/-- Statement lists, as `List Core.Statement` literals. -/
partial def stmtsE : List Core.Statement → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Core.Statement)
  | s :: ss => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Core.Statement) (stmtE s) (stmtsE ss)

end

instance : ToExpr Core.Statement where
  toExpr := stmtE
  toTypeExpr := mkConst ``Core.Statement

instance : ToExpr (Check Core.Expression) where
  toExpr c := mkApp4 (mkConst ``Check.mk) pureExprE (toExpr c.expr) (toExpr c.attr) (mdE c.md)
  toTypeExpr := mkApp (mkConst ``Check) pureExprE

instance : ToExpr (Spec Core.Expression) where
  toExpr s :=
    mkApp3 (mkConst ``Spec.mk) pureExprE (toExpr s.preconditions) (toExpr s.postconditions)
  toTypeExpr := mkApp (mkConst ``Spec) pureExprE

/-! ## Procedures -/

/-- A procedure body. Only structured bodies are supported; the lowering never produces a CFG. -/
def bodyE : Core.Procedure.Body → MetaM Expr
  | .structured ss => pure (mkApp3 (mkConst ``Body.structured) pureExprE cmdE (stmtsE ss))
  | .cfg _ => throwError "shallow_reflect: a procedure body given as a CFG cannot be reflected"

/-- The procedure `p` as a closed term of type `Core.Procedure`. -/
def procedureE (p : Core.Procedure) : MetaM Expr := do
  let body ← bodyE p.body
  mkAppOptM ``Imperative.Procedure.mk
    #[pureExprE, cmdE, mkConst ``Core.Procedure.Header, none, none,
      toExpr p.header, toExpr p.spec, body]

/-- Add `name : Core.Procedure := p` to the environment. -/
def addProcedureAst (name : Name) (p : Core.Procedure) : MetaM Unit := do
  let value ← procedureE p
  let _ ← mkAuxDefinition name (mkConst ``Core.Procedure) value
  enableRealizationsForConst name

end Strata.Shallow.Reflect
