/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import Strata.Languages.Core.Procedure
import StrataBoole.Deep.Lang

/-! # Deep embedding of Core: reading Core ASTs in goals

Delaborators that print the Core AST inside goals in Core's own notation:

* an expression `Lambda.LExpr …` as `⟪m >= x || m == y⟫`;
* a statement, or a list of statements, as `⟦m := x; assert [l]: m >= y⟧`;
* a procedure as its Core declaration, `⟦procedure max2(x : int, …) spec { … } { … }⟧`;
* `Holds σ e` as `σ ⊨ e`.

Built-in operators print infix (`+`, `<=`, `==`, `&&`, `==>`, …). Any other operator,
or a function, prints as a call `f(a, b)`. The type annotations the translator puts on
variables and operators are not shown.

The notation is for reading only: no elaborator turns `⟪…⟫` back into a term. A part
of the AST that is not a literal, such as a Lean variable standing for an expression,
prints as `⦃e⦄` inside the Core notation. `set_option pp.core false` turns all of this
off and shows the raw constructors.

This file is not a `module`, so its delaborators need no `meta` phase annotations.
-/

register_option pp.core : Bool := {
  defValue := true
  descr := "(pretty printer) display Core expressions, statements and procedures in Core notation"
}

namespace Strata.Deep.Delab

open Lean PrettyPrinter Delaborator SubExpr

/-! ## Display syntax -/

declare_syntax_cat core_expr (behavior := both)
declare_syntax_cat core_type
declare_syntax_cat core_label
declare_syntax_cat core_guard
declare_syntax_cat core_loop_spec (behavior := both)
declare_syntax_cat core_call_arg (behavior := both)
declare_syntax_cat core_stmt (behavior := both)
declare_syntax_cat core_block
declare_syntax_cat core_param (behavior := both)
declare_syntax_cat core_clause (behavior := both)
declare_syntax_cat core_proc (behavior := both)

syntax:max ident : core_expr
syntax:max num : core_expr
syntax:max str : core_expr
syntax:max "(" core_expr ")" : core_expr
syntax:max "⦃" term "⦄" : core_expr
syntax:max core_expr:max "(" core_expr,* ")" : core_expr
syntax:75 "!" core_expr:75 : core_expr
syntax:75 "-" core_expr:75 : core_expr
syntax:70 core_expr:70 " * " core_expr:71 : core_expr
syntax:70 core_expr:70 " / " core_expr:71 : core_expr
syntax:70 core_expr:70 " % " core_expr:71 : core_expr
syntax:65 core_expr:65 " + " core_expr:66 : core_expr
syntax:65 core_expr:65 " - " core_expr:66 : core_expr
syntax:50 core_expr:51 " == " core_expr:51 : core_expr
syntax:50 core_expr:51 " < " core_expr:51 : core_expr
syntax:50 core_expr:51 " <= " core_expr:51 : core_expr
syntax:50 core_expr:51 " > " core_expr:51 : core_expr
syntax:50 core_expr:51 " >= " core_expr:51 : core_expr
syntax:35 core_expr:35 " && " core_expr:36 : core_expr
syntax:30 core_expr:30 " || " core_expr:31 : core_expr
syntax:25 core_expr:26 " ==> " core_expr:25 : core_expr
syntax:20 core_expr:21 " <==> " core_expr:21 : core_expr
syntax:10 "if " core_expr " then " core_expr " else " core_expr:10 : core_expr
syntax:10 &"forall" ident " : " core_type " :: " core_expr:10 : core_expr
syntax:10 &"exists" ident " : " core_type " :: " core_expr:10 : core_expr
syntax:10 &"fun" ident " : " core_type " => " core_expr:10 : core_expr

syntax:max ident : core_type
syntax:max "(" core_type ")" : core_type
syntax:max "⦃" term "⦄" : core_type
syntax:60 ident (ppSpace core_type:max)+ : core_type
syntax:25 core_type:26 " -> " core_type:25 : core_type

syntax "[" ident "]" ":" ppHardSpace : core_label

syntax "(" core_expr ")" : core_guard
syntax "*" : core_guard

syntax ppAllowUngrouped &"decreases" ppHardSpace core_expr : core_loop_spec
syntax ppAllowUngrouped &"invariant" ppHardSpace (core_label)? core_expr : core_loop_spec

syntax core_expr : core_call_arg
syntax &"out" ppSpace ident : core_call_arg
syntax &"inout" ppSpace ident : core_call_arg

-- Layout: `ppRealGroup` is an all-or-nothing group, and `ppSpace` a line break that is
-- taken only when its group does not fit; `ppLine` is a hard line break. (`ppGroup`
-- also indents, which would shift every nested block.) `ppAllowUngrouped` keeps the
-- category formatter from indenting each statement once more.
syntax ppAllowUngrouped ppRealGroup(ident " := " core_expr) : core_stmt
syntax ppAllowUngrouped &"havoc" ppHardSpace ident : core_stmt
syntax ppAllowUngrouped ppRealGroup(&"var" ppHardSpace ident " : " core_type (" := " core_expr)?) :
  core_stmt
syntax ppAllowUngrouped ppRealGroup(&"assert" ppHardSpace (core_label)? core_expr) : core_stmt
syntax ppAllowUngrouped ppRealGroup(&"assume" ppHardSpace (core_label)? core_expr) : core_stmt
syntax ppAllowUngrouped ppRealGroup(&"cover" ppHardSpace (core_label)? core_expr) : core_stmt
syntax ppAllowUngrouped "if" ppHardSpace core_guard ppHardSpace core_block
  (ppHardSpace "else" ppHardSpace core_block)? : core_stmt
syntax ppAllowUngrouped ppRealGroup("while" ppHardSpace core_guard
  ppIndent((ppLine core_loop_spec)*) ppLine core_block) : core_stmt
syntax ppAllowUngrouped (ident ":" ppHardSpace)? core_block : core_stmt
syntax ppAllowUngrouped &"exit" ppHardSpace ident : core_stmt
syntax ppAllowUngrouped ppRealGroup(&"call" ppHardSpace ident "(" core_call_arg,* ")") : core_stmt
syntax ppAllowUngrouped "⦃" term "⦄" : core_stmt

syntax ppAllowUngrouped ppRealGroup("{" ppIndent(ppSpace sepBy(core_stmt, ";", ";" ppSpace))
  ppSpace "}") : core_block
syntax ppAllowUngrouped "⦃" term "⦄" : core_block

syntax ident " : " core_type : core_param
syntax &"out" ppHardSpace ident " : " core_type : core_param
syntax &"inout" ppHardSpace ident " : " core_type : core_param

syntax ppAllowUngrouped (&"free" ppHardSpace)? &"requires" ppHardSpace (core_label)? core_expr :
  core_clause
syntax ppAllowUngrouped (&"free" ppHardSpace)? &"ensures" ppHardSpace (core_label)? core_expr :
  core_clause

syntax ppAllowUngrouped &"procedure" ppHardSpace ident "(" core_param,* ")"
  ppIndent(ppLine &"spec" ppHardSpace "{" ppIndent((ppLine core_clause ";")*) ppLine "}"
    ppLine "{" ppIndent(ppLine sepBy(core_stmt, ";", ";" ppLine)) ppLine "}") : core_proc

/-- A Core expression, displayed. -/
syntax:max "⟪" core_expr "⟫" : term
/-- A list of Core statements, displayed. -/
syntax:max "⟦" sepBy(core_stmt, ";", "; ") "⟧" : term
/-- A Core procedure, displayed. -/
syntax:max "⟦" core_proc "⟧" : term

/-- `σ ⊨ e`: the Core formula `e` holds in `σ`. -/
notation:50 σ:51 " ⊨ " e:51 => Strata.Deep.Holds σ e

section
open Lean.PrettyPrinter.Parenthesizer

/-- Visit a node of a display category without letting the precedences inside it decide
the parentheses around it. The notation always brackets such a node (`⟪…⟫`, `⟦…⟧`), and
the delaborators below parenthesize inside it themselves. -/
def opaqueCategory (cat : Lean.Name) : CategoryParenthesizer := fun prec => do
  let st ← get
  parenthesizeCategoryCore cat prec
  modify fun st' => { st' with
    contPrec := st.contPrec, contCat := st.contCat, minPrec := st.minPrec,
    trailPrec := st.trailPrec, trailCat := st.trailCat, visitedToken := st.visitedToken }

@[category_parenthesizer core_expr] def core_expr.parenthesizer := opaqueCategory `core_expr
@[category_parenthesizer core_stmt] def core_stmt.parenthesizer := opaqueCategory `core_stmt
@[category_parenthesizer core_proc] def core_proc.parenthesizer := opaqueCategory `core_proc

end

/-! ## Reading literals out of terms -/

def getPPCore (o : Options) : Bool := o.get `pp.core true

def strLit? (e : Lean.Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- The name of an identifier literal `⟨s, ()⟩`. -/
def identName? (e : Lean.Expr) : Option String := do
  let e := e.consumeMData
  guard (e.isAppOfArity ``Lambda.Identifier.mk 3)
  strLit? (e.getArg! 1)

/-- A Core variable or label, as an identifier. -/
def nameIdent (s : String) : Ident := mkIdent (.mkSimple s)

/-- A Core operator name such as `Int.DivT`, as a dotted identifier. -/
def opIdent (s : String) : Ident := mkIdent s.toName

/-- Attach the current subterm to `stx`, so that hovering over it shows the AST. -/
def annot {k} (stx : TSyntax k) : DelabM (TSyntax k) := do
  let pos ← getPos
  let stx' := annotatePos pos ⟨stx.raw⟩
  addTermInfo pos stx' (← getExpr)
  return ⟨stx'.raw⟩

/-- The elements of the list literal at the current position, each displayed by `k`;
`none` if the list is not a literal. -/
partial def listLit? {α} (k : DelabM α) : DelabM (Option (Array α)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``List.nil 1 then
    return some #[]
  else if e.isAppOfArity ``List.cons 3 then
    let x ← withNaryArg 1 k
    let some xs ← withNaryArg 2 (listLit? k) | return none
    return some (#[x] ++ xs)
  else
    return none

/-! ## Types -/

partial def coreType : DelabM (TSyntax `core_type) := do
  let e := (← getExpr).consumeMData
  let embed : DelabM (TSyntax `core_type) := do `(core_type| ⦃$(← delab)⦄)
  if e.isAppOfArity ``Lambda.LMonoTy.tcons 2 then
    let some n := strLit? (e.getArg! 0) | embed
    let some args ← withNaryArg 1 (listLit? coreType) | embed
    if n == "arrow" ∧ args.size == 2 then
      -- `->` associates to the right, so only an arrow on the left needs parentheses.
      let isArrow (t : Lean.Expr) : Bool :=
        t.consumeMData.isAppOfArity ``Lambda.LMonoTy.tcons 2 ∧
          strLit? (t.consumeMData.getArg! 0) == some "arrow"
      let domE := ((e.getArg! 1).consumeMData.getArg! 1).consumeMData
      let dom ← if isArrow domE then `(core_type| ($(args[0]!))) else pure args[0]!
      annot (← `(core_type| $dom -> $(args[1]!)))
    else if args.isEmpty then
      annot (← `(core_type| $(nameIdent n):ident))
    else
      let args ← args.mapM fun a => `(core_type| ($a))
      annot (← `(core_type| $(nameIdent n):ident $args*))
  else if e.isAppOfArity ``Lambda.LMonoTy.ftvar 1 then
    let some n := strLit? (e.getArg! 0) | embed
    annot (← `(core_type| $(nameIdent n):ident))
  else if e.isAppOfArity ``Lambda.LMonoTy.bitvec 1 then
    let some n ← Meta.getNatValue? (e.getArg! 0) | embed
    annot (← `(core_type| $(nameIdent s!"bv{n}"):ident))
  else
    embed

/-! ## Expressions -/

/-- The precedence of an atom. -/
def atomPrec : Nat := 1024

/-- A displayed expression and the precedence it was printed at. -/
structure Shown where
  stx : TSyntax `core_expr
  prec : Nat

/-- Parenthesize `s` where an operand of precedence at least `p` is expected. -/
def Shown.at (s : Shown) (p : Nat) : DelabM (TSyntax `core_expr) :=
  if s.prec < p then `(core_expr| ($(s.stx))) else pure s.stx

/-- Precedences of the infix built-ins: the operator's, then its two operands'. -/
def infixPrec? : String → Option (Nat × Nat × Nat)
  | "Int.Mul" | "Int.Div" | "Int.Mod" => some (70, 70, 71)
  | "Int.Add" | "Int.Sub" => some (65, 65, 66)
  | "Int.Lt" | "Int.Le" | "Int.Gt" | "Int.Ge" => some (50, 51, 51)
  | "Bool.And" => some (35, 35, 36)
  | "Bool.Or" => some (30, 30, 31)
  | "Bool.Implies" => some (25, 26, 25)
  | "Bool.Equiv" => some (20, 21, 21)
  | _ => none

def infixStx (o : String) (a b : TSyntax `core_expr) : DelabM (TSyntax `core_expr) :=
  match o with
  | "Int.Mul" => `(core_expr| $a * $b)
  | "Int.Div" => `(core_expr| $a / $b)
  | "Int.Mod" => `(core_expr| $a % $b)
  | "Int.Add" => `(core_expr| $a + $b)
  | "Int.Sub" => `(core_expr| $a - $b)
  | "Int.Lt" => `(core_expr| $a < $b)
  | "Int.Le" => `(core_expr| $a <= $b)
  | "Int.Gt" => `(core_expr| $a > $b)
  | "Int.Ge" => `(core_expr| $a >= $b)
  | "Bool.And" => `(core_expr| $a && $b)
  | "Bool.Or" => `(core_expr| $a || $b)
  | "Bool.Implies" => `(core_expr| $a ==> $b)
  | _ => `(core_expr| $a <==> $b)

/-- The value of an integer literal, in any of the forms `toExpr` and the elaborator
produce. -/
def intLit? (e : Lean.Expr) : MetaM (Option Int) := do
  if let some i ← Meta.getIntValue? e then return some i
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 then
    return (← Meta.getNatValue? (e.getArg! 0)).map Int.ofNat
  if e.isAppOfArity ``Int.negSucc 1 then
    return (← Meta.getNatValue? (e.getArg! 0)).map Int.negSucc
  return none

/-- The Core expression at the current position. `bound` names the enclosing binders,
innermost first, for de Bruijn indices. -/
partial def coreExpr (bound : List String) : DelabM Shown := do
  let e := (← getExpr).consumeMData
  let atom (stx : TSyntax `core_expr) : DelabM Shown := do return ⟨← annot stx, atomPrec⟩
  let embed : DelabM Shown := do return ⟨← `(core_expr| ⦃$(← delab)⦄), atomPrec⟩
  let some c := e.getAppFn.constName? | embed
  match c, e.getAppNumArgs with
  | ``Lambda.LExpr.fvar, 4 =>
    let some x := identName? (e.getArg! 2) | embed
    if x.startsWith "old " then
      let arg ← `(core_expr| $(nameIdent (x.drop 4).toString):ident)
      atom (← `(core_expr| $(nameIdent "old"):ident($arg)))
    else atom (← `(core_expr| $(nameIdent x):ident))
  | ``Lambda.LExpr.bvar, 3 =>
    let some i ← Meta.getNatValue? (e.getArg! 2) | embed
    let some x := bound[i]? | embed
    atom (← `(core_expr| $(nameIdent x):ident))
  | ``Lambda.LExpr.op, 4 =>
    let some o := identName? (e.getArg! 2) | embed
    atom (← `(core_expr| $(opIdent o):ident))
  | ``Lambda.LExpr.const, 3 =>
    let k := (e.getArg! 2).consumeMData
    if k.isAppOfArity ``Lambda.LConst.intConst 1 then
      let some i ← intLit? (k.getArg! 0) | embed
      let n := Syntax.mkNumLit (toString i.natAbs)
      if i < 0 then return ⟨← annot (← `(core_expr| -$n:num)), 75⟩
      else atom (← `(core_expr| $n:num))
    else if k.isAppOfArity ``Lambda.LConst.boolConst 1 then
      match (k.getArg! 0).consumeMData with
      | .const ``Bool.true _ => atom (← `(core_expr| true))
      | .const ``Bool.false _ => atom (← `(core_expr| false))
      | _ => embed
    else if k.isAppOfArity ``Lambda.LConst.strConst 1 then
      let some s := strLit? (k.getArg! 0) | embed
      atom (← `(core_expr| $(Syntax.mkStrLit s):str))
    else embed
  | ``Lambda.LExpr.eq, 4 =>
    let a ← withNaryArg 2 (coreExpr bound)
    let b ← withNaryArg 3 (coreExpr bound)
    return ⟨← annot (← `(core_expr| $(← a.at 51) == $(← b.at 51))), 50⟩
  | ``Lambda.LExpr.ite, 5 =>
    let i ← withNaryArg 2 (coreExpr bound)
    let t ← withNaryArg 3 (coreExpr bound)
    let f ← withNaryArg 4 (coreExpr bound)
    return ⟨← annot (← `(core_expr| if $(i.stx) then $(t.stx) else $(← f.at 10))), 10⟩
  | ``Lambda.LExpr.abs, 5 =>
    let x := (strLit? (e.getArg! 2)).getD "x"
    let ty ← withNaryArg 3 optType
    let body ← withNaryArg 4 (coreExpr (x :: bound))
    return ⟨← annot (← `(core_expr| fun $(nameIdent x) : $ty => $(body.stx))), 10⟩
  | ``Lambda.LExpr.quant, 7 =>
    let x := (strLit? (e.getArg! 3)).getD "x"
    let ty ← withNaryArg 4 optType
    let body ← withNaryArg 6 (coreExpr (x :: bound))
    let all := (e.getArg! 2).consumeMData.isConstOf ``Lambda.QuantifierKind.all
    let stx ← if all then `(core_expr| forall $(nameIdent x) : $ty :: $(body.stx))
      else `(core_expr| exists $(nameIdent x) : $ty :: $(body.stx))
    return ⟨← annot stx, 10⟩
  | ``Lambda.LExpr.app, 4 =>
    let (o, head, args) ← spine bound
    match o, args with
    | some o, #[a, b] =>
      if let some (p, pa, pb) := infixPrec? o then
        return ⟨← annot (← infixStx o (← a.at pa) (← b.at pb)), p⟩
      call head args
    | some "Bool.Not", #[a] => return ⟨← annot (← `(core_expr| !$(← a.at 75))), 75⟩
    | some "Int.Neg", #[a] => return ⟨← annot (← `(core_expr| -$(← a.at 75))), 75⟩
    | _, _ => call head args
  | _, _ => embed
where
  /-- `app (… (app f a₁) …) aₙ`: the operator name if `f` is one, `f`, and the `aᵢ`. -/
  spine (bound : List String) : DelabM (Option String × Shown × Array Shown) := do
    let e := (← getExpr).consumeMData
    if e.isAppOfArity ``Lambda.LExpr.app 4 then
      let (o, head, args) ← withNaryArg 2 (spine bound)
      return (o, head, args.push (← withNaryArg 3 (coreExpr bound)))
    else
      let o := if e.isAppOfArity ``Lambda.LExpr.op 4 then identName? (e.getArg! 2) else none
      return (o, ← coreExpr bound, #[])
  call (head : Shown) (args : Array Shown) : DelabM Shown := do
    let args := args.map (·.stx)
    return ⟨← annot (← `(core_expr| $(← head.at atomPrec)($args,*))), atomPrec⟩
  /-- An optional type annotation; a missing one prints as `_`. -/
  optType : DelabM (TSyntax `core_type) := do
    let e := (← getExpr).consumeMData
    if e.isAppOfArity ``Option.some 2 then withNaryArg 1 coreType
    else `(core_type| $(mkIdent `_):ident)

/-! ## Statements -/

def label? (l : String) : DelabM (Option (TSyntax `core_label)) :=
  if l.isEmpty then pure none else some <$> `(core_label| [$(nameIdent l)]: )

def guardStx : DelabM (TSyntax `core_guard) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Imperative.ExprOrNondet.det 2 then
    let c ← withNaryArg 1 (coreExpr [])
    `(core_guard| ($(c.stx)))
  else `(core_guard| *)

mutual
partial def coreStmt : DelabM (TSyntax `core_stmt) := do
  let e := (← getExpr).consumeMData
  let embed : DelabM (TSyntax `core_stmt) := do `(core_stmt| ⦃$(← delab)⦄)
  if e.isAppOfArity ``Imperative.Stmt.cmd 3 then
    withNaryArg 2 coreCommand
  else if e.isAppOfArity ``Imperative.Stmt.block 5 then
    let b ← withNaryArg 3 coreBlock
    let l := (strLit? (e.getArg! 2)).getD ""
    if l.isEmpty then
      annot (← `(core_stmt| $b:core_block))
    else
      let lbl := nameIdent l
      annot (← `(core_stmt| $lbl:ident : $b:core_block))
  else if e.isAppOfArity ``Imperative.Stmt.ite 6 then
    let c ← withNaryArg 2 guardStx
    let t ← withNaryArg 3 coreBlock
    if (e.getArg! 4).consumeMData.isAppOfArity ``List.nil 1 then
      annot (← `(core_stmt| if $c $t))
    else
      let f ← withNaryArg 4 coreBlock
      annot (← `(core_stmt| if $c $t else $f))
  else if e.isAppOfArity ``Imperative.Stmt.loop 7 then
    let g ← withNaryArg 2 guardStx
    let m := (e.getArg! 3).consumeMData
    let measure ← if m.isAppOfArity ``Option.some 2 then
        withNaryArg 3 (withNaryArg 1 do
          let d ← coreExpr []
          some <$> `(core_loop_spec| decreases $(d.stx)))
      else pure none
    let some invs ← withNaryArg 4 (listLit? invariant) | embed
    let body ← withNaryArg 5 coreBlock
    let specs := measure.toArray ++ invs
    annot (← `(core_stmt| while $g $specs* $body:core_block))
  else if e.isAppOfArity ``Imperative.Stmt.exit 4 then
    let some l := strLit? (e.getArg! 2) | embed
    annot (← `(core_stmt| exit $(nameIdent l)))
  else embed
where
  invariant : DelabM (TSyntax `core_loop_spec) := do
    let e := (← getExpr).consumeMData
    if e.isAppOfArity ``Prod.mk 4 then
      let l ← label? ((strLit? (e.getArg! 2)).getD "")
      let i := (← withNaryArg 3 (coreExpr [])).stx
      `(core_loop_spec| invariant $[$l]? $i:core_expr)
    else
      let t ← delab
      `(core_loop_spec| invariant ⦃$t⦄)

partial def coreCommand : DelabM (TSyntax `core_stmt) := do
  let e := (← getExpr).consumeMData
  let embed : DelabM (TSyntax `core_stmt) := do `(core_stmt| ⦃$(← delab)⦄)
  if e.isAppOfArity ``Imperative.CmdExt.cmd 2 then
    withNaryArg 1 coreCmd
  else if e.isAppOfArity ``Imperative.CmdExt.call 4 then
    let some p := strLit? (e.getArg! 1) | embed
    let some args ← withNaryArg 2 (listLit? callArg) | embed
    annot (← `(core_stmt| call $(nameIdent p)($args,*)))
  else embed
where
  callArg : DelabM (TSyntax `core_call_arg) := do
    let e := (← getExpr).consumeMData
    if e.isAppOfArity ``Imperative.CallArg.inArg 2 then
      let a ← withNaryArg 1 (coreExpr [])
      `(core_call_arg| $(a.stx):core_expr)
    else if let some x := (if e.getAppNumArgs == 2 then identName? (e.getArg! 1) else none) then
      if e.isAppOf ``Imperative.CallArg.outArg then `(core_call_arg| out $(nameIdent x))
      else `(core_call_arg| inout $(nameIdent x))
    else `(core_call_arg| ⦃$(← delab)⦄)

partial def coreCmd : DelabM (TSyntax `core_stmt) := do
  let e := (← getExpr).consumeMData
  let embed : DelabM (TSyntax `core_stmt) := do `(core_stmt| ⦃$(← delab)⦄)
  let det? (i : Nat) : DelabM (Option (TSyntax `core_expr)) := do
    let d := (e.getArg! i).consumeMData
    if d.isAppOfArity ``Imperative.ExprOrNondet.det 2 then
      some <$> withNaryArg i (withNaryArg 1 do return (← coreExpr []).stx)
    else pure none
  if e.isAppOfArity ``Imperative.Cmd.set 4 then
    let some x := identName? (e.getArg! 1) | embed
    match ← det? 2 with
    | some v => annot (← `(core_stmt| $(nameIdent x):ident := $v))
    | none => annot (← `(core_stmt| havoc $(nameIdent x)))
  else if e.isAppOfArity ``Imperative.Cmd.init 5 then
    let some x := identName? (e.getArg! 1) | embed
    let ty ← withNaryArg 2 do
      let t := (← getExpr).consumeMData
      if t.isAppOfArity ``Lambda.LTy.forAll 2 then withNaryArg 1 coreType
      else `(core_type| ⦃$(← delab)⦄)
    let v ← det? 3
    annot (← `(core_stmt| var $(nameIdent x) : $ty $[:= $v]?))
  else if e.getAppNumArgs == 4 ∧ (e.isAppOf ``Imperative.Cmd.assert ∨
      e.isAppOf ``Imperative.Cmd.assume ∨ e.isAppOf ``Imperative.Cmd.cover) then
    let l ← label? ((strLit? (e.getArg! 1)).getD "")
    let b ← withNaryArg 2 (coreExpr [])
    if e.isAppOf ``Imperative.Cmd.assert then annot (← `(core_stmt| assert $[$l]? $(b.stx):core_expr))
    else if e.isAppOf ``Imperative.Cmd.assume then annot (← `(core_stmt| assume $[$l]? $(b.stx):core_expr))
    else annot (← `(core_stmt| cover $[$l]? $(b.stx):core_expr))
  else embed

partial def coreBlock : DelabM (TSyntax `core_block) := do
  match ← listLit? coreStmt with
  | some ss => `(core_block| { $ss;* })
  | none => `(core_block| ⦃$(← delab)⦄)
end

/-! ## Procedures -/

/-- A parameter `(x, ty)` of a signature. -/
def param : DelabM (Option (String × TSyntax `core_type)) := do
  let e := (← getExpr).consumeMData
  unless e.isAppOfArity ``Prod.mk 4 do return none
  let some x := identName? (e.getArg! 2) | return none
  return some (x, ← withNaryArg 3 coreType)

/-- A specification clause `(label, check)`, as a `requires` or `ensures` clause. -/
def clause (ensures : Bool) : DelabM (Option (TSyntax `core_clause)) := do
  let e := (← getExpr).consumeMData
  unless e.isAppOfArity ``Prod.mk 4 do return none
  let chk := (e.getArg! 3).consumeMData
  unless chk.isAppOfArity ``Imperative.Check.mk 4 do return none
  let l ← label? ((strLit? (e.getArg! 2)).getD "")
  let b ← withNaryArg 3 (withNaryArg 1 (coreExpr []))
  let free := (chk.getArg! 2).consumeMData.isConstOf ``Imperative.CheckAttr.Free
  match ensures, free with
  | true, true => some <$> `(core_clause| free ensures $[$l]? $(b.stx):core_expr)
  | true, false => some <$> `(core_clause| ensures $[$l]? $(b.stx):core_expr)
  | false, true => some <$> `(core_clause| free requires $[$l]? $(b.stx):core_expr)
  | false, false => some <$> `(core_clause| requires $[$l]? $(b.stx):core_expr)

def coreProc : DelabM (TSyntax `core_proc) := do
  let e := (← getExpr).consumeMData
  guard (e.isAppOfArity ``Imperative.Procedure.mk 8)
  let hdr := (e.getArg! 5).consumeMData
  guard (hdr.isAppOfArity ``Core.Procedure.Header.mk 5)
  let some name := identName? (hdr.getArg! 0) | failure
  let some ins ← withNaryArg 5 (withNaryArg 2 (listLit? param)) | failure
  let some outs ← withNaryArg 5 (withNaryArg 3 (listLit? param)) | failure
  let some ins := ins.mapM id | failure
  let some outs := outs.mapM id | failure
  let outNames := outs.map (·.1)
  let inNames := ins.map (·.1)
  let mut params := #[]
  for (x, ty) in ins do
    params := params.push <| ← if outNames.contains x then `(core_param| inout $(nameIdent x) : $ty)
      else `(core_param| $(nameIdent x):ident : $ty)
  for (x, ty) in outs do
    unless inNames.contains x do params := params.push (← `(core_param| out $(nameIdent x) : $ty))
  let spec := (e.getArg! 6).consumeMData
  guard (spec.isAppOfArity ``Imperative.Spec.mk 3)
  let some pres ← withNaryArg 6 (withNaryArg 1 (listLit? (clause false))) | failure
  let some posts ← withNaryArg 6 (withNaryArg 2 (listLit? (clause true))) | failure
  let some clauses := (pres ++ posts).mapM id | failure
  let body := (e.getArg! 7).consumeMData
  guard (body.isAppOfArity ``Imperative.Body.structured 3)
  let some ss ← withNaryArg 7 (withNaryArg 2 (listLit? coreStmt)) | failure
  `(core_proc| procedure $(nameIdent name)($params,*) spec { $[$clauses;]* } { $ss;* })

/-! ## Delaborators -/

@[delab app.Lambda.LExpr.app, delab app.Lambda.LExpr.fvar, delab app.Lambda.LExpr.bvar,
  delab app.Lambda.LExpr.op, delab app.Lambda.LExpr.const, delab app.Lambda.LExpr.eq,
  delab app.Lambda.LExpr.ite, delab app.Lambda.LExpr.abs, delab app.Lambda.LExpr.quant]
def delabExpr : Delab := whenPPOption getPPCore do
  let e ← getExpr
  let arity := match e.getAppFn.constName? with
    | some ``Lambda.LExpr.app | some ``Lambda.LExpr.fvar | some ``Lambda.LExpr.op
    | some ``Lambda.LExpr.eq => 4
    | some ``Lambda.LExpr.ite | some ``Lambda.LExpr.abs => 5
    | some ``Lambda.LExpr.quant => 7
    | _ => 3
  guard (e.getAppNumArgs == arity)
  `(⟪$((← coreExpr []).stx)⟫)

@[delab app.Imperative.Stmt.cmd, delab app.Imperative.Stmt.block, delab app.Imperative.Stmt.ite,
  delab app.Imperative.Stmt.loop, delab app.Imperative.Stmt.exit]
def delabStmt : Delab := whenPPOption getPPCore do
  let e ← getExpr
  guard (e.getAppNumArgs ≥ 3)
  let s ← coreStmt
  `(⟦$s:core_stmt⟧)

/-- A list literal of statements prints as one block. -/
@[delab app.List.cons]
def delabStmts : Delab := whenPPOption getPPCore do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let elem ← Meta.whnfR (e.getArg! 0)
  guard (elem.isAppOf ``Imperative.Stmt)
  let some ss ← listLit? coreStmt | failure
  `(⟦$ss;*⟧)

@[delab app.Imperative.Procedure.mk]
def delabProc : Delab := whenPPOption getPPCore do
  let p ← coreProc
  `(⟦$p:core_proc⟧)

end Strata.Deep.Delab
