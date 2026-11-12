/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement

/-! # Deep embedding of Core: values, states, expressions

A deep embedding of Strata Core in the style of the `lean-vcgen-tutorial`: Core
programs stay ASTs (`Core.Statement`), and their meaning is a relation (`Exec`, in
`Deep/Exec.lean`). This file fixes the value model and gives the expression fragment its
meaning.

**Values are tagged, projections are total.** `Val` has an `int` and a `bool`
constructor. Every read goes through `Val.toInt` / `Val.toBool`, which are total, so an
operator never fails on a mistyped operand. Core programs are type checked before
verification, so a well-typed program never reaches the defaults. Equality is the one
operator whose meaning depends on a type: `==` compares integers as integers and
booleans as booleans, at the type the translator annotated its operands with. A
well-typed state therefore never has to be assumed: no verification condition mentions
a value's tag.

**Expressions outside the fragment are undefined.** `eval` returns `none` for any
expression it does not cover (maps, unknown operators, ...). Statements treat an undefined
expression as a failure (`Deep/Exec.lean`), so a program outside the fragment cannot be
verified, rather than verified vacuously.

**Clauses are propositions.** An `assert`, a `requires`, an `ensures` or an `invariant` may
quantify over integers and booleans, which no evaluator computes. `SatT`/`SatF` read a clause
as a Lean proposition: quantifiers become Lean quantifiers over the values of the bound type,
connectives become connectives, and an atom is true when it evaluates to `true`, with the bound
values in scope.
-/

@[expose] public section

namespace Strata.Deep

/-! ## Values and states -/

inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Val

/-- Read a value as an integer; a boolean reads as `0`. -/
def toInt : Val → Int
  | int i => i
  | bool _ => 0

/-- Read a value as a boolean; an integer reads as `false`. -/
def toBool : Val → Bool
  | bool b => b
  | int _ => false

/-- Stated as rewrite lemmas rather than by `rfl`, so that `simp` applies them through
congruence and re-synthesizes a `Decidable` instance whose proposition they change. -/
@[simp] theorem toInt_int (i : Int) : (int i).toInt = i := by simp [toInt]
@[simp] theorem toBool_bool (b : Bool) : (bool b).toBool = b := by simp [toBool]

/-- The type a value's tag says it has; a bound variable is typed by its value. -/
def ty : Val → Lambda.LMonoTy
  | int _ => .tcons "int" []
  | bool _ => .tcons "bool" []

end Val

/-- A state maps each variable name to its value. Every name has a value, so a state
never needs to be checked for definedness. -/
abbrev State := String → Val

def State.update (σ : State) (x : String) (v : Val) : State :=
  fun y => if y = x then v else σ y

/-! ## Expressions -/

abbrev Expr := Core.Expression.Expr

/-- Core's unary built-ins, by their factory names (`Strata/DL/Lambda/IntBoolFactory.lean`). -/
def unop : String → Val → Option Val
  | "Int.Neg", v => some (.int (- v.toInt))
  | "Bool.Not", v => some (.bool (! v.toBool))
  | _, _ => none

/-- Core's binary built-ins. `Int.Div` and `Int.Mod` are undefined on a zero divisor,
matching the factory, which only evaluates them for a nonzero divisor. -/
def binop : String → Val → Val → Option Val
  | "Int.Add", v, w => some (.int (v.toInt + w.toInt))
  | "Int.Sub", v, w => some (.int (v.toInt - w.toInt))
  | "Int.Mul", v, w => some (.int (v.toInt * w.toInt))
  | "Int.Div", v, w => if w.toInt = 0 then none else some (.int (v.toInt / w.toInt))
  | "Int.Mod", v, w => if w.toInt = 0 then none else some (.int (v.toInt % w.toInt))
  | "Int.Lt", v, w => some (.bool (decide (v.toInt < w.toInt)))
  | "Int.Le", v, w => some (.bool (decide (v.toInt ≤ w.toInt)))
  | "Int.Gt", v, w => some (.bool (decide (v.toInt > w.toInt)))
  | "Int.Ge", v, w => some (.bool (decide (v.toInt ≥ w.toInt)))
  | "Bool.And", v, w => some (.bool (v.toBool && w.toBool))
  | "Bool.Or", v, w => some (.bool (v.toBool || w.toBool))
  | "Bool.Implies", v, w => some (.bool (!v.toBool || w.toBool))
  | "Bool.Equiv", v, w => some (.bool (v.toBool == w.toBool))
  | _, _, _ => none

/-- The type of `e`, read off the annotations the Core translator leaves on variables
and operators (an operator's annotation is its arrow type), with `bs` the values of the
bound variables in scope, innermost first, whose tags give their types. -/
def typeOf (bs : List Val) : Expr → Option Lambda.LMonoTy
  | .const _ (.intConst _) => some (.tcons "int" [])
  | .const _ (.boolConst _) => some (.tcons "bool" [])
  | .fvar _ _ ty => ty
  | .bvar _ i => (bs[i]?).map Val.ty
  | .app _ (.app _ (.op _ _ (some (.tcons "arrow" [_, .tcons "arrow" [_, r]]))) _) _ => some r
  | .app _ (.op _ _ (some (.tcons "arrow" [_, r]))) _ => some r
  | .ite _ _ t _ => typeOf bs t
  | .eq _ _ _ => some (.tcons "bool" [])
  | _ => none

/-- Equality at a type: integers compare as integers, booleans as booleans. It is
undefined at any other type. -/
def eqAt : Option Lambda.LMonoTy → Val → Val → Option Val
  | some (.tcons "int" []), v, w => some (.bool (decide (v.toInt = w.toInt)))
  | some (.tcons "bool" []), v, w => some (.bool (decide (v.toBool = w.toBool)))
  | _, _, _ => none

/-- The value of a Core expression in `σ`, with `bs` the values of the bound variables in
scope, innermost first; `none` outside the fragment. Built-ins are applied curried,
`app (app (op o) a) b`, as the Core translator produces them. -/
def evalIn (σ : State) (bs : List Val) : Expr → Option Val
  | .const _ (.intConst i) => some (.int i)
  | .const _ (.boolConst b) => some (.bool b)
  | .fvar _ x _ => some (σ x.name)
  | .bvar _ i => bs[i]?
  | .app _ (.app _ (.op _ o _) a) b =>
    match evalIn σ bs a, evalIn σ bs b with
    | some va, some vb => binop o.name va vb
    | _, _ => none
  | .app _ (.op _ o _) a =>
    match evalIn σ bs a with
    | some va => unop o.name va
    | none => none
  | .ite _ c t e =>
    match evalIn σ bs c with
    | some vc => if vc.toBool then evalIn σ bs t else evalIn σ bs e
    | none => none
  | .eq _ a b =>
    match evalIn σ bs a, evalIn σ bs b with
    | some va, some vb => eqAt (typeOf bs a) va vb
    | _, _ => none
  | _ => none

/-- The value of a closed Core expression in `σ`, or `none` outside the fragment. -/
def eval (σ : State) (e : Expr) : Option Val := evalIn σ [] e

/-- The value of `e` read as a boolean, with bound values `bs`; `none` if `e` is undefined. -/
def evalBoolIn (σ : State) (bs : List Val) (e : Expr) : Option Bool :=
  (evalIn σ bs e).map Val.toBool

/-- The value of `e` read as a boolean; `none` if `e` is undefined. -/
def evalBool (σ : State) (e : Expr) : Option Bool := (eval σ e).map Val.toBool

/-- The value of `e` read as an integer; `none` if `e` is undefined. -/
def evalInt (σ : State) (e : Expr) : Option Int := (eval σ e).map Val.toInt

/-! ## Clauses

A clause may quantify; its meaning is a proposition. `SatT σ bs e` says `e` is true at `σ`
with the bound values `bs` in scope, `SatF` that it is false. A quantifier over `int` or
`bool` is the Lean quantifier over `Int` or `Bool`, the body read with the bound value pushed
on `bs`; a connective is the Lean connective (`==>` an implication, `<==>` an equivalence);
anything else is an atom, true or false according to its value. An atom outside the fragment
is neither true nor false. -/

mutual
/-- `e` is true at `σ`, with bound values `bs`. The shape is matched first and the operator
name second, so that `simp` can reduce the match on a concrete expression. -/
def SatT (σ : State) (bs : List Val) : Expr → Prop
  | .quant _ .all _ ty _ body =>
    if ty = some (.tcons "int" []) then ∀ i : Int, SatT σ (.int i :: bs) body
    else if ty = some (.tcons "bool" []) then ∀ b : Bool, SatT σ (.bool b :: bs) body
    else False
  | .quant _ .exist _ ty _ body =>
    if ty = some (.tcons "int" []) then ∃ i : Int, SatT σ (.int i :: bs) body
    else if ty = some (.tcons "bool" []) then ∃ b : Bool, SatT σ (.bool b :: bs) body
    else False
  | e@(.app _ (.app _ (.op _ o _) a) b) =>
    match o.name with
    | "Bool.And" => SatT σ bs a ∧ SatT σ bs b
    | "Bool.Or" => SatT σ bs a ∨ SatT σ bs b
    | "Bool.Implies" => SatT σ bs a → SatT σ bs b
    | "Bool.Equiv" => SatT σ bs a ↔ SatT σ bs b
    | _ => evalBoolIn σ bs e = some true
  | e@(.app _ (.op _ o _) a) =>
    match o.name with
    | "Bool.Not" => SatF σ bs a
    | _ => evalBoolIn σ bs e = some true
  | e => evalBoolIn σ bs e = some true

/-- `e` is false at `σ`, with bound values `bs`. -/
def SatF (σ : State) (bs : List Val) : Expr → Prop
  | .quant _ .all _ ty _ body =>
    if ty = some (.tcons "int" []) then ∃ i : Int, SatF σ (.int i :: bs) body
    else if ty = some (.tcons "bool" []) then ∃ b : Bool, SatF σ (.bool b :: bs) body
    else False
  | .quant _ .exist _ ty _ body =>
    if ty = some (.tcons "int" []) then ∀ i : Int, SatF σ (.int i :: bs) body
    else if ty = some (.tcons "bool" []) then ∀ b : Bool, SatF σ (.bool b :: bs) body
    else False
  | e@(.app _ (.app _ (.op _ o _) a) b) =>
    match o.name with
    | "Bool.And" => SatF σ bs a ∨ SatF σ bs b
    | "Bool.Or" => SatF σ bs a ∧ SatF σ bs b
    | "Bool.Implies" => SatT σ bs a ∧ SatF σ bs b
    | "Bool.Equiv" => ¬ (SatT σ bs a ↔ SatT σ bs b)
    | _ => evalBoolIn σ bs e = some false
  | e@(.app _ (.op _ o _) a) =>
    match o.name with
    | "Bool.Not" => SatT σ bs a
    | _ => evalBoolIn σ bs e = some false
  | e => evalBoolIn σ bs e = some false
end

/-- `e` is true at `σ`. This is what a program must establish: asserts, postconditions,
loop invariants. -/
def Holds (σ : State) (e : Expr) : Prop := SatT σ [] e

/-- `e` is not false at `σ`: it is true, or it is outside the fragment. This is what a
program may assume (`assume`, `requires`). Dropping an assumption that cannot be
evaluated over-approximates the runs, so it is sound, and it keeps such an assumption
from making a triple hold vacuously. -/
def MayHold (σ : State) (e : Expr) : Prop := ¬ SatF σ [] e

end Strata.Deep

end
