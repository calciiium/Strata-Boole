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
expression it does not cover (quantifiers, maps, unknown operators, ...). Statements
treat an undefined expression as a failure (`Deep/Exec.lean`), so a program outside the
fragment cannot be verified, rather than verified vacuously.
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

@[simp] theorem toInt_int (i : Int) : (int i).toInt = i := rfl
@[simp] theorem toBool_bool (b : Bool) : (bool b).toBool = b := rfl

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
and operators (an operator's annotation is its arrow type). -/
def typeOf : Expr → Option Lambda.LMonoTy
  | .const _ (.intConst _) => some (.tcons "int" [])
  | .const _ (.boolConst _) => some (.tcons "bool" [])
  | .fvar _ _ ty => ty
  | .app _ (.app _ (.op _ _ (some (.tcons "arrow" [_, .tcons "arrow" [_, r]]))) _) _ => some r
  | .app _ (.op _ _ (some (.tcons "arrow" [_, r]))) _ => some r
  | .ite _ _ t _ => typeOf t
  | .eq _ _ _ => some (.tcons "bool" [])
  | _ => none

/-- Equality at a type: integers compare as integers, booleans as booleans. It is
undefined at any other type. -/
def eqAt : Option Lambda.LMonoTy → Val → Val → Option Val
  | some (.tcons "int" []), v, w => some (.bool (decide (v.toInt = w.toInt)))
  | some (.tcons "bool" []), v, w => some (.bool (decide (v.toBool = w.toBool)))
  | _, _, _ => none

/-- The value of a Core expression in `σ`, or `none` outside the fragment. Built-ins are
applied curried, `app (app (op o) a) b`, as the Core translator produces them. -/
def eval (σ : State) : Expr → Option Val
  | .const _ (.intConst i) => some (.int i)
  | .const _ (.boolConst b) => some (.bool b)
  | .fvar _ x _ => some (σ x.name)
  | .app _ (.app _ (.op _ o _) a) b =>
    match eval σ a, eval σ b with
    | some va, some vb => binop o.name va vb
    | _, _ => none
  | .app _ (.op _ o _) a =>
    match eval σ a with
    | some va => unop o.name va
    | none => none
  | .ite _ c t e =>
    match eval σ c with
    | some vc => if vc.toBool then eval σ t else eval σ e
    | none => none
  | .eq _ a b =>
    match eval σ a, eval σ b with
    | some va, some vb => eqAt (typeOf a) va vb
    | _, _ => none
  | _ => none

/-- The value of `e` read as a boolean; `none` if `e` is undefined. -/
def evalBool (σ : State) (e : Expr) : Option Bool := (eval σ e).map Val.toBool

/-- The value of `e` read as an integer; `none` if `e` is undefined. -/
def evalInt (σ : State) (e : Expr) : Option Int := (eval σ e).map Val.toInt

/-- `e` is true at `σ`. This is what a program must establish: asserts, postconditions,
loop invariants. -/
def Holds (σ : State) (e : Expr) : Prop := evalBool σ e = some true

/-- `e` is not false at `σ`: it holds, or it is outside the fragment. This is what a
program may assume (`assume`, `requires`). Dropping an assumption that cannot be
evaluated over-approximates the runs, so it is sound, and it keeps such an assumption
from making a triple hold vacuously. -/
def MayHold (σ : State) (e : Expr) : Prop := evalBool σ e ≠ some false

end Strata.Deep

end
