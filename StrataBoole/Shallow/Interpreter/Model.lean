/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprDenote
public import StrataBoole.Shallow.Interpreter.Sort
import all Strata.DL.Lambda.Denote.LExprDenote

/-! # A concrete model of Core's built-in types and operators

`LExpr.denote` (`Strata/DL/Lambda/Denote/LExprDenote.lean`) gives Core expressions a
meaning in Lean, but it is parametric in two things Strata does not fix:

* `tcInterp : TyConstrInterp` — a Lean type for every type constructor that `SortDenote`
  does not already map (`SortDenote` fixes `bool`, `int`, `real`, `string`, `bitvec`, `arrow`);
* `opInterp : OpInterp tcInterp` — a Lean value for every operator, by name and sort.

The model is partial: it covers the four non-built-in type constructors Core uses and the
operators of the `int`/`bool`/`Map`/`Sequence` fragment. Every other operator is interpreted
by `default`; an operator without a `body` or `concreteEval` imposes no consistency
obligation, so these can be refined later without touching any proof. The consistency proofs
relating the model to Strata's `concreteEval` functions (`InterpConsistentEval`) are not part
of this file.

Conventions: `Int.Div`/`Int.Mod` are Lean's `/`/`%` (`Int.ediv`/`Int.emod`, the SMT-LIB
convention, as Lean's own docstring says), `DivT`/`ModT` are `Int.tdiv`/`Int.tmod`, the
`Safe*` operators denote the same functions as their unchecked versions (their preconditions
are obligations, not part of the value). Comparisons return `Bool`.
-/

@[expose] public section

namespace Strata.Shallow.Model

open Lambda

/-! ## Sorts -/

/-- A Lean type for every sort. Agrees with `SortDenote` on the built-ins and adds `Map`,
`Sequence`, `Set` and `regex`; unknown constructors get `Unit`. -/
def coreSortDenote : LSort → Type
  | .tcons "bool" []          => Bool
  | .tcons "int" []           => Int
  | .tcons "real" []          => Rat
  | .tcons "string" []        => String
  | .bitvec n                 => BitVec n
  | .tcons "arrow" [a, b]     => coreSortDenote a → coreSortDenote b
  | .tcons "Map" [k, v]       => coreSortDenote k → coreSortDenote v
  | .tcons "Sequence" [t]     => List (coreSortDenote t)
  | .tcons "Set" [t]          => coreSortDenote t → Prop
  | .tcons "regex" []         => String → Prop
  | .tcons _ _                => Unit


/-- Every sort is inhabited. The catch-all branch of `coreSortDenote` does not reduce on a
variable sort, so this goes through `split`, as Strata's `SortDenote.inhabited` does. -/
@[reducible] def coreSortDenote.inhabited : (s : LSort) → Inhabited (coreSortDenote s) :=
  sortRec (P := fun s => Inhabited (coreSortDenote s))
    (fun name args ih => by
      unfold coreSortDenote
      split
      all_goals first
        | exact ⟨false⟩
        | exact ⟨(0 : Int)⟩
        | exact ⟨(0 : Rat)⟩
        | exact ⟨""⟩
        | exact ⟨(0 : BitVec _)⟩
        | exact ⟨[]⟩
        | exact ⟨fun _ => False⟩
        | exact ⟨()⟩
        | exact ⟨fun _ => (ih _ (by simp_all)).default⟩)
    (fun n => ⟨(0 : BitVec n)⟩)

/-- The type-constructor interpretation handed to `SortDenote`: whatever `SortDenote` does
not fix is looked up in `coreSortDenote`. -/
def coreTcInterp : TyConstrInterp := fun name args => coreSortDenote (.tcons name args)

instance : TyConstrInterp.AllInhabited coreTcInterp :=
  ⟨fun name args => coreSortDenote.inhabited (.tcons name args)⟩

/-- `SortDenote coreTcInterp` and `coreSortDenote` are the same type family (by induction on
the sort; the built-in cases are identical, the others go through `coreTcInterp`). Used to
cast the arguments of polymorphic operators. -/
theorem sortDenote_eq : ∀ s, SortDenote coreTcInterp s = coreSortDenote s :=
  sortRec (P := fun s => SortDenote coreTcInterp s = coreSortDenote s)
    (fun name args ih => by
      unfold SortDenote
      split
      all_goals first
        | rfl
        | (rename_i heq
           cases heq <;> first
             | rfl
             | exact congr (congrArg (fun (A B : Type) => A → B) (ih _ (by simp))) (ih _ (by simp))))
    (fun n => rfl)

/-! ## Sort patterns -/

@[match_pattern] def sInt : LSort := .tcons "int" []
@[match_pattern] def sBool : LSort := .tcons "bool" []
@[match_pattern] def sArrow (a b : LSort) : LSort := .tcons "arrow" [a, b]
@[match_pattern] def sMap (k v : LSort) : LSort := .tcons "Map" [k, v]
@[match_pattern] def sSeq (t : LSort) : LSort := .tcons "Sequence" [t]

/-! ## Operators -/

/-- Transport a value between the two spellings of a sort's type. -/
def toSD {s : LSort} (v : coreSortDenote s) : SortDenote coreTcInterp s :=
  cast (sortDenote_eq s).symm v
def ofSD {s : LSort} (v : SortDenote coreTcInterp s) : coreSortDenote s :=
  cast (sortDenote_eq s) v

theorem coreSortDenote_map (k v : LSort) :
    coreSortDenote (sMap k v) = (coreSortDenote k → coreSortDenote v) := rfl
theorem coreSortDenote_seq (t : LSort) :
    coreSortDenote (sSeq t) = List (coreSortDenote t) := rfl

/-- A map value as a Lean function, and back. -/
def mapOf {k v : LSort} (m : SortDenote coreTcInterp (sMap k v)) : coreSortDenote k → coreSortDenote v :=
  cast (coreSortDenote_map k v) (ofSD m)
def mapTo {k v : LSort} (f : coreSortDenote k → coreSortDenote v) : SortDenote coreTcInterp (sMap k v) :=
  toSD (cast (coreSortDenote_map k v).symm f)
/-- A sequence value as a Lean list, and back. -/
def seqOf {t : LSort} (l : SortDenote coreTcInterp (sSeq t)) : List (coreSortDenote t) :=
  cast (coreSortDenote_seq t) (ofSD l)
def seqTo {t : LSort} (l : List (coreSortDenote t)) : SortDenote coreTcInterp (sSeq t) :=
  toSD (cast (coreSortDenote_seq t).symm l)

open Classical in
/-- The operator interpretation: by name (`CoreOp.toString`) and instantiated sort. Monomorphic
`int`/`bool` operators match a literal sort; the polymorphic `Map` and `Sequence` operators
match the sort's shape and transport through `toSD`/`ofSD`. Everything else is `default`. -/
noncomputable def coreOpInterp : OpInterp coreTcInterp := fun name s =>
  match name, s with
  -- integers
  | "Int.Add", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a + b
  | "Int.Sub", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a - b
  | "Int.Mul", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a * b
  | "Int.Div", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a / b
  | "Int.Mod", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a % b
  | "Int.DivT", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => Int.tdiv a b
  | "Int.ModT", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => Int.tmod a b
  | "Int.SafeDiv", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a / b
  | "Int.SafeMod", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => a % b
  | "Int.SafeDivT", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => Int.tdiv a b
  | "Int.SafeModT", sArrow sInt (sArrow sInt sInt) => fun (a b : Int) => Int.tmod a b
  | "Int.Neg", sArrow sInt sInt => fun (a : Int) => -a
  | "Int.Lt", sArrow sInt (sArrow sInt sBool) => fun (a b : Int) => decide (a < b)
  | "Int.Le", sArrow sInt (sArrow sInt sBool) => fun (a b : Int) => decide (a ≤ b)
  | "Int.Gt", sArrow sInt (sArrow sInt sBool) => fun (a b : Int) => decide (a > b)
  | "Int.Ge", sArrow sInt (sArrow sInt sBool) => fun (a b : Int) => decide (a ≥ b)
  -- booleans
  | "Bool.And", sArrow sBool (sArrow sBool sBool) => fun (a b : Bool) => a && b
  | "Bool.Or", sArrow sBool (sArrow sBool sBool) => fun (a b : Bool) => a || b
  | "Bool.Implies", sArrow sBool (sArrow sBool sBool) => fun (a b : Bool) => !a || b
  | "Bool.Equiv", sArrow sBool (sArrow sBool sBool) => fun (a b : Bool) => a == b
  | "Bool.Not", sArrow sBool sBool => fun (a : Bool) => !a
  -- maps: `select m k`, `update m k v`, `mapConst v`
  | "select", sArrow (sMap k v) (sArrow k' v') =>
    if h : k = k' ∧ v = v' then
      h.1 ▸ h.2 ▸ (fun (m : SortDenote coreTcInterp (sMap k v)) (x : SortDenote coreTcInterp k) =>
        toSD (mapOf m (ofSD x)))
    else default
  | "update", sArrow (sMap k v) (sArrow k' (sArrow v' (sMap k'' v''))) =>
    if h : k = k' ∧ v = v' ∧ k = k'' ∧ v = v'' then
      h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ h.2.2.2 ▸
        (fun (m : SortDenote coreTcInterp (sMap k v)) (x : SortDenote coreTcInterp k)
             (y : SortDenote coreTcInterp v) =>
          mapTo (fun z => if toSD z = x then ofSD y else mapOf m z))
    else default
  | "mapConst", sArrow v (sMap k v') =>
    if h : v = v' then
      h ▸ (fun (y : SortDenote coreTcInterp v) => mapTo (fun (_ : coreSortDenote k) => ofSD y))
    else default
  -- sequences (as lists): the unchecked operations
  | "Sequence.length", sArrow (sSeq t) sInt =>
    fun (l : SortDenote coreTcInterp (sSeq t)) => ((seqOf l).length : Int)
  | "Sequence.empty", sSeq t => seqTo ([] : List (coreSortDenote t))
  | "Sequence.append", sArrow (sSeq t) (sArrow (sSeq t') (sSeq t'')) =>
    if h : t = t' ∧ t = t'' then
      h.1 ▸ h.2 ▸ (fun (a b : SortDenote coreTcInterp (sSeq t)) => seqTo (seqOf a ++ seqOf b))
    else default
  | "Sequence.select!", sArrow (sSeq t) (sArrow sInt t') =>
    if h : t = t' then
      h ▸ (fun (l : SortDenote coreTcInterp (sSeq t)) (i : Int) =>
        toSD ((seqOf l).getD i.toNat (coreSortDenote.inhabited t).default))
    else default
  | "Sequence.update!", sArrow (sSeq t) (sArrow sInt (sArrow t' (sSeq t''))) =>
    if h : t = t' ∧ t = t'' then
      h.1 ▸ h.2 ▸ (fun (l : SortDenote coreTcInterp (sSeq t)) (i : Int) (y : SortDenote coreTcInterp t) =>
        seqTo ((seqOf l).set i.toNat (ofSD y)))
    else default
  | _, _ => default

/-! ## Sanity checks: the monomorphic cases compute by `rfl` -/

example : coreOpInterp "Int.Add" (sArrow sInt (sArrow sInt sInt)) = fun (a b : Int) => a + b := rfl
example : coreOpInterp "Int.Ge" (sArrow sInt (sArrow sInt sBool)) = fun (a b : Int) => decide (a ≥ b) := rfl
example : coreOpInterp "Bool.And" (sArrow sBool (sArrow sBool sBool)) = fun (a b : Bool) => a && b := rfl
example : coreOpInterp "Int.Neg" (sArrow sInt sInt) = fun (a : Int) => -a := rfl
example : SortDenote coreTcInterp (sMap sInt sInt) = (Int → Int) := rfl
example : SortDenote coreTcInterp (sSeq sInt) = List Int := rfl

end Strata.Shallow.Model

end
