/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.Denote.LExprDenote

/-! # Sorts: recursion principle and decidable equality for `LSort`

`LSort` is a nested inductive (`tcons` carries a `List LSort`), so the auto-generated recursor
is awkward to use. Strata already has what is needed, in
`Strata/DL/Lambda/Denote/LExprDenote.lean`, but not as public declarations of that module:

* `LSort.rec'` (and its `Prop` version `LSort.ind`): recursion with the hypothesis available
  for every member of the argument list;
* `instance : DecidableEq LSort`, built from the Boolean comparison `LSort_eqb` and the
  private lemmas `LSort_eqb_eq` and `LSort_eqb_refl`.

A non-public declaration can be used in the proof of a public theorem, but not in a public
statement or in the body of an exposed definition, which is where the model and the interpreter
need these. This file therefore provides public replacements: `sortRec` restates `LSort.rec'`
(with the motive implicit), and `LSort.decEq` decides equality directly by structural recursion
instead of going through `LSort_eqb`. Both are shared by `Model.lean` and `Interp.lean`; they
can be dropped once Strata exports its own. -/

@[expose] public section

namespace Strata.Shallow

open Lambda

/-- Recursion over `LSort` with the hypothesis available for every member of the argument list:
Strata's `LSort.rec'` (`Strata/DL/Lambda/Denote/LExprDenote.lean`), which is not public. -/
def sortRec {P : LSort → Sort u}
    (htcons : ∀ name args, (∀ x, x ∈ args → P x) → P (.tcons name args))
    (hbitvec : ∀ n, P (.bitvec n)) : ∀ s, P s
  | .tcons name args => htcons name args (fun x _ => sortRec htcons hbitvec x)
  | .bitvec n => hbitvec n

/-- Decidable equality on sorts, by structural recursion. Strata's own instance
(`instance : DecidableEq LSort` in `Strata/DL/Lambda/Denote/LExprDenote.lean`, via `LSort_eqb`)
is not public. -/
def LSort.decEq : (a b : LSort) → Decidable (a = b)
  | .tcons n as, .tcons n' as' =>
    if hn : n = n' then
      match decEqList as as' with
      | isTrue h => isTrue (by rw [hn, h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hn rfl)
  | .tcons .., .bitvec .. => isFalse nofun
  | .bitvec .., .tcons .. => isFalse nofun
  | .bitvec n, .bitvec n' =>
    if h : n = n' then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
where
  decEqList : (as bs : List LSort) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | a :: as, b :: bs =>
    match LSort.decEq a b, decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)

instance : DecidableEq LSort := LSort.decEq

example : (LSort.tcons "int" [] = LSort.tcons "int" []) := by decide
example : (LSort.tcons "arrow" [.tcons "int" [], .bitvec 32] ≠ LSort.tcons "arrow" [.tcons "int" [], .bitvec 64]) := by
  decide

end Strata.Shallow

end
