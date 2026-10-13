/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean
import Std.Do
import Std.Tactic.Do
import StrataBoole.Shallow.Layer

/-! # Shallow embedding: emitting Lean syntax

Builders for the `do`-notation programs and `Triple` theorems that the Core-to-Lean
translator produces (`StrataBoole.Shallow.Translate`). This half has no dependency on
Strata, so the shape of the output can be fixed and tested on its own.

The generated code refers to the layer (`Strata.Shallow.ND.*`) by full name (the layer is
imported here so the quotations pre-resolve those names) and wraps each theorem in
`open Std.Do in`, because the triple notations `⦃ ⦄`, `⌜ ⌝`, `⇓` are scoped. The output shape follows `StrataBooleTest/shallow_find_max.lean`:
parameters are arguments, locals are `let mut`, a loop is `whileInv` on the tuple of
the variables its body assigns.
-/

open Lean Elab Command Term Meta
open Std.Do

namespace Strata.Shallow.Emit

abbrev DoItem := TSyntax ``Lean.Parser.Term.doSeqItem
abbrev DoElem := TSyntax `doElem

/-- Wrap a `doElem` as a sequence item. -/
def item (e : DoElem) : MacroM DoItem := `(Lean.Parser.Term.doSeqItem| $e:doElem)

/-- `do` block from items; an empty block is `pure ()`. -/
def doBlock (items : Array DoItem) : MacroM Term := do
  if items.isEmpty then `(do pure ()) else `(do $items*)

/-! ## Tuples: right-nested products, as Lean's `(a, b, c)` -/

/-- `(a, b, c)`; `()` for none; the term itself for one. -/
def tuple (xs : Array Term) : MacroM Term := do
  match xs.size with
  | 0 => `(())
  | 1 => pure xs[0]!
  | _ =>
    let x := xs[0]!
    let rest := xs[1:].toArray
    `(($x, $rest,*))

/-- `A × B × C`; `Unit` for none. -/
def tupleType (ts : Array Term) : MacroM Term := do
  match ts.size with
  | 0 => `(Unit)
  | _ => do
    let mut acc := ts.back!
    for t in ts.pop.reverse do
      acc ← `($t × $acc)
    pure acc

/-- Projection of component `j` out of `k` from a right-nested tuple `s`. -/
def proj (s : Term) (j k : Nat) : MacroM Term := do
  if k ≤ 1 then pure s
  else
    let mut acc := s
    for _ in [:j] do
      acc ← `(($acc).2)
    if j + 1 < k then `(($acc).1) else pure acc

/-! ## Statements -/

def letMut (x : Ident) (ty : Term) (e : Term) : MacroM DoElem :=
  `(doElem| let mut $x:ident : $ty := $e)

def letMutHavoc (x : Ident) (ty : Term) : MacroM DoElem :=
  `(doElem| let mut $x:ident : $ty ← Strata.Shallow.ND.havoc)

def assign (x : Ident) (e : Term) : MacroM DoElem :=
  `(doElem| $x:ident := $e)

def assignHavoc (x : Ident) : MacroM DoElem :=
  `(doElem| $x:ident ← Strata.Shallow.ND.havoc)

def assume (p : Term) : MacroM DoElem :=
  `(doElem| Strata.Shallow.ND.assume $p)

def assert (p : Term) : MacroM DoElem :=
  `(doElem| Strata.Shallow.ND.assert $p)

def ret (e : Term) : MacroM DoElem :=
  `(doElem| return $e)

/-- `if c then … else …`; an empty branch becomes `pure ()`. -/
def ite (c : Term) (thenItems elseItems : Array DoItem) : MacroM DoElem := do
  let thenItems ← if thenItems.isEmpty then pure #[← item (← `(doElem| pure ()))] else pure thenItems
  if elseItems.isEmpty then
    `(doElem| if $c then $thenItems*)
  else
    `(doElem| if $c then $thenItems* else $elseItems*)

/-- A nondeterministic branch: `let b ← havoc; if b then … else …`. -/
def iteNondet (b : Ident) (thenItems elseItems : Array DoItem) : MacroM (Array DoElem) := do
  let pick ← `(doElem| let $b:ident : Bool ← Strata.Shallow.ND.havoc)
  let branch ← ite (← `($b)) thenItems elseItems
  pure #[pick, branch]

/-- A `while` loop with invariant on the state tuple of the variables `vars` that the body
assigns. `inv` and `guard` receive the state term (so the caller can substitute projections
for the variables); `body` receives it as well and returns the body items, which may assign
the `vars` (they are rebound with `let mut` from the state). Generic in the monad so the
translator can run its own context inside the callbacks. Returns the items: the loop
bound to `s`, then one assignment per variable. -/
def whileInv {m : Type → Type} [Monad m] [MonadLiftT MacroM m]
    (s : Ident) (vars : Array Ident) (tys : Array Term)
    (inv guard : Term → m Term) (body : Term → m (Array DoItem)) :
    m (Array DoItem) := do
  let k := vars.size
  let stTy ← (tupleType tys : MacroM Term)
  let sTerm : Term ← (`($s) : MacroM Term)
  let invBody ← inv sTerm
  let guardBody ← guard sTerm
  let invFn ← (`(fun ($s : $stTy) => $invBody) : MacroM Term)
  let guardFn ← (`(fun ($s : $stTy) => $guardBody) : MacroM Term)
  -- body: rebind each variable mutably from the state, run the body, return the tuple
  let mut bodyItems : Array DoItem := #[]
  for j in [:k] do
    let pj ← (proj sTerm j k : MacroM Term)
    let v := vars[j]!
    let t := tys[j]!
    bodyItems := bodyItems.push (← (do item (← `(doElem| let mut $v:ident : $t := $pj)) : MacroM DoItem))
  bodyItems := bodyItems ++ (← body sTerm)
  let tup ← (tuple (vars.map fun v => (v : Term)) : MacroM Term)
  bodyItems := bodyItems.push (← (do item (← `(doElem| pure $tup)) : MacroM DoItem))
  let bodyBlock ← (doBlock bodyItems : MacroM Term)
  let bodyFn ← (`(fun ($s : $stTy) => $bodyBlock) : MacroM Term)
  let init ← (tuple (vars.map fun v => (v : Term)) : MacroM Term)
  let loop ← (do item (← `(doElem| let $s:ident ← Strata.Shallow.ND.whileInv $invFn $guardFn $bodyFn $init)) : MacroM DoItem)
  let mut out : Array DoItem := #[loop]
  for j in [:k] do
    let pj ← (proj sTerm j k : MacroM Term)
    let v := vars[j]!
    out := out.push (← (do item (← `(doElem| $v:ident := $pj)) : MacroM DoItem))
  pure out

/-! ## Declarations -/

/-- `def name (x₁ : T₁) … : Strata.Shallow.ND R := body`. -/
def procDef (name : Ident) (params : Array (Ident × Term)) (retTy : Term) (body : Term) :
    MacroM Command := do
  let binders ← params.mapM fun (x, t) => `(bracketedBinder| ($x:ident : $t))
  `(command| def $name:ident $binders* : Strata.Shallow.ND $retTy := $body)

/-- `theorem name_spec (x₁ : T₁) … : ⦃⌜pre⌝⦄ name x₁ … ⦃⇓ r => ⌜post⌝⦄ := by …`, wrapped in
`open Std.Do in` for the scoped notation and with the experimental-tactic warning off. -/
def specTheorem (thmName fnName : Ident) (params : Array (Ident × Term)) (pre : Term)
    (r : Ident) (post : Term) : MacroM Command := do
  let binders ← params.mapM fun (x, t) => `(bracketedBinder| ($x:ident : $t))
  let args : Array Term := params.map fun (x, _) => (x : Term)
  let warnOpt := mkIdent `mvcgen.warning
  let stdDo := mkIdent `Std.Do
  `(command|
    set_option $warnOpt:ident false in
    open $stdDo:ident in
    theorem $thmName:ident $binders* :
        ⦃⌜$pre⌝⦄ $fnName:ident $args* ⦃⇓ $r:ident => ⌜$post⌝⦄ := by
      (mvcgen [$fnName:ident]; all_goals (try grind)))

end Strata.Shallow.Emit
