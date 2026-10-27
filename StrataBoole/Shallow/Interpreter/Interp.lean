/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Verify
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
public import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprAnnotated
public import StrataBoole.Shallow.Layer
public import StrataBoole.Shallow.Interpreter.Sort

/-! # The interpreter: Core statements as `ND` computations

One Lean function gives every Core program its meaning in the `ND` layer. It is the object
the adequacy theorem is about (Core's operational semantics on one side, `interpStmts` on
the other) and the object that is unfolded on a concrete program to obtain its verification
conditions.

* **Store.** `FreeVarVal Core.CoreLParams tcInterp`: a Lean value for every variable at every
  sort. This is exactly the free-variable valuation that `LExpr.denote` reads, so expressions
  are evaluated by `denote` directly; there is no second evaluator.
* **Expressions.** `evalExpr σ e τ` runs Strata's computable type checker `LExpr.typeCheck`
  and, on success, `LExpr.denote` with the derivation obtained from `typeCheck_to_HasTypeA`.
* **Failure, never vacuity.** An ill-typed expression (a loop guard is checked before the loop,
  since inside `whileInv` it is a proposition), and every construct the interpreter does not
  handle, is `ND.fail`: the outcome `none` of a failed `assert`. A computation with no outcome
  at all would satisfy every specification; this one satisfies none.
* **Loops are frame-aware.** The loop state carries only the variables the body assigns
  (`Block.modifiedVars` minus `Block.initVars`); all other variables are read from the store
  at loop entry (`Store.merge`). Without this the loop invariant would have to restate that
  every unmodified variable is unchanged.
* **Blocks** restore the entry values of the names they declare on exit, as Core's
  `projectStore` does.
* **Outputs** are arbitrary at procedure entry (`havoc`); an inout parameter keeps its input
  value.
* **Unsupported for now** (`ND.fail`): procedure calls, `exit`, nondeterministic loops, local
  `type` declarations.

The model `(tcInterp, opInterp, vt)` is a parameter bundled in `Sem`; `Model.lean` provides
the concrete one for Core's built-ins.
-/

@[expose] public section

namespace Strata.Shallow.Interp

open Lambda Imperative Strata.Shallow

/-- The semantic parameters: a type-constructor interpretation, an operator interpretation,
and a type-variable valuation. -/
structure Sem where
  tcInterp : TyConstrInterp
  opInterp : OpInterp tcInterp
  [inhab : TyConstrInterp.AllInhabited tcInterp]
  vt : TyVarVal

attribute [instance] Sem.inhab

abbrev Ident := Core.CoreIdent

/-! ### Re-exported unfolding lemmas for `denote`

Strata states these without `public`; they are visible here only through `import all`, and a
module may use them in *proofs* of public theorems but not in public statements or exposed
bodies. A proof written in a user's file (or generated into it) can refer to public names only,
so each lemma is restated under a primed name. `denote_op'` and `denote_fvar'` are stated at the
annotated type (`τ := ty`), which is the form `typeCheck` produces, so no cast appears.
(`denote_boolConst`, `denote_eq_true`, `denote_quant_all_true` are already public.) -/

section ReExports

variable {T : LExprParams} {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
  {fvarVal : FreeVarVal T tcInterp} {vt : TyVarVal} {Δ : List LMonoTy}
  (bvarVal : BVarVal tcInterp vt Δ)

theorem denote_intConst' {m : T.mono.base.Metadata} {i : Int}
    (h : LExpr.HasTypeA Δ (.const m (.intConst i)) (.tcons "int" [])) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.const m (.intConst i)) (.tcons "int" []) h
      = i :=
  Lambda.denote_intConst tcInterp opInterp fvarVal vt bvarVal h

theorem denote_op' {m : T.mono.base.Metadata} {o : T.Identifier} {ty : LMonoTy}
    (h : LExpr.HasTypeA Δ (.op m o (some ty)) ty) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.op m o (some ty)) ty h
      = opInterp o.name (ty.substTyVars vt) :=
  Lambda.denote_op tcInterp opInterp fvarVal vt bvarVal h

theorem denote_fvar' {m : T.mono.base.Metadata} {name : T.Identifier} {ty : LMonoTy}
    (h : LExpr.HasTypeA Δ (.fvar m name (some ty)) ty) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.fvar m name (some ty)) ty h
      = fvarVal name (ty.substTyVars vt) :=
  Lambda.denote_fvar tcInterp opInterp fvarVal vt bvarVal h

theorem denote_bvar' {m : T.mono.base.Metadata} {i : Nat} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ (.bvar m i) τ) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.bvar m i) τ h
      = bvarVal.get i (HasTypeA.bvar_inv h) :=
  Lambda.denote_bvar tcInterp opInterp fvarVal vt bvarVal h

theorem denote_app' {m : T.Metadata} {fn arg : LExpr T.mono} {aty τ : LMonoTy}
    (h_fn : LExpr.HasTypeA Δ fn (.arrow aty τ)) (h_arg : LExpr.HasTypeA Δ arg aty)
    (h_app : LExpr.HasTypeA Δ (.app m fn arg) τ) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.app m fn arg) τ h_app =
      (LExpr.denote tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn)
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal arg aty h_arg) :=
  Lambda.denote_app bvarVal h_fn h_arg h_app

theorem denote_abs' {m : T.Metadata} {name : String} {body : LExpr T.mono} {aty rty : LMonoTy}
    (h_body : LExpr.HasTypeA (aty :: Δ) body rty)
    (h_abs : LExpr.HasTypeA Δ (.abs m name (some aty) body) (.arrow aty rty)) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.abs m name (some aty) body) (.arrow aty rty) h_abs =
      fun x => LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body :=
  Lambda.denote_abs bvarVal h_body h_abs

theorem denote_eq_false' {m : T.Metadata} {e1 e2 : LExpr T.mono} {ty' : LMonoTy}
    (h_1 : LExpr.HasTypeA Δ e1 ty') (h_2 : LExpr.HasTypeA Δ e2 ty')
    (h_eq : LExpr.HasTypeA Δ (.eq m e1 e2) .bool)
    (hne : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1 ≠
           LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h_eq = false :=
  Lambda.denote_eq_false bvarVal h_1 h_2 h_eq hne

theorem denote_ite' {m : T.Metadata} {c t e : LExpr T.mono} {τ : LMonoTy}
    (h_c : LExpr.HasTypeA Δ c .bool) (h_t : LExpr.HasTypeA Δ t τ) (h_e : LExpr.HasTypeA Δ e τ)
    (h_ite : LExpr.HasTypeA Δ (.ite m c t e) τ) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h_ite =
      bif LExpr.denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c
      then LExpr.denote tcInterp opInterp fvarVal vt bvarVal t τ h_t
      else LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h_e :=
  Lambda.denote_ite bvarVal h_c h_t h_e h_ite

theorem denote_quant_all_false' {m : T.Metadata} {name : String} {tr body : LExpr T.mono}
    {qty : LMonoTy}
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .all name (some qty) tr body) .bool)
    (w : TyDenote tcInterp vt qty)
    (hw : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body : Bool)
            = false) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .all name (some qty) tr body) .bool h_quant = false :=
  Lambda.denote_quant_all_false bvarVal h_body h_quant w hw

theorem denote_quant_exist_true' {m : T.Metadata} {name : String} {tr body : LExpr T.mono}
    {qty : LMonoTy}
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool)
    (w : TyDenote tcInterp vt qty)
    (hw : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body : Bool)
            = true) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .exist name (some qty) tr body) .bool h_quant = true :=
  Lambda.denote_quant_exist_true bvarVal h_body h_quant w hw

theorem denote_quant_exist_false' {m : T.Metadata} {name : String} {tr body : LExpr T.mono}
    {qty : LMonoTy}
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool)
    (hall : ∀ x : TyDenote tcInterp vt qty,
      (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool)
        = false) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .exist name (some qty) tr body) .bool h_quant = false :=
  Lambda.denote_quant_exist_false bvarVal h_body h_quant hall

end ReExports

/-- The store: a value for every variable at every sort (Strata's `FreeVarVal`). -/
abbrev Store (M : Sem) := FreeVarVal Core.CoreLParams M.tcInterp

/-- The sort of a Core type under the type-variable valuation. -/
abbrev sortOf (M : Sem) (τ : LMonoTy) : LSort := LMonoTy.substTyVars M.vt τ

namespace Store

variable {M : Sem}

/-- Write `v` for `x` at sort `s`; every other (name, sort) pair is unchanged. -/
def upd (σ : Store M) (x : Ident) (s : LSort) (v : SortDenote M.tcInterp s) : Store M :=
  fun y s' =>
    if y = x then
      if h : s' = s then cast (congrArg (SortDenote M.tcInterp) h.symm) v else σ y s'
    else σ y s'

/-- Names in `vs` from `t`, everything else from `σ`. -/
def merge (σ : Store M) (vs : List Ident) (t : Store M) : Store M :=
  fun y s => if y ∈ vs then t y s else σ y s

/-- The store with every variable at its default value. -/
noncomputable def default : Store M := fun _ s => (Inhabited.default : SortDenote M.tcInterp s)

@[simp] theorem upd_same (σ : Store M) (x : Ident) (s : LSort) (v : SortDenote M.tcInterp s) :
    upd σ x s v x s = v := by
  simp [upd]

@[simp] theorem upd_other (σ : Store M) (x y : Ident) (s s' : LSort) (v : SortDenote M.tcInterp s)
    (h : y ≠ x) : upd σ x s v y s' = σ y s' := by
  simp [upd, h]

@[simp] theorem merge_mem (σ t : Store M) (vs : List Ident) (y : Ident) (s : LSort) (h : y ∈ vs) :
    merge σ vs t y s = t y s := by
  simp [merge, h]

@[simp] theorem merge_not_mem (σ t : Store M) (vs : List Ident) (y : Ident) (s : LSort)
    (h : y ∉ vs) : merge σ vs t y s = σ y s := by
  simp [merge, h]

end Store

/-- The failing computation: its only outcome is `none`, as after a failed `assert`. Used for
ill-typed expressions and for every statement the interpreter does not handle, so that no
specification holds of them vacuously. -/
def ND.fail {α : Type} : ND α := ⟨fun r => r = none⟩

/-! ## Expressions -/

/-- The value of the closed, annotated expression `e` at type `τ`, if it type-checks at `τ`. -/
noncomputable def evalExpr (M : Sem) (σ : Store M) (e : Core.Expression.Expr) (τ : LMonoTy) :
    Option (TyDenote M.tcInterp M.vt τ) :=
  if h : LExpr.typeCheck (T := Core.CoreLParams) [] e = some τ then
    some (LExpr.denote (T := Core.CoreLParams) M.tcInterp M.opInterp σ M.vt .nil e τ
      (LExpr.typeCheck_to_HasTypeA h))
  else none

/-- A Boolean condition: `some b` if `e` type-checks at `bool`. -/
noncomputable def evalBool (M : Sem) (σ : Store M) (e : Core.Expression.Expr) : Option Bool :=
  evalExpr M σ e LMonoTy.bool

/-- All invariants of a loop hold in `σ`. -/
def invsHold (M : Sem) (σ : Store M) : List (String × Core.Expression.Expr) → Prop
  | [] => True
  | (_, e) :: rest => evalBool M σ e = some true ∧ invsHold M σ rest

/-! ## Statements -/

/-- What the interpreter carries along a statement list: the declared types of the variables
in scope, needed only to pick the sort of a `havoc`. -/
structure Ctx where
  tys : List (Ident × LMonoTy)

/-- The loop-carried variables of a body: assigned in it, not declared in it. -/
def loopVars (body : List Core.Statement) : List Ident :=
  let decl := Imperative.Block.initVars body
  (Imperative.Block.modifiedVars body).filter (· ∉ decl)

/-- `x := e` or `x := *` for a variable of type `τ`. -/
noncomputable def assignVar (M : Sem) (σ : Store M) (x : Ident) (τ : LMonoTy) :
    ExprOrNondet Core.Expression → ND (Store M)
  | .det e =>
    match evalExpr M σ e τ with
    | some v => pure (σ.upd x (sortOf M τ) v)
    | none => ND.fail
  | .nondet => do
    let v ← ND.havoc (α := SortDenote M.tcInterp (sortOf M τ))
    pure (σ.upd x (sortOf M τ) v)

/-- One base command. `init` is handled by `interpStmts`, which also extends the context. -/
noncomputable def interpCmd (M : Sem) (Γ : Ctx) (σ : Store M) : Cmd Core.Expression → ND (Store M)
  | .init .. => ND.fail
  | .set x (.det e) _ =>
    match LExpr.typeCheck (T := Core.CoreLParams) [] e with
    | some τ => assignVar M σ x τ (.det e)
    | none => ND.fail
  | .set x .nondet _ =>
    match Γ.tys.lookup x with
    | some τ => assignVar M σ x τ .nondet
    | none => ND.fail
  | .assert _ e _ =>
    match evalBool M σ e with
    | some b => do ND.assert (b = true); pure σ
    | none => ND.fail
  | .assume _ e _ =>
    match evalBool M σ e with
    | some b => do ND.assume (b = true); pure σ
    | none => ND.fail
  | .cover _ _ _ => pure σ

mutual

/-- A statement list. `init` extends the context for the rest of the list. -/
noncomputable def interpStmts (M : Sem) (Γ : Ctx) : List Core.Statement → Store M → ND (Store M)
  | [], σ => pure σ
  | .cmd (.cmd (.init x ty rhs _)) :: rest, σ =>
    match ty.toMonoType? with
    | some τ => do
      let σ' ← assignVar M σ x τ rhs
      interpStmts M { tys := (x, τ) :: Γ.tys } rest σ'
    | none => ND.fail
  | s :: rest, σ => do
    let σ' ← interpStmt M Γ s σ
    interpStmts M Γ rest σ'

/-- One statement. -/
noncomputable def interpStmt (M : Sem) (Γ : Ctx) : Core.Statement → Store M → ND (Store M)
  | .cmd (.cmd c), σ => interpCmd M Γ σ c
  | .cmd (.call ..), _ => ND.fail
  | .block _ ss _, σ => interpBlock M Γ ss σ
  | .ite (.det c) t e _, σ =>
    match evalBool M σ c with
    | some true => interpBlock M Γ t σ
    | some false => interpBlock M Γ e σ
    | none => ND.fail
  | .ite .nondet t e _, σ => do
    let b ← ND.havoc (α := Bool)
    if b then interpBlock M Γ t σ else interpBlock M Γ e σ
  | .loop (.det g) _ invs body _, σ =>
    if LExpr.typeCheck (T := Core.CoreLParams) [] g = some LMonoTy.bool then do
      let vs := loopVars body
      let t ← ND.whileInv
        (fun t => invsHold M (σ.merge vs t) invs)
        (fun t => evalBool M (σ.merge vs t) g = some true)
        (fun t => interpBlock M Γ body (σ.merge vs t))
        σ
      pure (σ.merge vs t)
    else ND.fail
  | .loop .nondet .., _ => ND.fail
  | .exit .., _ => ND.fail
  | .typeDecl .., _ => ND.fail

/-- A block: run the statements, then restore the entry values of the names declared inside. -/
noncomputable def interpBlock (M : Sem) (Γ : Ctx) (ss : List Core.Statement) (σ : Store M) :
    ND (Store M) := do
  let σ' ← interpStmts M Γ ss σ
  pure (σ'.merge (Imperative.Block.initVars ss) σ)

end

/-! ## Procedures -/

/-- Give each listed variable an arbitrary value of its type. -/
noncomputable def havocVars (M : Sem) : List (Ident × LMonoTy) → Store M → ND (Store M)
  | [], σ => pure σ
  | (x, τ) :: rest, σ => do
    let v ← ND.havoc (α := SortDenote M.tcInterp (sortOf M τ))
    havocVars M rest (σ.upd x (sortOf M τ) v)

/-- A procedure from a store holding its inputs: outputs that are not also inputs start
arbitrary, then the body runs. The result is the final store; outputs are read from it. -/
noncomputable def interpProc (M : Sem) (p : Core.Procedure) (σ₀ : Store M) : ND (Store M) :=
  let inputs := p.header.inputs.toList
  let outputs := p.header.outputs.toList
  let outOnly := outputs.filter fun (o, _) => inputs.all fun (i, _) => i ≠ o
  do
    let σ ← havocVars M outOnly σ₀
    match p.body with
    | .structured ss => interpStmts M ⟨inputs ++ outputs⟩ ss σ
    | .cfg _ => ND.fail

end Strata.Shallow.Interp

end
