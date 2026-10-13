/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Verify
import StrataBoole.Shallow.Layer
import StrataBoole.Shallow.Emit

/-! # Shallow embedding: Core to Lean

`shallow_embed p` takes a `StrataDDM.Program` (a `#strata program Boole; … #end` block),
lowers and type-checks it with `Strata.Boole.typeCheck` (`getProgram → toCoreProgram →
Core.typeCheck`, i.e. before any Core transform phase), and for every procedure emits

* `def p (inputs) : Strata.Shallow.ND (outputs) := do …`
* `theorem p_spec (inputs) : ⦃⌜requires⌝⦄ p inputs ⦃⇓ r => ⌜ensures⌝⦄ := by mvcgen [p]; …`

in the shape fixed by `StrataBooleTest/shallow_find_max.lean`: parameters are arguments,
outputs are `let mut` variables (arbitrary at entry, copies of the input for `inout`),
locals are `let mut`, a loop is `whileInv` on the tuple of the variables its body assigns.

Supported in this first cut: `init`, `set`, `havoc`, `assert`, `assume`, deterministic and
nondeterministic `if`, deterministic `while` with invariants (partial correctness; a measure
is ignored with a warning), the procedure's own `exit` (Boole `return`) outside loops, and
the `int`/`bool`/`bv`/`Map`/`Sequence` expression layer. Not yet: `call`, `cover`, labelled
`exit`, nondeterministic `while`, local `function`/`type`, `old`, clause names on goals.

Operators that carry a precondition obligation in Core (`Safe*`, the checked sequence
operations) are rejected rather than translated without their obligation. The total
operations are mapped to Lean's total functions: `Int.Div`/`Int.Mod` to `/`/`%` (Euclidean on
both sides), `DivT`/`ModT` to `Int.tdiv`/`Int.tmod`, `select!` to `a[i]!`. Where Core leaves a
result unconstrained (division by zero, out-of-range `select!`) Lean returns a default value;
a proof must not rely on that value (open decision in `docs/ShallowEmbedding.md`).
-/

open Lean Elab Command Term Meta
open Lambda Imperative
open Strata.Shallow.Emit

namespace Strata.Shallow.Translate

/-- Lower and type-check; render the error as a string so the result can be evaluated at
elaboration time without naming Strata's message type. -/
def typeCheckStr (p : StrataDDM.Program) : Except String Core.Program :=
  match Strata.Boole.typeCheck p Core.VerifyOptions.quiet with
  | .ok cp => .ok cp
  | .error m => .error (toString (m.format none))

/-! ## Translation monad -/

/-- What the translator knows while walking a procedure body. -/
structure Ctx where
  /-- Lean term standing for each Core variable in scope: its identifier, or, inside a loop's
  invariant and guard, a projection of the loop state. -/
  vars : Std.HashMap String Term := {}
  /-- Types of the variables in scope (Bool-typed variables become `x = true` in `Prop`). -/
  tys : Std.HashMap String LMonoTy := {}
  /-- Enclosing expression binders for de Bruijn indices, innermost first. -/
  bvars : List (Ident × Option LMonoTy) := []
  /-- The procedure's own block label; `exit` to it is `return`. -/
  procLabel : String := ""
  /-- The output variables, returned by `exit procLabel` and at the end of the body. -/
  outputs : Array Ident := #[]
  /-- Inside a loop body, `return` would leave the body function, not the procedure. -/
  inLoop : Bool := false

structure St where
  fresh : Nat := 0
  warnings : Array String := #[]

abbrev TransM := ReaderT Ctx (StateT St MacroM)

def warn (msg : String) : TransM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

def fresh (base : String) : TransM Ident := do
  let n ← modifyGet fun s => (s.fresh, { s with fresh := s.fresh + 1 })
  pure (mkIdent (Name.mkSimple s!"__{base}{n}"))

def ident (x : String) : Ident := mkIdent (Name.mkSimple x)

def fail {α} (msg : String) : TransM α := Macro.throwError s!"shallow_embed: {msg}"

/-! ## Types -/

partial def transTy (t : LMonoTy) : TransM Term := do
  match t with
  | .tcons "int" [] => `(Int)
  | .tcons "bool" [] => `(Bool)
  | .tcons "nat" [] => `(Nat)
  | .tcons "real" [] => `(Rat)
  | .tcons "string" [] => `(String)
  | .bitvec n => `(BitVec $(quote n))
  | .tcons "Map" [k, v] => do `($(← transTy k) → $(← transTy v))
  | .tcons "Sequence" [a] => do `(Array $(← transTy a))
  | .tcons "arrow" [a, b] => do `($(← transTy a) → $(← transTy b))
  | .tcons n [] => pure (ident n)
  | .tcons n args => do
    let args ← args.mapM transTy
    `($(ident n) $(args.toArray)*)
  | .ftvar n => pure (ident n)

def isBoolTy : Option LMonoTy → Bool
  | some (.tcons "bool" []) => true
  | _ => false

/-- Result type of an operator of type `ty` applied to `n` arguments. -/
def resultTy : Option LMonoTy → Nat → Option LMonoTy
  | some (.tcons "arrow" [_, b]), n + 1 => resultTy (some b) n
  | t, 0 => t
  | _, _ => none

/-! ## Expressions -/

/-- `prop`: the result is a `Prop` (assertion positions). `val`: the result is a value, a
`Bool` for Boolean expressions. -/
inductive Mode | prop | val

def asProp (t : Term) : TransM Term := `($t = true)
def asBool (p : Term) : TransM Term := `(decide $p)

/-- Head and arguments of an application spine. -/
def spine : Core.Expression.Expr → Core.Expression.Expr × List Core.Expression.Expr
  | .app _ f a => let (h, as) := spine f; (h, as ++ [a])
  | e => (e, [])

def conj (ps : List Term) : TransM Term := do
  match ps with
  | [] => `(True)
  | [p] => pure p
  | p :: rest => do `($p ∧ $(← conj rest))

def transConst (mode : Mode) (c : LConst) : TransM Term := do
  match c with
  | .intConst i =>
    if i < 0 then `((-$(quote i.natAbs) : Int)) else `(($(quote i.toNat) : Int))
  | .boolConst b =>
    match mode, b with
    | .prop, true => `(True)
    | .prop, false => `(False)
    | .val, true => `(true)
    | .val, false => `(false)
  | .strConst s => pure (quote s)
  | .bitvecConst n v => `(($(quote v.toNat) : BitVec $(quote n)))
  | .realConst _ => fail "real constants are not supported yet"

/-- A binder name for a quantifier or lambda that does not clash with enclosing binders. -/
def binderName (n : String) : TransM Ident := do
  let base := if n.isEmpty then "x" else n
  let taken := (← read).bvars.map (·.1.getId)
  if taken.contains (Name.mkSimple base) then fresh base else pure (ident base)

mutual

partial def transExpr (mode : Mode) (e : Core.Expression.Expr) : TransM Term := do
  let ctx ← read
  match e with
  | .const _ c => transConst mode c
  | .fvar _ x ty =>
    let t := ctx.vars.getD x.name (ident x.name)
    let ty := ty <|> ctx.tys[x.name]?
    match mode with
    | .prop => if isBoolTy ty then asProp t else pure t
    | .val => pure t
  | .bvar _ i =>
    match ctx.bvars[i]? with
    | some (x, ty) =>
      match mode with
      | .prop => if isBoolTy ty then asProp x else pure x
      | .val => pure x
    | none => fail s!"unbound de Bruijn index {i}"
  | .op _ o ty => transOp mode o.name ty []
  | .app .. =>
    let (h, args) := spine e
    match h with
    | .op _ o ty => transOp mode o.name ty args
    | _ =>
      let f ← transExpr .val h
      let args ← args.mapM (transExpr .val)
      `($f $(args.toArray)*)
  | .ite _ c t f =>
    let c ← transExpr .prop c
    let t ← transExpr mode t
    let f ← transExpr mode f
    `(if $c then $t else $f)
  | .eq _ a b =>
    let a ← transExpr .val a
    let b ← transExpr .val b
    match mode with
    | .prop => `($a = $b)
    | .val => `(decide ($a = $b))
  | .quant _ k n ty _trig body =>
    let x ← binderName n
    let some mty := ty | fail "quantifier without a type annotation"
    let tyT ← transTy mty
    let body ← withReader (fun c => { c with bvars := (x, ty) :: c.bvars }) (transExpr .prop body)
    let p ← match k with
      | .all => `(∀ $x:ident : $tyT, $body)
      | .exist => `(∃ $x:ident : $tyT, $body)
    match mode with
    | .prop => pure p
    | .val => asBool p
  | .abs _ n ty body =>
    let x ← binderName n
    let body ← withReader (fun c => { c with bvars := (x, ty) :: c.bvars }) (transExpr .val body)
    match ty with
    | some mty => do `(fun ($x:ident : $(← transTy mty)) => $body)
    | none => `(fun $x:ident => $body)

/-- Operators by their Core name (`CoreOp.toString`): `Int.Add`, `Bool.And`, `Bv32.SLt`,
`select`, `Sequence.length`, …; anything else is a user function. -/
partial def transOp (mode : Mode) (name : String) (ty : Option LMonoTy)
    (args : List Core.Expression.Expr) : TransM Term := do
  let vals : TransM (List Term) := args.mapM (transExpr .val)
  let props : TransM (List Term) := args.mapM (transExpr .prop)
  -- a predicate: `Prop` in prop mode, `Bool` via `decide` in val mode
  let cmp (p : Term) : TransM Term := match mode with | .prop => pure p | .val => asBool p
  -- a `Bool`-valued operation: `= true` in prop mode
  let boolRes (t : Term) : TransM Term := match mode with | .prop => asProp t | .val => pure t
  let un (f : Term → TransM Term) : TransM Term := do
    match ← vals with | [a] => f a | _ => fail s!"{name}: expected one argument"
  let bin (f : Term → Term → TransM Term) : TransM Term := do
    match ← vals with | [a, b] => f a b | _ => fail s!"{name}: expected two arguments"
  let binP (f : Term → Term → TransM Term) : TransM Term := do
    match ← props with | [a, b] => f a b | _ => fail s!"{name}: expected two arguments"
  let unP (f : Term → TransM Term) : TransM Term := do
    match ← props with | [a] => f a | _ => fail s!"{name}: expected one argument"
  let parts := name.splitOn "."
  match parts with
  -- integers and reals
  | ["Int", k] | ["Real", k] =>
    match k with
    | "Add" => bin fun a b => `($a + $b)
    | "Sub" => bin fun a b => `($a - $b)
    | "Mul" => bin fun a b => `($a * $b)
    | "Neg" => un fun a => `(-$a)
    | "Div" => bin fun a b => `($a / $b)
    | "Mod" => bin fun a b => `($a % $b)
    | "DivT" => bin fun a b => `(Int.tdiv $a $b)
    | "ModT" => bin fun a b => `(Int.tmod $a $b)
    | "SafeDiv" | "SafeMod" | "SafeDivT" | "SafeModT" =>
      fail s!"{name} carries a precondition obligation that the translator does not emit yet"

    | "Lt" => bin fun a b => do cmp (← `($a < $b))
    | "Le" => bin fun a b => do cmp (← `($a ≤ $b))
    | "Gt" => bin fun a b => do cmp (← `($a > $b))
    | "Ge" => bin fun a b => do cmp (← `($a ≥ $b))
    | _ =>
      if k.startsWith "ToBv" then
        let some n := (String.ofList (k.toList.drop 4)).toNat? | fail s!"bad operator {name}"
        un fun a => `(BitVec.ofInt $(quote n) $a)
      else fail s!"operator {name} is not supported yet"
  -- booleans
  | ["Bool", k] =>
    match mode, k with
    | .prop, "And" => binP fun a b => `($a ∧ $b)
    | .prop, "Or" => binP fun a b => `($a ∨ $b)
    | .prop, "Not" => unP fun a => `(¬ $a)
    | .prop, "Implies" => binP fun a b => `($a → $b)
    | .prop, "Equiv" => binP fun a b => `($a ↔ $b)
    | .val, "And" => bin fun a b => `($a && $b)
    | .val, "Or" => bin fun a b => `($a || $b)
    | .val, "Not" => un fun a => `(!$a)
    | .val, "Implies" => bin fun a b => `(!$a || $b)
    | .val, "Equiv" => bin fun a b => `($a == $b)
    | _, _ => fail s!"operator {name} is not supported yet"
  -- bit vectors `Bv{n}.{kind}`
  | [bv, k] =>
    if bv.startsWith "Bv" then
      match k with
      | "Add" => bin fun a b => `($a + $b)
      | "Sub" => bin fun a b => `($a - $b)
      | "Mul" => bin fun a b => `($a * $b)
      | "Neg" => un fun a => `(-$a)
      | "Not" => un fun a => `(~~~$a)
      | "And" => bin fun a b => `($a &&& $b)
      | "Or" => bin fun a b => `($a ||| $b)
      | "Xor" => bin fun a b => `($a ^^^ $b)
      | "Shl" => bin fun a b => `($a <<< $b)
      | "UShr" => bin fun a b => `($a >>> $b)
      | "SShr" => bin fun a b => `(BitVec.sshiftRight $a ($b).toNat)
      | "UDiv" => bin fun a b => `($a / $b)
      | "UMod" => bin fun a b => `($a % $b)
      | "SDiv" => bin fun a b => `(BitVec.sdiv $a $b)
      | "SMod" => bin fun a b => `(BitVec.smod $a $b)
      | "ULt" => bin fun a b => do cmp (← `($a < $b))
      | "ULe" => bin fun a b => do cmp (← `($a ≤ $b))
      | "UGt" => bin fun a b => do cmp (← `($a > $b))
      | "UGe" => bin fun a b => do cmp (← `($a ≥ $b))
      | "SLt" => bin fun a b => do boolRes (← `(BitVec.slt $a $b))
      | "SLe" => bin fun a b => do boolRes (← `(BitVec.sle $a $b))
      | "SGt" => bin fun a b => do boolRes (← `(BitVec.slt $b $a))
      | "SGe" => bin fun a b => do boolRes (← `(BitVec.sle $b $a))
      | "Concat" => bin fun a b => `($a ++ $b)
      | "ToUInt" => un fun a => `((($a).toNat : Int))
      | "ToInt" => un fun a => `(($a).toInt)
      | _ =>
        if k.startsWith "Extract_" then
          match (String.ofList (k.toList.drop 8)).splitOn "_" with
          | [hi, lo] =>
            let some hi := hi.toNat? | fail s!"bad operator {name}"
            let some lo := lo.toNat? | fail s!"bad operator {name}"
            un fun a => `(BitVec.extractLsb $(quote hi) $(quote lo) $a)
          | _ => fail s!"bad operator {name}"
        else if k.startsWith "Safe" || k.endsWith "Overflow" then
          fail s!"{name} carries an overflow obligation that the translator does not emit yet"
        else fail s!"operator {name} is not supported yet"
    else if bv == "Sequence" then
      match k with
      | "length" => un fun s => `((($s).size : Int))
      | "select!" => bin fun s i => `($s[($i).toNat]!)
      | "update!" => do
        match ← vals with
        | [s, i, v] => `(($s).set! ($i).toNat $v)
        | _ => fail s!"{name}: expected three arguments"
      | "empty" => `(#[])
      | "append" => bin fun a b => `($a ++ $b)
      | "contains" => bin fun s v => do boolRes (← `(($s).contains $v))
      | "take!" => bin fun s n => `(($s).extract 0 ($n).toNat)
      | "drop!" => bin fun s n => `(($s).extract ($n).toNat ($s).size)
      | "select" | "update" | "take" | "drop" =>
        fail s!"{name} carries a bounds obligation that the translator does not emit yet; the unchecked `{k}!` form is translated"
      | _ => fail s!"operator {name} is not supported yet"
    else userFn
  -- maps
  | ["select"] => bin fun m k => `($m $k)
  | ["update"] => do
    -- a lambda rather than `Function.update`, which lives in Mathlib
    match ← vals with
    | [m, k, v] => `(fun k' => if k' = $k then $v else $m k')
    | _ => fail "update: expected three arguments"
  | ["mapConst"] => un fun v => `(fun _ => $v)
  | _ => userFn
where
  /-- A user-declared function, applied; `= true` in prop mode if its result is `bool`. -/
  userFn : TransM Term := do
    let vs ← args.mapM (transExpr .val)
    let t ← if vs.isEmpty then pure (ident name : Term) else `($(ident name) $(vs.toArray)*)
    match mode with
    | .prop => if isBoolTy (resultTy ty args.length) then asProp t else pure t
    | .val => pure t

end

/-! ## Statements -/

/-- The loop-carried variables of a body, as the contract states them: Strata's
`Block.modifiedVars` (`set`, `havoc`, call `inout`/`out` arguments, at any depth) minus the
variables the body itself declares (`Block.initVars`, i.e. `definedVars` with scoped names
included), first occurrence first. -/
def loopVars (body : List Core.Statement) : List String :=
  let decl := (Imperative.Block.initVars body).map (·.name)
  (((Imperative.Block.modifiedVars body).map (·.name)).filter (· ∉ decl)).eraseDups

mutual

partial def transStmts (ss : List Core.Statement) : TransM (Array DoItem) := do
  match ss with
  | [] => pure #[]
  | .cmd (.cmd (.init x ty rhs _)) :: rest =>
    let some mty := ty.toMonoType? | fail s!"local {x.name} has a polymorphic type"
    let tyT ← transTy mty
    let xI := ident x.name
    let it ← match rhs with
      | .det e => do letMut xI tyT (← transExpr .val e)
      | .nondet => letMutHavoc xI tyT
    let restItems ← withReader
      (fun c => { c with vars := c.vars.insert x.name xI, tys := c.tys.insert x.name mty })
      (transStmts rest)
    pure (#[← item it] ++ restItems)
  | s :: rest =>
    let items ← transStmt s
    let restItems ← transStmts rest
    pure (items ++ restItems)

partial def transStmt (s : Core.Statement) : TransM (Array DoItem) := do
  let ctx ← read
  match s with
  | .cmd (.cmd c) =>
    match c with
    | .init x .. => fail s!"internal: init {x.name} not handled by transStmts"
    | .set x (.det e) _ => do pure #[← item (← assign (ident x.name) (← transExpr .val e))]
    | .set x .nondet _ => do pure #[← item (← assignHavoc (ident x.name))]
    | .assert _ e _ => do pure #[← item (← assert (← transExpr .prop e))]
    | .assume _ e _ => do pure #[← item (← assume (← transExpr .prop e))]
    | .cover l _ _ => do warn s!"cover {l} ignored: no counterpart in the layer yet"; pure #[]
  | .cmd (.call n _ _) => fail s!"call to {n}: procedure calls are not supported yet"
  | .block _ ss _ => transStmts ss
  | .ite (.det c) t e _ => do
    let c ← transExpr .prop c
    let t ← transStmts t
    let e ← transStmts e
    pure #[← item (← ite c t e)]
  | .ite .nondet t e _ => do
    let b ← fresh "b"
    let t ← transStmts t
    let e ← transStmts e
    let elems ← iteNondet b t e
    elems.mapM fun el => do pure (← item el)
  | .loop (.det g) measure invs body _ => do
    if measure.isSome then warn "loop measure ignored (partial correctness)"
    let vars := (loopVars body).toArray
    let tys ← vars.mapM fun x => do
      let some t := ctx.tys[x]? | fail s!"loop assigns {x}, which is not in scope"
      transTy t
    let s ← fresh "s"
    let k := vars.size
    -- in the invariant and guard, each loop variable is a projection of the state
    let withProj (st : Term) (act : TransM Term) : TransM Term := do
      let mut m := ctx.vars
      for j in [:k] do
        m := m.insert vars[j]! (← proj st j k)
      withReader (fun c => { c with vars := m }) act
    let invConj : TransM Term := do
      let ps ← invs.mapM fun (_, e) => transExpr .prop e
      conj ps
    whileInv s (vars.map ident) tys
      (inv := fun st => withProj st invConj)
      (guard := fun st => withProj st (transExpr .prop g))
      (body := fun _ => withReader (fun c => { c with inLoop := true }) (transStmts body))
  | .loop .nondet .. => fail "nondeterministic loops are not supported yet"
  | .exit l _ =>
    if l == ctx.procLabel then
      if ctx.inLoop then fail "exit (return) inside a loop body is not supported yet"
      else do pure #[← item (← ret (← tuple (ctx.outputs.map fun o => (o : Term))))]
    else fail s!"exit {l}: labelled exits are not supported yet"
  | .funcDecl .. => fail "local function declarations are not supported (lift them first)"
  | .typeDecl .. => fail "local type declarations are not supported (lift them first)"

end

/-! ## Procedures -/

def transProc (p : Core.Procedure) : TransM (Array Command) := do
  let name := p.header.name.name
  let inputs := p.header.inputs.toList
  let outputs := p.header.outputs.toList
  let inputNames := inputs.map (·.1.name)
  let mut vars : Std.HashMap String Term := {}
  let mut tys : Std.HashMap String LMonoTy := {}
  for (x, t) in inputs ++ outputs do
    vars := vars.insert x.name (ident x.name)
    tys := tys.insert x.name t
  let outIds := (outputs.map fun (o, _) => ident o.name).toArray
  let ctx : Ctx := { vars, tys, procLabel := name, outputs := outIds }
  let body ← match p.body with
    | .structured ss => pure ss
    | .cfg _ => fail s!"{name}: CFG bodies are not supported"
  if body.isEmpty then
    warn s!"{name}: no body (abstract procedure), skipped"
    return #[]
  -- the definition
  let items ← withReader (fun _ => ctx) do
    let mut pre : Array DoItem := #[]
    for (o, t) in outputs do
      let tyT ← transTy t
      let oI := ident o.name
      if inputNames.contains o.name then pre := pre.push (← item (← letMut oI tyT oI))
      else pre := pre.push (← item (← letMutHavoc oI tyT))
    let bodyItems ← transStmts body
    let retItem ← item (← ret (← tuple (outIds.map fun o => (o : Term))))
    pure (pre ++ bodyItems ++ #[retItem])
  let params ← inputs.mapM fun (x, t) => do pure (ident x.name, ← transTy t)
  let outTys ← outputs.mapM fun (_, t) => transTy t
  let retTy ← tupleType outTys.toArray
  let defCmd ← procDef (ident name) params.toArray retTy (← doBlock items)
  -- the specification: requires (all) as precondition, non-free ensures as postcondition
  let rName := if inputNames.contains "r" || outputs.any (·.1.name == "r") then "__r" else "r"
  let r := ident rName
  let k := outputs.length
  let preT ← withReader (fun _ => ctx) do
    conj (← p.spec.preconditions.toList.mapM fun (_, c) => transExpr .prop c.expr)
  let postT ← do
    let mut m := vars
    for j in [:k] do
      m := m.insert (outputs[j]!).1.name (← proj (r : Term) j k)
    withReader (fun _ => { ctx with vars := m }) do
      let checked := p.spec.postconditions.toList.filter fun (_, c) =>
        match c.attr with | .Free => false | _ => true
      conj (← checked.mapM fun (_, c) => transExpr .prop c.expr)
  let specCmd ← specTheorem (ident s!"{name}_spec") (ident name) params.toArray preT r postT
  pure #[defCmd, specCmd]

/-! ## The command -/

unsafe def evalProgramUnsafe (t : Term) : TermElabM Core.Program := do
  let ty := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String) (mkConst ``Core.Program)
  let r ← Term.evalTerm (Except String Core.Program) ty (← `(Strata.Shallow.Translate.typeCheckStr $t))
  match r with
  | .ok p => pure p
  | .error m => throwError m!"shallow_embed: {m}"

@[implemented_by evalProgramUnsafe]
opaque evalProgram (t : Term) : TermElabM Core.Program

/-- `shallow_embed p`: translate every procedure of the Boole program `p` into a `def` on the
`ND` layer and a `_spec` theorem, elaborating both. The generated commands are shown as
info messages. -/
syntax (name := shallowEmbed) "shallow_embed " term : command

@[command_elab shallowEmbed] def elabShallowEmbed : CommandElab := fun stx => do
  let `(shallow_embed $t:term) := stx | throwUnsupportedSyntax
  let prog ← liftTermElabM (evalProgram t)
  for d in prog.decls do
    match d with
    | .proc p _ =>
      let (cmds, st) ← liftMacroM (((transProc p).run {}).run {})
      for w in st.warnings do logWarning w
      for c in cmds do
        logInfo m!"{c}"
        elabCommand c
    | .func f _ => logWarning m!"shallow_embed: function {f.name.name} skipped (not supported yet)"
    | .recFuncBlock .. => logWarning "shallow_embed: recursive functions skipped (not supported yet)"
    | .ax .. => logWarning "shallow_embed: axiom skipped (not supported yet)"
    | .type .. => logWarning "shallow_embed: type declaration skipped (not supported yet)"
    | .distinct .. => logWarning "shallow_embed: distinct declaration skipped (not supported yet)"

end Strata.Shallow.Translate
