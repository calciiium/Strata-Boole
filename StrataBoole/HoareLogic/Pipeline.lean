/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Boole
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataBoole.HoareLogic.Deep.Tactic

/-! # `boole_prove`: from a Boole program to its theorems in one command

```
def pgm : StrataDDM.Program := #strata program Boole; … #end
boole_prove pgm proc
```

reflects `pgm` to Core (`shallow_reflect`, once per program), then states and proves the
contract of `proc` on both routes:

* `proc_contract : Procedure.contractTriple pgm_ast params "proc"`, Strata's own Hoare triple
  about Core's operational semantics, proved by `hoare_contract`, `hoare_vcs`, `hoare_lift`;
* `proc_correct : Deep.Procedure.Correct proc_ast`, the triple of the deep embedding, proved by
  `core_vcgen`, `core_lift`.

Each verification condition the lifting leaves is closed by `omega`, then `grind`; one that
neither closes stays as an unsolved goal, named after its clause, with its hypotheses, which is
what the error of the failing theorem lists. `boole_prove pgm proc strata` or `… deep` runs one
route; `boole_prove pgm proc with tac` closes the conditions with `tac` instead. -/

open Lean Elab Command

namespace Strata.Boole

/-- The name a `shallow_reflect` of `p` binds, in the current namespace. -/
private def astName (p : Name) : CommandElabM Name := do
  return (← getCurrNamespace) ++ Name.mkSimple s!"{p.eraseMacroScopes.getString!}_ast"

syntax (name := booleProve) "boole_prove " ident ident (ident)? (" with " tacticSeq)? : command

@[command_elab booleProve] def elabBooleProve : CommandElab := fun stx => do
  let `(boole_prove $pgm:ident $proc:ident $[$route:ident]? $[with $tac:tacticSeq]?) := stx
    | throwUnsupportedSyntax
  let strata ← match route with
    | none => pure true
    | some r => match r.getId with
      | `strata => pure true | `deep => pure false
      | _ => throwErrorAt r "boole_prove: the route is `strata` or `deep`"
  let deep := match route with | none => true | some r => r.getId == `deep
  let pgmAst ← astName pgm.getId
  unless (← getEnv).contains pgmAst do
    elabCommand (← `(shallow_reflect $pgm))
  let procAst ← astName proc.getId
  unless (← getEnv).contains procAst do
    throwErrorAt proc "boole_prove: `{pgm.getId}` declares no procedure `{proc.getId}`"
  let pgmAstId := mkIdent pgmAst
  let procAstId := mkIdent procAst
  let procLit := Syntax.mkStrLit proc.getId.eraseMacroScopes.getString!
  let finish ← match tac with
    | some t => pure t
    | none => `(tacticSeq| first | omega | (intros; omega) | grind)
  if strata then
    let name := mkIdent (proc.getId.eraseMacroScopes.appendAfter "_contract")
    elabCommand (← `(command|
      theorem $name (params : Core.Logic.InitEnvWFParams) :
          Core.Logic.Hoare.Procedure.contractTriple $pgmAstId params $procLit := by
        hoare_contract
        all_goals hoare_vcs
        all_goals hoare_lift
        all_goals try ($finish)))
  if deep then
    let name := mkIdent (proc.getId.eraseMacroScopes.appendAfter "_correct")
    elabCommand (← `(command|
      theorem $name : Strata.Deep.Procedure.Correct $procAstId := by
        unfold $procAstId:ident
        core_vcgen
        all_goals core_lift
        all_goals try ($finish)))

end Strata.Boole
