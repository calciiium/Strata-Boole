/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.TypeCheck
import StrataBoole.HoareLogic.Reflect.ToExpr

/-! # `shallow_reflect`: a Boole program's Core AST as Lean terms

`shallow_reflect p` type-checks the Boole program `p` (`TypeCheck.lean`) and binds its Core AST
(`ToExpr.lean`): the whole program as `<p>_ast : Core.Program` when `p` is an identifier, and
every procedure as `<name>_ast : Core.Procedure`. Statements about a procedure, such as its
contract triple, are made on these definitions; the program literal carries the functions,
axioms and type declarations the procedure's names refer to. -/

open Lean Elab Command

namespace Strata.Reflect

syntax (name := shallowReflect) "shallow_reflect " term : command

@[command_elab shallowReflect] def elabShallowReflect : CommandElab := fun stx => do
  let `(shallow_reflect $t:term) := stx | throwUnsupportedSyntax
  let prog ← liftTermElabM (evalProgram t)
  let ns ← getCurrNamespace
  if let `($x:ident) := t then
    let pgmName := ns ++ Name.mkSimple s!"{x.getId.eraseMacroScopes.getString!}_ast"
    liftTermElabM (addProgramAst pgmName prog)
  else
    logWarning "shallow_reflect: the program is bound as a whole only when the argument is an \
      identifier; its procedures are bound either way"
  for d in prog.decls do
    if let .proc p _ := d then
      let astName := ns ++ Name.mkSimple s!"{p.header.name.name}_ast"
      liftTermElabM (addProcedureAst astName p)

end Strata.Reflect
