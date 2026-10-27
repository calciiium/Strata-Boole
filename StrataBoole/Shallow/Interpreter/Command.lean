/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Shallow.Pipeline
import StrataBoole.Shallow.Interpreter.Reflect

/-! # `shallow_reflect`: the interpreter's entry point from Boole source

`shallow_reflect p` type-checks the Boole program `p` (`Pipeline.lean`) and binds its Core AST
(`Reflect.lean`): the whole program as `<p>_ast : Core.Program` when `p` is an identifier, and
every procedure as `<name>_ast : Core.Procedure`. Statements about a procedure, its meaning
`interpProc M <name>_ast` and its specification, are made on these definitions; the program
literal carries the functions, axioms and type declarations the procedure's names refer to. -/

open Lean Elab Command

namespace Strata.Shallow.Interp

syntax (name := shallowReflect) "shallow_reflect " term : command

@[command_elab shallowReflect] def elabShallowReflect : CommandElab := fun stx => do
  let `(shallow_reflect $t:term) := stx | throwUnsupportedSyntax
  let prog ← liftTermElabM (Pipeline.evalProgram t)
  let ns ← getCurrNamespace
  if let `($x:ident) := t then
    let pgmName := ns ++ Name.mkSimple s!"{x.getId.eraseMacroScopes.getString!}_ast"
    liftTermElabM (Reflect.addProgramAst pgmName prog)
  else
    logWarning "shallow_reflect: the program is bound as a whole only when the argument is an \
      identifier; its procedures are bound either way"
  for d in prog.decls do
    if let .proc p _ := d then
      let astName := ns ++ Name.mkSimple s!"{p.header.name.name}_ast"
      liftTermElabM (Reflect.addProcedureAst astName p)

end Strata.Shallow.Interp
