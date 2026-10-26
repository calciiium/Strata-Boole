/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Shallow.Pipeline
import StrataBoole.Shallow.Interpreter.Reflect

/-! # `shallow_reflect`: the interpreter's entry point from Boole source

`shallow_reflect p` type-checks the Boole program `p` (`Pipeline.lean`) and binds the Core AST
of every procedure to `<name>_ast : Core.Procedure` (`Reflect.lean`). Statements about a
procedure, its meaning `interpProc M <name>_ast` and its specification, are made on that
definition. -/

open Lean Elab Command

namespace Strata.Shallow.Interp

syntax (name := shallowReflect) "shallow_reflect " term : command

@[command_elab shallowReflect] def elabShallowReflect : CommandElab := fun stx => do
  let `(shallow_reflect $t:term) := stx | throwUnsupportedSyntax
  let prog ← liftTermElabM (Pipeline.evalProgram t)
  for d in prog.decls do
    if let .proc p _ := d then
      let astName := (← getCurrNamespace) ++ Name.mkSimple s!"{p.header.name.name}_ast"
      liftTermElabM (Reflect.addProcedureAst astName p)

end Strata.Shallow.Interp
