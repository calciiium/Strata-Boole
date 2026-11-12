/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # The remaining integer and boolean operators, against `Core.Logic.Hoare`

Unary negation and `!`, the connectives `==>` and `<==>`, `==` on booleans, conditional
expressions, and guards built from `&&`, `||` and `!`. Each is read in two places: by the
evaluator when it sits in a guard or on the right of an assignment, and by the denotation when
it sits in a clause. -/

open StrataDDM (Program)

namespace Strata.HoareTest

def opsPgm : Program :=
#strata
program Core;

procedure absVal(x : int, out r : int)
spec {
  ensures [nonneg]: int.ge(r, 0);
  ensures [neg]: int.lt(x, 0) ==> r == int.neg(x);
  ensures [pos]: int.ge(x, 0) ==> r == x;
}
{
  r := if int.lt(x, 0) then int.neg(x) else x;
};

procedure clamp(x : int, lo : int, hi : int, out r : int)
spec {
  requires [ord]: int.le(lo, hi);
  ensures [inRange]: int.le(lo, r) && int.le(r, hi);
  ensures [fixed]: !(int.lt(x, lo) || int.gt(x, hi)) ==> r == x;
  ensures [same]: (r == x) <==> (int.le(lo, x) && int.le(x, hi));
  ensures [flags]: (int.lt(r, x) == int.gt(x, hi)) && (int.gt(r, x) == int.lt(x, lo));
}
{
  if (int.lt(x, lo) || int.gt(x, hi)) {
    if (int.lt(x, lo)) {
      r := lo;
    } else {
      r := hi;
    }
  } else {
    r := x;
  }
};

procedure countDown(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [zero]: r == 0;
}
{
  r := n;
  while (!(r == 0) && int.gt(r, 0))
    invariant [range]: int.ge(r, 0)
  {
    r := int.sub(r, 1);
  }
};
#end

#core_reflect opsPgm

noncomputable def opsProg : Core.Program :=
  { decls := [.proc absVal .empty, .proc clamp .empty, .proc countDown .empty] }

theorem absVal_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple opsProg params "absVal" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

theorem clamp_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple opsProg params "clamp" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

theorem countDown_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple opsProg params "countDown" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

/-- info: 'Strata.HoareTest.absVal_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms absVal_contract

/-- info: 'Strata.HoareTest.clamp_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms clamp_contract

/-- info: 'Strata.HoareTest.countDown_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms countDown_contract

end Strata.HoareTest
