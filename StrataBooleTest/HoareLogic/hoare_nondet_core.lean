/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Nondeterministic control and `cover`, against `Core.Logic.Hoare`

`if (*)` proves both branches, `while (*)` is the framed loop rule with nothing learned from a
guard, and `cover` is a skip. -/

open StrataDDM (Program)

namespace Strata.HoareTest

def nondetPgm : Program :=
#strata
program Core;

procedure pick(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [range]: int.le(0, r) && int.le(r, n);
}
{
  if * {
    r := 0;
  } else {
    r := n;
  }
  cover [reach]: int.ge(r, 0);
};

procedure drift(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [bound]: int.le(0, r) && int.le(r, n);
}
{
  r := 0;
  while *
    invariant [inv]: int.le(0, r) && int.le(r, n)
  {
    if (int.lt(r, n)) {
      r := int.add(r, 1);
    } else {
    }
  }
};
#end

#core_reflect nondetPgm

noncomputable def nondetProg : Core.Program :=
  { decls := [.proc pick .empty, .proc drift .empty] }

theorem pick_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple nondetProg params "pick" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals omega

theorem drift_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple nondetProg params "drift" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals omega

/-- info: 'Strata.HoareTest.pick_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms pick_contract

/-- info: 'Strata.HoareTest.drift_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms drift_contract

end Strata.HoareTest
