/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.MetaVerifier
import StrataBoole.HoareLogic.Reflect.Boole
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataBoole.HoareLogic.Deep.Tactic

/-! # Two results, a modified global and `old` across a loop, from Boole, on both routes

`returns (count: int, last: int)` gives two `out` parameters, `modifies total` makes the global
an `inout` parameter with an `old total` snapshot, and the loop writes the global. The frame
carries `old total` and `n` through the loop. -/

namespace Strata.BooleTest

def globalsPgm : StrataDDM.Program :=
#strata
program Boole;

var total : int;

procedure addAll (n: int) returns (count: int, last: int)
spec {
  modifies total;
  requires (n >= 0);
  ensures [cnt]: (count == n);
  ensures [tot]: (total == old(total) + n);
  ensures [lst]: (last == n);
}
{
  count := 0;
  last := 0;
  while (count < n)
    invariant [c]: (0 <= count && count <= n)
    invariant [t]: (total == old(total) + count)
    invariant [l]: (last == count)
  {
    total := total + 1;
    count := count + 1;
    last := count;
  }
};
#end

shallow_reflect globalsPgm

set_option maxHeartbeats 400000 in
theorem addAll_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple globalsPgm_ast params "addAll" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals omega

theorem addAll_correct : Strata.Deep.Procedure.Correct addAll_ast := by
  unfold addAll_ast
  core_vcgen <;> core_lift <;> omega

/-- info: 'Strata.BooleTest.addAll_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms addAll_contract

/-- info: 'Strata.BooleTest.addAll_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addAll_correct

end Strata.BooleTest
