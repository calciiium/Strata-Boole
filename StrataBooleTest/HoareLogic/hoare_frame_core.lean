/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Variables a loop does not write, against `Core.Logic.Hoare`

A loop only changes the variables its body writes. What the entry knew about any other variable
survives the loop without being repeated in an invariant: a precondition on an input (`addK`),
an assignment before the loop (`keep`), and both across nested loops (`nested`). -/

open StrataDDM (Program)

namespace Strata.HoareTest

def framePgm : Program :=
#strata
program Core;

procedure addK(n : int, k : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  requires [pos]: int.gt(k, 0);
  ensures [res]: r == int.add(n, k);
  ensures [more]: int.gt(r, n);
}
{
  var i : int := 0;
  r := k;
  while (int.lt(i, n))
    invariant [range]: int.le(0, i) && int.le(i, n)
    invariant [acc]: r == int.add(k, i)
  {
    r := int.add(r, 1);
    i := int.add(i, 1);
  }
};

procedure keep(n : int, c : int, out r : int, out k : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [count]: r == n;
  ensures [kept]: k == int.add(c, 1);
}
{
  var t : int := int.add(c, 1);
  r := 0;
  while (int.lt(r, n))
    invariant [range]: int.le(0, r) && int.le(r, n)
  {
    r := int.add(r, 1);
  }
  k := t;
};

procedure nested(n : int, k : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  requires [pos]: int.gt(k, 0);
  ensures [res]: int.gt(r, 0);
}
{
  var i : int := 0;
  r := k;
  while (int.lt(i, n))
    invariant [range]: int.le(0, i) && int.le(i, n)
    invariant [acc]: int.ge(r, k)
  {
    var j : int := 0;
    while (int.lt(j, i))
      invariant [jrange]: int.le(0, j) && int.le(j, i)
      invariant [acc]: int.ge(r, k)
    {
      r := int.add(r, 1);
      j := int.add(j, 1);
    }
    i := int.add(i, 1);
  }
};
#end

#core_reflect framePgm

noncomputable def frameProg : Core.Program :=
  { decls := [.proc addK .empty, .proc keep .empty, .proc nested .empty] }

theorem addK_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple frameProg params "addK" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

theorem keep_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple frameProg params "keep" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

set_option maxHeartbeats 400000 in
theorem nested_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple frameProg params "nested" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

/-- info: 'Strata.HoareTest.addK_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms addK_contract

/-- info: 'Strata.HoareTest.keep_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms keep_contract

/-- info: 'Strata.HoareTest.nested_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms nested_contract

end Strata.HoareTest
