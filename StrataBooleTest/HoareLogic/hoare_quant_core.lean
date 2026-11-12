/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Quantifiers in clauses, against `Core.Logic.Hoare`

`forall` and `exists` over integers lift to the Lean quantifiers wherever a clause is read: a
`requires` (a hypothesis to instantiate), an `ensures` and an `assert` (goals), an `invariant`
(both), nested binders included. An `assume` lifts to a hypothesis at the store it was passed
with. -/

open StrataDDM (Program)

namespace Strata.HoareTest

def quantPgm : Program :=
#strata
program Core;

procedure bounds(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [all]: forall i : int :: int.le(i, n) ==> int.lt(i, r);
  ensures [witness]: exists i : int :: int.gt(i, n) && int.lt(i, r);
  ensures [pairs]: forall i : int :: forall j : int ::
    int.le(i, j) ==> int.le(int.add(i, r), int.add(j, r));
}
{
  r := int.add(n, 2);
};

procedure fromForall(n : int, out r : int)
spec {
  requires [lb]: forall i : int :: int.ge(i, n) ==> int.ge(i, 0);
  ensures [nonneg]: int.ge(r, 0);
}
{
  r := n;
};

procedure fill(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [done]: forall i : int :: int.le(0, i) && int.lt(i, n) ==> int.lt(i, r);
}
{
  r := 0;
  while (int.lt(r, n))
    invariant [range]: int.le(0, r) && int.le(r, n)
    invariant [below]: forall i : int :: int.lt(i, r) ==> int.lt(i, n)
  {
    r := int.add(r, 1);
  }
};

procedure assumed(n : int, out r : int)
spec {
  ensures [big]: int.gt(r, n);
}
{
  r := n;
  assume [bump]: int.gt(n, 0);
  assert [gap]: exists i : int :: int.gt(i, 0) && int.le(i, n);
  r := int.add(r, n);
};
#end

#core_reflect quantPgm

noncomputable def quantProg : Core.Program :=
  { decls := [.proc bounds .empty, .proc fromForall .empty, .proc fill .empty, .proc assumed .empty] }

theorem bounds_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple quantProg params "bounds" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  case witness => exact ⟨n + 1, by omega⟩
  all_goals (intros; omega)

theorem fromForall_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple quantProg params "fromForall" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  case nonneg => have := hlb n; omega

theorem fill_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple quantProg params "fill" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals (intros; omega)

theorem assumed_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple quantProg params "assumed" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  case gap => exact ⟨n, by omega⟩
  all_goals omega

/-- info: 'Strata.HoareTest.bounds_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms bounds_contract

/-- info: 'Strata.HoareTest.fromForall_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms fromForall_contract

/-- info: 'Strata.HoareTest.fill_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms fill_contract

/-- info: 'Strata.HoareTest.assumed_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms assumed_contract

end Strata.HoareTest
