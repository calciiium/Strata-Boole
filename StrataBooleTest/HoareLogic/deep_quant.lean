/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Deep.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Quantifiers in clauses, on the deep embedding

A clause is read as a proposition (`SatT`), so `forall` and `exists` over integers lift to
the Lean quantifiers wherever a clause appears: a `requires` (a hypothesis to instantiate), an
`ensures` and an `assert` (goals), an `invariant` (both), nested binders included. The last
procedure is the shape a Boole `choose` lowers to: an `assert` of an `exists`, a `havoc`, an
`assume`; the deep embedding's values are canonical, so the havocked value lifts. -/

open StrataDDM (Program)
open Strata.Deep

set_option autoImplicit false

namespace Strata.DeepExamples

def quantPgm :=
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

procedure chooseIt(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [ge]: int.ge(r, n);
  ensures [lt]: int.lt(r, int.add(n, 2));
}
{
  assert [some_pick]: exists i : int :: int.ge(i, n) && int.lt(i, int.add(n, 2));
  havoc r;
  assume [pick]: int.ge(r, n) && int.lt(r, int.add(n, 2));
};
#end

#core_reflect quantPgm

theorem bounds_correct : Procedure.Correct bounds := by
  unfold bounds
  core_vcgen <;> core_lift
  case witness => exact ⟨n + 1, by omega⟩
  all_goals (intros; omega)

theorem fromForall_correct : Procedure.Correct fromForall := by
  unfold fromForall
  core_vcgen <;> core_lift

theorem fill_correct : Procedure.Correct fill := by
  unfold fill
  core_vcgen <;> core_lift <;> (intros; omega)

theorem chooseIt_correct : Procedure.Correct chooseIt := by
  unfold chooseIt
  core_vcgen <;> core_lift
  case some_pick => exact ⟨n, by omega⟩
  all_goals omega

/-- info: 'Strata.DeepExamples.bounds_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounds_correct

/-- info: 'Strata.DeepExamples.fromForall_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fromForall_correct

/-- info: 'Strata.DeepExamples.fill_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill_correct

/-- info: 'Strata.DeepExamples.chooseIt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chooseIt_correct

end Strata.DeepExamples
