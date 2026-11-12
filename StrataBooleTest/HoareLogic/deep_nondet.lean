/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Deep.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Nondeterministic control and `cover`, on the deep embedding

`if (*)` proves both branches, `while (*)` is the loop rule with nothing learned from a
guard, and `cover` is a skip. -/

open StrataDDM (Program)
open Strata.Deep

set_option autoImplicit false

namespace Strata.DeepExamples

def nondetPgm :=
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

theorem pick_correct : Procedure.Correct pick := by
  unfold pick
  core_vcgen <;> core_lift <;> omega

theorem drift_correct : Procedure.Correct drift := by
  unfold drift
  core_vcgen <;> core_lift <;> omega

/-- info: 'Strata.DeepExamples.pick_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pick_correct

/-- info: 'Strata.DeepExamples.drift_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drift_correct

end Strata.DeepExamples
