/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # Declarations that go out of scope, against `Core.Logic.Hoare`

Leaving a block drops the variables it declared, so the rules for blocks, branches and loop
bodies have to say how the postcondition survives that. The rules here state it at the projected
environment instead of asking for `PostWF`, so the three placements a Boole lowering produces
all go through: `sumTo` declares its locals at the procedure level and has an `ensures`;
`count` declares one in a nested block, as a `for` loop lowers, and one in a branch. -/

open StrataDDM (Program)

namespace Strata.HoareTest

def localsPgm : Program :=
#strata
program Core;

procedure sumTo(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [sum]: int.mul(2, r) == int.mul(n, int.add(n, 1));
}
{
  var s : int := 0;
  var i : int := 0;
  while (int.lt(i, n))
    invariant [bounds]: int.le(0, i) && int.le(i, n)
    invariant [partial]: int.mul(2, s) == int.mul(i, int.add(i, 1))
  {
    i := int.add(i, 1);
    s := int.add(s, i);
  }
  r := s;
};

procedure count(n : int, out r : int)
spec {
  requires [nonneg]: int.ge(n, 0);
  ensures [counted]: r == n;
}
{
  var c : int := 0;
  loop: {
    var i : int := 0;
    while (int.lt(i, n))
      invariant [range]: int.le(0, i) && int.le(i, n)
      invariant [tracks]: c == i
    {
      c := int.add(c, 1);
      i := int.add(i, 1);
    }
  }
  if (int.lt(c, 0)) {
    var t : int := 0;
    c := t;
  } else {
  }
  r := c;
};
#end

#core_reflect localsPgm

noncomputable def localsProg : Core.Program := { decls := [.proc sumTo .empty, .proc count .empty] }

theorem sumTo_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple localsProg params "sumTo" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

theorem count_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple localsProg params "count" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

end Strata.HoareTest
