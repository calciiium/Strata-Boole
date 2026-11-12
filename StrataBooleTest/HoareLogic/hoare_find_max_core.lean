/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Hoare.Tactic
import StrataDDM.Integration.Lean.HashCommands

/-! # The maximum of a map's first `n` entries: refused

The procedure reads `nums[0]` and `nums[i]`, applications of `select`, which `Core.Factory` has
no concrete evaluation for. `Expression.eval` then returns `none` on `var max : int := nums[0]`,
the statement has no execution, and every contract of the procedure holds vacuously of it. The
rules would prove any such contract, so `hoare_contract` refuses the procedure with an error
instead; the refusal is pinned below. The procedure becomes provable once `select` evaluates
over a map value form in Strata. -/

open StrataDDM (Program)

namespace Strata.HoareTest

def findMaxPgm : Program :=
#strata
program Core;

procedure findMax(nums : Map int int, n : int, out ret : int)
spec {
  requires [nonempty]: int.gt(n, 0);
  ensures [upper]: forall __q0 : int :: int.le(0, __q0) && int.lt(__q0, n) ==> int.ge(ret, nums[__q0]);
  ensures [attained]: exists __q0 : int :: int.le(0, __q0) && int.lt(__q0, n) && ret == nums[__q0];
}
{
  var max : int := nums[0];
  var maxIndex : int := 0;
  var i : int := 1;
  while (int.lt(i, n))
    decreases int.sub(n, i)
    invariant [bounds]: int.le(1, i) && int.le(i, n)
    invariant [above]: forall __q0 : int :: int.le(0, __q0) && int.lt(__q0, i) ==> int.ge(max, nums[__q0])
    invariant [witness]: int.le(0, maxIndex) && int.lt(maxIndex, i) && max == nums[maxIndex]
  {
    if (int.gt(nums[i], max)) {
      max := nums[i];
      maxIndex := i;
    }
    i := int.add(i, 1);
  }
  assert [found]: int.le(0, maxIndex) && int.lt(maxIndex, n) && max == nums[maxIndex];
  ret := nums[maxIndex];
};
#end

#core_reflect findMaxPgm

noncomputable def findMaxProg : Core.Program := { decls := [.proc findMax .empty] }

example : findMaxProg.findProcByString? "findMax" = some findMax := rfl

/--
error: hoare: `var max := …` applies `select`, which `Core.Factory` does not evaluate: the statement has no execution, so its triple would hold vacuously
-/
#guard_msgs in
example (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple findMaxProg params "findMax" := by
  hoare_contract

end Strata.HoareTest
