/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.HoareLogic.Reflect.Core
import StrataBoole.HoareLogic.Deep.Delab
import StrataBoole.HoareLogic.Deep.Tactic

/-! # Example: a loop with invariants and a `decreases` clause

The loop carries its own annotations, so `core_vcgen` needs no `invariants` clause:
the loop rule (`wp_loop`) reads them off the AST. After `core_lift`, five conditions are
left, named after the obligation and the clause (the invariants are unlabeled, so they are
`inv_1` and `inv_2`; `bound` is the lower bound of the measure at the head, `decreases` its
decrease over an iteration):
```
case step.inv_1
i : Int
hinv_1 : 0 ≤ i
n : Int
hcountUp_requires_0 : 0 ≤ n
hguard : i < n
hbound : i ≤ n
⊢ 0 ≤ i + 1
```
with `step.inv_2 : i + 1 ≤ n`, `step.bound : i + 1 ≤ n`, `step.decreases : i < i + 1` and
`exit.countUp_ensures_1 : i = n` (under `hguard : n ≤ i`). The entry conditions (`i := 0`
establishes the invariants and `n - i ≥ 0`) are closed by `core_lift`. In the VCs, `i` is the
value in an arbitrary loop-head state, while `n` is still the value in the initial state: the
body assigns only `i`, so the loop rule frames `n`.
-/

open StrataDDM (Program)
open Strata.Deep

-- `countUp` below is defined by `#core_reflect`; if that failed, an auto-bound implicit
-- would silently stand in for it.
set_option autoImplicit false

namespace Strata.DeepExamples

def countUpPgm :=
#strata
program Core;

procedure countUp(n : int, out i : int)
spec {
  requires (int.ge(n, 0));
  ensures (i == n);
}
{
  i := 0;
  while (int.lt(i, n))
    decreases int.sub(n, i)
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
};
#end

#core_reflect countUpPgm

theorem countUp_correct : Procedure.Correct countUp := by
  unfold countUp
  core_vcgen <;> core_lift <;> omega

end Strata.DeepExamples
