/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.Deep.Reflect
import StrataBoole.Deep.Tactic

/-! # Example: a loop with invariants and a `decreases` clause

The loop carries its own annotations, so `core_vcgen` needs no `invariants` clause:
the loop rule (`wp_loop`) reads them off the AST. After `core_lift`, two VCs are left:
* preservation: `0 ≤ i ∧ i ≤ n ∧ i < n ⊢ 0 ≤ i + 1 ∧ i + 1 ≤ n ∧ i < i + 1`, the last
  conjunct being the `decreases n - i` check;
* exit: `0 ≤ i ∧ i ≤ n ∧ n ≤ i ⊢ i = n`.

Entry (`i := 0` establishes the invariants and `n - i ≥ 0`) is closed by `core_lift`.
In the VCs, `i` is read from an arbitrary loop-head state `τ`, while `n` is still read
from the initial state `σ`: the body assigns only `i`, so the loop rule frames `n`.
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
