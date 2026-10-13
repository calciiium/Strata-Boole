/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.MetaVerifier
import StrataBoole.Shallow.Layer
import StrataBoole.Shallow.Translate

/-! # The translator against the hand-written programs

`shallow_embed` must produce, from Boole source, definitions on which the hand-written
specifications of `shallow_find_max.lean` still prove, and its own `_spec` theorems must
close. The three programs: `pick_nat` and `sum_to` (the sources recorded with the first
experiments) and the repository's Verus-emitted `findMax` without its final `call`
(procedure calls are not translated yet). -/

set_option mvcgen.warning false

namespace Strata.Shallow.TranslateTest

open Strata Std.Do Strata.Shallow Strata.Shallow.ND

/-! ## `havoc` and `assume` -/

def pickNatPgm : StrataDDM.Program := #strata
program Boole;

procedure pick_nat() returns (x : int)
spec { ensures x >= 0; }
{ havoc x; assume x >= 0; };
#end

#guard_msgs (drop info) in
shallow_embed pickNatPgm

/-- The hand-written specification, unchanged. -/
theorem pick_nat_spec' : ⦃⌜True⌝⦄ pick_nat ⦃⇓ x => ⌜x ≥ 0⌝⦄ := by
  mvcgen [pick_nat]

/-- info: 'Strata.Shallow.TranslateTest.pick_nat_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pick_nat_spec

/-- info: 'Strata.Shallow.TranslateTest.pick_nat_spec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pick_nat_spec'

/-! ## A loop with an invariant -/

def sumToPgm : StrataDDM.Program := #strata
program Boole;

procedure sum_to(n : int) returns (r : int)
spec { requires n >= 0; ensures 2 * r == n * (n + 1); }
{
  var i : int := 0;
  r := 0;
  while (i < n)
    invariant 0 <= i && i <= n && 2 * r == i * (i + 1)
  {
    i := i + 1;
    r := r + i;
  }
};
#end

#guard_msgs (drop info) in
shallow_embed sumToPgm

/-- The hand-written specification, unchanged. -/
theorem sum_to_spec' (n : Int) (h : n ≥ 0) :
    ⦃⌜True⌝⦄ sum_to n ⦃⇓ r => ⌜2 * r = n * (n + 1)⌝⦄ := by
  mvcgen [sum_to]
  all_goals grind

/-- info: 'Strata.Shallow.TranslateTest.sum_to_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_to_spec

/-- info: 'Strata.Shallow.TranslateTest.sum_to_spec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_to_spec'

/-! ## Maps, `if` without `else`, several invariants, quantifiers, a measure

The program of `find_max_verus.lean` without its last statement, `call witnessOccurs(...)`. -/

def findMaxPgm : StrataDDM.Program := #strata
program Boole;

procedure witnessOccurs(nums: Map int int, n: int, idx: int, value: int) returns ()
spec {
  requires 0 <= idx && idx < n;
  requires value == nums[idx];
  ensures ∃ j: int . 0 <= j && j < n && value == nums[j];
}
{
  assume ∃ j: int . 0 <= j && j < n && value == nums[j];
};

procedure findMax (nums: Map int int, n: int) returns (ret: int)
spec {
  requires n > 0;
  ensures ∀ i: int . 0 <= i && i < n ==> ret >= nums[i];
  ensures ∃ j: int . 0 <= j && j < n && ret == nums[j];
}
{
  var max : int := nums[0];
  var maxIndex : int := 0;
  var i : int := 1;

  while (i < n)
    decreases n - i
    invariant (1 <= i && i <= n)
    invariant (∀ k: int . 0 <= k && k < i ==> max >= nums[k])
    invariant (0 <= maxIndex && maxIndex < i && max == nums[maxIndex])
  {
    if (nums[i] > max) {
      max := nums[i];
      maxIndex := i;
    }
    i := i + 1;
  }
  assert 0 <= maxIndex && maxIndex < n && max == nums[maxIndex];
  ret := nums[maxIndex];
};
#end

/-- warning: loop measure ignored (partial correctness) -/
#guard_msgs (warning, drop info) in
shallow_embed findMaxPgm

/-- info: 'Strata.Shallow.TranslateTest.witnessOccurs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witnessOccurs_spec

/-- info: 'Strata.Shallow.TranslateTest.findMax_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms findMax_spec

end Strata.Shallow.TranslateTest
