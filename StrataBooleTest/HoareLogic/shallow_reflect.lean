/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.MetaVerifier
import StrataBoole.HoareLogic.Reflect.Boole

/-! # Reflection of the type-checked Core procedure

`shallow_reflect` binds the type-checked Core program to `<p>_ast` and each of its procedures to
`<name>_ast`. The literals must be the very values the type checker produced (both are computed
and compared here), and they must compute by kernel reduction. The programs cover `havoc` and
`assume`, `Map` types, quantifiers, nested loops, metadata and provenance. -/

namespace Strata.ReflectTest

open Strata

def pickNatPgm : StrataDDM.Program := #strata
program Boole;

procedure pick_nat() returns (x : int)
spec { ensures x >= 0; }
{ havoc x; assume x >= 0; };
#end

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

def loopNoStatePgm : StrataDDM.Program := #strata
program Boole;

procedure loop_no_state(n : int) returns ()
spec { requires n >= 0; }
{
  var j : int := 0;
  while (j < 0)
    invariant j == 0
  { var t : int := 1; assert t == 1; }
  assert j == 0;
};
#end

def loopOneVarPgm : StrataDDM.Program := #strata
program Boole;

procedure loop_one_var(n : int) returns (r : int)
spec { requires n >= 0; ensures r == n; }
{
  r := 0;
  while (r < n)
    invariant 0 <= r && r <= n
  { r := r + 1; }
};
#end

def loopNestedPgm : StrataDDM.Program := #strata
program Boole;

procedure loop_nested(n : int) returns (s : int)
spec { requires n >= 0; ensures s >= 0; }
{
  var i : int := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i && i <= n && s >= 0
  {
    var j : int := 0;
    while (j < i)
      invariant 0 <= j && j <= i && s >= 0
    { s := s + 1; j := j + 1; }
    i := i + 1;
  }
};
#end

#guard_msgs in
shallow_reflect pickNatPgm
#guard_msgs in
shallow_reflect sumToPgm
#guard_msgs in
shallow_reflect findMaxPgm
#guard_msgs in
shallow_reflect loopNoStatePgm
#guard_msgs in
shallow_reflect loopOneVarPgm
#guard_msgs in
shallow_reflect loopNestedPgm

example : Core.Procedure := sum_to_ast

/-- Every procedure of the type-checked program is among the reflected literals, and
conversely. -/
def reflectedFaithfully (pgm : StrataDDM.Program) (asts : List Core.Procedure) : Bool :=
  match Strata.Reflect.typeCheckStr pgm with
  | .ok cp =>
    let procs := cp.decls.filterMap fun | .proc p _ => some p | _ => none
    procs.length == asts.length && procs.all fun p => asts.any fun a => decide (p = a)
  | .error _ => false

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [reflectedFaithfully pickNatPgm [pick_nat_ast],
       reflectedFaithfully sumToPgm [sum_to_ast],
       reflectedFaithfully findMaxPgm [witnessOccurs_ast, findMax_ast],
       reflectedFaithfully loopNoStatePgm [loop_no_state_ast],
       reflectedFaithfully loopOneVarPgm [loop_one_var_ast],
       reflectedFaithfully loopNestedPgm [loop_nested_ast]]

/-! The whole program is bound as well, named after the identifier. -/

example : Core.Program := findMaxPgm_ast

def programFaithful (pgm : StrataDDM.Program) (ast : Core.Program) : Bool :=
  match Strata.Reflect.typeCheckStr pgm with
  | .ok cp => decide (cp = ast)
  | .error _ => false

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [programFaithful pickNatPgm pickNatPgm_ast,
       programFaithful sumToPgm sumToPgm_ast,
       programFaithful findMaxPgm findMaxPgm_ast,
       programFaithful loopNoStatePgm loopNoStatePgm_ast,
       programFaithful loopOneVarPgm loopOneVarPgm_ast,
       programFaithful loopNestedPgm loopNestedPgm_ast]

/-! ## Declarations other than procedures

An uninterpreted type and function, an axiom, a function with a body, and a datatype. -/

def declsPgm : StrataDDM.Program := #strata
program Boole;

type Scalar;
function reduce(b : Scalar) : Scalar;
axiom (∀ s : Scalar . (reduce(reduce(s)) == reduce(s)));
function twice(x : int) : int { x + x }
datatype OptionInt () { None(), Some(val: int) };

procedure use_decls(x : int) returns (r : int)
spec { ensures r == twice(x); }
{
  var o : OptionInt;
  o := Some(x);
  r := OptionInt..val(o) + x;
};
#end

#guard_msgs in
shallow_reflect declsPgm

/-- info: true -/
#guard_msgs in
#eval programFaithful declsPgm declsPgm_ast

def hasKind (p : Core.Program) (k : Core.Decl → Bool) : Bool := p.decls.any k

example : hasKind declsPgm_ast (fun | .type (.con _) _ => true | _ => false) = true := by decide
example : hasKind declsPgm_ast (fun | .type (.data _) _ => true | _ => false) = true := by decide
example : hasKind declsPgm_ast (fun | .ax .. => true | _ => false) = true := by decide
example : hasKind declsPgm_ast (fun | .func f _ => f.body.isSome | _ => false) = true := by decide
example : hasKind declsPgm_ast (fun | .func f _ => f.body.isNone | _ => false) = true := by decide
example : hasKind declsPgm_ast (fun | .proc .. => true | _ => false) = true := by decide

/-! The literal computes by kernel reduction. -/

example : sum_to_ast.header.name.name = "sum_to" := rfl
example : sum_to_ast.spec.preconditions.toList.length = 1 := rfl
example : sum_to_ast.spec.postconditions.toList.length = 1 := rfl

/-- The lowering wraps the body in a block named after the procedure. -/
example : (match sum_to_ast.body with
    | .structured [.block "sum_to" _ _] => true
    | _ => false) = true := by
  decide

end Strata.ReflectTest
