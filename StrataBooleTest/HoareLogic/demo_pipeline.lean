/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.HoareLogic.Pipeline

namespace Strata.PipelineDemo

def demoPgm : StrataDDM.Program :=
#strata
program Boole;

procedure max2 (x: int, y: int) returns (r: int)
spec {
  ensures [ge_x]: (r >= x);
  ensures [ge_y]: (r >= y);
  ensures [one_of]: (r == x || r == y);
}
{
  if (x >= y) {
    r := x;
  } else {
    r := y;
  }
};

procedure loopSimple (n: int) returns (r: int)
spec {
  requires [nonneg]: (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum))
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};

procedure max2Wrong (x: int, y: int) returns (r: int)
spec {
  ensures [strict]: (r > x);
}
{
  if (x >= y) {
    r := x;
  } else {
    r := y;
  }
};

procedure caller (x: int) returns (r: int)
spec {
  ensures [same]: (r == x);
}
{
  call r := max2(x, x);
};
#end

shallow_reflect demoPgm

/--
info: def Strata.PipelineDemo.max2_ast : Core.Procedure :=
⟦procedure max2(x : int, y : int, out r : int)
    spec {
      ensures [ge_x]: r >= x;
      ensures [ge_y]: r >= y;
      ensures [one_of]: r == x || r == y;
    }
    {
      max2: { if (x >= y) { r := x } else { r := y } }
    }⟧
-/
#guard_msgs in
#print max2_ast

/--
info: def Strata.PipelineDemo.loopSimple_ast : Core.Procedure :=
⟦procedure loopSimple(n : int, out r : int)
    spec {
      requires [nonneg]: n >= 0;
    }
    {
      loopSimple: {
        var sum : int;
        var i : int;
        sum := 0;
        i := 0;
        while (i < n)
          invariant i <= n && i * (i - 1) / 2 == sum
        { sum := sum + i; i := i + 1 };
        assert [sum_assert]: n * (n - 1) / 2 == sum;
        assert [neg_cond]: i == n;
        r := sum
      }
    }⟧
-/
#guard_msgs in
#print loopSimple_ast

theorem max2_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple demoPgm_ast params "max2" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals omega

theorem max2_correct : Strata.Deep.Procedure.Correct max2_ast := by
  unfold max2_ast
  core_vcgen
  all_goals core_lift
  all_goals omega

theorem loopSimple_contract (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.Procedure.contractTriple demoPgm_ast params "loopSimple" := by
  hoare_contract
  all_goals hoare_vcs
  all_goals hoare_lift
  all_goals first | omega | grind

theorem loopSimple_correct : Strata.Deep.Procedure.Correct loopSimple_ast := by
  unfold loopSimple_ast
  core_vcgen
  all_goals core_lift
  all_goals first | omega | grind

def morePgm : StrataDDM.Program :=
#strata
program Boole;

var total : int;

procedure sumTo (n: int) returns (s: int)
spec {
  requires (n >= 0);
  ensures [total]: (2 * s == n * (n + 1));
}
{
  s := 0;
  for i : int := 1 to n
    invariant [range]: (1 <= i && i <= n + 1)
    invariant [partial]: (2 * s == (i - 1) * i)
  {
    s := s + i;
  }
};

procedure bounds (n: int) returns (r: int)
spec {
  requires (n >= 0);
  ensures [all]: (∀ i : int :: (i <= n ==> i < r));
  ensures [pairs]: (∀ i : int :: (∀ j : int :: (i <= j ==> i + r <= j + r)));
}
{
  r := n + 2;
};

procedure pick (n: int) returns (r: int)
spec {
  requires (n >= 0);
  ensures [range]: (0 <= r && r <= n);
  ensures [positive]: (r + 1 > 0);
}
{
  if * {
    r := 0;
  } else {
    r := n;
  }
  cover [reach]: (r >= 0);
  assume [extra]: (r + 1 > 0);
};

procedure addAll (n: int) returns (count: int)
spec {
  modifies total;
  requires (n >= 0);
  ensures [cnt]: (count == n);
  ensures [tot]: (total == old(total) + n);
}
{
  count := 0;
  while (count < n)
    invariant [c]: (0 <= count && count <= n)
    invariant [t]: (total == old(total) + count)
  {
    total := total + 1;
    count := count + 1;
  }
};

procedure chooseIt (n: int) returns (r: int)
spec {
  requires (n >= 0);
  ensures [ge]: (r >= n);
  ensures [lt]: (r < n + 2);
}
{
  r := ε z : int :: (z >= n && z < n + 2);
};
#end

boole_prove morePgm sumTo
boole_prove morePgm bounds
boole_prove morePgm pick
boole_prove morePgm addAll
boole_prove morePgm chooseIt deep with (first | omega | exact ⟨n, by omega⟩)

/--
error: unsolved goals
case then.strict
x y : Int
hguard : x ≥ y
⊢ x > x
-/
#guard_msgs in
boole_prove demoPgm max2Wrong strata

/--
error: unsolved goals
case then.strict
y x : Int
hguard : y ≤ x
⊢ False
-/
#guard_msgs in
boole_prove demoPgm max2Wrong deep

/--
error: hoare: no rule for the statement
  ⟦call max2(x, x, out r)⟧
Supported: var, :=, havoc, assert, assume, cover, if, if *, { }, while, while *.
-/
#guard_msgs in
boole_prove demoPgm caller strata

/--
error: core: no rule for the statement
  ⟦call max2(x, x, out r)⟧
Supported: var, :=, havoc, assert, assume, cover, if, if *, { }, while, while *.
-/
#guard_msgs in
boole_prove demoPgm caller deep

/-- info: 'Strata.PipelineDemo.max2_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms max2_contract

/-- info: 'Strata.PipelineDemo.max2_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms max2_correct

/-- info: 'Strata.PipelineDemo.loopSimple_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms loopSimple_contract

/-- info: 'Strata.PipelineDemo.loopSimple_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loopSimple_correct

/-- info: 'Strata.PipelineDemo.sumTo_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.WFFactoryArray_func_name_nodup._native.native_decide.ax_1_1✝] -/
#guard_msgs in
#print axioms sumTo_contract

/-- info: 'Strata.PipelineDemo.chooseIt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chooseIt_correct

end Strata.PipelineDemo
