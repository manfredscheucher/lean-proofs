/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweeping lemma on the test instances (milestone 7)

The statement of the sweeping lemma is checked by `native_decide` on every test instance
(`n ≤ 4`), independently of its proof. Quantifying over all functions `Cell → ZMod 2` is too slow
(`2^14` for `n = 4`), so for each curve `C` one side function is computed (`sideFun`, a
breadth-first labelling of the darts), checked to be a side function of `C`, and then
`sweepTwoCells_of_exists` (uniqueness of side functions) and `sweepFirstMove_iff` give the
statement for every side function.
-/
import Pca.Sweep
import Pca.Instances.All2
import Pca.Instances.All3
import Pca.Instances.All4

open Equiv

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- One relaxation round on a table of labels (index = dart): a dart gets the label of its
`φ`-predecessor (same cell), or the label of its `σ`-predecessor `x` plus `[curve x = C]`
(`cellOf (σ x)` is the cell across the segment of `x`). -/
def sideStep {m : ℕ} (A : Arrangement n (Fin m)) (C : Fin n) (t : Array (Option (ZMod 2))) :
    Array (Option (ZMod 2)) :=
  Array.ofFn fun y : Fin m =>
    match t.getD y.val none with
    | some v => some v
    | none =>
      match t.getD (A.φ.symm y).val none with
      | some v => some v
      | none =>
        match t.getD (A.σ.symm y).val none with
        | some v => some (v + if A.curve (A.σ.symm y) = C then 1 else 0)
        | none => none

/-- The table of labels after `m` rounds, starting with label `0` at `d₀`. -/
def sideTable {m : ℕ} (A : Arrangement n (Fin m)) (C : Fin n) (d₀ : Fin m) : Array (ZMod 2) :=
  ((A.sideStep C)^[m] (Array.ofFn fun z : Fin m => if z = d₀ then some 0 else none)).map
    (·.getD 0)

/-- A function on darts that is invariant under `φ` is constant on cells. -/
theorem eq_of_sameCycle_φ (h : D → ZMod 2) (hh : ∀ y, h (A.φ y) = h y) {a b : D}
    (hab : A.φ.SameCycle a b) : h a = h b := by
  obtain ⟨k, -, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, hh, ih]

/-- The cell function of a `φ`-invariant dart function. -/
def cellFun (h : D → ZMod 2) (hh : ∀ y, h (A.φ y) = h y) : A.Cell → ZMod 2 :=
  Quotient.lift h fun _ _ hab => A.eq_of_sameCycle_φ h hh hab

theorem cellFun_cellOf (h : D → ZMod 2) (hh : ∀ y, h (A.φ y) = h y) (y : D) :
    A.cellFun h hh (A.cellOf y) = h y := rfl

/-- Dart-level form of `TwoCellsOn` (cheaper to evaluate). -/
def TwoDartsOn (C : Fin n) (s : A.Cell → ZMod 2) : Prop :=
  ∀ b : ZMod 2, ∃ y₁ y₂ : D,
    (A.curve y₁ = C ∧ (A.IsDigon (A.cellOf y₁) ∨ A.IsTriangle (A.cellOf y₁)) ∧
      s (A.cellOf y₁) = b) ∧
    (A.curve y₂ = C ∧ (A.IsDigon (A.cellOf y₂) ∨ A.IsTriangle (A.cellOf y₂)) ∧
      s (A.cellOf y₂) = b) ∧
    A.cellOf y₁ ≠ A.cellOf y₂

instance (C : Fin n) (s : A.Cell → ZMod 2) : Decidable (A.TwoDartsOn C s) := by
  unfold TwoDartsOn; infer_instance

theorem twoCellsOn_of_twoDartsOn {C : Fin n} {s : A.Cell → ZMod 2} (h : A.TwoDartsOn C s) :
    A.TwoCellsOn C s := by
  intro b
  obtain ⟨y₁, y₂, ⟨c₁, k₁, s₁⟩, ⟨c₂, k₂, s₂⟩, hne⟩ := h b
  exact ⟨_, _, hne, s₁, s₂, ⟨⟨y₁, A.mem_darts_cellOf_self y₁, c₁⟩, k₁⟩,
    ⟨⟨y₂, A.mem_darts_cellOf_self y₂, c₂⟩, k₂⟩⟩

/-- The check for one curve `C` and a table `t` of labels: the labels are `φ`-invariant, form a
side function of `C`, and both sides have two digons or triangles with a side on `C`. -/
def SweepCheckOn {m : ℕ} (A : Arrangement n (Fin m)) (C : Fin n) (t : Array (ZMod 2)) : Prop :=
  ∃ hh : ∀ y : Fin m, t.getD (A.φ y).val 0 = t.getD y.val 0,
    A.IsSide C (A.cellFun (fun y => t.getD y.val 0) hh) ∧
      A.TwoDartsOn C (A.cellFun (fun y => t.getD y.val 0) hh)

instance {m : ℕ} (A : Arrangement n (Fin m)) (C : Fin n) (t : Array (ZMod 2)) :
    Decidable (A.SweepCheckOn C t) := by
  unfold SweepCheckOn; infer_instance

/-- The check for all curves, with the computed tables. -/
def SweepCheck {m : ℕ} (A : Arrangement n (Fin m)) (d₀ : Fin m) : Prop :=
  ∀ C : Fin n, A.SweepCheckOn C (A.sideTable C d₀)

instance {m : ℕ} (A : Arrangement n (Fin m)) (d₀ : Fin m) : Decidable (A.SweepCheck d₀) := by
  unfold SweepCheck; infer_instance

theorem sweepTwoCells_of_check {m : ℕ} {A : Arrangement n (Fin m)} {d₀ : Fin m}
    (h : A.SweepCheck d₀) : A.SweepTwoCells :=
  A.sweepTwoCells_of_exists fun C => by
    obtain ⟨hh, h1, h2⟩ := h C
    exact ⟨_, h1, A.twoCellsOn_of_twoDartsOn h2⟩

theorem sweepFirstMove_of_check {m : ℕ} {A : Arrangement n (Fin m)} {d₀ : Fin m}
    (h : A.SweepCheck d₀) : A.SweepFirstMove :=
  (A.sweepFirstMove_iff).2 (sweepTwoCells_of_check h)

end Pca.Arrangement

namespace Pca.Instances

open Pca.Arrangement

theorem all2_A1_sweep : All2.A1.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all3_A1_sweep : All3.A1.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all3_A2_sweep : All3.A2.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A1_sweep : All4.A1.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A2_sweep : All4.A2.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A3_sweep : All4.A3.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A4_sweep : All4.A4.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A5_sweep : All4.A5.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A6_sweep : All4.A6.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A7_sweep : All4.A7.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)
theorem all4_A8_sweep : All4.A8.SweepFirstMove := sweepFirstMove_of_check (d₀ := 0) (by native_decide)

end Pca.Instances
