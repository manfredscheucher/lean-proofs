/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: generic facts and the hypotheses of the untangling

Plan: `doc/pca/sweep.md`. Generic facts on permutations (walks that avoid the set of changed
darts are unchanged; orbits as closed, connected sets), the two directions of a curve are different
straight walks, side and cut functions along `σ` and `straight`, and the hypotheses `UHyp` of the
untangling with their first consequences (curves and sides of the darts involved).
-/
import Pca.Sweep.Jordan

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u v

/-! ## Generic facts on permutations -/

section Gen

variable {X : Type v} [Fintype X] [DecidableEq X]

theorem u_zmod_ne (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

theorem u_pow_succ (g : Perm X) (y : X) (i : ℕ) : (g ^ (i + 1)) y = g ((g ^ i) y) := by
  rw [pow_succ', Perm.mul_apply]

theorem u_pow_succ' (g : Perm X) (y : X) (i : ℕ) : (g ^ (i + 1)) y = (g ^ i) (g y) := by
  rw [pow_succ, Perm.mul_apply]

theorem u_pow_add (g : Perm X) (y : X) (i j : ℕ) : (g ^ (i + j)) y = (g ^ i) ((g ^ j) y) := by
  rw [pow_add, Perm.mul_apply]

theorem u_sameCycle_pow (g : Perm X) (y : X) (i : ℕ) : g.SameCycle y ((g ^ i) y) :=
  ⟨i, by rw [zpow_natCast]⟩

theorem u_sameCycle_apply (g : Perm X) (y : X) : g.SameCycle y (g y) := ⟨1, by simp⟩

theorem u_sameCycle_iff_nat {g : Perm X} {a b : X} :
    g.SameCycle a b ↔ ∃ i : ℕ, (g ^ i) a = b :=
  ⟨fun h => h.exists_nat_pow_eq, fun ⟨i, h⟩ => h ▸ u_sameCycle_pow g a i⟩

/-- A walk that avoids the darts where `g'` and `g` differ is the same walk. -/
theorem u_pow_eq_of_avoid {g g' : Perm X} {M : X → Prop} (hg : ∀ x, ¬ M x → g' x = g x)
    (y : X) : ∀ j, (∀ i < j, ¬ M ((g ^ i) y)) → (g' ^ j) y = (g ^ j) y := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [u_pow_succ, u_pow_succ, ih (fun i hi => h i (by omega)), hg _ (h j (by omega))]

theorem u_exists_idx {g : Perm X} {y z : X} (h : g.SameCycle y z) :
    ∃ m < period g y, (g ^ m) y = z := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨m, List.mem_range.1 hm, by rw [Perm.coe_pow]⟩

theorem u_pow_period (g : Perm X) (y : X) : (g ^ period g y) y = y := by
  rw [Perm.coe_pow]; exact iterate_period _ _

theorem u_pow_inj {g : Perm X} {y : X} {i j : ℕ} (hi : i < period g y) (hj : j < period g y)
    (h : (g ^ i) y = (g ^ j) y) : i = j := by
  rw [period_eq_minimalPeriod] at hi hj
  rw [Perm.coe_pow, Perm.coe_pow] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

theorem u_period_le {g : Perm X} {y : X} {t : ℕ} (ht : 0 < t) (h : (g ^ t) y = y) :
    period g y ≤ t :=
  Nat.find_min' _ ⟨ht, by rw [← Perm.coe_pow]; exact h⟩

theorem u_pow_mod (g : Perm X) (y : X) (m : ℕ) : (g ^ m) y = (g ^ (m % period g y)) y := by
  conv_lhs => rw [← Nat.mod_add_div m (period g y)]
  rw [u_pow_add]
  congr 1
  induction m / period g y with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, u_pow_add, u_pow_period, ih]

theorem u_pow_pred_period (g : Perm X) (y : X) :
    g ((g ^ (period g y - 1)) y) = y := by
  rw [← u_pow_succ, Nat.sub_add_cancel (period_pos g y), u_pow_period]

/-- In the cycle through `e`, every element other than `g e` is reached from `g (g e)` before
`e` and `g e`. -/
theorem u_reach_before {g : Perm X} {e z : X} (hz : g.SameCycle (g (g e)) z) (hne : z ≠ g e) :
    ∃ j, (g ^ j) (g (g e)) = z ∧ ∀ i < j, (g ^ i) (g (g e)) ≠ e ∧ (g ^ i) (g (g e)) ≠ g e := by
  obtain ⟨m, hm, rfl⟩ := u_exists_idx hz
  refine ⟨m, rfl, fun i hi => ⟨fun he => ?_, fun he => ?_⟩⟩
  · have h2 : (g ^ (i + 2)) (g (g e)) = g (g e) := by
      rw [u_pow_succ, u_pow_succ, he]
    have := u_period_le (by omega) h2
    have hm1 : m = i + 1 := by omega
    apply hne
    rw [hm1, u_pow_succ, he]
  · have h2 : (g ^ (i + 1)) (g (g e)) = g (g e) := by rw [u_pow_succ, he]
    have := u_period_le (by omega) h2
    omega

/-- An orbit given as a closed set in which every element is reached. -/
theorem u_orbitFinset_eq {g : Perm X} {y : X} {Z : Finset X} (hcl : ∀ z ∈ Z, g z ∈ Z)
    (hy : y ∈ Z) (hr : ∀ z ∈ Z, g.SameCycle y z) : orbitFinset g y = Z := by
  ext z
  rw [mem_orbitFinset]
  refine ⟨fun h => ?_, hr z⟩
  obtain ⟨m, rfl⟩ := u_sameCycle_iff_nat.1 h
  clear h
  induction m with
  | zero => exact hy
  | succ m ih => rw [u_pow_succ]; exact hcl _ ih

/-- An orbit that avoids the darts where `g'` and `g` differ is unchanged. -/
theorem u_orbitFinset_of_avoid {g g' : Perm X} {M : X → Prop} (hg : ∀ x, ¬ M x → g' x = g x)
    {y : X} (hy : ∀ i : ℕ, ¬ M ((g ^ i) y)) : orbitFinset g' y = orbitFinset g y := by
  ext z
  rw [mem_orbitFinset, mem_orbitFinset, u_sameCycle_iff_nat,
    u_sameCycle_iff_nat]
  refine exists_congr fun j => ?_
  rw [u_pow_eq_of_avoid hg y j (fun i _ => hy i)]

end Gen

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-! ## Facts on one configuration -/

theorem u_σ4 (d : D) : Γ.σ (Γ.σ (Γ.σ (Γ.σ d))) = d := Γ.j_σ4 d

theorem u_α_straight (d : D) : Γ.α d = Γ.σ (Γ.σ (Γ.straight d)) := by
  rw [j_straight_apply, Γ.j_σ4]

theorem u_curve_pow (d : D) (i : ℕ) : Γ.curve ((Γ.straight ^ i) d) = Γ.curve d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [u_pow_succ, j_curve_straight, ih]

theorem u_curve_σσσ (d : D) : Γ.curve (Γ.σ (Γ.σ (Γ.σ d))) = Γ.curve (Γ.σ d) :=
  Γ.j_curve_σσ (Γ.σ d)

/-- The two directions of a curve are different straight walks (as `Pca/Side.lean`). -/
theorem u_not_sameCycle_σσ (d : D) : ¬ Γ.straight.SameCycle d (Γ.σ (Γ.σ d)) := by
  set τ : Perm D := Γ.σ * Γ.σ with hτdef
  have hτ : ∀ y, τ y = Γ.σ (Γ.σ y) := fun y => rfl
  have hττ : τ * τ = 1 := by
    ext y; simp only [Perm.mul_apply, hτ, Γ.j_σ4, Perm.one_apply]
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hconj : τ * Γ.straight * τ⁻¹ = Γ.straight⁻¹ := by
    rw [hτinv]
    ext y
    rw [Perm.mul_apply, Perm.mul_apply, hτ, hτ, j_straight_apply, Γ.j_σ4, eq_comm,
      Perm.inv_eq_iff_eq, j_straight_apply, j_α_α, Γ.j_σ4]
  have hcomm : ∀ j : ℤ, ∀ y, τ ((Γ.straight ^ j) y) = (Γ.straight ^ (-j)) (τ y) := by
    intro j y
    have h1 : (τ * Γ.straight * τ⁻¹) ^ j = τ * Γ.straight ^ j * τ⁻¹ := conj_zpow
    rw [hconj, inv_zpow', hτinv] at h1
    have := congrArg (fun p : Perm D => p (τ y)) h1
    simp only [Perm.mul_apply] at this
    rw [this, show τ (τ y) = y by rw [← Perm.mul_apply, hττ, Perm.one_apply]]
  rintro ⟨i, hi⟩
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · apply Γ.j_σσ_ne ((Γ.straight ^ j) d)
    rw [← hτ, hcomm, show τ d = (Γ.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add,
      hj]
    congr 2; ring
  · apply Γ.isSConf.α_ne ((Γ.straight ^ j) d)
    have h1 : τ ((Γ.straight ^ j) d) = Γ.straight ((Γ.straight ^ j) d) := by
      rw [hcomm, show τ d = (Γ.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add,
        ← Perm.mul_apply, ← zpow_one_add, hj]
      congr 2; ring
    have h2 : Γ.straight ((Γ.straight ^ j) d) = τ (Γ.α ((Γ.straight ^ j) d)) := rfl
    rw [h2] at h1
    exact (τ.injective h1).symm

/-- A reversed dart is not on the straight walk of `d`. -/
theorem u_ne_rev (d : D) (i j : ℕ) :
    Γ.σ (Γ.σ ((Γ.straight ^ i) d)) ≠ (Γ.straight ^ j) d := by
  intro h
  apply Γ.u_not_sameCycle_σσ ((Γ.straight ^ i) d)
  rw [h]
  exact ((u_sameCycle_pow _ d i).symm.trans (u_sameCycle_pow _ d j))

/-- A function on cells whose jumps across segments are given by `P`. -/
theorem u_cut_σ {r : Γ.Cell → ZMod 2} {P : D → Prop} [DecidablePred P]
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if P y then 1 else 0) (y : D) :
    r (Γ.cellOf (Γ.σ y)) = r (Γ.cellOf y) + if P y then 1 else 0 := by
  rw [j_cellOf_σ]; exact j_zmod2_eq_add_of_add_eq (hr y)

theorem u_side_σ (y : D) :
    Γ.side (Γ.cellOf (Γ.σ y)) = Γ.side (Γ.cellOf y) + if Γ.curve y = Γ.S then 1 else 0 :=
  Γ.u_cut_σ (r := Γ.side) (fun y => Γ.isSide y) y

theorem u_side_α (y : D) :
    Γ.side (Γ.cellOf (Γ.α y)) = Γ.side (Γ.cellOf y) + if Γ.curve y = Γ.S then 1 else 0 :=
  j_zmod2_eq_add_of_add_eq (Γ.isSide y)

theorem u_side_straight (y : D) :
    Γ.side (Γ.cellOf (Γ.straight y)) =
      Γ.side (Γ.cellOf y) + if Γ.curve (Γ.σ (Γ.α y)) = Γ.S then 1 else 0 := by
  rw [j_straight_apply, Γ.u_side_σ, ← j_φ_apply, j_cellOf_φ]

/-- The cut of a curve `c` (Jordan): a function on cells that jumps exactly across `c`. -/
theorem u_exists_curveCut (c : Fin n) : ∃ g : Γ.Cell → ZMod 2,
    ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0 := by
  have hh : ∀ z, (if ∃ w ∈ (Γ.segmentOf z).darts, Γ.curve w = c then (1 : ZMod 2) else 0) =
      if Γ.curve z = c then 1 else 0 := by
    intro z
    simp only [j_darts_segmentOf, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left,
      j_curve_α, or_self]
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker
    (fun s => if ∃ w ∈ s.darts, Γ.curve w = c then 1 else 0) (by
      funext x
      obtain ⟨z, rfl⟩ := x.exists_mk
      change Γ.jSegBdry _ (Γ.crossingOf z) = 0
      rw [j_segBdry_crossingOf, hh, hh, hh, hh, j_curve_σσ, j_curve_σσ]
      split_ifs <;> decide)
  refine ⟨g, fun y => ?_⟩
  have h1 := Γ.j_cellBdry_segmentOf g y
  rw [hg] at h1
  beta_reduce at h1
  rw [hh] at h1
  exact h1.symm

/-! ## The hypotheses of the untangling -/

/-- Up along `γ1` at `i`. -/
def ub1 (d : D) : D := Γ.σ d
/-- Up along `γ2` at `i + 1`. -/
def ub2 (d : D) : D := Γ.σ (Γ.σ (Γ.σ (Γ.α d)))
/-- Down along `γ1` at `i` (on the cell `Q` below `[i, i + 1]`). -/
def up1 (d : D) : D := Γ.σ (Γ.σ (Γ.σ d))
/-- Down along `γ2` at `i + 1` (on `Q`). -/
def up2 (d : D) : D := Γ.σ (Γ.α d)


/-- Hypotheses of the untangling (`doc/pca/sweep.md`): `d` is the sweep dart of the edge
`[i, i + 1]`; the legs are the straight walks of `γ1` from `σ d` (up at `i`) and of `γ2` from
`σ³ (α d)` (up at `i + 1`), both of `k` segments, ending at the vertex `v = crossingOf a` with
`straight^k (σ d) = σ a` and `straight^k (σ³ (α d)) = σ² a`; the inner crossings of both legs are
crossings with one further curve `γ`. -/
structure UHyp (d a : D) (k : ℕ) (γ : Fin n) : Prop where
  sweep : Γ.IsSweepDart d
  k_pos : 0 < k
  leg1 : (Γ.straight ^ k) (Γ.ub1 d) = Γ.σ a
  leg2 : (Γ.straight ^ k) (Γ.ub2 d) = Γ.σ (Γ.σ a)
  γ_S : γ ≠ Γ.S
  γ_1 : γ ≠ Γ.curve (Γ.ub1 d)
  γ_2 : γ ≠ Γ.curve (Γ.ub2 d)
  mid1 : ∀ j, 0 < j → j < k → Γ.curve (Γ.σ ((Γ.straight ^ j) (Γ.ub1 d))) = γ
  mid2 : ∀ j, 0 < j → j < k → Γ.curve (Γ.σ ((Γ.straight ^ j) (Γ.ub2 d))) = γ

end SConf

end Pca.Sweep
