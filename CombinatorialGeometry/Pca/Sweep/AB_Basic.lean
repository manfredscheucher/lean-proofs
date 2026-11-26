/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Packages A and B (G1, Lemma 3.4), helpers

* local facts: all four darts at a vertex above the sweep are above; a curve through a crossing
  on `S` has a dart there going up; two darts of one straight walk at the same crossing are equal;
  a walk above the sweep never returns to a dart starting on `S`;
* the ∞-arc: a sweep dart starting at a crossing inside the ∞-arc lies in the ∞-arc, and a dart of
  the ∞-arc is its start or starts at a crossing inside it;
* removals: where the joined segment of `d'` is not joined (`α` of `ι d'` at a kept crossing),
  `ι` commutes with `α` and `φ`; then cells correspond and have the same size.
-/
import Pca.Sweep.Removal
import Pca.Sweep.NO_Sweep

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-! ## Local facts -/

theorem ab_mem_darts {x : Γ.Crossing} {d : D} (h : d ∈ x.darts) : Γ.crossingOf d = x :=
  Orbit.mem_darts.1 h

theorem ab_self_mem_darts (d : D) : d ∈ (Γ.crossingOf d).darts := Orbit.mem_darts.2 rfl

theorem ab_curves_ne_S {x : Γ.Crossing} (hx : ¬ Γ.OnSweep x) {y : D} (hy : Γ.crossingOf y = x) :
    Γ.curve y ≠ Γ.S := by
  intro h
  apply hx
  rw [← hy]
  change Γ.S ∈ Γ.curves _
  rw [j_curves_crossingOf, h]
  exact mem_insert_self _ _

theorem ab_mem_curves_self (y : D) : Γ.curve y ∈ Γ.curves (Γ.crossingOf y) := by
  rw [j_curves_crossingOf]; exact mem_insert_self _ _

theorem ab_mem_curves_σ (y : D) : Γ.curve (Γ.σ y) ∈ Γ.curves (Γ.crossingOf y) := by
  rw [j_curves_crossingOf]; exact mem_insert_of_mem (mem_singleton_self _)

/-- The other curve at a crossing. -/
theorem ab_other_curve {y : D} {c : Fin n} (hc : c ∈ Γ.curves (Γ.crossingOf y))
    (hne : c ≠ Γ.curve y) : Γ.curve (Γ.σ y) = c := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hc
  rcases hc with h | h
  · exact absurd h hne
  · exact h.symm

/-- All four darts at a vertex above the sweep are above the sweep. -/
theorem ab_above_of_aboveVertex {x : Γ.Crossing} (hx : Γ.IsAboveVertex x) {d : D}
    (hd : Γ.crossingOf d = x) : Γ.Above d := by
  obtain ⟨a, ha, hA⟩ := hx.2
  have ha' := ab_mem_darts ha
  have hσ : ∀ y, Γ.crossingOf y = x → Γ.Above y → Γ.Above (Γ.σ y) := by
    intro y hy h
    refine ⟨ab_curves_ne_S hx.1 (by rw [j_crossingOf_σ]; exact hy), ?_⟩
    unfold Up
    rw [no_side_σ, if_neg (ab_curves_ne_S hx.1 hy), add_zero]
    exact h.2
  have h1 : Γ.crossingOf (Γ.σ a) = x := by rw [j_crossingOf_σ]; exact ha'
  have h2 : Γ.crossingOf (Γ.σ (Γ.σ a)) = x := by rw [j_crossingOf_σ]; exact h1
  rcases no_mem_crossing (hd.trans ha'.symm) with rfl | rfl | rfl | rfl
  · exact hA
  · exact hσ a ha' hA
  · exact hσ _ h1 (hσ a ha' hA)
  · exact hσ _ h2 (hσ _ h1 (hσ a ha' hA))

/-- A crossing not on `S` with an above dart is a vertex above the sweep. -/
theorem ab_aboveVertex_of {y : D} (hy : Γ.Above y) (hS : ¬ Γ.OnSweep (Γ.crossingOf y)) :
    Γ.IsAboveVertex (Γ.crossingOf y) :=
  ⟨hS, y, ab_self_mem_darts y, hy⟩

theorem ab_above_α {y : D} (hy : Γ.Above y) : Γ.Above (Γ.α y) :=
  ⟨by rw [j_curve_α]; exact hy.1, by unfold Up; rw [no_side_α hy.1]; exact hy.2⟩

/-- A curve `c ≠ S` through a crossing on `S` has a dart there going up. -/
theorem ab_up_dart {x : Γ.Crossing} (hx : Γ.OnSweep x) {c : Fin n} (hc : c ∈ Γ.curves x)
    (hcS : c ≠ Γ.S) : ∃ y, Γ.crossingOf y = x ∧ Γ.curve y = c ∧ Γ.Above y ∧
      Γ.IsSweepDart (Γ.σ (Γ.σ (Γ.σ y))) ∧ Γ.σ (Γ.σ (Γ.σ (Γ.σ y))) = y := by
  obtain ⟨s, hs, rfl⟩ := no_onSweep hx
  have hA := no_above_σ hs
  have hcur : Γ.curve (Γ.σ s) = c := ab_other_curve hc (by rw [hs.1]; exact hcS)
  refine ⟨Γ.σ s, j_crossingOf_σ _ _, hcur, hA, ?_⟩
  exact no_sweep_of_above hA (by rw [j_crossingOf_σ]; exact hx)

/-- Two darts of one straight walk at the same crossing are equal. -/
theorem ab_cross_eq {a : D} {i j : ℕ}
    (h : Γ.crossingOf ((Γ.straight ^ i) a) = Γ.crossingOf ((Γ.straight ^ j) a)) :
    (Γ.straight ^ i) a = (Γ.straight ^ j) a := by
  have hc : Γ.curve ((Γ.straight ^ i) a) = Γ.curve ((Γ.straight ^ j) a) := by
    rw [no_curve_pow, no_curve_pow]
  rcases no_mem_crossing h with h1 | h1 | h1 | h1
  · exact h1
  · exact absurd (hc.symm.trans (congrArg Γ.curve h1)).symm (no_curve_σ_ne _)
  · exfalso
    apply no_not_sameCycle_straight_σσ ((Γ.straight ^ j) a)
    rw [← h1]
    exact Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))
  · have h2 := congrArg Γ.curve h1
    rw [j_curve_σσ] at h2
    exact absurd (hc.symm.trans h2).symm (no_curve_σ_ne _)

theorem ab_pow_cancel {x : D} {p q : ℕ} (hpq : p ≤ q)
    (h : (Γ.straight ^ p) x = (Γ.straight ^ q) x) : (Γ.straight ^ (q - p)) x = x := by
  have h2 : (Γ.straight ^ q) x = (Γ.straight ^ p) ((Γ.straight ^ (q - p)) x) := by
    rw [← no_pow_add, Nat.add_sub_cancel' hpq]
  rw [h2] at h
  exact ((Γ.straight ^ p).injective h).symm

/-- A walk above the sweep from a dart starting on `S` never returns to it. -/
theorem ab_no_return {a : D} (ha : Γ.Above a) (haS : Γ.S ∈ Γ.curves (Γ.crossingOf a)) {j : ℕ}
    (hj : 1 ≤ j) (hall : ∀ i < j, Γ.Above ((Γ.straight ^ i) a)) (h : (Γ.straight ^ j) a = a) :
    False :=
  no_enter ha haS (hall (j - 1) (by omega)) (by rw [← no_pow_succ, Nat.sub_add_cancel hj, h])

/-- Two crossings of a walk above the sweep from a dart starting on `S` are distinct. -/
theorem ab_walk_inj {a : D} (ha : Γ.Above a) (haS : Γ.S ∈ Γ.curves (Γ.crossingOf a)) {N : ℕ}
    (hall : ∀ i ≤ N, Γ.Above ((Γ.straight ^ i) a)) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    (h : Γ.crossingOf ((Γ.straight ^ i) a) = Γ.crossingOf ((Γ.straight ^ j) a)) : i = j := by
  have he := ab_cross_eq h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (ab_no_return ha haS (j := j - i) (by omega)
      (fun t ht => hall t (by omega)) (ab_pow_cancel hij.le he)).elim
  · exact hij
  · exact (ab_no_return ha haS (j := i - j) (by omega)
      (fun t ht => hall t (by omega)) (ab_pow_cancel hij.le he.symm)).elim

/-- An above dart and a dart of the same curve at a crossing on `S` with the same crossing are
equal. -/
theorem ab_above_unique {a b : D} (ha : Γ.Above a) (hb : Γ.Above b)
    (hS : Γ.S ∈ Γ.curves (Γ.crossingOf a)) (hc : Γ.curve a = Γ.curve b)
    (h : Γ.crossingOf b = Γ.crossingOf a) : b = a := by
  have hσS : Γ.curve (Γ.σ a) = Γ.S := ab_other_curve hS (Ne.symm ha.1)
  rcases no_mem_crossing h with h1 | h1 | h1 | h1
  · exact h1
  · exact absurd (hc.trans (by rw [h1, hσS])) ha.1
  · exfalso
    have h2 : Γ.side (Γ.cellOf b) = Γ.side (Γ.cellOf a) + 1 := by
      rw [h1, no_side_σ, if_pos hσS, no_side_σ, if_neg ha.1, add_zero]
    have e1 : Γ.side (Γ.cellOf b) = 1 := hb.2
    have e2 : Γ.side (Γ.cellOf a) = 1 := ha.2
    rw [e1, e2] at h2
    exact absurd h2 (by decide)
  · exact absurd (hc.trans (by rw [h1, j_curve_σσ, hσS])) ha.1

/-! ## The ∞-arc -/

theorem ab_arc_of_inf {s : D} (hs : Γ.IsSweepDart s) (hinf : Γ.IsInfVertex (Γ.crossingOf s)) :
    s ∈ Γ.infArc := by
  obtain ⟨z, hz, -⟩ := id hinf
  have hz' : Γ.infStart = some z := hz
  obtain ⟨t, ht, rfl⟩ := no_noC_surj hz' hs
  rw [no_noC_arc hz' ht]
  have := (no_noC_inner hz' ht).1 hinf
  omega

theorem ab_inf_of_arc {z s : D} (hz : Γ.infStart = some z) (hs : s ∈ Γ.infArc) :
    s = z ∨ Γ.IsInfVertex (Γ.crossingOf s) := by
  obtain ⟨i, hi, rfl⟩ := (no_mem_infArc hz).1 hs
  rcases i with _ | j
  · exact Or.inl rfl
  · right
    refine ⟨z, by rw [hz]; rfl, j, by omega, ?_⟩
    rw [no_pow_succ, no_crossingOf_α_straight]

theorem ab_infVertex_onSweep {x : Γ.Crossing} (h : Γ.IsInfVertex x) : Γ.OnSweep x := by
  obtain ⟨z, hz, i, hi, rfl⟩ := h
  have hz' : Γ.infStart = some z := hz
  have hs := no_sweep_pow (no_z_sweep hz') i
  change Γ.S ∈ Γ.curves _
  rw [j_curves_crossingOf, j_curve_α, hs.1]
  exact mem_insert_self _ _

/-! ## Removals: where a segment is not joined -/

namespace Removal

variable {R : Finset (Fin n)} (X : Γ.Removal R)

theorem ab_ι_α (d' : X.D') (h : Γ.rK R (Γ.α (X.ι d'))) : X.ι (X.Γ'.α d') = Γ.α (X.ι d') := by
  obtain ⟨e, hp, -, he⟩ := X.isRemoval.α d'
  obtain ⟨k, hk, rfl⟩ := (Γ.r_piece_iff R).1 hp
  rcases k with _ | k
  · exact he
  · exact absurd h (hk 0 (Nat.succ_pos k))

theorem ab_ι_φ (d' : X.D') (h : Γ.rK R (Γ.α (X.ι d'))) : X.ι (X.Γ'.φ d') = Γ.φ (X.ι d') := by
  rw [j_φ_apply, j_φ_apply, X.isRemoval.σ, ab_ι_α X d' h]

theorem ab_ι_φ_pow (x' : X.D') (h : ∀ k : ℕ, Γ.rK R (Γ.α ((Γ.φ ^ k) (X.ι x')))) (k : ℕ) :
    X.ι ((X.Γ'.φ ^ k) x') = (Γ.φ ^ k) (X.ι x') := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ab_ι_φ X _ (by rw [ih]; exact h k), ih, pow_succ',
      Perm.mul_apply]

theorem ab_period_eq (x' : X.D') (h : ∀ k : ℕ, X.ι ((X.Γ'.φ ^ k) x') = (Γ.φ ^ k) (X.ι x')) :
    period X.Γ'.φ x' = period Γ.φ (X.ι x') := by
  have key : ∀ k, (X.Γ'.φ^[k]) x' = x' ↔ (Γ.φ^[k]) (X.ι x') = X.ι x' := by
    intro k
    rw [← Perm.coe_pow, ← Perm.coe_pow, ← h k]
    exact ⟨fun e => by rw [e], fun e => X.isRemoval.inj e⟩
  apply le_antisymm
  · exact Nat.find_min' _ ⟨period_pos _ _, (key _).2 (iterate_period _ _)⟩
  · exact Nat.find_min' _ ⟨period_pos _ _, (key _).1 (iterate_period _ _)⟩

theorem ab_size_eq (x' : X.D') (h : ∀ k : ℕ, X.ι ((X.Γ'.φ ^ k) x') = (Γ.φ ^ k) (X.ι x')) :
    (X.Γ'.cellOf x').size = (Γ.cellOf (X.ι x')).size := by
  unfold Orbit.size cellOf
  rw [Orbit.darts_mk, Orbit.darts_mk, card_orbitFinset, card_orbitFinset, ab_period_eq X x' h]

end Removal

theorem ab_mem_cell_pow (y : D) (k : ℕ) : (Γ.φ ^ k) y ∈ (Γ.cellOf y).darts :=
  Orbit.mem_darts.2 (Orbit.mk_eq_mk.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm)

theorem ab_exists_pow_of_mem_cell {y e : D} (h : e ∈ (Γ.cellOf y).darts) :
    ∃ k : ℕ, (Γ.φ ^ k) y = e := by
  have h1 : Γ.φ.SameCycle y e := (Orbit.mk_eq_mk.1 (Orbit.mem_darts.1 h)).symm
  exact h1.exists_nat_pow_eq

theorem ab_cellOf_eq_of_mem {y e : D} (h : e ∈ (Γ.cellOf y).darts) : Γ.cellOf e = Γ.cellOf y :=
  Orbit.mem_darts.1 h

end SConf

end Pca.Sweep
