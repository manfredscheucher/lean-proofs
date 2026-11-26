/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package O, helpers: the sweep cycle, positions, and walks against a cut

Facts used by Lemma 3.10 (`Pca/Sweep/L310.lean`):

* local facts at a crossing (the sides of its four corners, the unique sweep dart at a crossing
  on `S`);
* the sweep cycle: the sweep darts are `noC z t = straight^t w`, `t < P`, with `w` the dart after
  the ∞-arc (`z = infStart`, `P` the period of `straight` at `z`); the crossing of `noC z t` has
  position `t + 1`, it is a vertex on the sweep iff `t + infLen < P`, and `noC z t` is in the ∞-arc
  iff `P ≤ t + infLen + 1`;
* walks against a cut `r` (`r (cellOf y) + r (cellOf (α y)) = f y`): along the upper side of `S`
  (`no_walk_sweep`), along a curve (`no_walk_straight`), and around a crossing (`no_corner_sum`).
-/
import Pca.Sweep.Jordan

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-! ## Local facts -/

theorem no_z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem no_side_σ (y : D) : Γ.side (Γ.cellOf (Γ.σ y)) =
    Γ.side (Γ.cellOf y) + if Γ.curve y = Γ.S then 1 else 0 := by
  rw [j_cellOf_σ]
  exact j_zmod2_eq_add_of_add_eq (Γ.isSide y)

theorem no_side_α {y : D} (hy : Γ.curve y ≠ Γ.S) :
    Γ.side (Γ.cellOf (Γ.α y)) = Γ.side (Γ.cellOf y) := by
  rw [← j_cellOf_σ, no_side_σ, if_neg hy, add_zero]

theorem no_curve_σ_ne (d : D) : Γ.curve (Γ.σ d) ≠ Γ.curve d := Γ.isSConf.curve_σ d

theorem no_mem_crossing {d e : D} (h : Γ.crossingOf e = Γ.crossingOf d) :
    e = d ∨ e = Γ.σ d ∨ e = Γ.σ (Γ.σ d) ∨ e = Γ.σ (Γ.σ (Γ.σ d)) := by
  have h' : Γ.σ.SameCycle d e := Orbit.mk_eq_mk.1 h.symm
  have := mem_orbitList.2 h'
  rw [j_orbitList_σ] at this
  simpa using this

theorem no_crossingOf_α_straight (e : D) :
    Γ.crossingOf (Γ.straight e) = Γ.crossingOf (Γ.α e) := by
  rw [j_straight_apply, j_crossingOf_σ, j_crossingOf_σ]

theorem no_mem_curves {S γ : Fin n} {x : Γ.Crossing} (hS : S ∈ Γ.curves x) (hγ : γ ∈ Γ.curves x)
    (hne : γ ≠ S) : Γ.curves x = {γ, S} := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  change S ∈ Γ.curves (Γ.crossingOf y) at hS
  change γ ∈ Γ.curves (Γ.crossingOf y) at hγ
  change Γ.curves (Γ.crossingOf y) = _
  rw [j_curves_crossingOf] at hS hγ ⊢
  simp only [mem_insert, mem_singleton] at hS hγ
  rcases hS with rfl | rfl <;> rcases hγ with rfl | rfl
  · exact absurd rfl hne
  · exact pair_comm _ _
  · rfl
  · exact absurd rfl hne

/-- At a crossing of `S`: the dart `s` of `S` is a sweep dart iff its cell has side `0`. -/
theorem no_sweep_iff {s : D} (hs : Γ.curve s = Γ.S) :
    Γ.IsSweepDart s ↔ Γ.side (Γ.cellOf s) = 0 := by
  have h : Γ.side (Γ.cellOf (Γ.α s)) = Γ.side (Γ.cellOf s) + 1 := by
    rw [← j_cellOf_σ, no_side_σ, if_pos hs]
  unfold IsSweepDart Up
  rw [h]
  rcases no_z2_cases (Γ.side (Γ.cellOf s)) with h0 | h0 <;> rw [h0] <;>
    simp only [hs, true_and] <;> decide

theorem no_side_σσ_of_S {s : D} (hs : Γ.curve s = Γ.S) :
    Γ.side (Γ.cellOf (Γ.σ (Γ.σ s))) = Γ.side (Γ.cellOf s) + 1 := by
  have h1 : Γ.curve (Γ.σ s) ≠ Γ.S := hs ▸ no_curve_σ_ne s
  rw [no_side_σ, if_neg h1, add_zero, no_side_σ, if_pos hs]

theorem no_sweep_unique {e e' : D} (he : Γ.IsSweepDart e) (he' : Γ.IsSweepDart e')
    (h : Γ.crossingOf e' = Γ.crossingOf e) : e' = e := by
  have h0 := (no_sweep_iff he.1).1 he
  rcases no_mem_crossing h with h1 | h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ he'.1 : Γ.curve (Γ.σ e) = Γ.S) (he.1 ▸ no_curve_σ_ne e)
  · have := (no_sweep_iff he'.1).1 he'
    rw [h1, no_side_σσ_of_S he.1, h0] at this
    exact absurd this (by decide)
  · have : Γ.curve (Γ.σ (Γ.σ (Γ.σ e))) = Γ.S := h1 ▸ he'.1
    rw [j_curve_σσ] at this
    exact absurd this (he.1 ▸ no_curve_σ_ne e)

theorem no_sweep_straight {e : D} (he : Γ.IsSweepDart e) : Γ.IsSweepDart (Γ.straight e) := by
  have hc : Γ.curve (Γ.straight e) = Γ.S := by rw [j_curve_straight]; exact he.1
  rw [no_sweep_iff hc, j_straight_apply]
  have h1 : Γ.curve (Γ.α e) = Γ.S := by rw [j_curve_α]; exact he.1
  rw [no_side_σσ_of_S h1]
  have h2 : Γ.side (Γ.cellOf (Γ.α e)) = 1 := he.2
  rw [h2]; decide

theorem no_above_σ {s : D} (hs : Γ.IsSweepDart s) : Γ.Above (Γ.σ s) :=
  ⟨hs.1 ▸ no_curve_σ_ne s, by unfold Up; rw [j_cellOf_σ]; exact hs.2⟩

/-- The dart of `S` before an above dart `y` at a crossing on `S` is a sweep dart. -/
theorem no_sweep_of_above {y : D} (hy : Γ.Above y) (hS : Γ.S ∈ Γ.curves (Γ.crossingOf y)) :
    Γ.IsSweepDart (Γ.σ (Γ.σ (Γ.σ y))) ∧ Γ.σ (Γ.σ (Γ.σ (Γ.σ y))) = y := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hS
  have hσ : Γ.curve (Γ.σ y) = Γ.S := by
    rcases hS with h | h
    · exact absurd h.symm hy.1
    · exact h.symm
  refine ⟨⟨by rw [j_curve_σσ]; exact hσ, ?_⟩, Γ.j_σ4 y⟩
  unfold Up
  rw [← j_cellOf_σ, Γ.j_σ4]
  exact hy.2

theorem no_onSweep {x : Γ.Crossing} (hx : Γ.OnSweep x) :
    ∃ s, Γ.IsSweepDart s ∧ Γ.crossingOf s = x := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Γ.S ∈ Γ.curves (Γ.crossingOf y) at hx
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hx
  obtain ⟨u, hu, hux⟩ : ∃ u, Γ.curve u = Γ.S ∧ Γ.crossingOf u = Γ.crossingOf y := by
    rcases hx with h | h
    · exact ⟨y, h.symm, rfl⟩
    · exact ⟨Γ.σ y, h.symm, j_crossingOf_σ _ _⟩
  rcases no_z2_cases (Γ.side (Γ.cellOf u)) with h0 | h0
  · exact ⟨u, (no_sweep_iff hu).2 h0, hux⟩
  · refine ⟨Γ.σ (Γ.σ u), (no_sweep_iff (by rw [j_curve_σσ]; exact hu)).2 ?_, ?_⟩
    · rw [no_side_σσ_of_S hu, h0]; decide
    · rw [j_crossingOf_σ, j_crossingOf_σ, hux]; rfl

theorem no_side_straight (y : D) :
    Γ.side (Γ.cellOf (Γ.straight y)) =
      Γ.side (Γ.cellOf y) + if Γ.curve (Γ.σ (Γ.α y)) = Γ.S then 1 else 0 := by
  rw [j_straight_apply, no_side_σ, j_cellOf_σ, j_α_α]

/-- The dart before `s` on its straight walk. -/
theorem no_pred {e s : D} (h : Γ.straight e = s) : Γ.α (Γ.σ (Γ.σ s)) = e := by
  rw [← h, j_straight_apply, Γ.j_σ4, j_α_α]

/-! ## Powers of `straight` -/

theorem no_pow_add (d : D) (a b : ℕ) :
    (Γ.straight ^ (a + b)) d = (Γ.straight ^ a) ((Γ.straight ^ b) d) := by
  rw [pow_add, Perm.mul_apply]

theorem no_pow_succ (d : D) (i : ℕ) :
    (Γ.straight ^ (i + 1)) d = Γ.straight ((Γ.straight ^ i) d) := by
  rw [pow_succ', Perm.mul_apply]

theorem no_pow_period (d : D) (a : ℕ) :
    (Γ.straight ^ (a + period Γ.straight d)) d = (Γ.straight ^ a) d := by
  rw [no_pow_add, Perm.coe_pow Γ.straight (period _ _), iterate_period]

theorem no_pow_inj {d : D} {i j : ℕ} (hi : i < period Γ.straight d)
    (hj : j < period Γ.straight d) (h : (Γ.straight ^ i) d = (Γ.straight ^ j) d) : i = j := by
  rw [period_eq_minimalPeriod] at hi hj
  rw [Perm.coe_pow, Perm.coe_pow] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

theorem no_exists_idx {d e : D} (h : Γ.straight.SameCycle d e) :
    ∃ k < period Γ.straight d, (Γ.straight ^ k) d = e := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨k, List.mem_range.1 hk, by rw [Perm.coe_pow]⟩

theorem no_period_pow (d : D) (i : ℕ) :
    period Γ.straight ((Γ.straight ^ i) d) = period Γ.straight d := by
  have hmem : d ∈ Function.periodicPts Γ.straight :=
    ⟨period _ d, period_pos _ d, iterate_period _ d⟩
  rw [period_eq_minimalPeriod, period_eq_minimalPeriod, Perm.coe_pow,
    Function.minimalPeriod_apply_iterate hmem]

theorem no_sweep_pow {d : D} (hd : Γ.IsSweepDart d) (i : ℕ) :
    Γ.IsSweepDart ((Γ.straight ^ i) d) := by
  induction i with
  | zero => exact hd
  | succ i ih => rw [no_pow_succ]; exact no_sweep_straight ih

theorem no_curve_pow (d : D) (i : ℕ) : Γ.curve ((Γ.straight ^ i) d) = Γ.curve d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [no_pow_succ, j_curve_straight, ih]

/-! ## The sweep cycle -/

variable (Γ) in
/-- The `t`-th sweep dart after the ∞-arc (`t = 0`: the dart starting at vertex `1`). -/
def noC (z : D) (t : ℕ) : D := (Γ.straight ^ t) ((Γ.straight ^ (Γ.infLen + 1)) z)

theorem no_noC_eq (z : D) (t : ℕ) :
    Γ.noC z t = (Γ.straight ^ (t + (Γ.infLen + 1))) z := (no_pow_add z _ _).symm

theorem no_mem_infArc {z : D} (hz : Γ.infStart = some z) {d : D} :
    d ∈ Γ.infArc ↔ ∃ i ≤ Γ.infLen, (Γ.straight ^ i) z = d := by
  unfold infArc arcOf
  rw [hz]
  simp only [Option.elim, mem_image, mem_range, Nat.lt_succ_iff]
  rfl

theorem no_infLen_le {z : D} (hz : Γ.infStart = some z) :
    Γ.infLen ≤ period Γ.straight z := Γ.infLen_le z hz

theorem no_z_sweep {z : D} (hz : Γ.infStart = some z) : Γ.IsSweepDart z :=
  Γ.infArc_sweep z ((no_mem_infArc hz).2 ⟨0, Nat.zero_le _, rfl⟩)

theorem no_arc_sweep {z : D} (hz : Γ.infStart = some z) {d : D} (hd : d ∈ Γ.infArc) :
    Γ.IsSweepDart d := by
  obtain ⟨i, -, rfl⟩ := (no_mem_infArc hz).1 hd
  exact no_sweep_pow (no_z_sweep hz) i

theorem no_noC_sweep {z : D} (hz : Γ.infStart = some z) (t : ℕ) : Γ.IsSweepDart (Γ.noC z t) :=
  no_sweep_pow (no_sweep_pow (no_z_sweep hz) _) _

theorem no_period_w (z : D) :
    period Γ.straight ((Γ.straight ^ (Γ.infLen + 1)) z) = period Γ.straight z :=
  no_period_pow z _

theorem no_noC_straight (z : D) (t : ℕ) : Γ.straight (Γ.noC z t) = Γ.noC z (t + 1) :=
  (no_pow_succ _ t).symm

theorem no_noC_period (z : D) : Γ.noC z (period Γ.straight z) = Γ.noC z 0 := by
  unfold noC
  rw [← no_period_w z, Perm.coe_pow Γ.straight (period _ _), iterate_period]
  rfl

theorem no_noC_inj' {z : D} {t t' : ℕ} (ht : t < period Γ.straight z)
    (ht' : t' < period Γ.straight z) (h : Γ.noC z t = Γ.noC z t') : t = t' := by
  rw [← no_period_w] at ht ht'
  exact no_pow_inj ht ht' h

theorem no_noC_inj {z : D} (hz : Γ.infStart = some z) {t t' : ℕ} (ht : t < period Γ.straight z)
    (ht' : t' < period Γ.straight z)
    (h : Γ.crossingOf (Γ.noC z t) = Γ.crossingOf (Γ.noC z t')) : t = t' :=
  no_noC_inj' ht ht' (no_sweep_unique (no_noC_sweep hz t') (no_noC_sweep hz t) h)

/-- Every sweep dart is in the straight cycle of `z`. -/
theorem no_sweep_all {z : D} (hz : Γ.infStart = some z) {e : D} (he : Γ.IsSweepDart e) :
    ∃ j < period Γ.straight z, (Γ.straight ^ j) z = e := by
  have hzs := no_z_sweep hz
  rcases Γ.isSConf.straight z e (hzs.1.trans he.1.symm) with h | h
  · exact no_exists_idx h
  · obtain ⟨j, -, hj⟩ := no_exists_idx (d := z) h
    have hs : Γ.IsSweepDart (Γ.σ (Γ.σ e)) := hj ▸ no_sweep_pow hzs j
    have := no_sweep_unique he hs (by rw [j_crossingOf_σ, j_crossingOf_σ])
    exact absurd this (Γ.j_σσ_ne e)

theorem no_noC_surj {z : D} (hz : Γ.infStart = some z) {e : D} (he : Γ.IsSweepDart e) :
    ∃ t < period Γ.straight z, Γ.noC z t = e := by
  obtain ⟨j, hj, rfl⟩ := no_sweep_all hz he
  have hk := no_infLen_le hz
  set P := period Γ.straight z
  by_cases h1 : Γ.infLen + 1 ≤ j
  · refine ⟨j - (Γ.infLen + 1), by omega, ?_⟩
    rw [no_noC_eq, Nat.sub_add_cancel h1]
  by_cases h2 : Γ.infLen + 1 ≤ j + P
  · refine ⟨j + P - (Γ.infLen + 1), by omega, ?_⟩
    rw [no_noC_eq, Nat.sub_add_cancel h2, no_pow_period]
  · refine ⟨j + P + P - (Γ.infLen + 1), by omega, ?_⟩
    rw [no_noC_eq, Nat.sub_add_cancel (by omega), no_pow_period, no_pow_period]

theorem no_noC_pos {z : D} (hz : Γ.infStart = some z) {t : ℕ} (ht : t < period Γ.straight z) :
    Γ.pos (Γ.crossingOf (Γ.noC z t)) = t + 1 := by
  unfold pos
  rw [hz]
  simp only [Option.elim]
  rw [add_comm]
  congr 1
  have hlen : t < (orbitList Γ.straight ((Γ.straight ^ (Γ.infLen + 1)) z)).length := by
    rw [orbitList, List.length_map, List.length_range, no_period_w]; exact ht
  rw [List.findIdx_eq hlen]
  simp only [orbitList, List.getElem_map, List.getElem_range, decide_eq_true_eq,
    decide_eq_false_iff_not]
  refine ⟨by rw [← Perm.coe_pow]; rfl, fun j hj => ?_⟩
  rw [← Perm.coe_pow]
  intro h
  have := no_noC_inj hz (by omega) ht (h : Γ.crossingOf (Γ.noC z j) = _)
  omega

theorem no_noC_inner {z : D} (hz : Γ.infStart = some z) {t : ℕ} (ht : t < period Γ.straight z) :
    Γ.IsInfVertex (Γ.crossingOf (Γ.noC z t)) ↔ period Γ.straight z ≤ t + Γ.infLen := by
  have hk := no_infLen_le hz
  set P := period Γ.straight z
  constructor
  · rintro ⟨z', hz', i, hi, hx⟩
    rw [hz, Option.mem_def, Option.some_inj] at hz'
    subst hz'
    rw [← no_crossingOf_α_straight, ← no_pow_succ] at hx
    have he := no_sweep_unique (no_noC_sweep hz t) (no_sweep_pow (no_z_sweep hz) (i + 1)) hx
    rw [no_noC_eq] at he
    by_contra hlt
    push Not at hlt
    by_cases h1 : t + (Γ.infLen + 1) < P
    · have := no_pow_inj (by omega) h1 he
      omega
    · have h2 : t + (Γ.infLen + 1) = 0 + P := by omega
      rw [h2, no_pow_period] at he
      have := no_pow_inj (by omega) (period_pos _ _) he
      omega
  · intro h
    refine ⟨z, by rw [hz]; rfl, t + Γ.infLen - P, by omega, ?_⟩
    rw [← no_crossingOf_α_straight, ← no_pow_succ, no_noC_eq,
      show t + (Γ.infLen + 1) = (t + Γ.infLen - P + 1) + P by omega, no_pow_period]

theorem no_noC_arc {z : D} (hz : Γ.infStart = some z) {t : ℕ} (ht : t < period Γ.straight z) :
    Γ.noC z t ∈ Γ.infArc ↔ period Γ.straight z ≤ t + Γ.infLen + 1 := by
  have hk := no_infLen_le hz
  set P := period Γ.straight z
  rw [no_mem_infArc hz]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [no_noC_eq] at he
    by_contra hlt
    push Not at hlt
    have := no_pow_inj (by omega) (by omega) he
    omega
  · intro h
    refine ⟨t + Γ.infLen + 1 - P, by omega, ?_⟩
    rw [no_noC_eq, show t + (Γ.infLen + 1) = (t + Γ.infLen + 1 - P) + P by omega, no_pow_period]

/-! ## Vertices on the sweep and their positions -/

theorem no_onSweep_noC {z : D} (hz : Γ.infStart = some z) {x : Γ.Crossing} (hx : Γ.OnSweep x) :
    ∃ t < period Γ.straight z, Γ.crossingOf (Γ.noC z t) = x := by
  obtain ⟨s, hs, rfl⟩ := no_onSweep hx
  obtain ⟨t, ht, rfl⟩ := no_noC_surj hz hs
  exact ⟨t, ht, rfl⟩

theorem no_S_mem_noC {z : D} (hz : Γ.infStart = some z) (t : ℕ) :
    Γ.OnSweep (Γ.crossingOf (Γ.noC z t)) := by
  change Γ.S ∈ Γ.curves _
  rw [j_curves_crossingOf, ← (no_noC_sweep hz t).1]
  exact mem_insert_self _ _

theorem no_noC_fin {z : D} (hz : Γ.infStart = some z) {t : ℕ} (ht : t < period Γ.straight z) :
    Γ.IsFinVertex (Γ.crossingOf (Γ.noC z t)) ↔ t + Γ.infLen < period Γ.straight z := by
  unfold IsFinVertex
  rw [no_noC_inner hz ht]
  simp only [no_S_mem_noC hz t, true_and, not_le]

theorem no_mem_sweepEnds {z : D} (hz : Γ.infStart = some z) {γ : Fin n} {p : ℕ} :
    p ∈ Γ.sweepEnds γ ↔ ∃ t, t + Γ.infLen < period Γ.straight z ∧ p = t + 1 ∧
      γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) := by
  classical
  unfold sweepEnds
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨hxf, hxγ⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := no_onSweep_noC hz hxf.1
    exact ⟨t, (no_noC_fin hz ht).1 hxf, no_noC_pos hz ht, hxγ⟩
  · rintro ⟨t, ht, rfl, hγ⟩
    exact ⟨_, ⟨(no_noC_fin hz (by omega)).2 ht, hγ⟩, no_noC_pos hz (by omega)⟩

/-- A loop other than `S` meets `S` only at vertices on the sweep. -/
theorem no_loop_fin {γ : Fin n} (hγ : Γ.IsLoop γ) (hS : γ ≠ Γ.S) {x : Γ.Crossing}
    (hx : Γ.OnSweep x) (hxγ : γ ∈ Γ.curves x) : Γ.IsFinVertex x := by
  classical
  set F := univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)
  set G := univ.filter (fun x : Γ.Crossing => Γ.curves x = {γ, Γ.S})
  have hF : F.card = 2 := hγ
  have hFG : F ⊆ G := by
    intro y hy
    obtain ⟨hyf, hyγ⟩ := (mem_filter.1 hy).2
    exact mem_filter.2 ⟨mem_univ _, no_mem_curves hyf.1 hyγ hS⟩
  have hG : G.card = 2 := by
    have hc : G.card = 0 ∨ G.card = 2 := by convert card_sweep_crossings γ hS
    rcases hc with h | h
    · have := card_le_card hFG; omega
    · exact h
  have hEq : F = G := eq_of_subset_of_card_le hFG (by omega)
  have : x ∈ G := mem_filter.2 ⟨mem_univ _, no_mem_curves hx hxγ hS⟩
  rw [← hEq] at this
  exact (mem_filter.1 this).2.1


/-! ## The upper arc of a loop -/

/-- The two directions of a curve are different straight walks (copy of the private
`j_not_sameCycle_straight_σσ`, `Pca/Sweep/Jordan.lean`). -/
theorem no_not_sameCycle_straight_σσ (d : D) :
    ¬ Γ.straight.SameCycle d (Γ.σ (Γ.σ d)) := by
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

/-- A walk above the sweep cannot enter a dart that starts on `S`. -/
theorem no_enter {a y : D} (ha : Γ.Above a) (hS : Γ.S ∈ Γ.curves (Γ.crossingOf a))
    (hy : Γ.Above y) (h : Γ.straight y = a) : False := by
  have hc : Γ.curve (Γ.α y) = Γ.curve a := by rw [← h, j_curve_straight, j_curve_α]
  have hx : Γ.crossingOf (Γ.α y) = Γ.crossingOf a := by rw [← h, no_crossingOf_α_straight]
  rw [← hx, j_curves_crossingOf, mem_insert, mem_singleton] at hS
  have hσ : Γ.curve (Γ.σ (Γ.α y)) = Γ.S := by
    rcases hS with h' | h'
    · exact absurd (h'.trans hc).symm ha.1
    · exact h'.symm
  have h1 := no_side_straight (Γ := Γ) y
  have e1 : Γ.side (Γ.cellOf a) = 1 := ha.2
  have e2 : Γ.side (Γ.cellOf y) = 1 := hy.2
  rw [if_pos hσ, h, e1, e2] at h1
  exact absurd h1 (by decide)

/-- A walk above the sweep cannot leave through a crossing on `S`. -/
theorem no_exit {y : D} (hy : Γ.Above y) (hS : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α y))) :
    ¬ Γ.Above (Γ.straight y) := by
  intro h
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hS
  have hσ : Γ.curve (Γ.σ (Γ.α y)) = Γ.S := by
    rcases hS with h' | h'
    · rw [j_curve_α] at h'; exact absurd h'.symm hy.1
    · exact h'.symm
  have h1 := no_side_straight (Γ := Γ) y
  have e1 : Γ.side (Γ.cellOf (Γ.straight y)) = 1 := h.2
  have e2 : Γ.side (Γ.cellOf y) = 1 := hy.2
  rw [if_pos hσ, e1, e2] at h1
  exact absurd h1 (by decide)

theorem no_upperWalk_to {a e : D} (ha : Γ.Above a) (hS : Γ.S ∈ Γ.curves (Γ.crossingOf a))
    (h : Γ.UpperWalk e a) : e = a := by
  obtain ⟨k, hk, hka⟩ := h
  cases k with
  | zero => exact hka
  | succ k =>
    exact (no_enter ha hS (hk k (Nat.le_succ k)) (by rw [← no_pow_succ]; exact hka)).elim

/-- **The upper arc of a loop**: `a` starts at a crossing with `S`, `b` at another one, both
above `S` on the same curve. Then walking straight from `a` stays above `S` until it arrives at
`b` (as `α b`), and every dart of the curve above `S` is on this walk (in one of its two
directions). -/
theorem no_upper_arc {a b : D} (ha : Γ.Above a) (hb : Γ.Above b) (hab : Γ.curve a = Γ.curve b)
    (haS : Γ.S ∈ Γ.curves (Γ.crossingOf a)) (hbS : Γ.S ∈ Γ.curves (Γ.crossingOf b))
    (hne : Γ.crossingOf a ≠ Γ.crossingOf b) :
    ∃ L, (∀ q ≤ L, Γ.Above ((Γ.straight ^ q) a)) ∧ (Γ.straight ^ L) a = Γ.α b ∧
      L < period Γ.straight a ∧
      (∀ q < L, ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)))) ∧
      ∀ y, Γ.Above y → Γ.curve y = Γ.curve a →
        ∃ q ≤ L, (Γ.straight ^ q) a = y ∨ (Γ.straight ^ q) a = Γ.α y := by
  have hbα : Γ.crossingOf (Γ.α (Γ.α b)) = Γ.crossingOf b := by rw [j_α_α]
  have hAα : ∀ {y}, Γ.Above y → Γ.Above (Γ.α y) := fun {y} hy =>
    ⟨by rw [j_curve_α]; exact hy.1, by unfold Up; rw [no_side_α hy.1]; exact hy.2⟩
  -- the walk from `a` to `α b`
  obtain ⟨L, hall, hL⟩ : Γ.UpperWalk a (Γ.α b) := by
    rcases upper_arc ha hb hab with h | h | h | h
    · exfalso
      obtain ⟨k, hk, hkb⟩ := h
      cases k with
      | zero => exact hne (congrArg _ hkb)
      | succ k =>
        exact no_enter hb hbS (hk k (Nat.le_succ k)) (by rw [← no_pow_succ]; exact hkb)
    · exact absurd (congrArg Γ.crossingOf (no_upperWalk_to ha haS h)).symm hne
    · exact h
    · have := no_upperWalk_to ha haS h
      exact ⟨0, fun q hq => by rw [Nat.le_zero.1 hq]; exact ha, this.symm⟩
  -- a walk from `a` does not get past `α b`
  have hbound : ∀ v k, (∀ i ≤ k, Γ.Above ((Γ.straight ^ i) a)) → (Γ.straight ^ k) a = v →
      k ≤ L := by
    intro v k hk _
    by_contra hlt
    push Not at hlt
    have h1 := hk (L + 1) hlt
    rw [no_pow_succ, hL] at h1
    exact no_exit (hAα hb) (by rw [hbα]; exact hbS) h1
  refine ⟨L, hall, hL, ?_, ?_, ?_⟩
  · by_contra hle
    push Not at hle
    have hp := period_pos Γ.straight a
    have h1 := hall (period Γ.straight a - 1) (by omega)
    apply no_enter ha haS h1
    rw [← no_pow_succ, Nat.sub_add_cancel hp, Perm.coe_pow, iterate_period]
  · intro q hq hS
    have h1 := hall (q + 1) hq
    rw [no_pow_succ] at h1
    exact no_exit (hall q hq.le) hS h1
  · intro y hy hya
    rcases upper_arc ha hy hya.symm with h | h | h | h
    · obtain ⟨k, hk, hky⟩ := h
      exact ⟨k, hbound y k hk hky, Or.inl hky⟩
    · exact ⟨0, Nat.zero_le _, Or.inl (no_upperWalk_to ha haS h).symm⟩
    · obtain ⟨k, hk, hky⟩ := h
      exact ⟨k, hbound _ k hk hky, Or.inr hky⟩
    · exact ⟨0, Nat.zero_le _, Or.inr (no_upperWalk_to ha haS h).symm⟩

/-! ## Walks against a cut -/

section Walk

variable {r : Γ.Cell → ZMod 2} {f : D → ZMod 2}

theorem no_corner {r : Γ.Cell → ZMod 2} {f : D → ZMod 2}
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = f y) (y : D) :
    r (Γ.cellOf y) + r (Γ.cellOf (Γ.σ y)) = f y := by
  rw [j_cellOf_σ]; exact hr y

/-- Along the upper side of `S`: from the cell above `e` to the cell above `straight e`, across
the segment of `σ (straight e)`. -/
theorem no_walk_sweep (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = f y) (e : D) :
    r (Γ.cellOf (Γ.α (Γ.straight e))) =
      r (Γ.cellOf (Γ.α e)) + f (Γ.σ (Γ.straight e)) := by
  set s := Γ.straight e
  have h1 : Γ.α e = Γ.σ (Γ.σ s) := by rw [← no_pred (rfl : Γ.straight e = s), j_α_α]
  have h2 := no_corner hr (Γ.σ s)
  rw [← j_cellOf_σ, h1, ← h2, add_comm (r (Γ.cellOf (Γ.σ s))), ← add_assoc,
    j_zmod2_add_self, zero_add]

/-- Along a curve: from the cell of `y` to the cell of `straight y`, across the segment of
`σ (α y)`. -/
theorem no_walk_straight (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = f y) (y : D) :
    r (Γ.cellOf (Γ.straight y)) = r (Γ.cellOf y) + f (Γ.σ (Γ.α y)) := by
  have h := no_corner hr (Γ.σ (Γ.α y))
  rw [j_cellOf_σ, j_α_α] at h
  rw [j_straight_apply]
  exact j_zmod2_eq_add_of_add_eq h

/-- Around a crossing, the cut changes an even number of times. -/
theorem no_corner_sum (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = f y) (y : D) :
    f y + f (Γ.σ y) + f (Γ.σ (Γ.σ y)) + f (Γ.σ (Γ.σ (Γ.σ y))) = 0 := by
  have h1 := no_corner hr y
  have h2 := no_corner hr (Γ.σ y)
  have h3 := no_corner hr (Γ.σ (Γ.σ y))
  have h4 := no_corner hr (Γ.σ (Γ.σ (Γ.σ y)))
  rw [Γ.j_σ4] at h4
  rw [← h1, ← h2, ← h3, ← h4]
  exact j_zmod2_cycle _ _ _ _

end Walk

end SConf

end Pca.Sweep
