/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Helpers for package L (`Pca/Sweep/Lower.lean`): local facts of one sweep configuration

The upper side seen from one configuration: sides around a crossing, the unique dart of `S` above
the sweep at a crossing on `S`, and counting crossings by darts.
-/
import Pca.Sweep.J_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

omit [Fintype D] [DecidableEq D] in
theorem ld_perm_apply_inv (f : Perm D) (x : D) : f (f⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

variable (Γ : SConf n D)

/-! ## Sides -/

theorem ld_z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem ld_side_σ (y : D) : Γ.side (Γ.cellOf (Γ.σ y)) =
    Γ.side (Γ.cellOf y) + if Γ.curve y = Γ.S then 1 else 0 := by
  rw [j_cellOf_σ]
  exact j_zmod2_eq_add_of_add_eq (Γ.isSide y)

theorem ld_up_σ_iff {y : D} (hy : Γ.curve y ≠ Γ.S) :
    Γ.Up (Γ.cellOf (Γ.σ y)) ↔ Γ.Up (Γ.cellOf y) := by
  unfold Up; rw [ld_side_σ, if_neg hy, add_zero]

theorem ld_up_σ_S {y : D} (hy : Γ.curve y = Γ.S) :
    Γ.Up (Γ.cellOf (Γ.σ y)) ↔ ¬ Γ.Up (Γ.cellOf y) := by
  unfold Up; rw [ld_side_σ, if_pos hy]
  rcases ld_z2_cases (Γ.side (Γ.cellOf y)) with h | h <;> rw [h] <;> decide

theorem ld_up_α_iff {y : D} (hy : Γ.curve y ≠ Γ.S) :
    Γ.Up (Γ.cellOf (Γ.α y)) ↔ Γ.Up (Γ.cellOf y) := by
  rw [← j_cellOf_σ]; exact Γ.ld_up_σ_iff hy

theorem ld_cellOf_pow (k : ℕ) (y : D) : Γ.cellOf ((Γ.φ ^ k) y) = Γ.cellOf y := by
  rw [cellOf, cellOf, Orbit.mk_eq_mk]
  exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm

theorem ld_cellOf_φinv (y : D) : Γ.cellOf (Γ.φ⁻¹ y) = Γ.cellOf y := by
  conv_rhs => rw [← ld_perm_apply_inv Γ.φ y, j_cellOf_φ]

theorem ld_σinv_eq (y : D) : Γ.σ⁻¹ y = Γ.σ (Γ.σ (Γ.σ y)) := by
  rw [Perm.inv_eq_iff_eq, Γ.j_σ4]

theorem ld_φinv_apply (y : D) : Γ.φ⁻¹ y = Γ.α (Γ.σ⁻¹ y) := by
  rw [Perm.inv_eq_iff_eq, j_φ_apply, j_α_α, ld_perm_apply_inv]

theorem ld_σ_σinv (y : D) : Γ.σ (Γ.σ⁻¹ y) = y := ld_perm_apply_inv _ _

theorem ld_curve_σinv_ne {b : D} (hb : Γ.curve b = Γ.S) : Γ.curve (Γ.σ⁻¹ b) ≠ Γ.S := by
  intro h
  have := Γ.isSConf.curve_σ (Γ.σ⁻¹ b)
  rw [ld_σ_σinv, hb, h] at this
  exact this rfl

/-- Above `S` at a dart `b` of `S`: the dart before `b` at its crossing is above `S` too. -/
theorem ld_up_σinv {b : D} (hb : Γ.curve b = Γ.S) (hu : Γ.Up (Γ.cellOf b)) :
    Γ.Up (Γ.cellOf (Γ.σ⁻¹ b)) := by
  rw [← Γ.ld_up_σ_iff (Γ.ld_curve_σinv_ne hb), ld_σ_σinv]; exact hu

/-! ## Crossings -/

theorem ld_crossingOf_σinv (y : D) : Γ.crossingOf (Γ.σ⁻¹ y) = Γ.crossingOf y := by
  conv_rhs => rw [← Γ.ld_σ_σinv y, j_crossingOf_σ]

theorem ld_mem_crossing {d e : D} (h : Γ.crossingOf e = Γ.crossingOf d) :
    e = d ∨ e = Γ.σ d ∨ e = Γ.σ (Γ.σ d) ∨ e = Γ.σ (Γ.σ (Γ.σ d)) := by
  have h' : Γ.σ.SameCycle d e := Orbit.mk_eq_mk.1 h.symm
  have := mem_orbitList.2 h'
  rw [j_orbitList_σ] at this
  simpa using this

/-- A crossing on `S` has exactly one dart of `S` above `S` (uniqueness). -/
theorem ld_upS_unique {b b' : D} (hb : Γ.curve b = Γ.S) (hu : Γ.Up (Γ.cellOf b))
    (hb' : Γ.curve b' = Γ.S) (hu' : Γ.Up (Γ.cellOf b')) (h : Γ.crossingOf b' = Γ.crossingOf b) :
    b' = b := by
  have h1 : Γ.curve (Γ.σ b) ≠ Γ.S := hb ▸ Γ.isSConf.curve_σ b
  rcases Γ.ld_mem_crossing h with h2 | h2 | h2 | h2
  · exact h2
  · exact absurd (h2 ▸ hb') h1
  · rw [h2, Γ.ld_up_σ_iff h1, Γ.ld_up_σ_S hb] at hu'
    exact absurd hu hu'
  · rw [h2, j_curve_σσ] at hb'
    exact absurd hb' h1

/-- A crossing on `S` has a dart of `S` above `S` (existence). -/
theorem ld_exists_upS {x : Γ.Crossing} (hx : Γ.OnSweep x) :
    ∃ b, Γ.curve b = Γ.S ∧ Γ.Up (Γ.cellOf b) ∧ Γ.crossingOf b = x := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Γ.S ∈ Γ.curves (Γ.crossingOf y) at hx
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hx
  obtain ⟨s, hs, hsx⟩ : ∃ s, Γ.curve s = Γ.S ∧ Γ.crossingOf s = Γ.crossingOf y := by
    rcases hx with h | h
    · exact ⟨y, h.symm, rfl⟩
    · exact ⟨Γ.σ y, h.symm, j_crossingOf_σ _ _⟩
  by_cases hu : Γ.Up (Γ.cellOf s)
  · exact ⟨s, hs, hu, hsx⟩
  · have h1 : Γ.curve (Γ.σ s) ≠ Γ.S := hs ▸ Γ.isSConf.curve_σ s
    refine ⟨Γ.σ (Γ.σ s), by rw [j_curve_σσ]; exact hs, ?_, ?_⟩
    · rw [Γ.ld_up_σ_iff h1, Γ.ld_up_σ_S hs]; exact hu
    · rw [j_crossingOf_σ, j_crossingOf_σ, hsx]; rfl

/-- The curves at the crossing of a dart `b` of `S`. -/
theorem ld_curves_S {b : D} (hb : Γ.curve b = Γ.S) :
    Γ.curves (Γ.crossingOf b) = {Γ.curve (Γ.σ⁻¹ b), Γ.S} := by
  rw [← Γ.ld_crossingOf_σinv b, j_curves_crossingOf, ld_σ_σinv, hb]

theorem ld_onCurve_S {b : D} (hb : Γ.curve b = Γ.S) (γ : Fin n) :
    Γ.OnCurve γ (Γ.crossingOf b) ↔ γ = Γ.S ∨ γ = Γ.curve (Γ.σ⁻¹ b) := by
  unfold OnCurve
  rw [Γ.ld_curves_S hb, mem_insert, mem_singleton]
  exact or_comm

theorem ld_onSweep_S {b : D} (hb : Γ.curve b = Γ.S) : Γ.OnSweep (Γ.crossingOf b) := by
  unfold OnSweep; rw [Γ.ld_curves_S hb]; simp

/-- The darts of the ∞-arc are darts of `S` with the upper side on their left. -/
theorem ld_arc {z : D} (hz : z ∈ Γ.infStart) {i : ℕ} (hi : i ≤ Γ.infLen) :
    Γ.curve (Γ.α ((Γ.straight ^ i) z)) = Γ.S ∧ Γ.Up (Γ.cellOf (Γ.α ((Γ.straight ^ i) z))) := by
  have hm : (Γ.straight ^ i) z ∈ Γ.infArc := by
    rw [Option.mem_def] at hz
    simp only [infArc, arcOf, hz, Option.elim, mem_image, mem_range]
    exact ⟨i, by omega, rfl⟩
  obtain ⟨h1, h2⟩ := Γ.infArc_sweep _ hm
  exact ⟨by rw [j_curve_α]; exact h1, h2⟩

/-- `b` (a dart of `S` above `S`) is at an inner crossing of the ∞-arc. -/
def ldInfB (b : D) : Prop :=
  ∃ z ∈ Γ.infStart, ∃ i < Γ.infLen, Γ.α ((Γ.straight ^ i) z) = b

theorem ld_infVertex_iff {b : D} (hb : Γ.curve b = Γ.S) (hu : Γ.Up (Γ.cellOf b)) :
    Γ.IsInfVertex (Γ.crossingOf b) ↔ Γ.ldInfB b := by
  constructor
  · rintro ⟨z, hz, i, hi, hx⟩
    obtain ⟨h1, h2⟩ := Γ.ld_arc hz hi.le
    exact ⟨z, hz, i, hi, Γ.ld_upS_unique hb hu h1 h2 hx⟩
  · rintro ⟨z, hz, i, hi, rfl⟩
    exact ⟨z, hz, i, hi, rfl⟩

theorem ld_finVertex_iff {b : D} (hb : Γ.curve b = Γ.S) (hu : Γ.Up (Γ.cellOf b)) :
    Γ.IsFinVertex (Γ.crossingOf b) ↔ ¬ Γ.ldInfB b := by
  unfold IsFinVertex
  rw [Γ.ld_infVertex_iff hb hu]
  exact ⟨fun h => h.2, fun h => ⟨Γ.ld_onSweep_S hb, h⟩⟩

theorem ld_onSweep_of_finVertex {x : Γ.Crossing} (hx : Γ.IsFinVertex x) : Γ.OnSweep x := hx.1

theorem ld_onSweep_of_infVertex {x : Γ.Crossing} (hx : Γ.IsInfVertex x) : Γ.OnSweep x := by
  obtain ⟨z, hz, i, hi, rfl⟩ := hx
  exact Γ.ld_onSweep_S (Γ.ld_arc hz hi.le).1

/-- A vertex above the sweep, seen from any of its darts. -/
theorem ld_aboveVertex_iff (d : D) : Γ.IsAboveVertex (Γ.crossingOf d) ↔
    Γ.Up (Γ.cellOf d) ∧ Γ.curve d ≠ Γ.S ∧ Γ.curve (Γ.σ d) ≠ Γ.S := by
  unfold IsAboveVertex OnSweep
  rw [j_curves_crossingOf, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨⟨h1, h2⟩, e, he, hA⟩
    have h1' : Γ.curve d ≠ Γ.S := fun h => h1 h.symm
    have h2' : Γ.curve (Γ.σ d) ≠ Γ.S := fun h => h2 h.symm
    have h3 : Γ.curve (Γ.σ (Γ.σ d)) ≠ Γ.S := by rw [j_curve_σσ]; exact h1'
    refine ⟨?_, h1', h2'⟩
    rcases Γ.ld_mem_crossing (Orbit.mem_darts.1 he) with rfl | rfl | rfl | rfl
    · exact hA.2
    · exact (Γ.ld_up_σ_iff h1').1 hA.2
    · exact (Γ.ld_up_σ_iff h1').1 ((Γ.ld_up_σ_iff h2').1 hA.2)
    · exact (Γ.ld_up_σ_iff h1').1 ((Γ.ld_up_σ_iff h2').1 ((Γ.ld_up_σ_iff h3).1 hA.2))
  · rintro ⟨hu, h1, h2⟩
    exact ⟨⟨fun h => h1 h.symm, fun h => h2 h.symm⟩, d, Orbit.mem_darts.2 rfl, h1, hu⟩

/-! ## Counting crossings by darts -/

theorem ld_card_crossings (R : D → Prop) [DecidablePred R] (Q : Γ.Crossing → Prop)
    [DecidablePred Q] (k : ℕ) (h : ∀ x, Q x → (x.darts.filter R).card = k) :
    (univ.filter (fun d => R d ∧ Q (Γ.crossingOf d))).card = k * (univ.filter Q).card := by
  rw [card_filter_eq_sum_orbits Γ.σ, card_eq_sum_ones, mul_sum, ← sum_filter_add_sum_filter_not
    univ Q]
  have h0 : ∑ x ∈ univ.filter (fun x => ¬ Q x),
      (x.darts.filter (fun d => R d ∧ Q (Γ.crossingOf d))).card = 0 := by
    refine sum_eq_zero fun x hx => ?_
    rw [card_eq_zero, filter_eq_empty_iff]
    intro d hd hRQ
    rw [mem_filter] at hx
    have : Γ.crossingOf d = x := Orbit.mem_darts.1 hd
    exact hx.2 (this ▸ hRQ.2)
  rw [h0, add_zero]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_filter] at hx
  rw [mul_one, ← h x hx.2]
  congr 1
  refine filter_congr fun d hd => ?_
  have : Γ.crossingOf d = x := Orbit.mem_darts.1 hd
  rw [this]
  exact ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩

/-- Crossings on `S` are counted by their darts of `S` above `S`. -/
theorem ld_card_onSweep (Q : Γ.Crossing → Prop) [DecidablePred Q] (hQ : ∀ x, Q x → Γ.OnSweep x) :
    (univ.filter Q).card = (univ.filter (fun d => (Γ.curve d = Γ.S ∧ Γ.Up (Γ.cellOf d)) ∧
      Q (Γ.crossingOf d))).card := by
  rw [Γ.ld_card_crossings _ Q 1, one_mul]
  intro x hx
  obtain ⟨b, hb, hu, rfl⟩ := Γ.ld_exists_upS (hQ x hx)
  rw [card_eq_one]
  refine ⟨b, ?_⟩
  ext e
  simp only [mem_filter, mem_singleton, Orbit.mem_darts]
  constructor
  · rintro ⟨he, hS, hU⟩
    exact Γ.ld_upS_unique hb hu hS hU he
  · rintro rfl
    exact ⟨rfl, hb, hu⟩

/-- Crossings on `S` (as a predicate on darts above `S`). -/
theorem ld_card_onSweep' (Q : Γ.Crossing → Prop) [DecidablePred Q]
    (hQ : ∀ x, Q x → Γ.OnSweep x) :
    (univ.filter Q).card = (univ.filter (fun d => Γ.Up (Γ.cellOf d) ∧
      (Γ.curve d = Γ.S ∧ Q (Γ.crossingOf d)))).card := by
  rw [Γ.ld_card_onSweep Q hQ]
  congr 1
  exact filter_congr fun d _ => ⟨fun h => ⟨h.1.2, h.1.1, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2.2⟩⟩

/-- Every crossing has four darts. -/
theorem ld_card_all (Q : Γ.Crossing → Prop) [DecidablePred Q] :
    4 * (univ.filter Q).card = (univ.filter (fun d => True ∧ Q (Γ.crossingOf d))).card := by
  rw [Γ.ld_card_crossings (fun _ => True) Q 4]
  intro x _
  obtain ⟨y, rfl⟩ := x.exists_mk
  rw [filter_true_of_mem (fun _ _ => trivial), Orbit.darts_mk]
  exact Γ.isSConf.card_crossing y

open Classical in
/-- The vertices above the sweep, counted four times by their darts. -/
theorem ld_card_above :
    4 * (univ.filter Γ.IsAboveVertex).card = (univ.filter (fun d => Γ.Up (Γ.cellOf d) ∧
      (Γ.curve d ≠ Γ.S ∧ Γ.curve (Γ.σ d) ≠ Γ.S))).card := by
  classical
  rw [Γ.ld_card_all]
  congr 1
  exact filter_congr fun d _ => by
    rw [Γ.ld_aboveVertex_iff d]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

open Classical in
theorem ld_numVertices :
    4 * Γ.numVertices = 4 * (univ.filter (fun d => Γ.Up (Γ.cellOf d) ∧
      (Γ.curve d = Γ.S ∧ Γ.IsFinVertex (Γ.crossingOf d)))).card +
      (univ.filter (fun d => Γ.Up (Γ.cellOf d) ∧
        (Γ.curve d ≠ Γ.S ∧ Γ.curve (Γ.σ d) ≠ Γ.S))).card := by
  classical
  unfold numVertices
  rw [filter_or, card_union_of_disjoint, mul_add, ← Γ.ld_card_above,
    Γ.ld_card_onSweep' _ (fun x hx => hx.1)]
  rw [disjoint_filter]
  intro x _ hF hA
  exact hA.1 hF.1

/-! ## The notions of SH section 2 through darts above `S` -/

theorem ld_meetsSweep_iff (γ : Fin n) : Γ.MeetsSweep γ ↔ ∃ d, Γ.Up (Γ.cellOf d) ∧
    (Γ.curve d = Γ.S ∧ Γ.IsFinVertex (Γ.crossingOf d) ∧ Γ.OnCurve γ (Γ.crossingOf d)) := by
  constructor
  · rintro ⟨x, hF, hO⟩
    obtain ⟨b, hb, hu, rfl⟩ := Γ.ld_exists_upS hF.1
    exact ⟨b, hu, hb, hF, hO⟩
  · rintro ⟨d, -, -, hF, hO⟩
    exact ⟨_, hF, hO⟩

theorem ld_infOn_iff (γ : Fin n) : (∃ x, Γ.IsInfVertex x ∧ Γ.OnCurve γ x) ↔ ∃ d,
    Γ.Up (Γ.cellOf d) ∧ (Γ.curve d = Γ.S ∧ Γ.ldInfB d ∧ Γ.OnCurve γ (Γ.crossingOf d)) := by
  constructor
  · rintro ⟨x, hI, hO⟩
    obtain ⟨b, hb, hu, rfl⟩ := Γ.ld_exists_upS (Γ.ld_onSweep_of_infVertex hI)
    exact ⟨b, hu, hb, (Γ.ld_infVertex_iff hb hu).1 hI, hO⟩
  · rintro ⟨d, hu, hb, hI, hO⟩
    exact ⟨_, (Γ.ld_infVertex_iff hb hu).2 hI, hO⟩

theorem ld_present_iff (γ : Fin n) : Γ.Present γ ↔
    γ ≠ Γ.S ∧ ∃ d, Γ.Up (Γ.cellOf d) ∧ (Γ.curve d = γ ∧ Γ.curve d ≠ Γ.S) := by
  unfold Present Above
  exact and_congr_right fun _ =>
    ⟨fun ⟨d, h1, h2, h3⟩ => ⟨d, h3, h1, h2⟩, fun ⟨d, h3, h1, h2⟩ => ⟨d, h1, h2, h3⟩⟩

theorem ld_noAbove_iff : (∀ x, ¬ Γ.IsAboveVertex x) ↔
    ¬ ∃ d, Γ.Up (Γ.cellOf d) ∧ (Γ.curve d ≠ Γ.S ∧ Γ.curve (Γ.σ d) ≠ Γ.S) := by
  constructor
  · rintro h ⟨d, hd⟩
    exact h _ ((Γ.ld_aboveVertex_iff d).2 hd)
  · intro h x hx
    obtain ⟨d, rfl⟩ := x.exists_mk
    exact h ⟨d, (Γ.ld_aboveVertex_iff d).1 hx⟩

theorem ld_emptyCell_iff (k : ℕ) : (∃ d, Γ.IsFinSeg d ∧ (Γ.upperCell d).size = k) ↔
    ∃ b, Γ.Up (Γ.cellOf b) ∧
      (Γ.curve b = Γ.S ∧ Γ.α b ∉ Γ.infArc ∧ (Γ.cellOf b).size = k) := by
  constructor
  · rintro ⟨d, ⟨⟨hS, hU⟩, hA⟩, hk⟩
    exact ⟨Γ.α d, hU, by rw [j_curve_α]; exact hS, by rw [j_α_α]; exact hA, hk⟩
  · rintro ⟨b, hU, hS, hA, hk⟩
    refine ⟨Γ.α b, ⟨⟨by rw [j_curve_α]; exact hS, ?_⟩, hA⟩, ?_⟩
    · unfold Up; rw [j_α_α]; exact hU
    · unfold upperCell; rw [j_α_α]; exact hk

theorem ld_canTakeLoop_iff : Γ.CanTakeLoop ↔ ∃ b, Γ.Up (Γ.cellOf b) ∧ (Γ.curve b = Γ.S ∧
    ∃ c, Γ.Up (Γ.cellOf c) ∧ (c ∈ (Γ.cellOf b).darts ∧ Γ.curve c ≠ Γ.S ∧
      ¬ Γ.MeetsSweep (Γ.curve c))) := by
  constructor
  · rintro ⟨d, c, ⟨hS, hU⟩, hc, hcS, hM⟩
    have hcell : Γ.cellOf c = Γ.cellOf (Γ.α d) := Orbit.mem_darts.1 hc
    exact ⟨Γ.α d, hU, by rw [j_curve_α]; exact hS, c, by unfold Up; rw [hcell]; exact hU,
      hc, hcS, hM⟩
  · rintro ⟨b, hU, hS, c, -, hc, hcS, hM⟩
    refine ⟨Γ.α b, c, ⟨by rw [j_curve_α]; exact hS, ?_⟩, ?_, hcS, hM⟩
    · unfold Up; rw [j_α_α]; exact hU
    · unfold upperCell; rw [j_α_α]; exact hc

end SConf

end Pca.Sweep
