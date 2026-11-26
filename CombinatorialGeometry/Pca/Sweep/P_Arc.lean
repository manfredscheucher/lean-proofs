/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: upper arcs of curves and cuts along them (helpers for Lemma 3.11)

`PArc Γ z a L t1 t2`: the upper arc of the curve of `a`, from the vertex `t1` (`a = σ (noC z t1)`)
straight on for `L` steps to the vertex `t2` (`straight^L a = α (σ (noC z t2))`), covering every
dart of its curve above `S`. Along it a cut changes at the crossings with its boundary darts
(`PArc.walk`), and a curve crosses it at most twice (`PArc.count_le`). Two ends strictly inside a
loop make a loop inside it (`p_inside_of_ends`).
-/
import Pca.Sweep.C_Lid
import Pca.Sweep.F_Basic
import Pca.Sweep.AB_G1

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

theorem p_curve_σ_iff {s : D} (hs : Γ.IsSweepDart s) {γ : Fin n} (hS : γ ≠ Γ.S) :
    Γ.curve (Γ.σ s) = γ ↔ γ ∈ Γ.curves (Γ.crossingOf s) := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton, hs.1]
  constructor
  · exact fun h => Or.inr h.symm
  · rintro (h | h)
    · exact absurd h hS
    · exact h.symm

theorem p_crossing_σ_noC (z : D) (t : ℕ) :
    Γ.crossingOf (Γ.σ (Γ.noC z t)) = Γ.crossingOf (Γ.noC z t) := j_crossingOf_σ _ _

theorem p_cell_σ_noC (z : D) (t : ℕ) :
    Γ.cellOf (Γ.σ (Γ.noC z t)) = Γ.upperCell (Γ.noC z t) := j_cellOf_σ _ _

/-- A curve crossing `S` at one vertex crosses it at a second one. -/
theorem p_second_end {z : D} (hz : Γ.infStart = some z) {c : Fin n} (hc : c ≠ Γ.S) {t1 : ℕ}
    (h1 : c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t1))) :
    ∃ t2 < period Γ.straight z, Γ.crossingOf (Γ.noC z t2) ≠ Γ.crossingOf (Γ.noC z t1) ∧
      c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t2)) := by
  classical
  set G := univ.filter (fun x : Γ.Crossing => Γ.curves x = {c, Γ.S})
  have hx1 : Γ.crossingOf (Γ.noC z t1) ∈ G :=
    mem_filter.2 ⟨mem_univ _, no_mem_curves (no_S_mem_noC hz t1) h1 hc⟩
  have hG : G.card = 2 := by
    have h02 : G.card = 0 ∨ G.card = 2 := by convert card_sweep_crossings c hc
    rcases h02 with h | h
    · rw [card_eq_zero] at h; rw [h] at hx1; exact absurd hx1 (notMem_empty _)
    · exact h
  obtain ⟨x, y, hxy, hGe⟩ := card_eq_two.1 hG
  obtain ⟨x2, hx2G, hx2⟩ : ∃ x2 ∈ G, x2 ≠ Γ.crossingOf (Γ.noC z t1) := by
    by_cases hx : x = Γ.crossingOf (Γ.noC z t1)
    · exact ⟨y, by rw [hGe]; simp, fun h => hxy (hx.trans h.symm)⟩
    · exact ⟨x, by rw [hGe]; simp, hx⟩
  have hcx := (mem_filter.1 hx2G).2
  have hS2 : Γ.OnSweep x2 := by
    change Γ.S ∈ Γ.curves x2; rw [hcx]; simp
  obtain ⟨t2, ht2, rfl⟩ := no_onSweep_noC hz hS2
  exact ⟨t2, ht2, hx2, by rw [hcx]; simp⟩

/-- The upper arc of a curve (module doc). -/
structure PArc (Γ : SConf n D) (z a : D) (L t1 t2 : ℕ) : Prop where
  hz : Γ.infStart = some z
  t1P : t1 < period Γ.straight z
  t2P : t2 < period Γ.straight z
  ne : t1 ≠ t2
  ha : a = Γ.σ (Γ.noC z t1)
  hall : ∀ q ≤ L, Γ.Above ((Γ.straight ^ q) a)
  hL : (Γ.straight ^ L) a = Γ.α (Γ.σ (Γ.noC z t2))
  hLP : L < period Γ.straight a
  hnos : ∀ q < L, ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)))
  hcov : ∀ y, Γ.Above y → Γ.curve y = Γ.curve a →
    ∃ q ≤ L, (Γ.straight ^ q) a = y ∨ (Γ.straight ^ q) a = Γ.α y

/-- Every curve through a vertex `t1` has an upper arc from `t1`. -/
theorem p_arc_exists {z : D} (hz : Γ.infStart = some z) {c : Fin n} (hc : c ≠ Γ.S) {t1 : ℕ}
    (ht1 : t1 < period Γ.straight z) (h1 : c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t1))) :
    ∃ L t2, PArc Γ z (Γ.σ (Γ.noC z t1)) L t1 t2 ∧ Γ.curve (Γ.σ (Γ.noC z t1)) = c ∧
      c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t2)) := by
  obtain ⟨t2, ht2, hne, h2⟩ := p_second_end hz hc h1
  have hs1 := no_noC_sweep hz t1
  have hs2 := no_noC_sweep hz t2
  have ca := (p_curve_σ_iff hs1 hc).2 h1
  have cb := (p_curve_σ_iff hs2 hc).2 h2
  have haS : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.σ (Γ.noC z t1))) := by
    rw [j_crossingOf_σ]; exact no_S_mem_noC hz t1
  have hbS : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.σ (Γ.noC z t2))) := by
    rw [j_crossingOf_σ]; exact no_S_mem_noC hz t2
  have hcr : Γ.crossingOf (Γ.σ (Γ.noC z t1)) ≠ Γ.crossingOf (Γ.σ (Γ.noC z t2)) := by
    rw [j_crossingOf_σ, j_crossingOf_σ]; exact fun h => hne h.symm
  obtain ⟨L, hall, hL, hLp, hnos, hcov⟩ :=
    no_upper_arc (no_above_σ hs1) (no_above_σ hs2) (ca.trans cb.symm) haS hbS hcr
  refine ⟨L, t2, ⟨hz, ht1, ht2, fun h => hne (by rw [h]), rfl, hall, hL, hLp, hnos, hcov⟩,
    ca, h2⟩

namespace PArc

variable {z a : D} {L t1 t2 : ℕ} (A : PArc Γ z a L t1 t2)
include A

theorem curve_end : Γ.curve (Γ.σ (Γ.noC z t2)) = Γ.curve a := by
  have := congrArg Γ.curve A.hL
  rw [no_curve_pow, j_curve_α] at this
  exact this.symm

theorem cell_start : Γ.cellOf a = Γ.upperCell (Γ.noC z t1) := by
  rw [A.ha]; exact j_cellOf_σ _ _

theorem curve_ne_S : Γ.curve a ≠ Γ.S := (A.hall 0 (Nat.zero_le _)).1

theorem crossing_start : Γ.crossingOf a = Γ.crossingOf (Γ.noC z t1) := by
  rw [A.ha]; exact j_crossingOf_σ _ _

/-- Along the arc, a cut changes at the crossings with its boundary darts. -/
theorem walk {g : Γ.Cell → ZMod 2} {F : Finset D}
    (hg : ∀ y, Γ.curve y ≠ Γ.S → g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = if y ∈ F then 1 else 0)
    {q : ℕ} (hq : q ≤ L) :
    g (Γ.cellOf ((Γ.straight ^ q) a)) = g (Γ.cellOf a) +
      (((range q).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ F)).card : ZMod 2) := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
    rw [no_pow_succ, no_walk_straight (r := g)
      (f := fun y => g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y))) (fun y => rfl), ih (by omega),
      range_add_one, filter_insert]
    have hc : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) ≠ Γ.S := by
      intro h
      apply A.hnos q (by omega)
      change Γ.S ∈ Γ.curves _
      rw [j_curves_crossingOf, h]; exact mem_insert_of_mem (mem_singleton_self _)
    rw [hg _ hc]
    by_cases hF : Γ.σ (Γ.α ((Γ.straight ^ q) a)) ∈ F
    · rw [if_pos hF, if_pos hF, card_insert_of_notMem (by simp)]
      push_cast; ring
    · rw [if_neg hF, if_neg hF, add_zero]

/-- The cut at the far end of the arc. -/
theorem walk_end {g : Γ.Cell → ZMod 2} {F : Finset D}
    (hg : ∀ y, Γ.curve y ≠ Γ.S → g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = if y ∈ F then 1 else 0)
    (hF : Γ.σ (Γ.noC z t2) ∉ F) :
    g (Γ.upperCell (Γ.noC z t2)) = g (Γ.upperCell (Γ.noC z t1)) +
      (((range L).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ F)).card : ZMod 2) := by
  have h1 := A.walk hg (le_refl L)
  rw [A.hL, A.cell_start] at h1
  have h2 := hg (Γ.σ (Γ.noC z t2)) (by rw [A.curve_end]; exact A.curve_ne_S)
  rw [if_neg hF] at h2
  rw [← p_cell_σ_noC, ← c_zmod2_eq_of_add h2, h1]

/-- The arc crosses another curve at most twice. -/
theorem count_le {γ : Fin n} (hγ : γ ≠ Γ.curve a) {F : Finset D}
    (hF : ∀ y ∈ F, Γ.curve y = γ) :
    ((range L).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ F)).card ≤ 2 := by
  classical
  have hle := Γ.isSConf.two_int (Γ.curve a) γ (Ne.symm hγ)
  refine le_trans (card_le_card_of_injOn (fun q => Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)))
    (fun q hq => ?_) (fun q₁ hq₁ q₂ hq₂ h => ?_)) hle
  · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    change Γ.curves _ = _
    rw [j_curves_crossingOf, j_curve_α, no_curve_pow, hF _ hq.2]
  · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hq₁ hq₂
    have hP := A.hLP
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact f_cross_ne h' (by omega) h
    · exact f_cross_ne h' (by omega) h.symm

end PArc

open Classical in
/-- Two fin vertices of a curve make it a loop (copy of the private `gk_loop_of_two`). -/
theorem p_loop_of_two {δ : Fin n} (hδ : δ ≠ Γ.S) {x₁ x₂ : Γ.Crossing}
    (h1 : Γ.IsFinVertex x₁ ∧ Γ.OnCurve δ x₁) (h2 : Γ.IsFinVertex x₂ ∧ Γ.OnCurve δ x₂)
    (hne : x₁ ≠ x₂) :
    (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x)) = {x₁, x₂} := by
  classical
  have hsub : univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x) ⊆
      univ.filter (fun x : Γ.Crossing => Γ.curves x = {δ, Γ.S}) := by
    intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨mem_univ _, no_mem_curves hx.2.1.1 hx.2.2 hδ⟩
  have hle := card_le_card hsub
  have h02 := card_sweep_crossings (Γ := Γ) δ hδ
  have hpair : ({x₁, x₂} : Finset Γ.Crossing) ⊆
      univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rw [mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨mem_univ _, h1⟩
    · exact ⟨mem_univ _, h2⟩
  have hge := card_le_card hpair
  rw [card_pair hne] at hge
  exact (eq_of_subset_of_card_le hpair (by rw [card_pair hne]; omega)).symm

/-- Two ends strictly between the ends of the loop `γ` make a loop inside `γ`. -/
theorem p_inside_of_ends {z : D} (hz : Γ.infStart = some z) {c γ : Fin n} (hcS : c ≠ Γ.S)
    {tk tl t1 t2 : ℕ} (hγ : Γ.LoopEnds γ (tk + 1) (tl + 1))
    (htl : tl + Γ.infLen < period Γ.straight z) (h1 : tk < t1 ∧ t1 < tl)
    (h2 : tk < t2 ∧ t2 < tl) (hne : t1 ≠ t2) (hc1 : c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t1)))
    (hc2 : c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t2))) : Γ.Inside c γ := by
  classical
  have hf : ∀ t, t < tl → Γ.IsFinVertex (Γ.crossingOf (Γ.noC z t)) :=
    fun t ht => (no_noC_fin hz (by omega)).2 (by omega)
  have hx : Γ.crossingOf (Γ.noC z t1) ≠ Γ.crossingOf (Γ.noC z t2) :=
    fun h => hne (no_noC_inj hz (by omega) (by omega) h)
  have hF := p_loop_of_two hcS ⟨hf t1 h1.2, hc1⟩ ⟨hf t2 h2.2, hc2⟩ hx
  have hloop : Γ.IsLoop c := by
    unfold IsLoop numSweepHits
    rw [hF, card_pair hx]
  have hends : Γ.sweepEnds c = {t1 + 1, t2 + 1} := by
    unfold sweepEnds
    rw [hF, image_insert, image_singleton, no_noC_pos hz (by omega), no_noC_pos hz (by omega)]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨t1 + 1, t2 + 1, tk + 1, tl + 1, ⟨hloop, by omega, hends⟩, hγ, by omega, by omega⟩
  · exact ⟨t2 + 1, t1 + 1, tk + 1, tl + 1, ⟨hloop, by omega, by rw [hends, pair_comm]⟩, hγ,
      by omega, by omega⟩

end SConf

end Pca.Sweep
