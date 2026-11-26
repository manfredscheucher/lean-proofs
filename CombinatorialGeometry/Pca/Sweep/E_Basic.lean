/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package E (SH Lemma 3.7), generic helpers

* `e_even`: the segments of a closed walk that uses no segment twice form an even set (so Jordan,
  `exists_cut`, applies to it);
* copies of two small facts of package F (`f_eq_or_eq_σσ`, `f_finSeg_fin`), kept here so that
  package E does not depend on files of other packages that are still in progress.
-/
import Pca.Sweep.NO_Sweep

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Two darts of the same curve at one crossing are equal or opposite. -/
theorem e_eq_or_eq_σσ {a b : D} (hx : Γ.crossingOf a = Γ.crossingOf b)
    (hc : Γ.curve a = Γ.curve b) : b = a ∨ b = Γ.σ (Γ.σ a) := by
  rcases no_mem_crossing hx.symm with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hc.symm) (no_curve_σ_ne a)
  · exact Or.inr h
  · exfalso
    have h1 := no_curve_σ_ne (Γ := Γ) (Γ.σ (Γ.σ a))
    rw [← h, Γ.j_curve_σσ] at h1
    exact h1 hc.symm

/-- Both ends of a finite edge are vertices on the sweep. -/
theorem e_finSeg_fin {d : D} (hd : Γ.IsFinSeg d) :
    Γ.IsFinVertex (Γ.crossingOf d) ∧ Γ.IsFinVertex (Γ.crossingOf (Γ.α d)) := by
  obtain ⟨hsw, hnot⟩ := hd
  have hS : Γ.curve d = Γ.S := hsw.1
  have hSα : Γ.curve (Γ.α d) = Γ.S := by rw [j_curve_α]; exact hS
  have hside : Γ.side (Γ.cellOf (Γ.α d)) = 1 := hsw.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show Γ.S ∈ Γ.curves (Γ.crossingOf d)
    rw [j_curves_crossingOf, hS]; exact mem_insert_self _ _
  · rintro ⟨z, hz, i, hi, hx⟩
    have hz' : Γ.infStart = some z := hz
    have hs : Γ.IsSweepDart ((Γ.straight ^ i) z) := no_sweep_pow (no_z_sweep hz') i
    have hcur : Γ.curve (Γ.α ((Γ.straight ^ i) z)) = Γ.curve d := by
      rw [j_curve_α, hs.1, hS]
    rcases e_eq_or_eq_σσ hx hcur with h | h
    · have h0 := (no_sweep_iff hs.1).1 hs
      rw [h, j_α_α, h0] at hside
      exact absurd hside (by decide)
    · apply hnot
      rw [no_mem_infArc hz']
      exact ⟨i + 1, hi, by rw [no_pow_succ, h]; rfl⟩
  · show Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α d))
    rw [j_curves_crossingOf, hSα]; exact mem_insert_self _ _
  · rintro ⟨z, hz, i, hi, hx⟩
    have hz' : Γ.infStart = some z := hz
    have hs : Γ.IsSweepDart ((Γ.straight ^ i) z) := no_sweep_pow (no_z_sweep hz') i
    have hcur : Γ.curve (Γ.α ((Γ.straight ^ i) z)) = Γ.curve (Γ.α d) := by
      rw [j_curve_α, hs.1, hSα]
    rcases e_eq_or_eq_σσ hx hcur with h | h
    · apply hnot
      have h2 := congrArg Γ.α h
      rw [j_α_α, j_α_α] at h2
      rw [no_mem_infArc hz']
      exact ⟨i, hi.le, h2.symm⟩
    · have hs1 : Γ.IsSweepDart ((Γ.straight ^ (i + 1)) z) := no_sweep_pow (no_z_sweep hz') _
      have he : (Γ.straight ^ (i + 1)) z = Γ.α d := by rw [no_pow_succ, h]; rfl
      rw [he] at hs1
      have h0 := (no_sweep_iff hsw.1).1 hsw
      have h1 : Γ.side (Γ.cellOf (Γ.α (Γ.α d))) = 1 := hs1.2
      rw [j_α_α, h0] at h1
      exact absurd h1 (by decide)

/-- **Closed walks are even.** A cyclic sequence of darts `w 0, …, w (M - 1)` (`w M = w 0`), each
starting where the previous one ends, with no dart twice and no segment used in both
directions: every crossing is the end of an even number of darts on its segments. -/
theorem e_even (w : ℕ → D) (M : ℕ)
    (hc : ∀ t < M, Γ.crossingOf (w (t + 1)) = Γ.crossingOf (Γ.α (w t))) (hper : w M = w 0)
    (hinj : ∀ s < M, ∀ t < M, w s = w t → s = t) (hα : ∀ s < M, ∀ t < M, Γ.α (w s) ≠ w t) :
    Γ.IsEven ((range M).image (fun t => Γ.segmentOf (w t))) := by
  intro x
  set A := (range M).filter (fun t => Γ.crossingOf (w t) = x) with hA
  set B := (range M).filter (fun t => Γ.crossingOf (Γ.α (w t)) = x) with hB
  have hset : x.darts.filter (fun y => Γ.segmentOf y ∈
      (range M).image (fun t => Γ.segmentOf (w t))) = A.image w ∪ B.image (fun t => Γ.α (w t)) := by
    ext y
    simp only [mem_filter, mem_image, mem_union, mem_range, Orbit.mem_darts, hA, hB]
    constructor
    · rintro ⟨hx, t, ht, hs⟩
      rw [j_segmentOf_eq_iff] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact Or.inl ⟨t, ⟨ht, hx⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨ht, hx⟩, rfl⟩
    · rintro (⟨t, ⟨ht, hx⟩, rfl⟩ | ⟨t, ⟨ht, hx⟩, rfl⟩)
      · exact ⟨hx, t, ht, rfl⟩
      · exact ⟨hx, t, ht, (j_segmentOf_α _ _).symm⟩
  have hAB : A.card = B.card := by
    refine card_nbij' (fun t => if t = 0 then M - 1 else t - 1)
      (fun t => if t + 1 = M then 0 else t + 1) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, hA, hB] at ht ⊢
      obtain ⟨ht, hx⟩ := ht
      split_ifs with h0
      · subst h0
        refine ⟨by omega, ?_⟩
        rw [← hc _ (by omega), Nat.sub_add_cancel (by omega), hper]; exact hx
      · refine ⟨by omega, ?_⟩
        rw [← hc _ (by omega), Nat.sub_add_cancel (by omega)]; exact hx
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, hA, hB] at ht ⊢
      obtain ⟨ht, hx⟩ := ht
      split_ifs with h0
      · refine ⟨by omega, ?_⟩
        rw [← hper, ← h0, hc _ ht]; exact hx
      · refine ⟨by omega, ?_⟩
        rw [hc _ ht]; exact hx
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, hA] at ht
      by_cases h0 : t = 0
      · simp only [h0, if_true]; rw [if_pos (by omega)]
      · simp only [h0, if_false]; rw [if_neg (by omega)]; omega
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, hB] at ht
      by_cases h0 : t + 1 = M
      · simp only [h0, if_true]; omega
      · simp only [h0, if_false]; rw [if_neg (by omega)]; omega
  have hdisj : Disjoint (A.image w) (B.image (fun t => Γ.α (w t))) := by
    rw [disjoint_left]
    intro y hy1 hy2
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hy1
    obtain ⟨t, ht, he⟩ := mem_image.1 hy2
    exact hα t (mem_range.1 (mem_filter.1 ht).1) s (mem_range.1 (mem_filter.1 hs).1) he
  rw [hset, card_union_of_disjoint hdisj,
    card_image_of_injOn (fun s hs t ht h => hinj s (mem_range.1 (mem_filter.1 hs).1) t
      (mem_range.1 (mem_filter.1 ht).1) h),
    card_image_of_injOn (fun s hs t ht h => hinj s (mem_range.1 (mem_filter.1 hs).1) t
      (mem_range.1 (mem_filter.1 ht).1) (Γ.isSConf.α_α (w s) ▸ Γ.isSConf.α_α (w t) ▸
        congrArg Γ.α h)), hAB]
  exact ⟨B.card, rfl⟩

end SConf

end Pca.Sweep
