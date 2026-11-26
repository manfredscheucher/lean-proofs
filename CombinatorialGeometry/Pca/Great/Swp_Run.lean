/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweep: one step and the induction
-/
import Pca.Great.Swp_Main
import Pca.Great.R_Exist

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D} {ι : D → D'}

/-- The triangle of one sweep step: on `L`, in `H`, on side `N`, away from `c0`. -/
theorem sweep_tri {B : Arrangement (n + 1) D'} (F : Frame B) (hB : B.IsGreat)
    (hc0 : F.c0 ≠ Fin.last n) {b c : Fin (n + 1)} (hb : b ≠ F.c0) (hc : c ≠ F.c0)
    (hbc : b ≠ c) (hbL : b ≠ Fin.last n) (hcL : c ≠ Fin.last n) {N : ZMod 2}
    (hU : F.Neg (Fin.last n) b c ↔ N = 0) :
    ∃ t : D', ∃ hT : B.IsTriangle (B.cellOf t), B.curve t = Fin.last n ∧
      F.c0 ∉ Arrangement.Cell.curves B (B.cellOf t) ∧ F.s0 (B.cellOf t) = 1 ∧
      F.sR (Fin.last n) (B.cellOf t) = N := by
  set z := (B.straight ^ F.hpos b c) (F.β b)
  have hz := F.curves_hcross hB hb hc hbc
  have hs0 : F.s0 (B.cellOf z) = 1 := F.s0_cell hB hb (F.hpos_spec hB hb hc hbc).2.1
  have hz0 : F.c0 ∉ Arrangement.Crossing.curves B (B.crossingOf z) := by
    rw [hz]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hb, Ne.symm hc⟩
  have hzL : Fin.last n ∉ Arrangement.Crossing.curves B (B.crossingOf z) := by
    rw [hz]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hbL, Ne.symm hcL⟩
  have hcs : B.crossSide F.s0 (B.crossingOf z) = 1 := by rw [crossSide_eq F.isSide_s0 hz0]; exact hs0
  have hside := (neg_iff_side F hB hb hc hbc (Ne.symm hbL) (Ne.symm hcL) hz hcs N).1 hU
  rw [crossSide_eq (F.isSide_sR _) hzL] at hside
  obtain ⟨t, hT, ht, htc, -, hH, hN⟩ := F.quarter hB (Ne.symm hc0) N univ (mem_univ _)
    ⟨z, hz0, hzL, subset_univ _, hs0, hside⟩ (fun t ht => absurd (mem_univ t) ht)
  exact ⟨t, hT, ht, htc, hH, hN⟩

end Pca.Great

namespace Pca.Great

variable {D' : Type*} [Fintype D'] [DecidableEq D'] {n : ℕ}

/-- An antipodal flip of the sweep triangle sweeps its pair and no other. -/
theorem unswept_lt {B B2 : Arrangement (n + 1) D'} (F : Frame B) (FB : Frame B2)
    (hB : B.IsGreat) {t : D'} (hT : B.IsTriangle (B.cellOf t)) (htL : B.curve t = Fin.last n)
    (hc0T : F.c0 ∉ Arrangement.Cell.curves B (B.cellOf t)) (hH : F.s0 (B.cellOf t) = 1)
    {N : ZMod 2} (hN : F.sR (Fin.last n) (B.cellOf t) = N) (hc0 : F.c0 ≠ Fin.last n)
    (hFB : FB.c0 = F.c0)
    (hneg : ∀ a b c : Fin (n + 1), a ≠ F.c0 → b ≠ F.c0 → c ≠ F.c0 → a ≠ b → a ≠ c → b ≠ c →
      (FB.Neg a b c ↔ (F.Neg a b c ↔ ¬ ({a, b, c} : Finset (Fin (n + 1))) =
        Arrangement.Cell.curves B (B.cellOf t)))) :
    (unswept FB N).card < (unswept F N).card := by
  classical
  set L := Fin.last n
  set b' := B.curve (B.φ t)
  set c' := B.curve (B.φ (B.φ t))
  have hcur : Arrangement.Cell.curves B (B.cellOf t) = {L, b', c'} := by rw [tri_curves hT, htL]
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hT
  rw [htL] at n1 n3
  have hb0 : b' ≠ F.c0 := fun h => hc0T (by rw [hcur, ← h]; simp)
  have hc0' : c' ≠ F.c0 := fun h => hc0T (by rw [hcur, ← h]; simp)
  -- the apex is unswept
  have hφφ : B.cellOf (B.φ (B.φ t)) = B.cellOf t := by rw [B.cellOf_φ, B.cellOf_φ]
  have hTφφ := Arrangement.isTriangle_of hT hφφ
  have hx : Arrangement.Crossing.curves B (B.crossingOf (B.φ (B.φ t))) = {b', c'} := by
    rw [tri_corner_curves hTφφ, Arrangement.tri_φφφ hT, pair_comm]
  have hx0 : F.c0 ∉ Arrangement.Crossing.curves B (B.crossingOf (B.φ (B.φ t))) := by
    rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hb0, Ne.symm hc0'⟩
  have hxL : L ∉ Arrangement.Crossing.curves B (B.crossingOf (B.φ (B.φ t))) := by
    rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨n1, n3⟩
  have hs : B.crossSide F.s0 (B.crossingOf (B.φ (B.φ t))) = 1 := by
    rw [crossSide_eq F.isSide_s0 hx0, hφφ]; exact hH
  have hU0 : F.Neg L b' c' ↔ N = 0 := by
    rw [neg_iff_side F hB hb0 hc0' n2 n1 n3 hx hs N, crossSide_eq (F.isSide_sR _) hxL, hφφ]
    exact hN
  have hmem : (b', c') ∈ unswept F N := by
    simp only [unswept, mem_filter, mem_univ, true_and]
    exact ⟨n2, hb0, hc0', Ne.symm n1, Ne.symm n3, hU0⟩
  have hsub : unswept FB N ⊆ (unswept F N).erase (b', c') := by
    intro p hp
    simp only [unswept, mem_filter, mem_univ, true_and, hFB] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    have hn := hneg L p.1 p.2 hc0.symm h2 h3 (Ne.symm h4) (Ne.symm h5) h1
    by_cases hs : ({L, p.1, p.2} : Finset (Fin (n + 1))) = Arrangement.Cell.curves B (B.cellOf t)
    · exfalso
      rw [hcur] at hs
      have hp1 : p.1 ∈ ({L, b', c'} : Finset _) := by rw [← hs]; simp
      have hp2 : p.2 ∈ ({L, b', c'} : Finset _) := by rw [← hs]; simp
      simp only [mem_insert, mem_singleton] at hp1 hp2
      have hold : F.Neg L p.1 p.2 ↔ N = 0 := by
        rcases hp1 with e1 | e1 | e1 <;> rcases hp2 with e2 | e2 | e2
        all_goals first
          | exact absurd e1 h4 | exact absurd e2 h5 | exact absurd (e1.trans e2.symm) h1
          | (rw [e1, e2]; exact hU0) | (rw [e1, e2, F.neg_comm hB]; exact hU0)
      rw [hn, hcur] at h6
      simp only [hs, not_true_eq_false, iff_false] at h6
      exact iff_not_self (hold.trans h6.symm)
    · rw [hn] at h6
      simp only [hs, not_false_eq_true, iff_true] at h6
      refine mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        exact hs (by rw [hcur])
      · simp only [unswept, mem_filter, mem_univ, true_and]
        exact ⟨h1, h2, h3, h4, h5, h6⟩
  calc (unswept FB N).card ≤ ((unswept F N).erase (b', c')).card := card_le_card hsub
    _ < (unswept F N).card := card_erase_lt_of_mem hmem

end Pca.Great
