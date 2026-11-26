/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweep: the induction (`doc/pca/great.md` 4.3-4.4)
-/
import Pca.Great.Swp_Run

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D} {ι : D → D'}

theorem sweep (hA : A.IsGreat) (h3 : 3 ≤ n) {f₁ f₂ : A.Cell} {y0 : D} (hy0 : y0 ∈ f₁.darts)
    {d₀ : D} (hd₀ : d₀ ∈ f₂.darts)
    (hx0 : A.curve y0 ∉ Arrangement.Crossing.curves A (A.crossingOf d₀)) :
    ∀ (m : ℕ) (B : Arrangement (n + 1) D') (F : Frame B) (N : ZMod 2),
      B.IsGreat → IsDeletion B A ι → PassAt B ι y0 → F.c0 = Fin.castSucc (A.curve y0) →
      (F.Neg (Fin.last n) (Fin.castSucc (A.curve d₀)) (Fin.castSucc (A.curve (A.σ d₀))) ↔
        N = 0) → (unswept F N).card = m →
      ∃ B' : Arrangement (n + 1) D', B'.IsGreat ∧ IsDeletion B' A ι ∧ Passes B' ι f₁ ∧
        Passes B' ι f₂ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro B F N hB hD hP hc0 hU hm
  set L := Fin.last n
  set b := Fin.castSucc (A.curve d₀)
  set c := Fin.castSucc (A.curve (A.σ d₀))
  have hbc : b ≠ c := fun h => A.isArrangement.curve_σ d₀ (Fin.castSucc_injective _ h).symm
  have hb0 : b ≠ F.c0 := by
    rw [hc0]; intro h
    exact hx0 (by rw [← Fin.castSucc_injective _ h]; exact A.mem_curves_crossingOf d₀)
  have hcc0 : c ≠ F.c0 := by
    rw [hc0]; intro h
    exact hx0 (by rw [← Fin.castSucc_injective _ h]; exact A.mem_curves_crossingOf_σ d₀)
  have hbL : b ≠ L := Fin.castSucc_ne_last _
  have hcL : c ≠ L := Fin.castSucc_ne_last _
  have hLc0 : F.c0 ≠ L := by rw [hc0]; exact Fin.castSucc_ne_last _
  by_cases hpass : Passes B ι f₂
  · exact ⟨B, hB, hD, ⟨y0, hy0, hP⟩, hpass⟩
  have hf : ∀ d ∈ f₂.darts, ¬ PassAt B ι d := fun d hd h => hpass ⟨d, hd, h⟩
  obtain ⟨t, hT, htL, hc0T, hH, hN⟩ := sweep_tri F hB hLc0 hb0 hcc0 hbc hbL hcL hU
  obtain ⟨hT', hc0', hneg⟩ := F.neg_aflip hB hT hc0T hH
  set e := B.α (ant B t)
  have hanti := isAntipodalTri_ant hB hT
  obtain ⟨hcurE, hcorE⟩ := aflip_data hT hanti
  have hL1 : L ∈ Arrangement.Cell.curves B (B.cellOf t) := by
    rw [tri_curves hT, htL]; exact mem_insert_self _ _
  have hmemE : ∀ y : B.Crossing, y ∈ Arrangement.Cell.corners B (B.cellOf e) ↔
      Arrangement.Crossing.curves B y ⊆ Arrangement.Cell.curves B (B.cellOf t) ∧
        y ∉ Arrangement.Cell.corners B (B.cellOf t) := by
    intro y; rw [hanti.2.2, mem_filter]; simp only [mem_univ, true_and]
  have hL2 : L ∈ Arrangement.Cell.curves (B.flip t hT) ((B.flip t hT).cellOf e) := by
    rw [hcurE]; exact hL1
  have hD1 := flip_isDeletion hD hT hL1
  have hD2 := flip_isDeletion hD1 hT' hL2
  have hB2 : ((B.flip t hT).flip e hT').IsGreat := AFlip.isGreat hB ⟨t, e, hT, hanti, hT', rfl⟩
  -- the witness for `f₁`
  have hy1 : F.c0 ∈ Arrangement.Crossing.curves B (B.crossingOf (ι y0)) := by
    rw [hc0, ← hD.curve]; exact B.mem_curves_crossingOf _
  have hy2 : ∀ X : Arrangement (n + 1) D', X.curve = B.curve →
      F.c0 ∈ Arrangement.Crossing.curves X (X.crossingOf (X.α (ι y0))) := by
    intro X hX
    have := X.mem_curves_crossingOf (X.α (ι y0))
    rwa [X.isArrangement.curve_α, hX, hD.curve, ← hc0] at this
  have hP1 : PassAt (B.flip t hT) ι y0 :=
    passAt_flip hT hP (not_corner_of_curve hT hc0T hy1) (not_corner_of_curve hT hc0T (hy2 B rfl))
  have hP2 : PassAt ((B.flip t hT).flip e hT') ι y0 :=
    passAt_flip hT' hP1 (not_corner_of_curve hT' hc0' hy1)
      (not_corner_of_curve hT' hc0' (hy2 _ rfl))
  by_cases hcase : ({L, b, c} : Finset (Fin (n + 1))) = Arrangement.Cell.curves B (B.cellOf t)
  · -- the pair of `x` is swept now: `x` is the old corner of `T` or of its antipode
    set xB := B.crossingOf (ι d₀)
    have hxBc : Arrangement.Crossing.curves B xB = {b, c} := by
      rw [B.curves_crossingOf, ← hD.σ, hD.curve, hD.curve]
    have hxsub : Arrangement.Crossing.curves B xB ⊆ Arrangement.Cell.curves B (B.cellOf t) := by
      rw [hxBc, ← hcase]; intro C hC; simp only [mem_insert, mem_singleton] at hC ⊢; tauto
    have hcorT' : ∀ y, y ∈ Arrangement.Cell.corners B (B.cellOf t) →
        y ∉ Arrangement.Cell.corners (B.flip t hT) ((B.flip t hT).cellOf e) := by
      intro y hy hy'
      rw [hcorE] at hy'
      exact ((hmemE y).1 hy').2 hy
    by_cases hxT : xB ∈ Arrangement.Cell.corners B (B.cellOf t)
    · obtain ⟨hPa, hca⟩ := passAt_apex hD hT hL1 hf hd₀ hxT
      have hPb := passAt_flip hT' hPa (hcorT' _ hxT) (hcorT' _ hca)
      exact ⟨_, hB2, hD2, ⟨y0, hy0, hP2⟩, ⟨d₀, hd₀, hPb⟩⟩
    · have hxT' : B.crossingOf (ι d₀) ∈
          Arrangement.Cell.corners (B.flip t hT) ((B.flip t hT).cellOf e) := by
        rw [hcorE]; exact (hmemE _).2 ⟨hxsub, hxT⟩
      have hc : ∀ d ∈ f₂.darts, B.crossingOf (ι d) ∉ Arrangement.Cell.corners B (B.cellOf t) := by
        intro d hd hdT
        have hold := old_crossing hD d
        have hsub := curves_corner_sub hT hdT
        have heq : Arrangement.Crossing.curves B (B.crossingOf (ι d)) = {b, c} := by
          refine eq_of_subset_of_card_le (fun C hC => ?_) ?_
          · have := hsub hC
            rw [← hcase] at this
            simp only [mem_insert, mem_singleton] at this ⊢
            rcases this with rfl | h | h
            · exact absurd hC hold
            · exact Or.inl h
            · exact Or.inr h
          · rw [B.card_curves, card_pair hbc]
        have hA' : Arrangement.Crossing.curves A (A.crossingOf d) =
            Arrangement.Crossing.curves A (A.crossingOf d₀) := by
          have h1 := del_curves hD d
          have h2 := del_curves hD d₀
          rw [heq] at h1
          rw [hxBc] at h2
          exact Finset.map_injective Fin.castSuccEmb (h1.symm.trans h2)
        have := del_crossing hD (cell_pair_unique hA h3 hd hd₀ hA')
        rw [this] at hdT
        exact hxT hdT
      have hf1 := unpassed_flip hD hT hf hc
      obtain ⟨hPa, -⟩ := passAt_apex hD1 hT' hL2 hf1 hd₀ hxT'
      exact ⟨_, hB2, hD2, ⟨y0, hy0, hP2⟩, ⟨d₀, hd₀, hPa⟩⟩
  · -- another pair is swept: recurse
    set FB := (F.flipF hT).flipF hT'
    have hU' : FB.Neg L b c ↔ N = 0 := by
      rw [hneg L b c hLc0.symm hb0 hcc0 hbL.symm hcL.symm hbc]
      simp only [hcase, not_false_eq_true, iff_true]
      exact hU
    have hlt := unswept_lt F FB hB hT htL hc0T hH hN hLc0 rfl hneg
    exact ih _ (hm ▸ hlt) _ FB N hB2 hD2 hP2 hc0 hU' rfl

end Pca.Great
