/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): flips away from `C` and `C'` keep them parallel (for `Mimic.lean`)

`par_flip_away`: flipping a triangle without a corner on `C` or `C'` keeps `C`, `C'` parallel
(the digon is not touched, and the interior statuses of crossings for `C`, `C'` do not change,
`crossInside_flip`).
-/
import Pca.FlipGraph.MimicPar
import Pca.FlipGraph.FlipCross

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- A digon without a corner of the flipped triangle stays a digon with the same darts and the same
interior statuses. -/
theorem digon_keep_flip (N : Marked n D) {a d : D} (hT : N.A.IsTriangle (N.A.cellOf d))
    (hdz : N.A.cellOf d ≠ N.z) (hD : N.A.IsDigon (N.A.cellOf a))
    (hna : ¬ N.A.IsCorner d a) (hnαa : ¬ N.A.IsCorner d (N.A.α a)) (C : Fin n) :
    (N.flip d hT).A.IsDigon ((N.flip d hT).A.cellOf a) ∧ (N.flip d hT).A.φ a = N.A.φ a ∧
      ((N.flip d hT).Inside C ((N.flip d hT).A.cellOf a) ↔ N.Inside C (N.A.cellOf a)) := by
  have hφφ : N.A.φ (N.A.φ a) = a := N.A.φ_φ_of_digon hD
  have hgT : N.A.cellOf a ≠ N.A.cellOf d := Arrangement.not_mem_of_not_corner hna
  have hcell : (N.A.flip d hT).cellOf a = Arrangement.flipCellEquiv hT (N.A.cellOf a) :=
    Arrangement.flip_cellOf_of_not_corner hT hna
  refine ⟨?_, Arrangement.flipφ_generic hT hna hnαa, ?_⟩
  · change Orbit.size ((N.A.flip d hT).cellOf a) = 2
    rw [hcell, Arrangement.flip_size_of_ne hT]
    · exact hD
    intro c hc
    have hcc : N.A.IsCorner d c := Arrangement.isCorner_of_mem hc
    have corner_of : ∀ y, N.A.crossingOf c = N.A.crossingOf y → N.A.IsCorner d y :=
      fun y e => by unfold Arrangement.IsCorner at hcc ⊢; rwa [← e]
    have hφ_cross : N.A.crossingOf (N.A.φ a) = N.A.crossingOf (N.A.α a) := by
      rw [N.A.φ_apply, N.A.crossingOf_σ]
    have hαφ_cross : N.A.crossingOf (N.A.α (N.A.φ a)) = N.A.crossingOf a := by
      rw [← N.A.crossingOf_σ, ← N.A.φ_apply, hφφ]
    constructor
    · intro e
      rcases two_cycle hφφ ((Arrangement.cellOf_eq_iff N.A).1 e) with e' | e'
      · exact hnαa (corner_of _ (by rw [← e', N.A.α_α]))
      · exact hna (corner_of _ (by rw [← hαφ_cross, ← e', N.A.α_α]))
    · intro e
      rcases two_cycle hφφ ((Arrangement.cellOf_eq_iff N.A).1 e) with e' | e'
      · exact hna (corner_of _ (by rw [← N.A.crossingOf_σσ c, e']))
      · exact hnαa (corner_of _ (by rw [← N.A.crossingOf_σσ c, e', hφ_cross]))
  · change (N.flip d hT).Inside C ((N.A.flip d hT).cellOf a) ↔ _
    rw [hcell, flip_inside N hT hdz C]
    tauto

/-- **A flip away from `C` and `C'` keeps them parallel.** -/
theorem par_flip_away (M : Marked n D) {C C' : Fin n} (hpar : M.Par C C') {d : D}
    (hT : M.A.IsTriangle (M.A.cellOf d)) (hdz : M.A.cellOf d ≠ M.z)
    (hcor : ∀ y, M.A.cellOf y = M.A.cellOf d →
      C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
        C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y)) :
    (M.flip d hT).Par C C' := by
  obtain ⟨hne, ⟨a, hD, ha, hφa, hout, hin⟩, hX⟩ := hpar
  have notc : ∀ y, C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) → ¬ M.A.IsCorner d y := by
    intro y hy hc
    obtain ⟨t, ht, hty⟩ := mem_image.1 hc
    rw [Orbit.mem_darts] at ht
    exact (hcor t ht).1 (by rw [hty]; exact hy)
  have hna : ¬ M.A.IsCorner d a := notc a (ha ▸ M.A.mem_curves_crossingOf a)
  have hnαa : ¬ M.A.IsCorner d (M.A.α a) := notc _ (ha ▸ M.A.mem_curves_end a)
  have hside : ∀ E, E = C ∨ E = C' → ¬ M.HasSideOn E (M.A.cellOf d) := by
    rintro E hE ⟨y, hy, hyE⟩
    rw [Orbit.mem_darts] at hy
    have h := hcor y hy
    rcases hE with rfl | rfl
    · exact h.1 (hyE ▸ M.A.mem_curves_crossingOf y)
    · exact h.2 (hyE ▸ M.A.mem_curves_crossingOf y)
  obtain ⟨hD', hφ', hC⟩ := digon_keep_flip M hT hdz hD hna hnαa C
  obtain ⟨-, -, hC'⟩ := digon_keep_flip M hT hdz hD hna hnαa C'
  refine ⟨hne, ⟨a, hD', ha, by rw [hφ']; exact hφa, by rw [hC]; exact hout, by rw [hC']; exact hin⟩,
    fun x hx hx' => ?_⟩
  obtain ⟨y, rfl⟩ := x.exists_mk
  change C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at hx
  change C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at hx'
  change ¬ ((M.flip d hT).CrossInside C (M.A.crossingOf y) ∧
    ¬ (M.flip d hT).CrossInside C' (M.A.crossingOf y))
  rw [crossInside_flip M hT hdz y hx, crossInside_flip M hT hdz y hx']
  have h1 := hside C (Or.inl rfl)
  have h2 := hside C' (Or.inr rfl)
  have := hX (M.A.crossingOf y) hx hx'
  tauto

end Pca.FlipGraph
