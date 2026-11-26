/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): moving the digon to the next edge of `C` (FROS' second case)

`C`, `C'` parallel with the digon `cellOf a` (`a` on `C`). Two flips with a side on `C'` (P1:
`M − C'` does not change):

1. the band end triangle `Δ = cellOf g`, `g = σ² a` (`band_tri`), with darts `g`, `u = φ g`,
   `v = φ u`;
2. the triangle `D' = (α g, φ a, straight u)` of the flipped arrangement (the digon has gained the
   side `α g` on `C`).

Afterwards `cellOf a` is again a digon (darts `a`, `φ a`) on the next edge of `C`, with the same
interior statuses; the crossings off `C ∪ C'` keep their statuses (every corner of `Δ` and `D'` is
on `C` or `C'`), so `C`, `C'` stay parallel. The segment of `α (straight a)` (the edge of `C`
arriving at the digon) now ends at the end `X₁` of `g`: `N.α (α (straight a)) = α g`.
-/
import Pca.FlipGraph.MimicDigon
import Pca.FlipGraph.FlipCross
import Pca.FlipGraph.Delete
import Pca.FlipGraph.SourceTri

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- A dart outside the three corner crossings of a triangle is not a corner. -/
theorem not_corner_of {A : Arrangement n D} {d y : D} (h3 : A.φ (A.φ (A.φ d)) = d)
    (h0 : A.crossingOf y ≠ A.crossingOf d) (h1 : A.crossingOf y ≠ A.crossingOf (A.φ d))
    (h2 : A.crossingOf y ≠ A.crossingOf (A.φ (A.φ d))) : ¬ A.IsCorner d y := by
  intro hc
  obtain ⟨t, ht, hty⟩ := mem_image.1 hc
  have ht' : t ∈ orbitFinset A.φ d := mem_orbitFinset.2 (A.mem_darts_cellOf.1 ht)
  rw [orbitFinset_three h3, mem_insert, mem_insert, mem_singleton] at ht'
  rcases ht' with rfl | rfl | rfl
  · exact h0 hty.symm
  · exact h1 hty.symm
  · exact h2 hty.symm

/-- A cell with `φ² d = d ≠ φ d` is a digon. -/
theorem isDigon_of {A : Arrangement n D} {d : D} (h2 : A.φ (A.φ d) = d) (h1 : A.φ d ≠ d) :
    A.IsDigon (A.cellOf d) := by
  unfold Arrangement.IsDigon Arrangement.IsKCell
  rw [A.size_cellOf]
  have hle : period A.φ d ≤ 2 := Nat.find_min' _ ⟨by norm_num, by simpa using h2⟩
  have hpos := period_pos A.φ d
  have hit := iterate_period A.φ d
  rcases (show period A.φ d = 1 ∨ period A.φ d = 2 by omega) with h | h
  · rw [h] at hit; exact absurd (by simpa using hit) h1
  · exact h

/-- **Moving the digon** to the next edge of `C` by two flips with a side on `C'`. -/
theorem digon_move {m : ℕ} {C C' : Fin (m + 1)} (hm : 2 ≤ m) {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} (hK : ∀ e, K e ↔ Keep M.A C' e) (hpar : M.Par C C') {a : D}
    (hD : M.A.IsDigon (M.A.cellOf a)) (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C')
    (hout : ¬ M.Inside C (M.A.cellOf a)) (hin : M.Inside C' (M.A.cellOf a))
    {w : D} (hwK : K w) (hw : M.A.cellOf w = M.z) :
    ∃ N : Marked (m + 1) D, Reach M N ∧ ∃ hK' : (∀ e, K e ↔ Keep N.A C' e),
      N.A.deleteOn C' hm K hK' = M.A.deleteOn C' hm K hK ∧ N.Par C C' ∧ N.A.curve = M.A.curve ∧
      (∃ (w' : D) (hw'K : K w'), N.A.cellOf w' = N.z ∧
        (M.A.deleteOn C' hm K hK).cellOf ⟨w', hw'K⟩ = (M.A.deleteOn C' hm K hK).cellOf ⟨w, hwK⟩) ∧
      N.A.α (M.A.α (M.A.straight a)) = M.A.α (M.A.σ (M.A.σ a)) := by
  classical
  have hCC := hpar.1
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨h3, hvC', hX₁⟩ := M.band_tri hn hpar hD ha hφa hout hin
  obtain ⟨hσa, hgC, hgC'⟩ := M.band_g hCC hD ha hφa hout hin
  generalize hg : M.A.σ (M.A.σ a) = g at h3 hvC' hX₁ hgC hgC' ⊢
  generalize hu : M.A.φ g = u at h3 hvC'
  generalize hv : M.A.φ u = v at h3 hvC'
  have ha2 : M.A.σ (M.A.σ g) = a := by rw [← hg, M.A.σ_σ_σ_σ]
  have cg : M.A.curve g = C := by rw [← hg, M.A.curve_σσ, ha]
  have cuC : M.A.curve u ≠ C := by rw [← hu, ← cg]; exact M.A.curve_φ_ne g
  have hcg : M.A.crossingOf g = M.A.crossingOf a := by rw [← hg, M.A.crossingOf_σσ]
  have hcu : M.A.crossingOf u = M.A.crossingOf (M.A.α g) := by rw [← hu, M.A.crossingOf_φ]
  have hcv : M.A.crossingOf v = M.A.crossingOf (M.A.α u) := by rw [← hv, M.A.crossingOf_φ]
  have cuC' : M.A.curve u ≠ C' := by
    intro h; apply hX₁; rw [← hcu, ← h]; exact M.A.mem_curves_crossingOf u
  have hσαu : M.A.σ (M.A.α u) = v := by rw [← hv, M.A.φ_apply]
  have hσαg : M.A.σ (M.A.α g) = u := by rw [← hu, M.A.φ_apply]
  have cellu : M.A.cellOf u = M.A.cellOf g := by rw [← hu, M.A.cellOf_φ]
  have cellv : M.A.cellOf v = M.A.cellOf g := by rw [← hv, M.A.cellOf_φ, cellu]
  -- the band end triangle `Δ`
  have h3' : M.A.φ (M.A.φ (M.A.φ g)) = g := by rw [hu, hv, h3]
  have hΔ : M.A.IsTriangle (M.A.cellOf g) :=
    Lens.isTriangle_of h3' (by rw [hu]; intro h; exact cuC (by rw [h, cg]))
      (by rw [hu, hv]; intro h; exact hCC (by rw [← cg, ← h, hvC']))
  have hzΔ : M.A.cellOf g ≠ M.z := fun h => M.not_inside_z C (h ▸ hgC)
  -- the crossings `Z₂ = a`, `Z₁ = α a`, `X₁ = α g`, `Y₁ = α u`, `X₀ = α (straight a)`
  have hZ2 := digon_corner M.A hD rfl
  rw [ha, hφa] at hZ2
  have hZ1 := digon_corner M.A hD (M.A.cellOf_φ a)
  rw [ha, hφa, M.A.crossingOf_φ] at hZ1
  have hZ12 : M.A.crossingOf (M.A.α a) ≠ M.A.crossingOf a := M.A.crossingOf_α_ne a
  have hX1C : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α g)) := by
    rw [← cg, ← M.A.curve_α]; exact M.A.mem_curves_crossingOf _
  have hY1C' : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α u)) := by
    rw [← hvC', ← hσαu]; exact M.A.mem_curves_crossingOf_σ _
  have hY1C : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α u)) := by
    rw [M.A.mem_curves_end_iff cuC, hσαu, hvC']; exact Ne.symm hCC
  have ne_cr : ∀ {x y : M.A.Crossing} {E : Fin (m + 1)}, E ∈ Arrangement.Crossing.curves M.A x →
      E ∉ Arrangement.Crossing.curves M.A y → x ≠ y := fun h1 h2 h => h2 (h ▸ h1)
  have haC' : M.A.curve a ≠ C' := by rw [ha]; exact hCC
  have hP := M.A.two_mul_le_period_straight a
  obtain ⟨-, hfa⟩ := M.walk_flips haC' hZ2.2 hZ1.2
  have hX0C' : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight a))) := by
    intro h
    have h1 : 1 ∈ Walk.flipsOn M.A C' a := by
      rw [Walk.mem_flipsOn, pow_one]
      exact ⟨by omega, (M.A.mem_curves_end_iff (by rw [M.A.curve_straight]; exact haC')).1 h⟩
    rw [hfa, mem_insert, mem_singleton] at h1
    omega
  have hpα : (M.A.straight ^ (period M.A.straight a - 1)) a = M.A.α g := by
    rw [← hg, ← M.A.straight_symm_apply]
    apply (Equiv.eq_symm_apply _).2
    have := Walk.pow_period_apply M.A a
    rwa [show period M.A.straight a = period M.A.straight a - 1 + 1 by omega, pow_succ',
      Perm.mul_apply] at this
  have hX0X1 : M.A.crossingOf (M.A.α (M.A.straight a)) ≠ M.A.crossingOf (M.A.α g) := by
    intro h
    have e1 : M.A.crossingOf (M.A.α (M.A.straight a)) = M.A.crossingOf ((M.A.straight ^ 2) a) := by
      have := Chain.crossingOf_α_pow (A := M.A) a 1; rwa [pow_one] at this
    rw [e1, ← hpα] at h
    have := Lens.cross_inj (A := M.A) (m := period M.A.straight a - 1) (by omega) (by omega)
      le_rfl h
    omega
  have hαaC' : M.A.curve (M.A.α a) ≠ C' := by rw [M.A.curve_α]; exact haC'
  obtain ⟨-, hfαa⟩ := M.walk_flips hαaC' hZ1.2 (by rw [M.A.α_α]; exact hZ2.2)
  have hP2 := M.A.two_mul_le_period_straight (M.A.α a)
  have hX2C' : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight g))) := by
    intro h
    have e : (M.A.straight ^ 2) (M.A.α a) = M.A.straight g := by
      rw [pow_two, Perm.mul_apply, M.A.straight_α, hg]
    have h2 : 2 ∈ Walk.flipsOn M.A C' (M.A.α a) := by
      rw [Walk.mem_flipsOn, e]
      exact ⟨by omega, (M.A.mem_curves_end_iff (by rw [M.A.curve_straight, cg]; exact hCC)).1 h⟩
    rw [hfαa, mem_insert, mem_singleton] at h2
    omega
  -- corners of `Δ`
  have ncΔ : ∀ y, M.A.crossingOf y ≠ M.A.crossingOf a → M.A.crossingOf y ≠ M.A.crossingOf (M.A.α g) →
      M.A.crossingOf y ≠ M.A.crossingOf (M.A.α u) → ¬ M.A.IsCorner g y := fun y h0 h1 h2 =>
    not_corner_of h3' (by rw [hcg]; exact h0) (by rw [hu, hcu]; exact h1) (by rw [hu, hv, hcv]; exact h2)
  have ncZ1 : ∀ y, M.A.crossingOf y = M.A.crossingOf (M.A.α a) → ¬ M.A.IsCorner g y := by
    intro y hy
    refine ncΔ y (by rw [hy]; exact hZ12) (by rw [hy]; exact ne_cr hZ1.2 hX₁) ?_
    rw [hy]; exact ne_cr hZ1.1 hY1C
  -- the first flip
  have hαv : M.A.α v = M.A.σ a := by
    apply M.A.σ.injective; rw [← M.A.φ_apply, h3, ← hg]
  have hαφa : M.A.α (M.A.φ a) = M.A.σ (M.A.σ (M.A.σ a)) := by
    apply M.A.σ.injective; rw [← M.A.φ_apply, M.A.φ_φ_of_digon hD, M.A.σ_σ_σ_σ]
  have hsv : M.A.straight v = M.A.α (M.A.φ a) := by rw [M.A.straight_apply, hαv, hαφa]
  have e1 : (M.flip g hΔ).A.φ (M.A.α g) = M.A.φ a := by
    change (M.A.σ * Arrangement.flipα hΔ) (M.A.α g) = _
    rw [Arrangement.flipφ_α hΔ rfl, ha2]
  have e2 : (M.flip g hΔ).A.φ (M.A.φ a) = M.A.straight u := by
    change (M.A.σ * Arrangement.flipα hΔ) (M.A.φ a) = _
    rw [show M.A.φ a = M.A.α (M.A.straight v) by rw [hsv, M.A.α_α],
      Arrangement.flipφ_end_straight hΔ cellv, M.A.straight_apply, hσαu]
  have e3 : (M.flip g hΔ).A.φ (M.A.straight u) = M.A.α g := by
    change (M.A.σ * Arrangement.flipα hΔ) (M.A.straight u) = _
    rw [Arrangement.flipφ_straight hΔ cellu, ← hσαg, M.A.σ_σ_σ_σ]
  have hD'3 : (M.flip g hΔ).A.φ ((M.flip g hΔ).A.φ ((M.flip g hΔ).A.φ (M.A.α g))) = M.A.α g := by
    rw [e1, e2, e3]
  have hD' : (M.flip g hΔ).A.IsTriangle ((M.flip g hΔ).A.cellOf (M.A.α g)) := by
    refine Lens.isTriangle_of hD'3 ?_ ?_
    · rw [e1]; intro h
      have := congrArg M.A.curve h; rw [M.A.curve_α, cg, hφa] at this; exact hCC this.symm
    · rw [e1, e2]; intro h
      have := congrArg M.A.curve h; rw [M.A.curve_straight, M.A.curve_α, cg] at this; exact cuC this
  have hzD' : (M.flip g hΔ).A.cellOf (M.A.α g) ≠ (M.flip g hΔ).z := by
    change (M.A.flip g hΔ).cellOf (M.A.α g) ≠ Arrangement.flipCellEquiv hΔ M.z
    rw [Arrangement.flip_cellOf hΔ, Arrangement.flipG'_α hΔ rfl, ha2]
    intro h; exact M.not_inside_z C' ((Arrangement.flipCellEquiv hΔ).injective h ▸ hin)
  have hbφa : (M.flip g hΔ).A.cellOf (M.A.φ a) = (M.flip g hΔ).A.cellOf (M.A.α g) := by
    rw [← e1, (M.flip g hΔ).A.cellOf_φ]
  -- corners of `D'`
  have ncD' : ∀ y, M.A.crossingOf y ≠ M.A.crossingOf (M.A.α g) →
      M.A.crossingOf y ≠ M.A.crossingOf (M.A.α a) → M.A.crossingOf y ≠ M.A.crossingOf (M.A.α u) →
      ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) y := by
    intro y h0 h1 h2
    refine not_corner_of hD'3 h0 ?_ ?_
    · rw [e1]; change M.A.crossingOf y ≠ M.A.crossingOf (M.A.φ a); rw [M.A.crossingOf_φ]; exact h1
    · rw [e1, e2]; change M.A.crossingOf y ≠ M.A.crossingOf (M.A.straight u)
      rw [M.A.crossingOf_straight]; exact h2
  -- the second flip: `cellOf a` is a digon again
  have hα1 : (M.flip g hΔ).A.α ((M.flip g hΔ).A.σ ((M.flip g hΔ).A.σ (M.A.α g))) = a := by
    change Arrangement.flipα hΔ (M.A.σ (M.A.σ (M.A.α g))) = a
    rw [Arrangement.flipα_apply, Arrangement.flipρ_σσ, Arrangement.flipρ_α_of_mem hΔ rfl,
      M.A.σ_σ_σ_σ, Arrangement.flipρ_α_of_mem hΔ rfl, ha2]
  have f1 : ((M.flip g hΔ).A.flip (M.A.α g) hD').φ a = M.A.φ a := by
    have := Arrangement.flipφ_end_σσ hD' rfl
    rw [hα1, e1] at this
    exact this
  have hρφa : Arrangement.flipρ hΔ (M.A.φ a) = M.A.φ a :=
    Arrangement.flipρ_of_not_corner hΔ (ncZ1 _ (M.A.crossingOf_φ a))
  have hα1φa : (M.flip g hΔ).A.α (M.A.φ a) = v := by
    change Arrangement.flipα hΔ (M.A.φ a) = v
    rw [Arrangement.flipα_apply, hρφa, ← hsv, Arrangement.flipρ_straight_of_mem hΔ cellv]
  have f2 : ((M.flip g hΔ).A.flip (M.A.α g) hD').φ (M.A.φ a) = a := by
    have := Arrangement.flipφ_of_mem hD' hbφa
    change (M.flip g hΔ).A.σ (Arrangement.flipα hD' (M.A.φ a)) = a
    change (M.flip g hΔ).A.σ (Arrangement.flipα hD' (M.A.φ a)) = _ at this
    rw [this]
    change (M.A.σ * Arrangement.flipα hΔ) (M.A.σ (M.A.σ ((M.flip g hΔ).A.α (M.A.φ a)))) = a
    rw [hα1φa, Arrangement.flipφ_σσ hΔ cellv, h3, ha2]
  have hD2 : ((M.flip g hΔ).A.flip (M.A.α g) hD').IsDigon
      (((M.flip g hΔ).A.flip (M.A.α g) hD').cellOf a) := by
    refine isDigon_of (by rw [f1, f2]) ?_
    rw [f1]; intro h
    have := congrArg M.A.curve h; rw [hφa, ha] at this; exact hCC this.symm
  -- interior statuses of the digon
  have hasC : M.HasSideOn C (M.A.cellOf g) := ⟨g, M.A.mem_darts_cellOf_self g, cg⟩
  have hasC' : M.HasSideOn C' (M.A.cellOf g) :=
    ⟨v, by rw [← cellv]; exact M.A.mem_darts_cellOf_self v, hvC'⟩
  have hc1 : (M.flip g hΔ).A.cellOf a = Arrangement.flipCellEquiv hΔ (M.A.cellOf g) := by
    change (M.A.flip g hΔ).cellOf a = _
    rw [Arrangement.flip_cellOf hΔ, ← ha2, Arrangement.flipG'_σσ (rfl : M.A.cellOf g = M.A.cellOf g)]
  have hout1 : ¬ (M.flip g hΔ).Inside C ((M.flip g hΔ).A.cellOf a) := by
    rw [hc1, flip_inside M hΔ hzΔ]; simp [hgC, hasC]
  have hin1 : (M.flip g hΔ).Inside C' ((M.flip g hΔ).A.cellOf a) := by
    rw [hc1, flip_inside M hΔ hzΔ]; simp [hgC', hasC']
  have nca : ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) a := by
    exact ncD' a (ne_cr hZ2.2 hX₁) (Ne.symm hZ12) (ne_cr hZ2.1 hY1C)
  have hc2 : ((M.flip g hΔ).A.flip (M.A.α g) hD').cellOf a =
      Arrangement.flipCellEquiv hD' ((M.flip g hΔ).A.cellOf a) :=
    Arrangement.flip_cellOf_of_not_corner hD' nca
  have hne : (M.flip g hΔ).A.cellOf a ≠ (M.flip g hΔ).A.cellOf (M.A.α g) :=
    Arrangement.not_mem_of_not_corner nca
  have hout2 : ¬ ((M.flip g hΔ).flip (M.A.α g) hD').Inside C (((M.flip g hΔ).flip (M.A.α g) hD').A.cellOf a) := by
    change ¬ ((M.flip g hΔ).flip (M.A.α g) hD').Inside C (((M.flip g hΔ).A.flip (M.A.α g) hD').cellOf a)
    rw [hc2, flip_inside (M.flip g hΔ) hD' hzD']; simp [hout1, hne]
  have hin2 : ((M.flip g hΔ).flip (M.A.α g) hD').Inside C' (((M.flip g hΔ).flip (M.A.α g) hD').A.cellOf a) := by
    change ((M.flip g hΔ).flip (M.A.α g) hD').Inside C' (((M.flip g hΔ).A.flip (M.A.α g) hD').cellOf a)
    rw [hc2, flip_inside (M.flip g hΔ) hD' hzD']; simp [hin1, hne]
  -- crossings off `C ∪ C'` keep their statuses
  have hstat : ∀ (E : Fin (m + 1)) (y : D), E ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
      ¬ M.A.IsCorner g y → ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) y →
      (((M.flip g hΔ).flip (M.A.α g) hD').CrossInside E (M.A.crossingOf y) ↔ M.CrossInside E (M.A.crossingOf y)) := by
    intro E y hE n1 n2
    have h1 := crossInside_flip (M.flip g hΔ) hD' hzD' y hE
    have h2 := crossInside_flip M hΔ hzΔ y hE
    simp only [n1, n2, false_and, not_false_eq_true, iff_true] at h1 h2
    exact h1.trans h2
  have hparN : ((M.flip g hΔ).flip (M.A.α g) hD').Par C C' := by
    have hφN : ((M.flip g hΔ).flip (M.A.α g) hD').A.curve (((M.flip g hΔ).flip (M.A.α g) hD').A.φ a) = C' := by
      change M.A.curve (((M.flip g hΔ).A.flip (M.A.α g) hD').φ a) = C'
      rw [f1]; exact hφa
    refine ⟨hCC, ⟨a, hD2, ha, hφN, hout2, hin2⟩, fun x h1 h2 => ?_⟩
    obtain ⟨y, rfl⟩ := x.exists_mk
    change C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at h1
    change C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at h2
    have n1 : ¬ M.A.IsCorner g y :=
      ncΔ y (fun h => h2 (by rw [h]; exact hZ2.2)) (fun h => h1 (by rw [h]; exact hX1C))
        (fun h => h2 (by rw [h]; exact hY1C'))
    have n2 : ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) y :=
      ncD' y (fun h => h1 (by rw [h]; exact hX1C)) (fun h => h2 (by rw [h]; exact hZ1.2))
        (fun h => h2 (by rw [h]; exact hY1C'))
    change ¬ (((M.flip g hΔ).flip (M.A.α g) hD').CrossInside C (M.A.crossingOf y) ∧ ¬ ((M.flip g hΔ).flip (M.A.α g) hD').CrossInside C' (M.A.crossingOf y))
    rw [hstat C y h1 n1 n2, hstat C' y h2 n1 n2]
    exact hpar.2.2 _ h1 h2
  -- the marked kept dart (moved off `X₁` if needed)
  have hwk := (hK w).1 hwK
  have keep_of : ∀ y, M.A.curve y ≠ C' → C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
      K y := fun y h1 h2 => (hK y).2 ⟨h1, h2⟩
  set δ := M.A.deleteOn C' hm K hK with hδ
  have hmove : ∀ (y : D) (hy : K y) (hαy : K (M.A.α y)) (hφy : M.A.φ y = w),
      δ.cellOf ⟨y, hy⟩ = δ.cellOf ⟨w, hwK⟩ := by
    intro y hy hαy hφy
    have h := deleteOn_φ_val (hm := hm) (hK := hK) (z := ⟨y, hy⟩) hαy
    rw [← δ.cellOf_φ ⟨y, hy⟩]
    congr 1
    exact Subtype.ext (h.trans hφy)
  obtain ⟨w', hw'K, hw'z, hw'δ, hw'X⟩ : ∃ (w' : D) (hw'K : K w'), M.A.cellOf w' = M.z ∧
      δ.cellOf ⟨w', hw'K⟩ = δ.cellOf ⟨w, hwK⟩ ∧
      M.A.crossingOf w' ≠ M.A.crossingOf (M.A.α g) := by
    by_cases hX : M.A.crossingOf w = M.A.crossingOf (M.A.α g)
    swap
    · exact ⟨w, hwK, hw, rfl, hX⟩
    have hz' : ∀ E, ¬ M.Inside E (M.A.cellOf w) := fun E => by rw [hw]; exact M.not_inside_z E
    have hmem := (M.A.crossingOf_eq_iff).1 hX.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hσu : M.A.curve (M.A.σ u) = C := by rw [← hσαg, M.A.curve_σσ, M.A.curve_α, cg]
    rcases hmem with h | h | h | h
    · -- `w = α g`: use the dart before it on the cell
      refine ⟨M.A.α (M.A.σ (M.A.σ u)), ?_, ?_, ?_, ?_⟩
      · refine keep_of _ (by rw [M.A.curve_α, M.A.curve_σσ]; exact cuC') fun hc => ?_
        have hcu2 : M.A.curve (M.A.σ (M.A.σ u)) ≠ C := by rw [M.A.curve_σσ]; exact cuC
        have hc' : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.σ (M.A.σ u)))) := by
          rw [M.A.mem_curves_end_iff hcu2]
          rw [M.A.mem_curves_end_iff (by rw [M.A.curve_σσ]; exact cuC')] at hc
          rw [hc]; exact Ne.symm hCC
        have := M.par_inside_C_end hpar hcu2 hc hc'
        rw [M.inside_σσ_iff, cellu, hσu] at this
        simp [hgC, cuC] at this
      · rw [← M.A.cellOf_φ, M.A.φ_apply, M.A.α_α, ← hσαg, M.A.σ_σ_σ_σ, ← h, hw]
      · refine hmove _ _ ?_ ?_
        · rw [M.A.α_α]
          refine keep_of _ (by rw [M.A.curve_σσ]; exact cuC') ?_
          rw [M.A.crossingOf_σσ, hcu]; exact hX₁
        · rw [M.A.φ_apply, M.A.α_α, ← hσαg, M.A.σ_σ_σ_σ, ← h]
      · rw [Ne, ← hcu, ← M.A.crossingOf_σσ u]
        exact M.A.crossingOf_α_ne _
    · exfalso; apply hz' C; rw [h, ← M.A.φ_apply, M.A.cellOf_φ]; exact hgC
    · exfalso; apply hz' C; rw [h]
      change M.Inside C (M.A.cellOf (M.A.straight g))
      rw [M.inside_straight, hσαg]; simp [hgC, cuC]
    · -- `w = σ³ (α g)`: use `α (straight g)`
      refine ⟨M.A.α (M.A.straight g), ?_, ?_, ?_, ?_⟩
      · refine keep_of _ (by rw [M.A.curve_α, M.A.curve_straight, cg]; exact hCC) hX2C'
      · rw [← M.A.cellOf_φ, M.A.φ_apply, M.A.α_α, M.A.straight_apply, ← h, hw]
      · refine hmove _ _ ?_ ?_
        · rw [M.A.α_α]
          refine keep_of _ (by rw [M.A.curve_straight, cg]; exact hCC) ?_
          rw [M.A.crossingOf_straight]; exact hX₁
        · rw [M.A.φ_apply, M.A.α_α, M.A.straight_apply, ← h]
      · rw [Ne, ← M.A.crossingOf_straight g]
        exact M.A.crossingOf_α_ne _
  have hw'k := (hK w').1 hw'K
  have hw'Δ : ¬ M.A.IsCorner g w' :=
    ncΔ w' (fun h => hw'k.2 (by rw [h]; exact hZ2.2)) hw'X (fun h => hw'k.2 (by rw [h]; exact hY1C'))
  have hw'D' : ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) w' :=
    ncD' w' hw'X (fun h => hw'k.2 (by rw [h]; exact hZ1.2)) (fun h => hw'k.2 (by rw [h]; exact hY1C'))
  have hw'1 : (M.flip g hΔ).A.cellOf w' = (M.flip g hΔ).z := by
    change (M.A.flip g hΔ).cellOf w' = Arrangement.flipCellEquiv hΔ M.z
    rw [Arrangement.flip_cellOf_of_not_corner hΔ hw'Δ, hw'z]
  have hw'2 : ((M.flip g hΔ).flip (M.A.α g) hD').A.cellOf w' = ((M.flip g hΔ).flip (M.A.α g) hD').z := by
    change ((M.flip g hΔ).A.flip (M.A.α g) hD').cellOf w' = Arrangement.flipCellEquiv hD' (M.flip g hΔ).z
    rw [Arrangement.flip_cellOf_of_not_corner hD' hw'D', hw'1]
  -- `M − C'` does not change (both flips have a side on `C'`)
  have hK1 : ∀ e, K e ↔ Keep (M.flip g hΔ).A C' e := hK
  have hK2 : ∀ e, K e ↔ Keep ((M.flip g hΔ).flip (M.A.α g) hD').A C' e := hK
  have hdel1 := deleteOn_flip_of_side M.A C' hm K hK hΔ
    ⟨v, by rw [← cellv]; exact M.A.mem_darts_cellOf_self v, hvC'⟩ hK1
  have hdel2 := deleteOn_flip_of_side (M.flip g hΔ).A C' hm K hK1 hD'
    ⟨M.A.φ a, by rw [← hbφa]; exact (M.flip g hΔ).A.mem_darts_cellOf_self _, hφa⟩ hK2
  -- the edge of `C` arriving at the digon now ends at `X₁`
  have hβΔ : ¬ M.A.IsCorner g (M.A.α (M.A.straight a)) :=
    ncΔ _ (fun h => hX0C' (by rw [h]; exact hZ2.2)) hX0X1
      (fun h => hX0C' (by rw [h]; exact hY1C'))
  have hsaΔ : ¬ M.A.IsCorner g (M.A.straight a) := ncZ1 _ (M.A.crossingOf_straight a)
  have hαaΔ : ¬ M.A.IsCorner g (M.A.α a) := ncZ1 _ rfl
  have hβD' : ¬ (M.flip g hΔ).A.IsCorner (M.A.α g) (M.A.α (M.A.straight a)) :=
    ncD' _ hX0X1 (fun h => hX0C' (by rw [h]; exact hZ1.2)) (fun h => hX0C' (by rw [h]; exact hY1C'))
  have hA1β : (M.flip g hΔ).A.α (M.A.α (M.A.straight a)) = M.A.straight a := by
    change Arrangement.flipα hΔ (M.A.α (M.A.straight a)) = _
    rw [Arrangement.flipα_apply, Arrangement.flipρ_of_not_corner hΔ hβΔ, M.A.α_α,
      Arrangement.flipρ_of_not_corner hΔ hsaΔ]
  have hA1αg : (M.flip g hΔ).A.α (M.A.α g) = M.A.α a := by
    change Arrangement.flipα hΔ (M.A.α g) = _
    rw [Arrangement.flipα_apply, Arrangement.flipρ_α_of_mem hΔ rfl, ha2,
      Arrangement.flipρ_of_not_corner hΔ hαaΔ]
  have hfin : ((M.flip g hΔ).flip (M.A.α g) hD').A.α (M.A.α (M.A.straight a)) = M.A.α g := by
    change Arrangement.flipα hD' (M.A.α (M.A.straight a)) = M.A.α g
    rw [Arrangement.flipα_apply, Arrangement.flipρ_of_not_corner hD' hβD', hA1β]
    rw [show M.A.straight a = (M.flip g hΔ).A.σ ((M.flip g hΔ).A.σ ((M.flip g hΔ).A.α (M.A.α g))) by
      rw [hA1αg]; rfl]
    rw [Arrangement.flipρ_σσ, Arrangement.flipρ_α_of_mem hD' rfl]
    exact M.A.σ_σ_σ_σ _
  refine ⟨_, (Relation.ReflTransGen.single ⟨g, hΔ, hzΔ, rfl⟩).tail ⟨M.A.α g, hD', hzD', rfl⟩,
    hK2, hdel2.trans hdel1, hparN, rfl, ⟨w', hw'K, hw'2, hw'δ⟩, hfin⟩

end Pca.FlipGraph
