/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: antipodal flips are reversible and can be transported along isomorphisms
(`doc/pca/great.md` section 3.4)
-/
import Pca.Great.R_Sym

open Equiv Finset

namespace Pca.Great

universe u v

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem corners_eq {f : A.Cell} {S : Finset D} (h : f.darts = S.image (fun b => A.σ (A.σ b))) :
    Arrangement.Cell.corners A f = S.image A.crossingOf := by
  simp only [Arrangement.Cell.corners, h, image_image]
  congr 1
  funext b
  simp only [Function.comp, A.crossingOf_σ]

theorem curves_eq {f : A.Cell} {S : Finset D} (h : f.darts = S.image (fun b => A.σ (A.σ b))) :
    Arrangement.Cell.curves A f = S.image A.curve := by
  simp only [Arrangement.Cell.curves, h, image_image]
  congr 1
  funext b
  simp only [Function.comp, A.isArrangement.curve_σσ]

/-- **Antipodal flips are reversible.** -/
theorem AFlip.symm {B : Arrangement n D} (h : A.AFlip B) : B.AFlip A := by
  obtain ⟨d, e, hT, hanti, hT', rfl⟩ := h
  set A1 := A.flip d hT
  have hdE := flip_darts_antipodal hT hanti
  -- the two flipped triangles in `B`
  have h1 : (((A.flip d hT).flip e hT').cellOf (A.σ (A.σ e))).darts =
      (A.cellOf e).darts.image (fun b => A.σ (A.σ b)) := by
    rw [← hdE]; exact Arrangement.flip_darts_triangle hT'
  have hcorE1 : Arrangement.Cell.corners A1 (A1.cellOf e) =
      Arrangement.Cell.corners A (A.cellOf e) := by
    simp only [Arrangement.Cell.corners]; rw [hdE]; rfl
  have hfar : ∀ z, A1.cellOf z = A1.cellOf (A.σ (A.σ d)) → ¬ A1.IsCorner e z := by
    intro z hz hc
    have hz' : z ∈ (A1.cellOf (A.σ (A.σ d))).darts := Orbit.mem_darts.2 hz
    rw [Arrangement.flip_darts_triangle hT] at hz'
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hz'
    unfold Arrangement.IsCorner at hc
    rw [hcorE1] at hc
    have hc' : A.crossingOf b ∈ Arrangement.Cell.corners A (A.cellOf e) := by
      rw [← A.crossingOf_σ, ← A.crossingOf_σ]; exact hc
    rw [hanti.2.2, mem_filter] at hc'
    exact hc'.2.2 (mem_image.2 ⟨b, hb, rfl⟩)
  have h2 : (((A.flip d hT).flip e hT').cellOf (A.σ (A.σ d))).darts =
      (A.cellOf d).darts.image (fun b => A.σ (A.σ b)) := by
    rw [flip_darts_far hT' hfar]; exact Arrangement.flip_darts_triangle hT
  have hT2 : ((A.flip d hT).flip e hT').IsTriangle
      (((A.flip d hT).flip e hT').cellOf (A.σ (A.σ d))) := by
    change Orbit.size _ = 3
    unfold Orbit.size
    rw [h2, card_image_of_injective _ (fun x y hxy => by
      have := congrArg (fun z => A.σ (A.σ z)) hxy
      simpa [A.σ_σ_σ_σ] using this)]
    exact hT
  have hc1 := corners_eq (A := (A.flip d hT).flip e hT') h1
  have hc2 := corners_eq (A := (A.flip d hT).flip e hT') h2
  have hv1 := curves_eq (A := (A.flip d hT).flip e hT') h1
  refine ⟨A.σ (A.σ e), A.σ (A.σ d), Pca.FlipGraph.flip_tri' hT', ⟨Pca.FlipGraph.flip_tri' hT',
    hT2, ?_⟩, ?_⟩
  · rw [hc2, hc1, hv1]
    change (A.cellOf d).darts.image A.crossingOf = univ.filter fun x =>
      Arrangement.Crossing.curves A x ⊆ (A.cellOf e).darts.image A.curve ∧
        x ∉ (A.cellOf e).darts.image A.crossingOf
    change Arrangement.Cell.corners A (A.cellOf d) = univ.filter fun x =>
      Arrangement.Crossing.curves A x ⊆ Arrangement.Cell.curves A (A.cellOf e) ∧
        x ∉ Arrangement.Cell.corners A (A.cellOf e)
    rw [curves_antipodal hanti]
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨curves_corner_sub hT hx, fun h => ?_⟩
      rw [hanti.2.2, mem_filter] at h
      exact h.2.2 hx
    · rintro ⟨hsub, hx⟩
      by_contra hc
      exact hx (by rw [hanti.2.2, mem_filter]; exact ⟨mem_univ _, hsub, hc⟩)
  · have key : ∀ X : Arrangement n D, X = A1 →
        ∃ hT2 : X.IsTriangle (X.cellOf (A.σ (A.σ d))), A = X.flip (A.σ (A.σ d)) hT2 := by
      intro X hX; subst hX
      exact ⟨Pca.FlipGraph.flip_tri' hT, (Pca.FlipGraph.flip_flip hT).symm⟩
    exact key _ (Pca.FlipGraph.flip_flip hT')

/-- **Transport of an antipodal flip along an isomorphism.** -/
theorem AFlip.transport {D' : Type v} [Fintype D'] [DecidableEq D'] {X : Arrangement n D}
    {Y Y₁ : Arrangement n D'} (hX : X.IsGreat) (hY : Y.IsGreat) (φ : Iso X Y) (h : Y.AFlip Y₁) :
    ∃ X₁, X.AFlip X₁ ∧ Nonempty (Iso X₁ Y₁) := by
  obtain ⟨d, e', hT, hanti, hT', rfl⟩ := h
  obtain ⟨dX, rfl⟩ := φ.toEquiv.surjective d
  set e := φ.toEquiv
  have hσ := φ.map_σ
  have hα := φ.map_α
  have hTX : X.IsTriangle (X.cellOf dX) := by
    change (X.cellOf dX).size = 3
    rw [← Pca.FlipGraph.size_cellOf_map e hσ hα dX]; exact hT
  obtain ⟨hTX', hXflip⟩ := exists_aflip hX hTX
  refine ⟨_, hXflip, ?_⟩
  -- the first flip
  have hα1 : ∀ y, e (Arrangement.flipα hTX y) = Arrangement.flipα hT (e y) :=
    fun y => Pca.FlipGraph.flipα_map e hσ hα hTX y
  have hσ1 : ∀ y, e ((X.flip dX hTX).σ y) = (Y.flip (e dX) hT).σ (e y) := hσ
  -- the antipodal darts correspond
  have hpow : ∀ (k : ℕ) (y : D), e ((X.straight ^ k) y) = (Y.straight ^ k) (e y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ', Perm.mul_apply, Pca.FlipGraph.map_straight e hσ hα, ih, pow_succ',
        Perm.mul_apply]
  have hant : e (X.α (ant X dX)) = Y.α (ant Y (e dX)) := by
    rw [hα]; unfold ant; rw [hpow]
  have hcell : (Y.flip (e dX) hT).cellOf (e (X.α (ant X dX))) = (Y.flip (e dX) hT).cellOf e' := by
    apply cellOf_eq_of_darts
    rw [hant, flip_darts_antipodal hT (isAntipodalTri_ant hY hT), flip_darts_antipodal hT hanti,
      isAntipodalTri_unique (isAntipodalTri_ant hY hT) hanti]
  have hα2 : ∀ y, e (Arrangement.flipα hTX' y) = Arrangement.flipα hT' (e y) := by
    intro y
    rw [Pca.FlipGraph.flipα_map e hσ1 hα1 hTX' y]
    exact congrFun (congrArg (⇑) (flipα_congr _ hT' hcell)) (e y)
  exact ⟨⟨e, φ.curveEquiv, hσ, hα2, φ.map_curve⟩⟩

end Pca.Great
