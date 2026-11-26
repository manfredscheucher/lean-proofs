/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): side functions after a triangle flip

If `s` is a side function of `C` in `A`, then on the flipped arrangement the function
`g ↦ s (Φ⁻¹ g) + [Φ⁻¹ g = T and C is a curve of T]` is a side function of `C` (`flip_isSide`):
only the flipped triangle changes its side, and only for its three curves.

Proof: a function is a side function iff it changes across `σ` exactly at darts of `C`
(`cellOf (σ y) = cellOf (α y)`), and `σ` is not changed by the flip. At a crossing that is not a
corner of `T` nothing changes; at a corner, the four new cells are (in the order of the darts
`b, σ b, σ² b, σ³ b`, `b` a dart of `T` there) the cell across the side `φ b`, the cell opposite at
the start of `φ b`, `T`, and the cell opposite at the start of `φ² b`.
-/
import Pca.FlipGraph.Basic

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement

variable {A : Arrangement n D} {d : D} (hT : A.IsTriangle (A.cellOf d))

/-- The correction of the side function at the flipped triangle. -/
noncomputable def flipCorr (C : Fin n) (f : A.Cell) : ZMod 2 :=
  if f = A.cellOf d ∧ ∃ y ∈ (A.cellOf d).darts, A.curve y = C then 1 else 0

/-- The side function after the flip. -/
noncomputable def flipSide (C : Fin n) (s : A.Cell → ZMod 2) : (A.flip d hT).Cell → ZMod 2 :=
  fun g => s ((flipCellEquiv hT).symm g) + flipCorr (d := d) C ((flipCellEquiv hT).symm g)

private theorem z0 : ∀ t g p : ZMod 2, t + g + (t + g + p) = p := by decide
private theorem z1 : ∀ t g p q : ZMod 2, t + g + p + (t + (p + g + q)) = q := by decide
private theorem z2 : ∀ t g p q : ZMod 2, t + (p + g + q) + (t + q + g) = p := by decide
private theorem z3 : ∀ t g q : ZMod 2, t + q + g + (t + g) = q := by decide
private theorem z4 : ∀ a c : ZMod 2, a + (a + c) = c := by decide

include hT in
/-- The correction at `T` is the sum of the indicators of its three curves. -/
theorem flipCorr_self (C : Fin n) {b : D} (hb : A.cellOf b = A.cellOf d) :
    flipCorr (d := d) C (A.cellOf d) =
      (if A.curve b = C then 1 else 0) + (if A.curve (A.φ b) = C then 1 else 0) +
        (if A.curve (A.φ (A.φ b)) = C then 1 else 0) := by
  have hTb : A.IsTriangle (A.cellOf b) := hb ▸ hT
  have h1 : A.curve (A.φ b) ≠ A.curve b := A.curve_φ_ne b
  have h2 : A.curve (A.φ (A.φ b)) ≠ A.curve (A.φ b) := A.curve_φ_ne (A.φ b)
  have h3 : A.curve b ≠ A.curve (A.φ (A.φ b)) := by
    have := A.curve_φ_ne (A.φ (A.φ b)); rwa [tri_φφφ hTb] at this
  have hmem : (∃ y ∈ (A.cellOf d).darts, A.curve y = C) ↔
      (A.curve b = C ∨ A.curve (A.φ b) = C ∨ A.curve (A.φ (A.φ b)) = C) := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Orbit.mem_darts] at hy
      change A.cellOf y = _ at hy
      rcases (tri_mem_iff hTb).1 (hy.trans hb.symm) with rfl | rfl | rfl <;> simp
    · rintro (h | h | h)
      · exact ⟨b, Orbit.mem_darts.2 hb, h⟩
      · exact ⟨A.φ b, Orbit.mem_darts.2 (by rw [← hb]; exact A.cellOf_φ b), h⟩
      · refine ⟨A.φ (A.φ b), Orbit.mem_darts.2 ?_, h⟩
        change A.cellOf (A.φ (A.φ b)) = _
        rw [A.cellOf_φ, A.cellOf_φ, hb]
  unfold flipCorr
  simp only [true_and, hmem]
  by_cases ha : A.curve b = C <;> by_cases hb' : A.curve (A.φ b) = C <;>
    by_cases hc : A.curve (A.φ (A.φ b)) = C <;>
    simp only [ha, hb', hc, if_true, if_false, true_or, or_true, or_false, false_or] <;>
    first
    | decide
    | (exfalso; exact h1 (hb'.trans ha.symm))
    | (exfalso; exact h2 (hc.trans hb'.symm))
    | (exfalso; exact h3 (ha.trans hc.symm))

/-- The old cell of the new cell of `y`, and its corrected side value. -/
private noncomputable def V (C : Fin n) (s : A.Cell → ZMod 2) (x : D) : ZMod 2 :=
  s (A.cellOf x) + flipCorr (d := d) C (A.cellOf x)

theorem flip_isSide {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) :
    (A.flip d hT).IsSide C (flipSide hT C s) := by
  -- reduce to the `σ`-form: `cellOf' (α' y) = cellOf' (σ y)`
  intro y
  rw [← (A.flip d hT).cellOf_σ y, flip_σ]
  simp only [flipSide, flipCellEquiv_symm_cellOf, flip_curve]
  change V (d := d) C s (flipG' A d y) + V (d := d) C s (flipG' A d (A.σ y)) = _
  by_cases hy : A.IsCorner d y
  · obtain ⟨b, hb, k, hk, rfl⟩ : ∃ b, A.cellOf b = A.cellOf d ∧ ∃ k < 4, y = (A.σ ^ k) b := by
      obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hy
      · exact ⟨b, hb, 0, by norm_num, by simp [h]⟩
      · have hTb : A.IsTriangle (A.cellOf (A.φ b)) := by rw [A.cellOf_φ, hb]; exact hT
        refine ⟨A.φ b, by rw [A.cellOf_φ, hb], 3, by norm_num, ?_⟩
        rw [h, show (A.σ ^ 3) (A.φ b) = A.σ (A.σ (A.σ (A.φ b))) by simp [pow_succ],
          tri_σσσ hTb, tri_φφφ (hb ▸ hT)]
      · have hTb : A.IsTriangle (A.cellOf (A.φ b)) := by rw [A.cellOf_φ, hb]; exact hT
        refine ⟨A.φ b, by rw [A.cellOf_φ, hb], 1, by norm_num, ?_⟩
        rw [h, pow_one, tri_σ hTb, tri_φφφ (hb ▸ hT)]
      · exact ⟨b, hb, 2, by norm_num, by simp [h, pow_succ]⟩
    have hTb : A.IsTriangle (A.cellOf b) := hb ▸ hT
    have hφb : A.cellOf (A.φ b) = A.cellOf d := by rw [A.cellOf_φ, hb]
    have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [A.cellOf_φ, A.cellOf_φ, hb]
    have hTφb : A.IsTriangle (A.cellOf (A.φ b)) := hφb ▸ hT
    have hTφφb : A.IsTriangle (A.cellOf (A.φ (A.φ b))) := hφφb ▸ hT
    -- the four corrected values around the corner
    have v0 : V (d := d) C s (flipG' A d b) = s (A.cellOf d) + if A.curve (A.φ b) = C then 1 else 0 := by
      rw [flipG'_of_mem hT hb, V, cellOf_straight, flipCorr, if_neg (fun h => ne_α hT hφb
        (by rw [h.1])), add_zero, zmod2_eq_add_of_add_eq (hs (A.φ b)), hφb]
    have v1 : V (d := d) C s (flipG' A d (A.σ b)) =
        s (A.cellOf d) + (if A.curve (A.φ b) = C then 1 else 0) + if A.curve b = C then 1 else 0 := by
      rw [tri_σ hTb, flipG'_straight hT hφφb]
      rw [show A.φ (A.φ (A.φ (A.φ b))) = A.φ b by rw [tri_φφφ hTb]]
      rw [V, flipCorr, if_neg (fun h => ne_σσ hT hφb (by rw [h.1])), add_zero, A.side_σσ hs,
        curve_σ_tri hTφb, tri_φφφ hTb, hφb]
    have v2 : V (d := d) C s (flipG' A d (A.σ (A.σ b))) =
        s (A.cellOf d) + ((if A.curve b = C then 1 else 0) + (if A.curve (A.φ b) = C then 1 else 0) + if A.curve (A.φ (A.φ b)) = C then 1 else 0) := by
      rw [flipG'_σσ hb, V, hb, flipCorr_self hT C hb]
    have v3 : V (d := d) C s (flipG' A d (A.σ (A.σ (A.σ b)))) =
        s (A.cellOf d) + (if A.curve (A.φ (A.φ b)) = C then 1 else 0) + if A.curve (A.φ b) = C then 1 else 0 := by
      rw [tri_σσσ hTb, flipG'_α hT hφφb, V, flipCorr,
        if_neg (fun h => ne_σσ hT hφφb (by rw [h.1])), add_zero, A.side_σσ hs,
        curve_σ_tri hTφφb, tri_φφφ hTb, hφφb]
    have cσ : A.curve (A.σ b) = A.curve (A.φ (A.φ b)) := curve_σ_tri hTb
    have cσσ : A.curve (A.σ (A.σ b)) = A.curve b := A.curve_σσ b
    have cσσσ : A.curve (A.σ (A.σ (A.σ b))) = A.curve (A.φ (A.φ b)) := by rw [A.curve_σσσ, cσ]
    have hσ4 : A.σ (A.σ (A.σ (A.σ b))) = b := A.σ_σ_σ_σ b
    interval_cases k
    · simp only [pow_zero, Perm.one_apply]
      rw [v0, v1]; exact z0 _ _ _
    · simp only [pow_one]
      rw [v1, v2, cσ]; exact z1 _ _ _ _
    · simp only [show (A.σ ^ 2) b = A.σ (A.σ b) by simp [pow_succ]]
      rw [v2, v3, cσσ]; exact z2 _ _ _ _
    · simp only [show (A.σ ^ 3) b = A.σ (A.σ (A.σ b)) by simp [pow_succ]]
      rw [hσ4, v3, v0, cσσσ]; exact z3 _ _ _
  · have hσy : ¬ A.IsCorner d (A.σ y) := by rwa [IsCorner, crossingOf_σ]
    rw [flipG'_of_not_corner hy, flipG'_of_not_corner hσy, V, V, flipCorr, flipCorr,
      if_neg (fun h => not_mem_of_not_corner hy h.1),
      if_neg (fun h => not_mem_of_not_corner hσy h.1), add_zero, add_zero, A.side_σ hs]
    exact z4 _ _

end Pca.FlipGraph
