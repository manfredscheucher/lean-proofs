/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): crossings inside a curve after a flip

A triangle flip changes the interior status of a crossing `x` with respect to a curve `C` (not
through `x`) exactly when `x` is a corner of the flipped triangle `T` and `C` is a curve of `T`
(the curve of the side opposite to `x`): the flip moves that curve over `x`.
-/
import Pca.FlipGraph.Lens

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

theorem crossInside_flip (M : Marked n D) {d : D} (hT : M.A.IsTriangle (M.A.cellOf d))
    (hz : M.A.cellOf d ≠ M.z) {C : Fin n} (y : D)
    (hx : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y)) :
    (M.flip d hT).CrossInside C (M.A.crossingOf y) ↔
      (M.CrossInside C (M.A.crossingOf y) ↔
        ¬ (M.A.IsCorner d y ∧ M.HasSideOn C (M.A.cellOf d))) := by
  have hx' : ∀ w, M.A.crossingOf w = M.A.crossingOf y →
      C ∉ Arrangement.Crossing.curves (M.flip d hT).A ((M.flip d hT).A.crossingOf w) :=
    fun w hw => by change C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w); rwa [hw]
  by_cases hc : M.A.IsCorner d y
  · obtain ⟨b, hb, hby⟩ := mem_image.1 hc
    rw [Orbit.mem_darts] at hb
    change M.A.cellOf b = M.A.cellOf d at hb
    have hbx : M.A.crossingOf (M.A.σ (M.A.σ b)) = M.A.crossingOf y := by
      rw [M.A.crossingOf_σσ]; exact hby
    have e := (M.flip d hT).crossInside_iff (hx' _ hbx)
    change (M.flip d hT).CrossInside C (M.A.crossingOf _) ↔ _ at e
    rw [hbx] at e
    have e' : M.CrossInside C (M.A.crossingOf y) ↔ M.Inside C (M.A.cellOf d) := by
      rw [← hby, M.crossInside_iff (by rwa [hby]), hb]
    rw [e, e']
    change (M.flip d hT).Inside C ((M.A.flip d hT).cellOf (M.A.σ (M.A.σ b))) ↔ _
    rw [Arrangement.flip_cellOf, Arrangement.flipG'_σσ hb, hb, flip_inside M hT hz]
    simp only [hc, true_and]
  · have e := (M.flip d hT).crossInside_iff (hx' y rfl)
    change (M.flip d hT).CrossInside C (M.A.crossingOf y) ↔ _ at e
    rw [e, M.crossInside_iff hx]
    change (M.flip d hT).Inside C ((M.A.flip d hT).cellOf y) ↔ _
    rw [Arrangement.flip_cellOf_of_not_corner hT hc, flip_inside M hT hz]
    have hne : M.A.cellOf y ≠ M.A.cellOf d := Arrangement.not_mem_of_not_corner hc
    simp only [hne, false_and, not_false_eq_true, iff_true, hc]

end Pca.FlipGraph
