/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweep: auxiliary facts
-/
import Pca.Great.Swp_F2
import Pca.Great.R_PotFlip

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}

theorem not_corner_of_curve {B : Arrangement n D'} {t : D'} (hT : B.IsTriangle (B.cellOf t))
    {C : Fin n} (hC : C ∉ Arrangement.Cell.curves B (B.cellOf t)) {y : D'}
    (hy : C ∈ Arrangement.Crossing.curves B (B.crossingOf y)) : ¬ B.IsCorner t y :=
  fun h => hC (curves_corner_sub hT h hy)

/-- The antipodal triangle in the flipped arrangement: same darts, curves and corners. -/
theorem aflip_data {B : Arrangement n D'} {d e : D'} (hT : B.IsTriangle (B.cellOf d))
    (hanti : B.IsAntipodalTri (B.cellOf d) (B.cellOf e)) :
    Arrangement.Cell.curves (B.flip d hT) ((B.flip d hT).cellOf e) =
        Arrangement.Cell.curves B (B.cellOf d) ∧
      Arrangement.Cell.corners (B.flip d hT) ((B.flip d hT).cellOf e) =
        Arrangement.Cell.corners B (B.cellOf e) := by
  have hdarts := flip_darts_antipodal hT hanti
  refine ⟨?_, ?_⟩
  · rw [← curves_antipodal hanti]; simp only [Arrangement.Cell.curves]; rw [hdarts]; rfl
  · simp only [Arrangement.Cell.corners]; rw [hdarts]; rfl

/-- In a great arrangement with `n ≥ 3`, a cell has at most one corner on a given pair of
curves. -/
theorem cell_pair_unique {A : Arrangement n D} (hA : A.IsGreat) (h3 : 3 ≤ n) {f : A.Cell}
    {d d' : D} (hd : d ∈ f.darts) (hd' : d' ∈ f.darts)
    (h : Arrangement.Crossing.curves A (A.crossingOf d) =
      Arrangement.Crossing.curves A (A.crossingOf d')) :
    A.crossingOf d = A.crossingOf d' := by
  by_contra hne
  set a := A.curve d
  set b := A.curve (A.σ d)
  have hab : a ≠ b := (A.isArrangement.curve_σ d).symm
  obtain ⟨e, hea, heb⟩ : ∃ e : Fin n, e ≠ a ∧ e ≠ b := by
    have : ({a, b} : Finset (Fin n)).card < (univ : Finset (Fin n)).card := by
      rw [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (card_le_two) (by omega)
    obtain ⟨e, -, he⟩ := exists_mem_notMem_of_card_lt_card this
    simp only [mem_insert, mem_singleton, not_or] at he
    exact ⟨e, he.1, he.2⟩
  obtain ⟨s, hs⟩ := Arrangement.exists_isSide (A := A) e
  have hx : Arrangement.Crossing.curves A (A.crossingOf d) = {a, b} := A.curves_crossingOf d
  have := hA a b e hab (Ne.symm hea) (Ne.symm heb) s hs (A.crossingOf d) (A.crossingOf d') hne
    hx (h.symm.trans hx) d (Orbit.mem_darts.2 rfl) d' (Orbit.mem_darts.2 rfl)
  apply this
  have e1 : A.cellOf d = f := Orbit.mem_darts.1 hd
  have e2 : A.cellOf d' = f := Orbit.mem_darts.1 hd'
  rw [e1, e2]

variable {A : Arrangement n D} {B : Arrangement (n + 1) D'} {ι : D → D'} (hD : IsDeletion B A ι)
include hD

theorem del_curves (d : D) :
    Arrangement.Crossing.curves B (B.crossingOf (ι d)) =
      (Arrangement.Crossing.curves A (A.crossingOf d)).map Fin.castSuccEmb := by
  rw [B.curves_crossingOf, A.curves_crossingOf, ← hD.σ, hD.curve, hD.curve]
  simp [Finset.map_insert]

theorem del_crossing {d d' : D} (h : A.crossingOf d = A.crossingOf d') :
    B.crossingOf (ι d) = B.crossingOf (ι d') := by
  rw [A.crossingOf_eq_iff] at h
  rw [B.crossingOf_eq_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · left; rfl
  · right; left; rw [hD.σ]
  · right; right; left; rw [hD.σ, hD.σ]
  · right; right; right; rw [hD.σ, hD.σ, hD.σ]

end Pca.Great
