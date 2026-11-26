/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Levi's triangle theorem: the quarter lemma without a frame (`doc/pca/great.md` section 7)

`quarter_tri`: the quarter lemma (`Frame.quarter` with `T = univ`) for arbitrary side functions:
if the quarter `{s_c = u, s_ℓ = v}` contains a crossing off `c` and `ℓ`, it contains a triangle with
a side on `ℓ` that does not touch `c` (Levi's sweep of the lune of `ℓ` and `c`).

`tri_step`: the step of the triangle theorem. `t` runs along a curve from a crossing with `b` to
a crossing with `c`; a fourth curve `g` crosses the curve of `t` on the other projective side of
`b, c` (walk lemma), so the quarter lemma (frame `b`, line `c`) gives a triangle with a side on
`c`, not touching `b`, on the side of `c` of `t` and on the other side of `b`.
-/
import Pca.Great.Tri.Walk
import Pca.Great.Q_Final

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem exists_dart_crossing' {c c' : Fin n} (h : c ≠ c') :
    ∃ w, A.curve w = c ∧ A.curve (A.σ w) = c' := by
  have hcard := A.isArrangement.intersecting c c' h
  obtain ⟨x, hx⟩ := card_pos.1 (show 0 < (univ.filter (fun x : A.Crossing =>
    Arrangement.Crossing.curves A x = {c, c'})).card by
      change 0 < (univ.filter (fun x : Orbit A.σ => crossingCurves A.σ A.curve x = {c, c'})).card
      rw [hcard]; norm_num)
  have hx' : Arrangement.Crossing.curves A x = {c, c'} := (mem_filter.1 hx).2
  obtain ⟨w₀, rfl⟩ := x.exists_mk
  have hw₀ : Arrangement.Crossing.curves A (A.crossingOf w₀) = {c, c'} := hx'
  have m0 := A.mem_curves_crossingOf w₀
  have m1 := A.mem_curves_crossingOf_σ w₀
  have hne := A.isArrangement.curve_σ w₀
  rw [hw₀, mem_insert, mem_singleton] at m0 m1
  rcases m0 with h0 | h0
  · refine ⟨w₀, h0, ?_⟩
    rcases m1 with h1 | h1
    · exact absurd (h1.trans h0.symm) hne
    · exact h1
  · refine ⟨A.σ w₀, ?_, by rw [A.curve_σσ, h0]⟩
    rcases m1 with h1 | h1
    · exact h1
    · exact absurd (h1.trans h0.symm) hne

variable (hA : A.IsGreat)
include hA

/-- **Quarter lemma** for arbitrary side functions. -/
theorem quarter_tri {c ℓ : Fin n} (hcℓ : c ≠ ℓ) {sc sl : A.Cell → ZMod 2}
    (hsc : A.IsSide c sc) (hsl : A.IsSide ℓ sl) {x : D}
    (hxc : c ∉ Arrangement.Crossing.curves A (A.crossingOf x))
    (hxl : ℓ ∉ Arrangement.Crossing.curves A (A.crossingOf x)) :
    ∃ d, A.IsTriangle (A.cellOf d) ∧ A.curve d = ℓ ∧
      c ∉ Arrangement.Cell.curves A (A.cellOf d) ∧
      sc (A.cellOf d) = sc (A.cellOf x) ∧ sl (A.cellOf d) = sl (A.cellOf x) := by
  obtain ⟨y, hy, hys⟩ := Arrangement.exists_dart_on_side hsc (sc (A.cellOf x))
  let F : Frame A := ⟨c, A.α y, by rw [A.curve_α, hy]⟩
  have hL : F.s0 (A.cellOf y) = 1 := by
    have := F.s0_left
    rwa [show F.β0 = A.α y from rfl, A.α_α] at this
  have r0 := side_add_eq hsc F.isSide_s0
  have hx0 : F.s0 (A.cellOf x) = 1 := by
    have h := r0 (A.cellOf x) (A.cellOf y)
    rw [hL, hys] at h
    generalize F.s0 (A.cellOf x) = a at h
    generalize sc (A.cellOf x) = b at h
    revert a b; decide
  obtain ⟨d, hT, hd, hc0, -, hs0d, hsRd⟩ := F.quarter hA (ℓ := ℓ) hcℓ.symm
    (F.sR ℓ (A.cellOf x)) univ (mem_univ _) ⟨x, hxc, hxl, subset_univ _, hx0, rfl⟩
    (fun t ht => absurd (mem_univ t) ht)
  refine ⟨d, hT, hd, hc0, ?_, ?_⟩
  · have h := r0 (A.cellOf d) (A.cellOf x)
    rw [hs0d, hx0] at h
    generalize sc (A.cellOf d) = a at h
    generalize sc (A.cellOf x) = b at h
    revert a b; decide
  · have h := side_add_eq hsl (F.isSide_sR ℓ) (A.cellOf d) (A.cellOf x)
    rw [hsRd] at h
    generalize sl (A.cellOf d) = a at h
    generalize sl (A.cellOf x) = b at h
    generalize F.sR ℓ (A.cellOf x) = e at h
    revert a b e; decide

/-- **The step**: a triangle with a side on `c`, not touching `b`, on the side of `c` of the cell
of `t` and on the other side of `b`. -/
theorem tri_step (h3 : 3 ≤ n) {t : D} {b c g : Fin n}
    (hb : b ∈ Arrangement.Crossing.curves A (A.crossingOf t))
    (hc : c ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α t)))
    (hbt : b ≠ A.curve t) (hct : c ≠ A.curve t) (hbc : b ≠ c)
    (hgt : g ≠ A.curve t) (hgb : g ≠ b) (hgc : g ≠ c)
    {sb sc : A.Cell → ZMod 2} (hsb : A.IsSide b sb) (hsc : A.IsSide c sc) :
    ∃ d, A.IsTriangle (A.cellOf d) ∧ A.curve d = c ∧
      b ∉ Arrangement.Cell.curves A (A.cellOf d) ∧
      sc (A.cellOf d) = sc (A.cellOf t) ∧ sb (A.cellOf d) = sb (A.cellOf t) + 1 := by
  obtain ⟨w, hw, hwσ⟩ := exists_dart_crossing' (A := A) hgt.symm
  have hcw : Arrangement.Crossing.curves A (A.crossingOf w) = {A.curve t, g} := by
    rw [A.curves_crossingOf, hw, hwσ]
  have nb : b ∉ Arrangement.Crossing.curves A (A.crossingOf w) := by
    rw [hcw, mem_insert, mem_singleton, not_or]; exact ⟨hbt, hgb.symm⟩
  have nc : c ∉ Arrangement.Crossing.curves A (A.crossingOf w) := by
    rw [hcw, mem_insert, mem_singleton, not_or]; exact ⟨hct, hgc.symm⟩
  have K := chi_walk hA h3 hb hc hbt hct hsb hsc (by rw [hcw]; exact mem_insert_self _ _) nb nc
  by_cases hv : sc (A.cellOf w) = sc (A.cellOf t)
  · obtain ⟨d, hT, hd, hbd, h1, h2⟩ := quarter_tri hA hbc hsb hsc nb nc
    refine ⟨d, hT, hd, hbd, h2.trans hv, ?_⟩
    rw [h1]
    rw [hv] at K
    generalize sb (A.cellOf w) = a at K
    generalize sb (A.cellOf t) = e at K
    generalize sc (A.cellOf t) = f at K
    revert a e f; decide
  · have ha := curves_ant hA w
    have hwb : A.curve w ≠ b := hw ▸ hbt.symm
    have hwc : A.curve w ≠ c := hw ▸ hct.symm
    have sab := side_ant hA hsb w
    have sac := side_ant hA hsc w
    rw [if_neg hwb] at sab
    rw [if_neg hwc] at sac
    obtain ⟨d, hT, hd, hbd, h1, h2⟩ := quarter_tri hA hbc hsb hsc (x := ant A w)
      (by rw [ha]; exact nb) (by rw [ha]; exact nc)
    refine ⟨d, hT, hd, hbd, ?_, ?_⟩
    · rw [h2, sac]
      generalize sc (A.cellOf w) = a at hv
      generalize sc (A.cellOf t) = e at hv
      revert a e; decide
    · rw [h1, sab]
      generalize sb (A.cellOf w) = a at K
      generalize sc (A.cellOf w) = a' at K hv
      generalize sb (A.cellOf t) = e at K
      generalize sc (A.cellOf t) = f at K hv
      revert a a' e f; decide

end Pca.Great
