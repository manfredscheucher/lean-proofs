/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Levi's triangle theorem: the walk lemma (`doc/pca/great.md` section 7)

Along a curve `a` of a great arrangement, let `t` be a dart whose segment runs from a crossing with
`b` to a crossing with `c`. Every other crossing on `a` (not with `b` or `c`) lies on the other
"projective side": `s_b + s_c` differs from its value at the cells of `t`. In the projective
plane: the two pseudolines `b`, `c` cut the plane into two regions, the segment of `t` lies in one
of them, and the rest of `a` (between its crossings with `b` and `c` the long way round) lies in
the other one.
-/
import Pca.Great.Walk
import Pca.Great.Q_Sys

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- Two side functions of the same curve have the same differences. -/
theorem side_add_eq {C : Fin n} {s s' : A.Cell → ZMod 2} (hs : A.IsSide C s)
    (hs' : A.IsSide C s') (f g : A.Cell) : s' f + s' g = s f + s g := by
  rcases hs.eq_or_eq_add_one hs' with rfl | rfl
  · rfl
  · show s f + 1 + (s g + 1) = s f + s g
    generalize s f = x; generalize s g = y; revert x y; decide

/-- The two cells at a segment not on `C` are on the same side of `C`. -/
theorem side_α_of_ne {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {y : D}
    (hy : A.curve y ≠ C) : s (A.cellOf (A.α y)) = s (A.cellOf y) := by
  have h := hs y
  rw [if_neg hy] at h
  have := Arrangement.zmod2_eq_add_of_add_eq h
  rw [this, add_zero]

theorem crossingOf_straight (y : D) : A.crossingOf (A.straight y) = A.crossingOf (A.α y) := by
  rw [Arrangement.straight_apply, A.crossingOf_σ, A.crossingOf_σ]

/-- The curves at the crossing of `d` are curves of the cell of `d`. -/
theorem curves_crossingOf_subset (d : D) :
    Arrangement.Crossing.curves A (A.crossingOf d) ⊆ Arrangement.Cell.curves A (A.cellOf d) := by
  set y := A.φ.symm d
  have hy : A.φ y = d := A.φ.apply_symm_apply d
  have hx : A.crossingOf d = A.crossingOf (A.α y) := by
    rw [← hy, Arrangement.φ_apply, A.crossingOf_σ]
  have hcy : A.cellOf y = A.cellOf d := by rw [← hy, A.cellOf_φ]
  rw [hx, A.curves_crossingOf]
  intro C hC
  simp only [mem_insert, mem_singleton] at hC
  simp only [Arrangement.Cell.curves, mem_image, Orbit.mem_darts]
  rcases hC with rfl | rfl
  · exact ⟨y, hcy, (A.curve_α y).symm⟩
  · refine ⟨d, rfl, ?_⟩
    rw [← hy, Arrangement.φ_apply]

variable (hA : A.IsGreat)
include hA

/-- Consecutive crossings on a curve are crossings with different curves (`n ≥ 3`). -/
theorem not_mem_next (h3 : 3 ≤ n) (y : D) {x : Fin n} (hx : x ≠ A.curve y)
    (h1 : x ∈ Arrangement.Crossing.curves A (A.crossingOf y)) :
    x ∉ Arrangement.Crossing.curves A (A.crossingOf (A.α y)) := by
  intro h2
  obtain ⟨k₁, hk₁, hp⟩ := pos_two hA y hx
  have e0 := (hp 0 (by omega)).1 (by rw [pow_zero, Perm.one_apply]; exact h1)
  have e1 := (hp 1 (by omega)).1 (by rw [pow_one, crossingOf_straight]; exact h2)
  omega

/-- **Walk lemma.** `t` runs along `a = curve t` from a crossing with `b` to a crossing with `c`.
A crossing on `a` with neither `b` nor `c` has `s_b + s_c` different from the cells of `t`. -/
theorem chi_walk (h3 : 3 ≤ n) {t d : D} {b c : Fin n}
    (hb : b ∈ Arrangement.Crossing.curves A (A.crossingOf t))
    (hc : c ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α t)))
    (hbt : b ≠ A.curve t) (hct : c ≠ A.curve t)
    {sb sc : A.Cell → ZMod 2} (hsb : A.IsSide b sb) (hsc : A.IsSide c sc)
    (hd : A.curve t ∈ Arrangement.Crossing.curves A (A.crossingOf d))
    (hdb : b ∉ Arrangement.Crossing.curves A (A.crossingOf d))
    (hdc : c ∉ Arrangement.Crossing.curves A (A.crossingOf d)) :
    sb (A.cellOf d) + sc (A.cellOf d) = sb (A.cellOf t) + sc (A.cellOf t) + 1 := by
  obtain ⟨k, hk, hkx⟩ := exists_straight_pow_eq (d := t) hd
  obtain ⟨kb, hkb, hpb⟩ := pos_two hA t hbt
  obtain ⟨kc, hkc, hpc⟩ := pos_two hA t hct
  have eb := (hpb 0 (by omega)).1 (by rw [pow_zero, Perm.one_apply]; exact hb)
  have ec := (hpc 1 (by omega)).1 (by rw [pow_one, crossingOf_straight]; exact hc)
  have hkb0 : kb = 0 := by omega
  have hkc1 : kc = 1 := by omega
  subst hkb0 hkc1
  have nb := fun h => hdb (hkx ▸ (hpb k hk).2 h)
  have nc := fun h => hdc (hkx ▸ (hpc k hk).2 h)
  have sb1 := Frame.side_same_crossing hsb hkx (hkx ▸ hdb)
  have sc1 := Frame.side_same_crossing hsc hkx (hkx ▸ hdc)
  rw [← sb1, ← sc1, side_walk hA t hbt hsb hpb hkb hk, side_walk hA t hct hsc hpc hkc hk]
  generalize sb (A.cellOf t) = x
  generalize sc (A.cellOf t) = y
  have hn : ¬ (k = 0 ∨ k = 0 + (n - 1)) := nb
  have hn' : ¬ (k = 1 ∨ k = 1 + (n - 1)) := nc
  by_cases h1 : 0 + (n - 1) ≤ k
  · rw [if_neg (by omega), if_pos h1, if_pos (by omega), if_pos (by omega)]
    revert x y; decide
  · rw [if_neg (by omega), if_neg h1, if_pos (by omega), if_neg (by omega)]
    revert x y; decide

end Pca.Great
