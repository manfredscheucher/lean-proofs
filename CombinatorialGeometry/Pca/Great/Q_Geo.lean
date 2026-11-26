/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma: chords as a chord system, darts in chord coordinates (`doc/pca/great.md` 3.3)
-/
import Pca.Great.Frame
import Pca.Great.Q_Tri

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A dart whose face orbit closes after three steps bounds a triangle. -/
theorem isTriangle_of_cycle {d : D} (h : A.φ (A.φ (A.φ d)) = d) : A.IsTriangle (A.cellOf d) := by
  have hper : Function.IsPeriodicPt A.φ 3 d := h
  have hdvd := hper.minimalPeriod_dvd
  have h1 : Function.minimalPeriod A.φ d ≠ 1 := by
    intro h1
    have := Function.iterate_minimalPeriod (f := A.φ) (x := d)
    rw [h1, Function.iterate_one] at this
    exact A.curve_φ_ne d (by rw [this])
  have h3 : Function.minimalPeriod A.φ d = 3 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hm : Function.minimalPeriod A.φ d
    · exact absurd hdvd (by norm_num)
    · exact absurd rfl h1
    · exact absurd hdvd (by norm_num)
    · rfl
  change (A.cellOf d).size = 3
  rw [A.size_cellOf, period_eq_minimalPeriod, h3]

/-- The face orbit closes when the third dart ends at the start of the first one on another curve
than the second one... precisely: the far end of `φ² d` is the crossing of `d` and `φ² d` is not on
the curve of `d`. -/
theorem isTriangle_of_far_end {d : D} (h : A.crossingOf (A.α (A.φ (A.φ d))) = A.crossingOf d)
    (hc : A.curve (A.φ (A.φ d)) ≠ A.curve d) : A.IsTriangle (A.cellOf d) := by
  apply isTriangle_of_cycle
  set z := A.φ (A.φ (A.φ d))
  have hz : A.crossingOf z = A.crossingOf d := by
    show A.crossingOf (A.σ (A.α _)) = _; rw [A.crossingOf_σ, h]
  have hcz : A.curve z = A.curve d := by
    have h1 : A.curve z ≠ A.curve (A.α (A.φ (A.φ d))) := by
      show A.curve (A.σ _) ≠ _; exact A.isArrangement.curve_σ _
    rw [A.isArrangement.curve_α] at h1
    have hm := A.mem_curves_crossingOf z
    have hm' := A.mem_curves_crossingOf d
    rw [hz, A.curves_crossingOf, mem_insert, mem_singleton] at hm
    have hm2 : A.curve (A.φ (A.φ d)) ∈ Arrangement.Crossing.curves A (A.crossingOf d) := by
      rw [← h, ← A.isArrangement.curve_α]; exact A.mem_curves_crossingOf _
    rw [A.curves_crossingOf, mem_insert, mem_singleton] at hm2
    rcases hm with hm | hm
    · exact hm
    · rcases hm2 with hm2 | hm2
      · exact absurd hm2 hc
      · exact absurd (hm.trans hm2.symm) h1
  have hl := A.crossingOf_eq_iff.1 hz.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have hcell : A.cellOf z = A.cellOf d := by
    show A.cellOf (A.φ (A.φ (A.φ d))) = _; rw [A.cellOf_φ, A.cellOf_φ, A.cellOf_φ]
  rcases hl with hl | hl | hl | hl
  · exact hl
  · exact (A.isArrangement.curve_σ d (by rw [← hl]; exact hcz)).elim
  · exact absurd (by rw [← hl]; exact hcell) (A.cellOf_σσ_ne d)
  · exact (A.isArrangement.curve_σ d (by rw [← A.curve_σσσ, ← hl]; exact hcz)).elim

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

/-- The two darts of a chord at a crossing on it. -/
theorem dart_on_chord {t : Fin n} (ht : t ≠ F.c0) {k : ℕ} {z : D}
    (hz : A.crossingOf z = A.crossingOf ((A.straight ^ k) (F.β t))) (hc : A.curve z = t) :
    z = (A.straight ^ k) (F.β t) ∨ z = A.σ (A.σ ((A.straight ^ k) (F.β t))) := by
  set y := (A.straight ^ k) (F.β t)
  have hl := A.crossingOf_eq_iff.1 hz.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have hct : A.curve y = t := by rw [curve_straight_pow, F.curve_β hA ht]
  rcases hl with hl | hl | hl | hl
  · exact Or.inl hl
  · exact absurd (by rw [← hl]; exact hc.trans hct.symm) (A.isArrangement.curve_σ y)
  · exact Or.inr hl
  · exact absurd (by rw [← A.curve_σσσ, ← hl]; exact hc.trans hct.symm) (A.isArrangement.curve_σ y)

theorem far_fwd (t : Fin n) (k : ℕ) :
    A.crossingOf (A.α ((A.straight ^ k) (F.β t))) = A.crossingOf ((A.straight ^ (k + 1)) (F.β t)) :=
  (crossingOf_straight_pow_succ k _).symm

theorem far_bwd (t : Fin n) (k : ℕ) :
    A.crossingOf (A.α (A.σ (A.σ ((A.straight ^ (k + 1)) (F.β t))))) =
      A.crossingOf ((A.straight ^ k) (F.β t)) := by
  rw [← Arrangement.straight_symm_apply, pow_succ', Perm.mul_apply, Equiv.symm_apply_apply]

end Frame

end Pca.Great
