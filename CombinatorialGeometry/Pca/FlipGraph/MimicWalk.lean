/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): sides of a triangle of `M − C'` crossed by `C'`

Third case of the mimicking, crossed form: a side of a triangle of `M − C'` (a straight run of
`k + 1` segments of `M` through `k` crossings with `C'`, `deleteOn_α`) is crossed by `C'` exactly
once, in the two situations of the proof (`k_one_out`: from `int C ∩ ext C'` to the apex;
`k_one_in`: from inside `C'` to a cell outside `C'`). A curve crosses `C'` only twice
(`walk_status`), and `int C ∩ ext C'` contains no crossing of two other curves (`Par`).
-/
import Pca.FlipGraph.MimicPar

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Marked

variable (M : Marked n D)

/-- The run of `k` segments of `y` passing `k` crossings with `E` (the last not on `E`) is shorter
than the period, if the start of `y` is not on `E`. -/
theorem run_lt_period {E : Fin n} {y : D} {k : ℕ}
    (hy0 : E ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y))
    (hk : ∀ i < k, E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y)))) :
    k < period M.A.straight y := by
  by_contra h
  push Not at h
  have hp := period_pos M.A.straight y
  have := hk (period M.A.straight y - 1) (by omega)
  rw [← M.A.crossingOf_straight, ← Walk.pow_succ_apply, Nat.sub_add_cancel hp,
    Walk.pow_period_apply] at this
  exact hy0 this

/-- Two consecutive crossings with `E` on the run: after them the status for `E` is the opposite of
the status between them. -/
theorem run_two {E : Fin n} {y : D} {k : ℕ} (hy : M.A.curve y ≠ E)
    (hy0 : E ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y))
    (hk : ∀ i < k, E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y))))
    (h2 : 2 ≤ k) :
    M.Inside E (M.A.cellOf ((M.A.straight ^ k) y)) ↔
      ¬ M.Inside E (M.A.cellOf (M.A.straight y)) := by
  have hlt := M.run_lt_period hy0 hk
  have hy' : M.A.curve (M.A.straight y) ≠ E := by rw [M.A.curve_straight]; exact hy
  have hs : E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.straight y)) := by
    rw [M.A.crossingOf_straight]; have := hk 0 (by omega); rwa [pow_zero, Perm.one_apply] at this
  have he : E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight y))) := by
    have := hk 1 (by omega); rwa [pow_one] at this
  -- the period of `straight y` is at least the period of `y`
  have hP : period M.A.straight y ≤ period M.A.straight (M.A.straight y) := by
    have h1 := Walk.pow_period_apply M.A (M.A.straight y)
    rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply] at h1
    have h2 := M.A.straight.injective h1
    refine Nat.find_min' _ ⟨period_pos _ _, ?_⟩
    rw [← Perm.coe_pow]; exact h2
  have key := M.walk_status hy' hs he (k - 1) (by omega) (by omega)
  rwa [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)] at key

/-- Along the run the status for a curve `F` not met stays. -/
theorem run_keep {E F : Fin n} {y : D} {k : ℕ} (hy : M.A.curve y ≠ E) (hEF : E ≠ F)
    (hk : ∀ i < k, E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y)))) :
    ∀ i ≤ k, (M.Inside F (M.A.cellOf ((M.A.straight ^ i) y)) ↔ M.Inside F (M.A.cellOf y)) := by
  intro i hi
  induction i with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ i ih =>
    rw [Walk.pow_succ_apply, M.inside_straight, ih (by omega)]
    have hc : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y))) = E :=
      (M.A.mem_curves_end_iff (by rw [Walk.curve_pow]; exact hy)).1 (hk i (by omega))
    rw [hc]; simp [hEF]

/-- The first crossing of the run is on `E`: the status for `E` changes. -/
theorem run_one {E : Fin n} {y : D} {k : ℕ} (hy : M.A.curve y ≠ E) (hk1 : 1 ≤ k)
    (hk : ∀ i < k, E ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y)))) :
    M.Inside E (M.A.cellOf (M.A.straight y)) ↔ ¬ M.Inside E (M.A.cellOf y) := by
  rw [M.inside_straight]
  have hc : M.A.curve (M.A.σ (M.A.α y)) = E := by
    have := hk 0 (by omega); rw [pow_zero, Perm.one_apply] at this
    exact (M.A.mem_curves_end_iff hy).1 this
  rw [hc]; simp

/-- **A run from `int C ∩ ext C'` to a crossing of two other curves crosses `C'` once.** -/
theorem k_one_out {C C' : Fin n} (hpar : M.Par C C') {y : D} {k : ℕ} (hy : M.A.curve y ≠ C')
    (hy0 : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y))
    (hk : ∀ i < k, C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y))))
    (hkC : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ k) y))))
    (hkC' : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ k) y))))
    (hin : M.Inside C (M.A.cellOf y)) (hout : ¬ M.Inside C' (M.A.cellOf y)) : k = 1 := by
  have hCC := hpar.1
  -- the cell at the end of the run violates `Par` unless `k = 1`
  have hend : ¬ (M.Inside C (M.A.cellOf ((M.A.straight ^ k) y)) ∧
      ¬ M.Inside C' (M.A.cellOf ((M.A.straight ^ k) y))) := by
    intro h
    set z := (M.A.straight ^ k) y
    have hφ : M.A.cellOf (M.A.φ z) = M.A.cellOf z := M.A.cellOf_φ z
    have hx : M.A.crossingOf (M.A.φ z) = M.A.crossingOf (M.A.α z) := by
      rw [M.A.φ_apply, M.A.crossingOf_σ]
    apply hpar.2.2 (M.A.crossingOf (M.A.φ z)) (by rw [hx]; exact hkC') (by rw [hx]; exact hkC)
    rw [M.crossInside_iff (by rw [hx]; exact hkC'), M.crossInside_iff (by rw [hx]; exact hkC), hφ]
    exact h
  have hC := M.run_keep hy (Ne.symm hCC) hk k le_rfl
  rcases Nat.lt_trichotomy k 1 with h | h | h
  · obtain rfl : k = 0 := by omega
    exact absurd ⟨by rw [pow_zero, Perm.one_apply]; exact hin,
      by rw [pow_zero, Perm.one_apply]; exact hout⟩ hend
  · exact h
  · have h2 := M.run_two hy hy0 hk (by omega)
    have h1 := M.run_one hy (by omega) hk
    exact absurd ⟨hC.2 hin, by rw [h2, h1]; exact fun h => h hout⟩ hend

/-- **A run from inside `C'` to a cell outside `C'` crosses `C'` once.** -/
theorem k_one_in {C' : Fin n} {y : D} {k : ℕ} (hy : M.A.curve y ≠ C')
    (hy0 : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y))
    (hk : ∀ i < k, C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y))))
    (hin : M.Inside C' (M.A.cellOf y)) (hout : ¬ M.Inside C' (M.A.cellOf ((M.A.straight ^ k) y))) :
    k = 1 := by
  rcases Nat.lt_trichotomy k 1 with h | h | h
  · obtain rfl : k = 0 := by omega
    rw [pow_zero, Perm.one_apply] at hout; exact absurd hin hout
  · exact h
  · have h2 := M.run_two hy hy0 hk (by omega)
    have h1 := M.run_one hy (by omega) hk
    exact absurd (by rw [h2, h1]; exact fun h => h hin) hout

end Marked

end Pca.FlipGraph
