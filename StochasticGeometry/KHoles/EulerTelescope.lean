/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The telescoping series `Σ_n P_n(s)/((n+1)! n!)` (step iii)

With `P_n(s) = capPoly n s = ∏_{i<n} (s + i(i+1))` we have `P_{n+1} = P_n · (s + n(n+1))`, and
this yields the telescoping identity
`s · Σ_{n≤K} P_n(s)/((n+1)! n!) = P_{K+1}(s)/((K+1)! K!)`
(`capPoly_telescope`), by induction on `K`: the step is
`P_{K+1}/((K+1)! K!) + s · P_{K+1}/((K+2)! (K+1)!) = P_{K+1} · (s + (K+1)(K+2))/((K+2)! (K+1)!)`.

For `s = a(1-a)` with `0 < a < 1` the factors split as `s + i(i+1) = (i+a)(i+1-a)`, so
`P_{K+1}(s) · (K+1+a) = a · (K+1)!² · ∏_{j≤K} (1 - a²/(j+1)²)` (`capPoly_alpha`), and the
partial sum becomes
`Σ_{n≤K} P_n(s)/((n+1)! n!) = (K+1)/(K+1+a) · ∏_{j≤K} (1 - a²/(j+1)²) / (1-a)`.
As `K → ∞` the first factor tends to `1` and the product tends to `sin(πa)/(πa)` by Euler's
sine product (`Real.tendsto_euler_sin_prod`); since all terms are nonnegative this gives
`HasSum … (sin(πa)/(π a(1-a)))` (`hasSum_capPoly`).
-/

open Real Finset Filter Topology

namespace KHoles

/-- Telescoping identity `s · Σ_{n≤K} P_n(s)/((n+1)! n!) = P_{K+1}(s)/((K+1)! K!)`,
by induction on `K` using `P_{n+1} = P_n · (s + n(n+1))`. -/
theorem capPoly_telescope (s : ℝ) (K : ℕ) :
    s * ∑ n ∈ range (K + 1), capPoly n s / ((n + 1).factorial * n.factorial)
      = capPoly (K + 1) s / ((K + 1).factorial * K.factorial) := by
  induction K with
  | zero => simp [capPoly]
  | succ K ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [capPoly, prod_range_succ]
    push_cast [Nat.factorial_succ]
    field_simp
    ring

/-- For `s = a(1-a)`: `P_{K+1}(s) · (K+1+a) = a · (K+1)!² · ∏_{j≤K} (1 - a²/(j+1)²)`,
from the factorisation `s + i(i+1) = (i+a)(i+1-a)`. -/
theorem capPoly_alpha (a : ℝ) (K : ℕ) :
    capPoly (K + 1) (a * (1 - a)) * (K + 1 + a)
      = a * (((K + 1).factorial : ℝ) ^ 2 * ∏ j ∈ range (K + 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) := by
  induction K with
  | zero => simp [capPoly]; field_simp; ring
  | succ K ih =>
    have e : capPoly (K + 1 + 1) (a * (1 - a)) =
        capPoly (K + 1) (a * (1 - a)) * (((K : ℝ) + 1 + a) * ((K : ℝ) + 2 - a)) := by
      simp only [capPoly, prod_range_succ]; push_cast; ring
    rw [e]
    calc capPoly (K + 1) (a * (1 - a)) * (((K : ℝ) + 1 + a) * ((K : ℝ) + 2 - a))
            * (((K + 1 : ℕ) : ℝ) + 1 + a)
        = (capPoly (K + 1) (a * (1 - a)) * ((K : ℝ) + 1 + a))
            * (((K : ℝ) + 2 - a) * ((K : ℝ) + 2 + a)) := by
          push_cast; ring
      _ = _ := by
          rw [ih, Finset.prod_range_succ _ (K + 1)]
          generalize ∏ j ∈ range (K + 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2) = Q
          rw [Nat.factorial_succ (K + 1)]
          push_cast
          field_simp
          ring

/-- `Σ_n P_n(a(1-a))/((n+1)! n!) = sin(πa)/(π a(1-a))` for `0 < a < 1`: the partial sums equal
`(K+1)/(K+1+a) · ∏_{j≤K} (1 - a²/(j+1)²) / (1-a)` and converge by Euler's sine product. -/
theorem hasSum_capPoly {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    HasSum (fun n => capPoly n (a * (1 - a)) / ((n + 1).factorial * n.factorial))
      (Real.sin (π * a) / (π * (a * (1 - a)))) := by
  set s := a * (1 - a) with hs_def
  have hs : 0 < s := mul_pos h0 (by linarith)
  have hnn : ∀ n, 0 ≤ capPoly n s / ((n + 1).factorial * n.factorial) := fun n =>
    div_nonneg (prod_nonneg fun i _ => by positivity) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn, ← tendsto_add_atTop_iff_nat 1]
  -- closed form of the partial sums
  have hpart : ∀ K : ℕ, ∑ n ∈ range (K + 1), capPoly n s / ((n + 1).factorial * n.factorial)
      = ((K + 1 : ℝ) / (K + 1 + a)) *
          (∏ j ∈ range (K + 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) / (1 - a) := by
    intro K
    have ht := capPoly_telescope s K
    have hp := capPoly_alpha a K
    have hKa : (K : ℝ) + 1 + a ≠ 0 := by positivity
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    rw [← hs_def] at hp
    have hP : capPoly (K + 1) s = a * (((K + 1).factorial : ℝ) ^ 2 *
        ∏ j ∈ range (K + 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) / (K + 1 + a) := by
      rw [← hp]; field_simp
    rw [hP] at ht
    apply mul_left_cancel₀ hs.ne'
    rw [ht, hs_def]
    push_cast [Nat.factorial_succ]
    field_simp
  simp_rw [hpart]
  -- `(K+1)/(K+1+a) → 1`
  have hA : Tendsto (fun K : ℕ => ((K : ℝ) + 1) / ((K : ℝ) + 1 + a)) atTop (𝓝 1) := by
    have := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_natCast_div_add_atTop a)
    push_cast at this
    exact this
  -- Euler's sine product: `∏_{j≤K} (1 - a²/(j+1)²) → sin(πa)/(πa)`
  have hB : Tendsto (fun K : ℕ => ∏ j ∈ range (K + 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (sin (π * a) / (π * a))) := by
    have := ((tendsto_add_atTop_iff_nat 1).mpr (Real.tendsto_euler_sin_prod a)).div_const (π * a)
    refine this.congr fun K => ?_
    have : π * a ≠ 0 := by positivity
    field_simp
  have := (hA.mul hB).div_const (1 - a)
  convert this using 2
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  have : π * a ≠ 0 := by positivity
  rw [hs_def]
  field_simp

end KHoles
