/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapIntegral
import KHoles.CapDefs

/-!
# Bridge between `CapIntegral.lean` and `CapDefs.lean`

The simplex `simplexFin n` of `CapIntegral.lean` is the simplex `simplex (n + 1) 1` of
`CapDefs.lean`, the integrand `gapIntegrand` is `2 ^ (n + 1) * capDensity (n + 1) 1`, and hence
`capIntegral n = 2 ^ (n + 1) * capInt (n + 1)`.
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace KHoles

theorem simplexFin_eq_simplex (n : ℕ) : simplexFin n = simplex (n + 1) 1 := by
  ext x
  simp only [simplexFin, simplex, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, fun i => h0.trans_le (hx.monotone (Fin.zero_le i)),
      fun i => (hx.monotone (Fin.le_last i)).trans_lt h1⟩
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, h0 0, h1 _⟩

/-- The product of the `n + 2` gaps of `x̄` is the gap product of `gapIntegrand`. -/
theorem prod_xbar_gaps (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ∏ j ∈ range (n + 1 + 1), (xbar (n + 1) 1 x (j + 1) - xbar (n + 1) 1 x j) =
      x 0 * (∏ i : Fin n, (x i.succ - x i.castSucc)) * (1 - x (Fin.last n)) := by
  rw [prod_range_succ, prod_range_succ']
  have hlast : xbar (n + 1) 1 x (n + 1 + 1) - xbar (n + 1) 1 x (n + 1) = 1 - x (Fin.last n) := by
    rw [xbar_of_ge 1 x le_rfl, xbar_of_lt 1 x (Nat.lt_succ_self n)]
    rfl
  have hfirst : xbar (n + 1) 1 x (0 + 1) - xbar (n + 1) 1 x 0 = x 0 := by
    rw [xbar_of_lt 1 x (Nat.succ_pos n), xbar_zero, sub_zero]
    rfl
  have hmid : ∏ j ∈ range n, (xbar (n + 1) 1 x (j + 1 + 1) - xbar (n + 1) 1 x (j + 1)) =
      ∏ i : Fin n, (x i.succ - x i.castSucc) := by
    rw [← Fin.prod_univ_eq_prod_range (fun j => xbar (n + 1) 1 x (j + 1 + 1) -
      xbar (n + 1) 1 x (j + 1)) n]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [xbar_of_lt 1 x (Nat.succ_lt_succ i.isLt), xbar_of_lt 1 x (Nat.lt_succ_of_lt i.isLt)]
    rfl
  rw [hlast, hfirst, hmid]
  ring

theorem gapIntegrand_eq (n : ℕ) (x : Fin (n + 1) → ℝ) :
    gapIntegrand x = 2 ^ (n + 1) * capDensity (n + 1) 1 x := by
  rw [gapIntegrand, capDensity, prod_xbar_gaps, mul_div_assoc]

theorem capIntegral_eq_capInt (n : ℕ) :
    capIntegral n = ENNReal.ofReal (2 ^ (n + 1)) * capInt (n + 1) := by
  rw [capIntegral_eq, simplexFin_eq_simplex, capInt_eq, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [gapIntegrand_eq, ENNReal.ofReal_mul (by positivity)]

end KHoles
