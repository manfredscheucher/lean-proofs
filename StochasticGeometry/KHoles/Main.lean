/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.Bridge
import KHoles.CapClosedForm
import KHoles.Convolution

/-!
# Main results of the formalisation

Chain of files:

* `Constants`: closed-form finite sums `a m` (cap numbers), `C k` (k-hole constants) and
  `Cconv k = ½ Σ_m a m · a (k-2-m)`, with explicit values for small `m`, `k`.
* `CatalanPower`, `Convolution`: coefficients of powers of the Catalan series; via the formal
  power series `sin(π α)` and `cos(2π α)`, `Cconv k = C k` for all `k` (`Cconv_eq_C_all`).
* `Determinant`, `ConeGeometry`, `ConeIntegral`, `CapIntegral`: the Poisson cap integral
  `capIntegral n` (exp(-area) over strictly concave chains with `n+1` interior vertices)
  reduces to `2^m ∫_simplex ∏ gaps / ∏ x(1-x)` (Proposition 3.3 of the draft).
* `CapDefs`, `Bridge`: the simplex integral `capInt m`, and
  `capIntegral n = 2^(n+1) * capInt (n+1)`.
* `Volterra`, `CapPoly`, `CapSeries`, `EulerTelescope`, `AlphaSeries`, `SinAlpha`,
  `PowerSeriesUnique`, `CapClosedForm`: Volterra iteration, series expansion, telescoping,
  `sin(π α(s))` and uniqueness of power series coefficients give
  `capInt m = a m / 2^m` (`capInt_toReal`).
* `CapTwo`: independent direct evaluation of `a 1` and `a 2` as integrals.

The probabilistic side (n i.i.d. uniform points, Theorem 2.1 of the draft = Theorem 7 of
arXiv:2111.12533, and the split into independent upper and lower caps) is in the stage-4 files;
the end-to-end statement is `tendsto_EH_div_sq` in `Theorem7.lean`.
-/

open Finset

namespace KHoles

/-- The Poisson cap integral over a chain with `n+1` interior vertices is finite. -/
theorem capIntegral_ne_top (n : ℕ) : capIntegral n ≠ ⊤ := by
  rw [capIntegral_eq_capInt]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (capInt_ne_top _)

/-- Main analytic result: the cap integral equals the closed-form cap number `a (n+1)`. -/
theorem capIntegral_toReal (n : ℕ) : (capIntegral n).toReal = a (n + 1) := by
  rw [capIntegral_eq_capInt, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    capInt_toReal]
  field_simp

/-- Cap numbers as real integrals for all m (m = 0 is `a 0 = 1`). -/
theorem a_eq_capIntegral (m : ℕ) :
    a m = if m = 0 then 1 else (capIntegral (m - 1)).toReal := by
  cases m with
  | zero => simp [a_zero]
  | succ m => simp [capIntegral_toReal]

/-- The k-hole constants are the convolution of the cap integrals (Theorem main of the draft,
analytic side): `C k = ½ Σ_m a m · a (k-2-m)` with each `a m` given by the integral. -/
theorem C_eq_conv_capIntegral (k : ℕ) :
    C k = (1 / 2) * ∑ m ∈ Finset.range (k - 1),
      (if m = 0 then 1 else (capIntegral (m - 1)).toReal) *
      (if k - 2 - m = 0 then 1 else (capIntegral (k - 2 - m - 1)).toReal) := by
  rw [← Cconv_eq_C_all, Cconv]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← a_eq_capIntegral, ← a_eq_capIntegral]

end KHoles
