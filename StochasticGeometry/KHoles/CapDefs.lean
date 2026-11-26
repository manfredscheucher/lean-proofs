/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Real.Basic

/-!
# Shared definitions for stage 3 (closed form of `a m` from the simplex integral)

Definitions of §2.1 of `doc/kholes/kholes.md`, used by all stage-3 files:
the open ordered simplex, the cap density and the simplex integral `capInt`, the Volterra
iteration `F`, the polynomials `P_n(s) = ∏_{i<n} (s + i(i+1))` with coefficients `pc`,
the series coefficients `fc`, the Catalan power coefficients `kappa` and the analytic
Catalan function `alphaFn`. Only trivial unfolding lemmas are proved here.
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace KHoles

/-- The open ordered simplex `0 < x_0 < … < x_{m-1} < y`. -/
def simplex (m : ℕ) (y : ℝ) : Set (Fin m → ℝ) :=
  {x | StrictMono x ∧ (∀ i, 0 < x i) ∧ ∀ i, x i < y}

/-- Extended abscissae `x̄_0 = 0`, `x̄_k = x_{k-1}` (1 ≤ k ≤ m), `x̄_k = y` (k > m). -/
noncomputable def xbar (m : ℕ) (y : ℝ) (x : Fin m → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if h : k - 1 < m then x ⟨k - 1, h⟩ else y

/-- `∏_{j=0}^{m} (x̄_{j+1} - x̄_j) / ∏_i x_i (1 - x_i)`. -/
noncomputable def capDensity (m : ℕ) (y : ℝ) (x : Fin m → ℝ) : ℝ :=
  (∏ j ∈ range (m + 1), (xbar m y x (j + 1) - xbar m y x j)) / ∏ i, (x i * (1 - x i))

/-- The simplex integral `I_m(y) = ∫_{0<x_1<…<x_m<y} capDensity m y x dx` (in `ℝ≥0∞`). -/
noncomputable def capIntY (m : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in simplex m y, ENNReal.ofReal (capDensity m y x)

/-- The simplex integral of Proposition `prop:am` (without the factor `2^m`). -/
noncomputable def capInt (m : ℕ) : ℝ≥0∞ := capIntY m 1

/-- Volterra iteration `F_0 y = y`, `F_{j+1} y = ∫_0^y F_j t (y-t)/(t(1-t)) dt`. -/
noncomputable def F : ℕ → ℝ → ℝ≥0∞
  | 0, y => ENNReal.ofReal y
  | j + 1, y => ∫⁻ t in Ioo 0 y, F j t * ENNReal.ofReal ((y - t) / (t * (1 - t)))

/-- `P_n(s) = ∏_{i<n} (s + i(i+1))`. -/
noncomputable def capPoly (n : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range n, (s + (i : ℝ) * (i + 1))

/-- `pc n j = [s^j] P_n` (recursion `P_{n+1} = P_n · (s + n(n+1))`). -/
def pc : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, 0 => n * (n + 1) * pc n 0
  | n + 1, j + 1 => pc n j + n * (n + 1) * pc n (j + 1)

/-- `f(j,n) = [s^j] P_n / ((n+1)! n!)`. -/
noncomputable def fc (j n : ℕ) : ℝ := pc n j / ((n + 1).factorial * n.factorial)

/-- `κ r n = [s^n] (X · c)^r` (c = Catalan series), as in `CatalanPower.lean`. -/
noncomputable def kappa (r n : ℕ) : ℕ :=
  PowerSeries.coeff n ((PowerSeries.X * PowerSeries.catalanSeries) ^ r)

/-- The analytic Catalan function `α(s) = Σ_{n≥1} Cat_{n-1} s^n` (no square root). -/
noncomputable def alphaFn (s : ℝ) : ℝ := ∑' n, (kappa 1 n : ℝ) * s ^ n

/-! ### Trivial unfolding lemmas -/

theorem mem_simplex {m : ℕ} {y : ℝ} {x : Fin m → ℝ} :
    x ∈ simplex m y ↔ StrictMono x ∧ (∀ i, 0 < x i) ∧ ∀ i, x i < y := Iff.rfl

@[simp] theorem xbar_zero (m : ℕ) (y : ℝ) (x : Fin m → ℝ) : xbar m y x 0 = 0 := rfl

/-- `x̄_{k+1} = x_k` for `k < m`. -/
theorem xbar_of_lt {m : ℕ} (y : ℝ) (x : Fin m → ℝ) {k : ℕ} (hk : k < m) :
    xbar m y x (k + 1) = x ⟨k, hk⟩ := by
  simp [xbar, hk]

/-- `x̄_{k+1} = y` for `k ≥ m`. -/
theorem xbar_of_ge {m : ℕ} (y : ℝ) (x : Fin m → ℝ) {k : ℕ} (hk : m ≤ k) :
    xbar m y x (k + 1) = y := by
  simp [xbar, not_lt.mpr hk]

theorem capInt_def (m : ℕ) : capInt m = capIntY m 1 := rfl

theorem capIntY_def (m : ℕ) (y : ℝ) :
    capIntY m y = ∫⁻ x in simplex m y, ENNReal.ofReal (capDensity m y x) := rfl

theorem capInt_eq (m : ℕ) :
    capInt m = ∫⁻ x in simplex m 1, ENNReal.ofReal (capDensity m 1 x) := rfl

@[simp] theorem F_zero (y : ℝ) : F 0 y = ENNReal.ofReal y := rfl

theorem F_succ (j : ℕ) (y : ℝ) :
    F (j + 1) y = ∫⁻ t in Ioo 0 y, F j t * ENNReal.ofReal ((y - t) / (t * (1 - t))) := by
  rw [F]

@[simp] theorem capPoly_zero (s : ℝ) : capPoly 0 s = 1 := by simp [capPoly]

theorem capPoly_succ (n : ℕ) (s : ℝ) :
    capPoly (n + 1) s = capPoly n s * (s + (n : ℝ) * (n + 1)) := by
  simp [capPoly, prod_range_succ]

@[simp] theorem pc_zero (j : ℕ) : pc 0 j = if j = 0 then 1 else 0 := by rw [pc]

@[simp] theorem pc_zero_zero : pc 0 0 = 1 := by simp

@[simp] theorem pc_succ_zero (n : ℕ) : pc (n + 1) 0 = n * (n + 1) * pc n 0 := by rw [pc]

@[simp] theorem pc_succ_succ (n j : ℕ) :
    pc (n + 1) (j + 1) = pc n j + n * (n + 1) * pc n (j + 1) := by rw [pc]

theorem fc_def (j n : ℕ) : fc j n = pc n j / ((n + 1).factorial * n.factorial) := rfl

theorem kappa_def (r n : ℕ) :
    kappa r n = PowerSeries.coeff n ((PowerSeries.X * PowerSeries.catalanSeries) ^ r) := rfl

theorem alphaFn_def (s : ℝ) : alphaFn s = ∑' n, (kappa 1 n : ℝ) * s ^ n := rfl

end KHoles
