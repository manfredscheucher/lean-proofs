/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Uniqueness of real power series coefficients (step v)

If two real power series `Σ c_n s^n` and `Σ d_n s^n` both converge absolutely at some radius
`r > 0` and agree on the interval `(0, r)`, then `c = d`.

Proof route: view the coefficient sequences as scalar formal multilinear series
(`FormalMultilinearSeries.ofScalars`). Absolute convergence at `r` bounds the radius from
below, so both series have `HasFPowerSeriesOnBall` at `0`, hence their sums are analytic at
`0`. The sums agree on `(0, r)`, so they agree frequently in the punctured neighbourhood of
`0`; by the isolated zeros principle (`AnalyticAt.frequently_eq_iff_eventually_eq`) they agree
on a full neighbourhood of `0`. Uniqueness of power series expansions
(`HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`) gives equal formal series, and
`ofScalars` is injective.
-/

open Filter Topology

namespace KHoles

/-- Two real power series that converge absolutely at radius `r > 0` and coincide on
`(0, r)` have the same coefficients. -/
theorem coeff_unique (c d : ℕ → ℝ) (r : NNReal) (hr : 0 < r)
    (hc : Summable fun n => ‖c n‖ * (r : ℝ) ^ n) (hd : Summable fun n => ‖d n‖ * (r : ℝ) ^ n)
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) r, ∑' n, c n * s ^ n = ∑' n, d n * s ^ n) : c = d := by
  set p := FormalMultilinearSeries.ofScalars ℝ c
  set q := FormalMultilinearSeries.ofScalars ℝ d
  -- absolute convergence at `r` gives `r ≤ radius`
  have hp : (r : ENNReal) ≤ p.radius :=
    p.le_radius_of_summable (by simpa [p, FormalMultilinearSeries.ofScalars_norm] using hc)
  have hq : (r : ENNReal) ≤ q.radius :=
    q.le_radius_of_summable (by simpa [q, FormalMultilinearSeries.ofScalars_norm] using hd)
  have hr' : (0 : ENNReal) < r := by exact_mod_cast hr
  have hpa := (p.hasFPowerSeriesOnBall (lt_of_lt_of_le hr' hp)).hasFPowerSeriesAt
  have hqa := (q.hasFPowerSeriesOnBall (lt_of_lt_of_le hr' hq)).hasFPowerSeriesAt
  -- the sums of the formal series are the given `tsum`s
  have hsp : ∀ s : ℝ, p.sum s = ∑' n, c n * s ^ n := by
    intro s; simp [p, FormalMultilinearSeries.sum, mul_comm]
  have hsq : ∀ s : ℝ, q.sum s = ∑' n, d n * s ^ n := by
    intro s; simp [q, FormalMultilinearSeries.sum, mul_comm]
  -- agreement on `(0, r)` is agreement eventually to the right of `0`
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), p.sum z = q.sum z := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r from hr)] with z hz
    rw [hsp, hsq]; exact h z hz
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℝ), p.sum z = q.sum z :=
    hev.frequently.filter_mono (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')
  -- isolated zeros: frequent agreement near `0` upgrades to eventual agreement
  have h2 := (hpa.analyticAt.frequently_eq_iff_eventually_eq hqa.analyticAt).mp hfr
  -- uniqueness of the power series expansion, then injectivity of `ofScalars`
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (hpa.eq_formalMultilinearSeries_of_eventually hqa h2)

end KHoles
