/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.Exchange
import KHoles.DiamSqueeze
import KHoles.PairLimit
import KHoles.Elementary
import KHoles.LimitIntegral

/-!
# Theorem 7: `E[#k-holes] / n^2 → C k`

Step 6 of `doc/kholes/kholes.md` (wave 5, the final theorem). For a convex set `K` in
the plane with `volume K = 1` and `n` i.i.d. uniform points in `K`, the expected number of
`k`-holes satisfies `EH K n k / n^2 → C k`.

With `k = m + 2`, `2 n^m emptyProb K k (n - k)` is squeezed between
`k(k-1) n^m diamProb K m (IsDiamLT) (n - k)` and `k(k-1) n^m diamProb K m (IsDiamLE) (n - k)`
(DiamSqueeze), both of which tend to `k(k-1) limInt m` (PairLimit). Together with
`EH = choose n k * emptyProb` (Exchange), `choose n k / n^k → 1/k!` (Elementary) and
`limInt m = m! · 2 · C k` (LimitIntegral) this gives the limit. Measurability of `K` is
removed by passing to `interior K` (the frontier of a convex set is null).

Source: Theorem 7 of M. Balko, M. Scheucher, P. Valtr, https://arxiv.org/abs/2111.12533. The
closed form of `C k` is new (M. Scheucher), not yet published.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-- The squeeze of Step 6 in `ℝ≥0∞`: `n^m · 2 · emptyProb K (m+2) (n-(m+2)) → k(k-1) limInt m`. -/
lemma tendsto_two_mul_emptyProb {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) (m : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ m * (2 * emptyProb K (m + 2) (n - (m + 2)))) atTop
      (𝓝 ((((m + 2) * (m + 1) : ℕ) : ℝ≥0∞) * limInt m)) := by
  have hJ := limInt_ne_top m
  have hc : (((m + 2) * (m + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hle := ENNReal.Tendsto.const_mul (tendsto_diamProb_le K hK hKm hK1 m hJ) (Or.inr hc)
  have hlt := ENNReal.Tendsto.const_mul (tendsto_diamProb_lt K hK hKm hK1 m hJ) (Or.inr hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlt hle (fun n => ?_) (fun n => ?_)
  · dsimp only
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (diamProb_lt_le K m _) zero_le
  · dsimp only
    rw [mul_left_comm (((m + 2) * (m + 1) : ℕ) : ℝ≥0∞)]
    exact mul_le_mul_of_nonneg_left (two_mul_emptyProb_le K m _) zero_le

theorem tendsto_EH_div_sq_of_measurableSet {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hK1 : volume K = 1) {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => (EH K n k).toReal / (n : ℝ) ^ 2) atTop (𝓝 (C k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hc : (((m + 2) * (m + 1) : ℕ) : ℝ≥0∞) * limInt m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (limInt_ne_top m)
  have h1 := (ENNReal.tendsto_toReal hc).comp (tendsto_two_mul_emptyProb hK hKm hK1 m)
  have h2 := (tendsto_choose_div_pow (m + 2)).mul (h1.div_const 2)
  have hfac : ((m + 2).factorial : ℝ) = (m + 2) * (m + 1) * m.factorial := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hlim : 1 / ((m + 2).factorial : ℝ) *
      (((((m + 2) * (m + 1) : ℕ) : ℝ≥0∞) * limInt m).toReal / 2) = C (m + 2) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, limInt_toReal, hfac]
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hlim] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp, EH_eq_choose_mul hK hKm hK1, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  field_simp
  ring

/-- Replacing `K` by its interior does not change the law of the points. -/
lemma restrict_interior_eq {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) :
    volume.restrict (interior K) = volume.restrict K :=
  Measure.restrict_congr_set (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))

theorem tendsto_EH_div_sq {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hK1 : volume K = 1) {k : ℕ}
    (hk : 3 ≤ k) :
    Tendsto (fun n : ℕ => (EH K n k).toReal / (n : ℝ) ^ 2) atTop (𝓝 (C k)) := by
  have hEH : ∀ n, EH K n k = EH (interior K) n k := fun n => by
    simp only [EH, ptLaw, restrict_interior_eq hK]
  have hvol : volume (interior K) = 1 := by
    rw [measure_congr (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume)), hK1]
  simp_rw [hEH]
  exact tendsto_EH_div_sq_of_measurableSet hK.interior isOpen_interior.measurableSet hvol
    (by omega)

end KHoles
