/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
Coefficients of powers of the Catalan generating function (ballot numbers).

Let `c(s) = Σ Cat_n s^n` be the Catalan generating function (`c = 1 + s c²`) and
`α(s) = s c(s)` (so `α = s + α²`). This file proves, for all `r N : ℕ`,

  (2N + r) · [s^N] c(s)^r = r · C(2N + r, N),

i.e. `[s^N] c^r = r/(2N+r) · C(2N+r, N)` for `r ≥ 1`, and the corollary used in
the (unpublished) draft on the closed form (Theorem 3.4, "Coefficients", and Section 4):
for `1 ≤ r ≤ n`,

  [s^n] α(s)^r = (r/n) · C(2n - r - 1, n - 1).

Proof: from `c^(r+1) = c^r · (1 + X c²) = c^r + X c^(r+2)` one gets the coefficient
recursion `f(r+1, N+1) = f(r, N+1) + f(r+2, N)`; the closed form satisfies the same
recursion (a finite binomial identity), and induction on `N` (outer) and `r` (inner)
with the bases `f(0, N+1) = 0`, `f(r, 0) = 1` finishes.
-/
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring

open PowerSeries

namespace KHoles

/-- `c^(r+1) = c^r + X · c^(r+2)`, a consequence of `c = 1 + X c²`. -/
theorem catalanSeries_pow_succ (r : ℕ) :
    catalanSeries ^ (r + 1) = catalanSeries ^ r + catalanSeries ^ (r + 2) * X := by
  rw [pow_succ]
  nth_rewrite 2 [← catalanSeries_sq_mul_X_add_one]
  ring

/-- Coefficient recursion: `[s^(N+1)] c^(r+1) = [s^(N+1)] c^r + [s^N] c^(r+2)`. -/
theorem coeff_catalanSeries_pow_succ_succ (r N : ℕ) :
    coeff (N + 1) (catalanSeries ^ (r + 1)) =
      coeff (N + 1) (catalanSeries ^ r) + coeff N (catalanSeries ^ (r + 2)) := by
  rw [catalanSeries_pow_succ, map_add, coeff_succ_mul_X]

/-- The closed form satisfies the same recursion (cleared denominators).
With `m = 2N + r + 2`, `A = C(m, N)`, `B = C(m, N+1)`: if `m · x = r B` and
`m · y = (r+2) A` then `(m+1) · (x + y) = (r+1) · C(m+1, N+1)`. -/
theorem ballot_step (r N x y : ℕ)
    (hx : (2 * N + r + 2) * x = r * Nat.choose (2 * N + r + 2) (N + 1))
    (hy : (2 * N + r + 2) * y = (r + 2) * Nat.choose (2 * N + r + 2) N) :
    (2 * N + r + 3) * (x + y) = (r + 1) * Nat.choose (2 * N + r + 3) (N + 1) := by
  set m := 2 * N + r + 2 with hm
  have hpas : Nat.choose (m + 1) (N + 1) = Nat.choose m N + Nat.choose m (N + 1) :=
    Nat.choose_succ_succ' m N
  have hrat : Nat.choose m (N + 1) * (N + 1) = Nat.choose m N * (N + r + 2) := by
    rw [Nat.choose_succ_right_eq]
    congr 1
    omega
  have hm3 : 2 * N + r + 3 = m + 1 := by omega
  rw [hm3, hpas]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < m by omega)
  have hmz : (m : ℤ) = 2 * N + r + 2 := by rw [hm]; push_cast; ring
  zify at hx hy hrat ⊢
  linear_combination (↑m + 1 : ℤ) * hx + (↑m + 1 : ℤ) * hy + (-2 : ℤ) * hrat
    + ((Nat.choose m N : ℤ) - Nat.choose m (N + 1)) * hmz

/-- Main identity (ballot numbers), valid for all `r N : ℕ` (for `r = 0` both sides vanish
unless `N = 0`, where it reads `0 = 0`):
`(2N + r) · [s^N] c^r = r · C(2N + r, N)`. -/
theorem coeff_catalanSeries_pow (r N : ℕ) :
    (2 * N + r) * coeff N (catalanSeries ^ r) = r * Nat.choose (2 * N + r) N := by
  induction N generalizing r with
  | zero =>
    simp [coeff_zero_eq_constantCoeff_apply]
  | succ N ihN =>
    induction r with
    | zero => simp [coeff_one]
    | succ r ihr =>
      rw [coeff_catalanSeries_pow_succ_succ]
      have hx := ihr
      have hy := ihN (r + 2)
      have e1 : 2 * (N + 1) + r = 2 * N + r + 2 := by ring
      have e2 : 2 * N + (r + 2) = 2 * N + r + 2 := by ring
      have e3 : 2 * (N + 1) + (r + 1) = 2 * N + r + 3 := by ring
      rw [e1] at hx
      rw [e2] at hy
      rw [e3]
      exact ballot_step r N _ _ hx hy

/-- Rational form: for `r ≥ 1`, `[s^N] c^r = r / (2N + r) · C(2N + r, N)`. -/
theorem coeff_catalanSeries_pow_rat (r N : ℕ) (hr : 1 ≤ r) :
    ((coeff N (catalanSeries ^ r) : ℕ) : ℚ) =
      (r : ℚ) / (2 * N + r) * Nat.choose (2 * N + r) N := by
  have h := coeff_catalanSeries_pow r N
  have hpos : (0 : ℚ) < 2 * N + r := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  rw [mul_comm]
  exact_mod_cast h

/-- Sanity check: `r = 1` gives the Catalan numbers, `(N+1) · Cat_N = C(2N+1, N)`. -/
example (N : ℕ) : (2 * N + 1) * catalan N = 1 * Nat.choose (2 * N + 1) N := by
  simpa using coeff_catalanSeries_pow 1 N

/-- `α = X · c` satisfies `α = X + α²`. -/
theorem X_mul_catalanSeries_eq :
    X * catalanSeries = X + (X * catalanSeries) ^ 2 := by
  conv_lhs => rw [← catalanSeries_sq_mul_X_add_one]
  ring

/-- Corollary (natural-number form): for `1 ≤ r ≤ n`,
`n · [s^n] (X c)^r = r · C(2n - r - 1, n - 1)`. -/
theorem coeff_X_mul_catalanSeries_pow (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    n * coeff n ((X * catalanSeries) ^ r) = r * Nat.choose (2 * n - r - 1) (n - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + (s + 1) := ⟨n - (s + 1), by omega⟩
  rw [mul_pow, coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]
  have h := coeff_catalanSeries_pow (s + 1) N
  have e1 : 2 * (N + (s + 1)) - (s + 1) - 1 = 2 * N + s := by omega
  have e2 : N + (s + 1) - 1 = N + s := by omega
  rw [e1, e2]
  have hsym : Nat.choose (2 * N + (s + 1)) N = Nat.choose (2 * N + s + 1) (N + s + 1) :=
    Nat.choose_symm_of_eq_add (by ring)
  have hpas := Nat.add_one_mul_choose_eq (2 * N + s) (N + s)
  -- hpas : (2N+s+1) * C(2N+s, N+s) = C(2N+s+1, N+s+1) * (N+s+1)
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 * N + s + 1 by omega)
  have h' : (2 * N + s + 1) * coeff N (catalanSeries ^ (s + 1)) =
      (s + 1) * Nat.choose (2 * N + s + 1) (N + s + 1) := by
    rw [← hsym, show 2 * N + s + 1 = 2 * N + (s + 1) by ring]; exact h
  calc (2 * N + s + 1) * ((N + (s + 1)) * coeff N (catalanSeries ^ (s + 1)))
      = (N + s + 1) * ((2 * N + s + 1) * coeff N (catalanSeries ^ (s + 1))) := by ring
    _ = (N + s + 1) * ((s + 1) * Nat.choose (2 * N + s + 1) (N + s + 1)) := by rw [h']
    _ = (s + 1) * (Nat.choose (2 * N + s + 1) (N + s + 1) * (N + s + 1)) := by ring
    _ = (s + 1) * ((2 * N + s + 1) * Nat.choose (2 * N + s) (N + s)) := by rw [hpas]
    _ = (2 * N + s + 1) * ((s + 1) * Nat.choose (2 * N + s) (N + s)) := by ring

/-- Corollary used in the paper: for `1 ≤ r ≤ n`,
`[s^n] α(s)^r = (r / n) · C(2n - r - 1, n - 1)` with `α = X · c`. -/
theorem coeff_X_mul_catalanSeries_pow_rat (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    ((coeff n ((X * catalanSeries) ^ r) : ℕ) : ℚ) =
      (r : ℚ) / n * Nat.choose (2 * n - r - 1) (n - 1) := by
  have h := coeff_X_mul_catalanSeries_pow r n hr hrn
  have hpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  rw [mul_comm]
  exact_mod_cast h

end KHoles
