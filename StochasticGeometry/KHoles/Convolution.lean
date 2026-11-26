/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
The convolution identity `C k = ½ Σ_m a_m a_{k-2-m}` for all `k`, via formal power series.

Let `c(s)` be the Catalan generating function and `α(s) = s · c(s)` (so `α = s + α²`, i.e.
`(1 - 2α)² = 1 - 4s`). Put

  S = sin(π α)    and    K = cos(2π α)

as formal power series over `ℝ` (substitution of `α` into the rescaled sine/cosine series).
Then, using `[s^n] α^r = (r/n) C(2n-r-1, n-1)` (file `CatalanPower`):

  a m = 2^m / π · [s^(m+1)] S,          C k = 2^k / (16 π²) · (-[s^k] K)   (k ≥ 1),

and the formal identity `sin(πT)² = (1 - cos(2πT))/2`, substituted at `T = α`, turns the
Cauchy product `[s^k] S²` into `-[s^k] K / 2`, which is exactly `Cconv k = C k`.
-/
import KHoles.Constants
import KHoles.CatalanPower
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

open Real Finset
open PowerSeries hiding C

namespace KHoles

/-! ### The series `α = X · c` over `ℝ` -/

/-- The Catalan generating function with real coefficients. -/
noncomputable def cR : ℝ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℝ) catalanSeries

/-- `α = X · c`, the (real) generating function of the shifted Catalan numbers. -/
noncomputable def α : ℝ⟦X⟧ := X * cR

lemma constantCoeff_α : constantCoeff α = 0 := by
  simp [α]

lemma hasSubst_α : HasSubst α := HasSubst.of_constantCoeff_zero' constantCoeff_α

lemma α_pow_eq_map (d : ℕ) :
    α ^ d = PowerSeries.map (Nat.castRingHom ℝ) ((X * catalanSeries) ^ d) := by
  simp [α, cR, map_pow, map_mul]

/-- `α = X + α²` over `ℝ`. -/
lemma α_eq : α = X + α ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℝ)) X_mul_catalanSeries_eq
  simpa [α, cR, map_pow, map_mul, map_add] using h

/-- `(1 - 2α)² = 1 - 4X`, i.e. formally `α = (1 - √(1 - 4X)) / 2`. -/
theorem one_sub_two_alpha_sq : (1 - 2 * α) ^ 2 = 1 - 4 * X := by
  have h := α_eq
  linear_combination (-4 : ℝ⟦X⟧) * h

lemma coeff_α_pow_of_lt (d n : ℕ) (h : n < d) : coeff n (α ^ d) = 0 := by
  rw [α, mul_pow, coeff_X_pow_mul', if_neg (by omega)]

lemma coeff_α_pow_zero (n : ℕ) (hn : 1 ≤ n) : coeff n (α ^ 0) = 0 := by
  simp [coeff_one]; omega

/-- `[s^n] α^d = (d/n) C(2n-d-1, n-1)` for `1 ≤ d ≤ n`. -/
lemma coeff_α_pow (d n : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ n) :
    coeff n (α ^ d) = (d : ℝ) / n * Nat.choose (2 * n - d - 1) (n - 1) := by
  have h := coeff_X_mul_catalanSeries_pow d n h1 h2
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [α_pow_eq_map, coeff_map, Nat.coe_castRingHom, div_mul_eq_mul_div, eq_div_iff hn]
  rw [mul_comm] at h
  exact_mod_cast h

/-- Coefficients of a substitution into `α` are finite sums. -/
lemma coeff_subst_α (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (subst α f) = ∑ d ∈ range (n + 1), coeff d f * coeff n (α ^ d) := by
  rw [coeff_subst' hasSubst_α, finsum_eq_sum_of_support_subset (s := range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [coeff_α_pow_of_lt d n (by omega), smul_zero])

/-! ### The formal sine and cosine series -/

lemma coeff_sin (n : ℕ) :
    coeff n (PowerSeries.sin ℝ) = if Even n then 0 else (-1 : ℝ) ^ (n / 2) / n.factorial := by
  simp [PowerSeries.sin]

lemma coeff_cos (n : ℕ) :
    coeff n (PowerSeries.cos ℝ) = if Even n then (-1 : ℝ) ^ (n / 2) / n.factorial else 0 := by
  simp [PowerSeries.cos]

lemma coeff_sin_two_mul (t : ℕ) : coeff (2 * t) (PowerSeries.sin ℝ) = 0 := by
  rw [coeff_sin, if_pos (even_two_mul t)]

lemma coeff_sin_two_mul_add_one (t : ℕ) :
    coeff (2 * t + 1) (PowerSeries.sin ℝ) = (-1 : ℝ) ^ t / (2 * t + 1).factorial := by
  rw [coeff_sin, if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one t)),
    show (2 * t + 1) / 2 = t by omega]

lemma coeff_cos_two_mul (t : ℕ) :
    coeff (2 * t) (PowerSeries.cos ℝ) = (-1 : ℝ) ^ t / (2 * t).factorial := by
  rw [coeff_cos, if_pos (even_two_mul t), show 2 * t / 2 = t by omega]

lemma coeff_cos_two_mul_add_one (t : ℕ) : coeff (2 * t + 1) (PowerSeries.cos ℝ) = 0 := by
  rw [coeff_cos, if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one t))]

lemma factorial_ne_zero_real (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

/-- One term of the Cauchy product of the sine series with itself in even degree `2m`. -/
lemma sin_mul_sin_term (m i : ℕ) (hi : i ≤ 2 * m) :
    coeff i (PowerSeries.sin ℝ) * coeff (2 * m - i) (PowerSeries.sin ℝ) =
      (1 - (-1 : ℝ) ^ i) * (Nat.choose (2 * m) i : ℝ) *
        ((-1 : ℝ) ^ (m + 1) / (2 * (2 * m).factorial)) := by
  rcases Nat.even_or_odd' i with ⟨t, rfl | rfl⟩
  · rw [coeff_sin_two_mul, pow_mul]
    norm_num
  · obtain ⟨u, rfl⟩ : ∃ u, m = t + 1 + u := ⟨m - (t + 1), by omega⟩
    have e : 2 * (t + 1 + u) - (2 * t + 1) = 2 * u + 1 := by omega
    have hc := Nat.choose_mul_factorial_mul_factorial (show 2 * t + 1 ≤ 2 * (t + 1 + u) by omega)
    rw [e] at hc
    have hc' : ((2 * (t + 1 + u)).choose (2 * t + 1) : ℝ) * (2 * t + 1).factorial *
        (2 * u + 1).factorial = (2 * (t + 1 + u)).factorial := by exact_mod_cast hc
    rw [e, coeff_sin_two_mul_add_one, coeff_sin_two_mul_add_one, ← hc']
    have p1 : (-1 : ℝ) ^ (2 * t + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have p2 : (-1 : ℝ) ^ (t + 1 + u + 1) = (-1) ^ t * (-1) ^ u := by
      rw [show t + 1 + u + 1 = t + u + 2 by ring, pow_add, pow_add]; norm_num
    rw [p1, p2]
    have f1 := factorial_ne_zero_real (2 * t + 1)
    have f2 := factorial_ne_zero_real (2 * u + 1)
    have hch : ((2 * (t + 1 + u)).choose (2 * t + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    field_simp
    ring

/-- One term of the Cauchy product of the sine series with itself in odd degree vanishes. -/
lemma sin_mul_sin_term_odd (m i : ℕ) (hi : i ≤ 2 * m + 1) :
    coeff i (PowerSeries.sin ℝ) * coeff (2 * m + 1 - i) (PowerSeries.sin ℝ) = 0 := by
  rcases Nat.even_or_odd' i with ⟨t, rfl | rfl⟩
  · rw [coeff_sin_two_mul, zero_mul]
  · rw [show 2 * m + 1 - (2 * t + 1) = 2 * (m - t) by omega, coeff_sin_two_mul, mul_zero]

/-- Formal identity `2 sin(πT)² + cos(2πT) = 1`. -/
theorem sin_sq_add_cos :
    rescale π (PowerSeries.sin ℝ) * rescale π (PowerSeries.sin ℝ) +
        rescale π (PowerSeries.sin ℝ) * rescale π (PowerSeries.sin ℝ) +
        rescale (2 * π) (PowerSeries.cos ℝ) = 1 := by
  ext n
  simp only [map_add, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_rescale,
    coeff_one]
  have hS : ∑ k ∈ range (n + 1), π ^ k * coeff k (PowerSeries.sin ℝ) *
      (π ^ (n - k) * coeff (n - k) (PowerSeries.sin ℝ)) =
      π ^ n * ∑ k ∈ range (n + 1), coeff k (PowerSeries.sin ℝ) *
        coeff (n - k) (PowerSeries.sin ℝ) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have : π ^ n = π ^ k * π ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_cancel' (by simp at hk; omega)]
    rw [this]
    ring
  rw [hS]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [coeff_sin, coeff_cos]
    rw [sum_congr rfl fun i hi => sin_mul_sin_term m i (by simp at hi; omega), ← sum_mul]
    simp only [sub_mul, one_mul, sum_sub_distrib]
    have h1 : ∑ i ∈ range (2 * m + 1), ((2 * m).choose i : ℝ) = 2 ^ (2 * m) := by
      exact_mod_cast Nat.sum_range_choose (2 * m)
    have h2 : ∑ i ∈ range (2 * m + 1), (-1 : ℝ) ^ i * ((2 * m).choose i : ℝ) = 0 := by
      have := (add_pow (-1 : ℝ) 1 (2 * m)).symm
      simpa [zero_pow (show 2 * m ≠ 0 by omega)] using this
    rw [h1, h2, coeff_cos_two_mul, if_neg (by omega), mul_pow, pow_succ]
    have := factorial_ne_zero_real (2 * m)
    field_simp
    ring
  · rw [sum_congr rfl fun i hi => sin_mul_sin_term_odd m i (by simp at hi; omega),
      coeff_cos_two_mul_add_one, if_neg (by omega)]
    simp

/-! ### `S = sin(π α)` and `K = cos(2π α)` -/

/-- `S = sin(π α)` as a formal power series. -/
noncomputable def S : ℝ⟦X⟧ := subst α (rescale π (PowerSeries.sin ℝ))

/-- `K = cos(2π α)` as a formal power series. -/
noncomputable def K : ℝ⟦X⟧ := subst α (rescale (2 * π) (PowerSeries.cos ℝ))

/-- `2 S² + K = 1`, i.e. `sin(πα)² = (1 - cos(2πα))/2`. -/
theorem S_mul_S_add_K : S * S + S * S + K = 1 := by
  have h := congrArg (substAlgHom (R := ℝ) hasSubst_α) sin_sq_add_cos
  simp only [map_add, map_mul, map_one, coe_substAlgHom] at h
  exact h

lemma coeff_zero_S : coeff 0 S = 0 := by
  simp [S, coeff_subst_α, coeff_sin]

lemma coeff_zero_K : coeff 0 K = 1 := by
  simp [K, coeff_subst_α, coeff_cos]

/-- `[s^(m+1)] S = π/(m+1) · Σ_j (-1)^j π^(2j)/(2j)! · C(2m-2j, m)`. -/
lemma coeff_succ_S (m : ℕ) :
    coeff (m + 1) S = π / (m + 1) * ∑ j ∈ range (m / 2 + 1),
      (-1 : ℝ) ^ j * π ^ (2 * j) / (2 * j).factorial * (2 * m - 2 * j).choose m := by
  rw [S, coeff_subst_α, mul_sum]
  set g : ℕ → ℝ := fun d => coeff d (rescale π (PowerSeries.sin ℝ)) * coeff (m + 1) (α ^ d)
    with hg
  have key : ∀ j ∈ range (m / 2 + 1), π / (m + 1) *
      ((-1 : ℝ) ^ j * π ^ (2 * j) / (2 * j).factorial * (2 * m - 2 * j).choose m) =
      g (2 * j + 1) := by
    intro j hj
    have hj' : 2 * j ≤ m := by simp at hj; omega
    rw [hg]
    simp only
    rw [coeff_rescale, coeff_sin_two_mul_add_one, coeff_α_pow _ _ (by omega) (by omega),
      show 2 * (m + 1) - (2 * j + 1) - 1 = 2 * m - 2 * j by omega, Nat.add_sub_cancel,
      Nat.factorial_succ]
    have := factorial_ne_zero_real (2 * j)
    push_cast
    field_simp
    ring
  rw [sum_congr rfl key, ← sum_image (g := fun j => 2 * j + 1) (by intro x _ y _ h; simpa using h)]
  symm
  apply sum_subset
  · intro d hd
    simp only [mem_image, mem_range] at hd ⊢
    omega
  · intro d hd hdn
    rw [hg]
    simp only
    rcases Nat.even_or_odd' d with ⟨t, rfl | rfl⟩
    · rw [coeff_rescale, coeff_sin_two_mul, mul_zero, zero_mul]
    · exfalso
      apply hdn
      simp only [mem_image, mem_range] at hd ⊢
      exact ⟨t, by omega, rfl⟩

/-- For `k ≥ 1`:
`[s^k] K = -(4π²/k) · Σ_{1 ≤ j ≤ k/2} (-1)^(j+1) (2π)^(2j-2)/(2j-1)! · C(2k-2j-1, k-1)`. -/
lemma coeff_K (k : ℕ) (hk : 1 ≤ k) :
    coeff k K = -(4 * π ^ 2 / k) * ∑ j ∈ Icc 1 (k / 2),
      (-1 : ℝ) ^ (j + 1) * (2 * π) ^ (2 * j - 2) / (2 * j - 1).factorial *
        (2 * k - 2 * j - 1).choose (k - 1) := by
  rw [K, coeff_subst_α, mul_sum]
  set g : ℕ → ℝ := fun d => coeff d (rescale (2 * π) (PowerSeries.cos ℝ)) * coeff k (α ^ d)
    with hg
  have key : ∀ j ∈ Icc 1 (k / 2), -(4 * π ^ 2 / k) *
      ((-1 : ℝ) ^ (j + 1) * (2 * π) ^ (2 * j - 2) / (2 * j - 1).factorial *
        (2 * k - 2 * j - 1).choose (k - 1)) = g (2 * j) := by
    intro j hj
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by simp at hj; omega⟩
    have hj' : 2 * (t + 1) ≤ k := by simp at hj; omega
    rw [hg]
    simp only
    rw [coeff_rescale, coeff_cos_two_mul, coeff_α_pow _ _ (by omega) hj',
      show 2 * (t + 1) - 2 = 2 * t by omega, show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
      show 2 * (t + 1) = 2 * t + 1 + 1 by ring, Nat.factorial_succ (2 * t + 1)]
    have := factorial_ne_zero_real (2 * t + 1)
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    push_cast
    field_simp
    ring
  rw [sum_congr rfl key, ← sum_image (g := fun j => 2 * j) (by intro x _ y _ h; simpa using h)]
  symm
  apply sum_subset
  · intro d hd
    simp only [mem_image, mem_range, mem_Icc] at hd ⊢
    omega
  · intro d hd hdn
    rw [hg]
    simp only
    rcases Nat.even_or_odd' d with ⟨t, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [mul_zero, coeff_α_pow_zero k hk, mul_zero]
      · exfalso
        apply hdn
        simp only [mem_image, mem_range, mem_Icc] at hd ⊢
        exact ⟨t, ⟨by omega, by omega⟩, rfl⟩
    · rw [coeff_rescale, coeff_cos_two_mul_add_one, mul_zero, zero_mul]

/-- `a m = 2^m / π · [s^(m+1)] S`. -/
lemma a_eq_coeff_S (m : ℕ) : a m = 2 ^ m / π * coeff (m + 1) S := by
  rw [coeff_succ_S, a]
  have := Real.pi_ne_zero
  field_simp

/-- `C k = 2^k / (16 π²) · (-[s^k] K)` for `k ≥ 1`. -/
lemma C_eq_coeff_K (k : ℕ) (hk : 1 ≤ k) : C k = 2 ^ k / (16 * π ^ 2) * -coeff k K := by
  rw [coeff_K k hk, C]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rcases n with _ | n
  · simp
  · rw [show n + 1 + 1 - 2 = n by omega, pow_succ, pow_succ]
    have := Real.pi_ne_zero
    field_simp
    ring

/-- Cauchy product, using `[s^0] S = 0`:
`[s^(n+2)] S² = Σ_{m ≤ n} [s^(m+1)] S · [s^(n-m+1)] S`. -/
lemma coeff_S_mul_S (n : ℕ) :
    coeff (n + 2) (S * S) = ∑ m ∈ range (n + 1), coeff (m + 1) S * coeff (n - m + 1) S := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    sum_range_succ']
  simp only [Nat.sub_self, coeff_zero_S, mul_zero, zero_mul, add_zero, Nat.sub_zero]
  refine sum_congr rfl fun m hm => ?_
  rw [show n + 2 - (m + 1) = n - m + 1 by simp at hm; omega]

/-! ### Main results -/

/-- The convolution identity `½ Σ_{m=0}^{k-2} a_m a_{k-2-m} = C k`, for every `k`. -/
theorem Cconv_eq_C_all (k : ℕ) : Cconv k = C k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [Cconv, C]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hK : coeff (n + 2) K = -2 * coeff (n + 2) (S * S) := by
    have h := congrArg (coeff (n + 2)) S_mul_S_add_K
    simp only [map_add, coeff_one, if_neg (show n + 2 ≠ 0 by omega)] at h
    linarith
  rw [C_eq_coeff_K _ (by omega), hK, coeff_S_mul_S, Cconv, show n + 2 - 1 = n + 1 by omega]
  simp only [neg_mul, sum_neg_distrib, neg_neg, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by simp at hm; omega
  rw [show n + 2 - 2 - m = n - m by omega, a_eq_coeff_S, a_eq_coeff_S]
  have h2 : (2 : ℝ) ^ n = 2 ^ m * 2 ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [pow_succ, pow_succ, h2]
  have := Real.pi_ne_zero
  field_simp
  ring

/-- Generating function of the cap numbers: `Σ_m a_m z^m = sin(π α(2z)) / (2π z)`, stated as
`z · Σ_m a_m z^m = (1/(2π)) · S(2z)`. -/
theorem genfun_a : X * mk a = PowerSeries.C (1 / (2 * π)) * rescale 2 S := by
  ext n
  rw [PowerSeries.coeff_C_mul, coeff_rescale]
  rcases n with _ | m
  · simp [coeff_zero_S]
  · rw [coeff_succ_X_mul, coeff_mk, a_eq_coeff_S, pow_succ]
    have := Real.pi_ne_zero
    field_simp

/-- Generating function of the k-hole constants:
`Σ_k C(k) z^k = (1 - cos(2π α(2z))) / (16 π²)`. Since `1 - 2α(2z) = √(1 - 8z)`
(`one_sub_two_alpha_sq`), this is `(1 + cos(π √(1 - 8z))) / (16 π²)`. -/
theorem genfun_C : mk C = PowerSeries.C (1 / (16 * π ^ 2)) * (1 - rescale 2 K) := by
  ext k
  rw [PowerSeries.coeff_C_mul, coeff_mk]
  simp only [map_sub, coeff_rescale, coeff_one]
  rcases k with _ | k
  · simp [C, coeff_zero_K]
  · rw [C_eq_coeff_K _ (by omega), if_neg (by omega)]
    ring

end KHoles
