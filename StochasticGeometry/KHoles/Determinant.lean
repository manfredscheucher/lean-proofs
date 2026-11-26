/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
Determinants of the Brownian-motion and Brownian-bridge covariance matrices
(Lemma 3.2 of the (unpublished) draft on the closed form).

Let `x : Fin (n+1) → ℝ` be strictly increasing with `0 < x 0` (so `m = n+1` points,
`Fin.last n` is the last index). With

  M i j = min (x i) (x j)                  (Brownian-motion covariance)
  G i j = min (x i) (x j) - x i * x j      (Brownian-bridge covariance)
  W i j = G i j / G i i                    (rows of `G` normalised by the diagonal)

we prove
  (T1) det M = x 0 * ∏_{i < n} (x (i+1) - x i)       (product of the gaps from 0)
  (T2) det G = det M * (1 - x (last))                (gaps including the last one to 1)
  (T3) det W = det G / ∏ i, x i * (1 - x i).

Proof of T1: `M = L * D * Lᵀ` with `L` the lower-triangular all-ones matrix and `D` the
diagonal matrix of gaps (the entry identity is a telescoping sum).
Proof of T2: `G = M - col x * row x`, the matrix determinant lemma, and `M e_last = x`.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

open Matrix Finset

namespace KHoles

variable {n : ℕ}

/-- Brownian-motion covariance matrix `M i j = min (x i) (x j)`. -/
def bmCov (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => min (x i) (x j)

/-- Brownian-bridge covariance matrix `G i j = min (x i) (x j) - x i * x j`. -/
def bbCov (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => min (x i) (x j) - x i * x j

/-- Row-normalised bridge covariance `W i j = G i j / G i i`. -/
noncomputable def bbCovNorm (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => bbCov x i j / bbCov x i i

/-! ### Auxiliary: `x` extended to `ℕ` and its gaps -/

/-- `x` as a function on `ℕ` (junk value `0` beyond index `n`). -/
def xNat (x : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k < n + 1 then x ⟨k, h⟩ else 0

/-- The gaps `x 0 - 0, x 1 - x 0, x 2 - x 1, …`. -/
def gap (x : Fin (n + 1) → ℝ) : ℕ → ℝ
  | 0 => xNat x 0
  | k + 1 => xNat x (k + 1) - xNat x k

lemma xNat_fin (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : xNat x i = x i := by
  simp [xNat, i.is_lt]

/-- Telescoping: summing the gaps up to `min N c` gives `x (min N c)`. -/
lemma sum_gap_ite (x : Fin (n + 1) → ℝ) (c : ℕ) :
    ∀ N : ℕ, ∑ k ∈ range (N + 1), (if k ≤ c then gap x k else 0) = xNat x (min N c)
  | 0 => by simp [gap]
  | N + 1 => by
    rw [sum_range_succ, sum_gap_ite x c N]
    by_cases h : N + 1 ≤ c
    · rw [if_pos h, min_eq_left h, min_eq_left (by omega)]
      simp [gap]
    · rw [if_neg h, min_eq_right (by omega), min_eq_right (by omega), add_zero]

/-- Lower-triangular all-ones matrix. -/
def lowerOnes (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if j ≤ i then 1 else 0

lemma det_lowerOnes : (lowerOnes n).det = 1 := by
  rw [det_of_isLowerTriangular]
  · simp [lowerOnes]
  · intro i j hij
    have : i < j := hij
    simp [lowerOnes, not_le.mpr this]

/-- `M = L * D * Lᵀ`. -/
lemma bmCov_eq_LDLt (x : Fin (n + 1) → ℝ) (hx : Monotone x) :
    bmCov x = lowerOnes n * diagonal (fun k : Fin (n + 1) => gap x k) * (lowerOnes n)ᵀ := by
  ext i j
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, lowerOnes, of_apply, bmCov]
  have hterm : ∀ k : Fin (n + 1),
      ((if k ≤ i then (1 : ℝ) else 0) * gap x k * if k ≤ j then 1 else 0) =
        (fun k : ℕ => if k ≤ min (i : ℕ) j then gap x k else 0) k := by
    intro k
    simp only [Fin.le_iff_val_le_val, le_min_iff]
    by_cases hi : (k : ℕ) ≤ i <;> by_cases hj : (k : ℕ) ≤ j <;> simp [hi, hj]
  have hij : min (i : ℕ) j ≤ n := by have := i.is_lt; omega
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if k ≤ min (i : ℕ) j then gap x k else 0) (n + 1),
    sum_gap_ite x _ n, min_eq_right hij, ← Fin.coe_min, xNat_fin, hx.map_min]

/-- **(T1)** `det [min (x i) (x j)] = x 0 * ∏_{i < n} (x (i+1) - x i)`. -/
theorem det_bmCov (x : Fin (n + 1) → ℝ) (hx : Monotone x) :
    (bmCov x).det = x 0 * ∏ i : Fin n, (x i.succ - x i.castSucc) := by
  rw [bmCov_eq_LDLt x hx, det_mul, det_mul, det_transpose, det_lowerOnes, det_diagonal,
    Fin.prod_univ_succ, one_mul, mul_one]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.val_succ]
  simp only [gap]
  rw [← Fin.val_succ, xNat_fin, ← Fin.val_castSucc, xNat_fin]

lemma det_bmCov_pos (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (h0 : 0 < x 0) :
    0 < (bmCov x).det := by
  rw [det_bmCov x hx.monotone]
  exact mul_pos h0 (prod_pos fun i _ => sub_pos.mpr (hx Fin.castSucc_lt_succ))

/-- The last column of `M` is `x`: `M * e_last = x` (as column matrices). -/
lemma bmCov_mul_single_last (x : Fin (n + 1) → ℝ) (hx : Monotone x) :
    bmCov x * replicateCol Unit (Pi.single (Fin.last n) (1 : ℝ)) = replicateCol Unit x := by
  ext i u
  simp [mul_apply, bmCov, replicateCol_apply, Pi.single_apply, min_eq_left (hx (Fin.le_last i))]

/-- **(T2)** `det [min (x i) (x j) - x i x j] = det M * (1 - x last)`. -/
theorem det_bbCov (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (h0 : 0 < x 0) :
    (bbCov x).det = (bmCov x).det * (1 - x (Fin.last n)) := by
  have hU : IsUnit (bmCov x).det := (det_bmCov_pos x hx h0).ne'.isUnit
  have hG : bbCov x = bmCov x + replicateCol Unit (-x) * replicateRow Unit x := by
    ext i j
    simp [bbCov, bmCov, sub_eq_add_neg, mul_apply, replicateCol_apply, replicateRow_apply]
  have hcol : replicateCol Unit (-x) =
      bmCov x * replicateCol Unit (-Pi.single (Fin.last n) (1 : ℝ)) := by
    ext i u
    simp [mul_apply, bmCov, replicateCol_apply, Pi.single_apply,
      min_eq_left (hx.monotone (Fin.le_last i))]
  rw [hG, det_add_replicateCol_mul_replicateRow hU, hcol, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left (A := bmCov x)
      (replicateCol Unit (-Pi.single (Fin.last n) (1 : ℝ))) hU]
  congr 1
  rw [det_unique, Matrix.add_apply, replicateRow_mul_replicateCol_apply]
  simp [sub_eq_add_neg]

/-- **(T3)** `det W = det G / ∏ i, x i * (1 - x i)` where `W i j = G i j / G i i`. -/
theorem det_bbCovNorm (x : Fin (n + 1) → ℝ) :
    (bbCovNorm x).det = (bbCov x).det / ∏ i, (x i * (1 - x i)) := by
  have hW : bbCovNorm x = diagonal (fun i => (bbCov x i i)⁻¹) * bbCov x := by
    ext i j
    simp [bbCovNorm, div_eq_inv_mul]
  have hd : ∀ i, bbCov x i i = x i * (1 - x i) := by
    intro i; simp [bbCov]; ring
  rw [hW, det_mul, det_diagonal, prod_inv_distrib, div_eq_inv_mul]
  simp only [hd]

/-- **(T2')** Combined form: `det G` is the product of all `n + 2` gaps
`x 0 - 0, x 1 - x 0, …, x last - x (last-1), 1 - x last`. -/
theorem det_bbCov_eq_prod_gaps (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (h0 : 0 < x 0) :
    (bbCov x).det =
      x 0 * (∏ i : Fin n, (x i.succ - x i.castSucc)) * (1 - x (Fin.last n)) := by
  rw [det_bbCov x hx h0, det_bmCov x hx.monotone]

end KHoles
