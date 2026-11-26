/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
Cone geometry of concave chains (Lemma 3.1 of the (unpublished) draft on the closed form).

Fix `0 < x 0 < … < x n < 1` (so `m = n + 1` interior abscissae) and pad them with
`0` and `1`. A height vector `Y : Fin (n+1) → ℝ` (with heights `0` at both ends)
describes the piecewise linear chain through `(0,0), (x i, Y i), (1,0)`.

For `lam : Fin (n+1) → ℝ` put `Y = lam ᵥ* W` with `W = bbCovNorm x`, i.e.
`Y = ∑ i, lam i • w_i` where `w_i` is the tent with peak `1` at `x i`. We prove
  (G1) the slope drop of `Y` at `x i` is `lam i / (x i * (1 - x i))`;
  (G2) the trapezoid area under `Y` is `(∑ i, lam i) / 2`;
  (G3) the strictly concave chains are exactly the image of the open positive orthant.

Encoding: padded abscissae and heights are `ℕ`-indexed (`xpad`, `ypad`); index `k`
of the padded sequence is `x (k-1)` for `1 ≤ k ≤ n+1`, with `xpad 0 = 0`,
`xpad (n+2) = 1` and `ypad 0 = ypad (n+2) = 0`.

Key identity: for `k ≤ n+2`, `ypad Y k = ∑ j, c j * (xpad (min (j+1) k) - x j * xpad k)`
with `c j = lam j / G j j`, i.e. each tent is `t ↦ (min (x j) t - x j t) / G j j`
sampled at the padded abscissae. Slopes and areas are then computed termwise.
-/
import KHoles.Determinant

open Matrix Finset

namespace KHoles

variable {n : ℕ}

/-- Padded abscissae `0, x 0, …, x n, 1` (junk value `1` beyond index `n + 2`). -/
def xpad (x : Fin (n + 1) → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if h : k < n + 1 then x ⟨k, h⟩ else 1

/-- Padded heights `0, Y 0, …, Y n, 0` (junk value `0` beyond index `n + 2`). -/
def ypad (Y : Fin (n + 1) → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => xNat Y k

/-- Slope of the `k`-th segment (from padded point `k` to `k + 1`), `k ≤ n + 1`. -/
noncomputable def slope (x Y : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  (ypad Y (k + 1) - ypad Y k) / (xpad x (k + 1) - xpad x k)

/-- Slope drop of the chain at the interior point `x i` (padded index `i + 1`). -/
noncomputable def slopeDrop (x Y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  slope x Y i - slope x Y ((i : ℕ) + 1)

/-- Height vectors whose chain is strictly concave: the slopes strictly decrease at
every interior point. -/
def Admissible (x : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {Y | ∀ i : Fin (n + 1), slope x Y ((i : ℕ) + 1) < slope x Y i}

/-- Area under the chain (trapezoid rule over the `n + 2` segments). -/
noncomputable def areaUnder (x Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k ∈ range (n + 2), (xpad x (k + 1) - xpad x k) * (ypad Y k + ypad Y (k + 1)) / 2

/-- The linear map `lam ↦ lam ᵥ* W` (`W = bbCovNorm x`), i.e. `lam ↦ ∑ i, lam i • w_i`. -/
noncomputable def coneMap (x : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  Matrix.vecMulLinear (bbCovNorm x)

lemma coneMap_apply (x lam : Fin (n + 1) → ℝ) : coneMap x lam = lam ᵥ* bbCovNorm x := rfl

/-! ### Padded abscissae -/

lemma xpad_succ_fin (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : xpad x ((i : ℕ) + 1) = x i := by
  simp [xpad, i.is_lt]

lemma xpad_last (x : Fin (n + 1) → ℝ) : xpad x (n + 2) = 1 := by
  simp [xpad]

lemma xpad_lt_succ {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) {k : ℕ} (hk : k < n + 2) : xpad x k < xpad x (k + 1) := by
  rcases k with _ | k
  · simpa [xpad] using h0
  · by_cases hk' : k + 1 < n + 1
    · simp only [xpad, dif_pos hk', dif_pos (show k < n + 1 by omega)]
      exact hx (Fin.mk_lt_mk.mpr (by omega))
    · have hkn : k < n + 1 := by omega
      simp only [xpad, dif_neg hk', dif_pos hkn]
      have hl : (⟨k, hkn⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
      rw [hl]
      exact h1

lemma xpad_mono {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) : Monotone (xpad x) := by
  refine monotone_nat_of_le_succ fun k => ?_
  by_cases hk : k < n + 2
  · exact (xpad_lt_succ hx h0 h1 hk).le
  · rcases k with _ | k
    · omega
    · simp [xpad, show ¬ k < n + 1 by omega, show ¬ k + 1 < n + 1 by omega]

lemma x_pos {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0) (i : Fin (n + 1)) :
    0 < x i :=
  h0.trans_le (hx.monotone (Fin.zero_le i))

lemma x_lt_one {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h1 : x (Fin.last n) < 1)
    (i : Fin (n + 1)) : x i < 1 :=
  (hx.monotone (Fin.le_last i)).trans_lt h1

lemma bbCov_diag (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : bbCov x i i = x i * (1 - x i) := by
  simp [bbCov]; ring

lemma bbCov_diag_pos {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (i : Fin (n + 1)) : 0 < x i * (1 - x i) :=
  mul_pos (x_pos hx h0 i) (sub_pos.mpr (x_lt_one hx h1 i))

/-! ### The cone map in padded coordinates -/

/-- Each tent `w_j` sampled at the padded abscissae:
`ypad (lam ᵥ* W) k = ∑ j, lam j / G j j * (min (x j) (xpad k) - x j * xpad k)`. -/
lemma ypad_coneMap {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (lam : Fin (n + 1) → ℝ) {k : ℕ} (hk : k ≤ n + 2) :
    ypad (coneMap x lam) k = ∑ j : Fin (n + 1), lam j / bbCov x j j *
      (xpad x (min ((j : ℕ) + 1) k) - x j * xpad x k) := by
  have hm := xpad_mono hx h0 h1
  rcases k with _ | k
  · simp [ypad, xpad]
  · by_cases hk' : k < n + 1
    · have hxk : xpad x (k + 1) = x ⟨k, hk'⟩ := by simp [xpad, hk']
      simp only [ypad, xNat, dif_pos hk', coneMap_apply, vecMul, dotProduct, bbCovNorm,
        of_apply]
      refine sum_congr rfl fun j _ => ?_
      rw [hm.map_min, xpad_succ_fin, hxk, bbCov, of_apply]
      ring
    · obtain rfl : k = n + 1 := by omega
      simp only [ypad, xNat, dif_neg (lt_irrefl (n + 1))]
      symm
      refine sum_eq_zero fun j _ => ?_
      rw [min_eq_left (by omega), xpad_succ_fin, xpad_last]
      ring

/-- Slope of the `k`-th segment of `lam ᵥ* W`. -/
lemma slope_coneMap {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (lam : Fin (n + 1) → ℝ) {k : ℕ} (hk : k < n + 2) :
    slope x (coneMap x lam) k =
      ∑ j : Fin (n + 1), lam j / bbCov x j j * ((if k ≤ (j : ℕ) then 1 else 0) - x j) := by
  have hpos := sub_pos.mpr (xpad_lt_succ hx h0 h1 hk)
  rw [slope, ypad_coneMap hx h0 h1 lam (by omega), ypad_coneMap hx h0 h1 lam (by omega),
    ← sum_sub_distrib, div_eq_iff hpos.ne', sum_mul]
  refine sum_congr rfl fun j _ => ?_
  by_cases hkj : k ≤ (j : ℕ)
  · rw [min_eq_right (by omega : k + 1 ≤ (j : ℕ) + 1), min_eq_right (by omega : k ≤ (j : ℕ) + 1),
      if_pos hkj]
    ring
  · rw [min_eq_left (by omega : (j : ℕ) + 1 ≤ k + 1), min_eq_left (by omega : (j : ℕ) + 1 ≤ k),
      if_neg hkj]
    ring

/-! ### (G1) slope drops -/

/-- **(G1)** The slope drop of `lam ᵥ* W` at `x i` is `lam i / (x i * (1 - x i))`. -/
theorem slopeDrop_coneMap {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (lam : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    slopeDrop x (coneMap x lam) i = lam i / (x i * (1 - x i)) := by
  rw [slopeDrop, slope_coneMap hx h0 h1 lam (by omega), slope_coneMap hx h0 h1 lam (by omega),
    ← sum_sub_distrib, sum_eq_single i]
  · rw [if_pos le_rfl, if_neg (by omega), bbCov_diag]
    ring
  · intro j _ hji
    have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    by_cases h : (i : ℕ) ≤ j
    · rw [if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg h, if_neg (by omega)]
      ring
  · simp

/-! ### (G2) area -/

/-- Trapezoid area of a single (unnormalised) tent `t ↦ min (x j) t - x j * t`. -/
lemma area_tent {x : Fin (n + 1) → ℝ} (j : Fin (n + 1)) :
    ∑ k ∈ range (n + 2), (xpad x (k + 1) - xpad x k) *
      ((xpad x (min ((j : ℕ) + 1) k) - x j * xpad x k) +
        (xpad x (min ((j : ℕ) + 1) (k + 1)) - x j * xpad x (k + 1))) / 2 =
      x j * (1 - x j) / 2 := by
  -- antiderivative-like potential `F` with `term k = F (k + 1) - F k`
  let F : ℕ → ℝ := fun k =>
    (1 - x j) * xpad x (min ((j : ℕ) + 1) k) ^ 2 / 2 + x j * (2 * xpad x k - xpad x k ^ 2) / 2
      - x j * (2 * xpad x (min ((j : ℕ) + 1) k) - xpad x (min ((j : ℕ) + 1) k) ^ 2) / 2
  have hterm : ∀ k : ℕ, (xpad x (k + 1) - xpad x k) *
      ((xpad x (min ((j : ℕ) + 1) k) - x j * xpad x k) +
        (xpad x (min ((j : ℕ) + 1) (k + 1)) - x j * xpad x (k + 1))) / 2 = F (k + 1) - F k := by
    intro k
    simp only [F]
    by_cases hkj : k ≤ (j : ℕ)
    · rw [min_eq_right (by omega : k + 1 ≤ (j : ℕ) + 1), min_eq_right (by omega : k ≤ (j : ℕ) + 1)]
      ring
    · rw [min_eq_left (by omega : (j : ℕ) + 1 ≤ k + 1), min_eq_left (by omega : (j : ℕ) + 1 ≤ k),
        xpad_succ_fin]
      ring
  rw [sum_congr rfl (fun k _ => hterm k), sum_range_sub]
  simp only [F]
  rw [min_eq_left (by omega : (j : ℕ) + 1 ≤ n + 2), Nat.min_zero, xpad_succ_fin, xpad_last]
  simp only [xpad]
  ring

/-- **(G2)** The area under `lam ᵥ* W` is `(∑ i, lam i) / 2` (every tent has area `1/2`). -/
theorem areaUnder_coneMap {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (lam : Fin (n + 1) → ℝ) :
    areaUnder x (coneMap x lam) = (∑ i, lam i) / 2 := by
  have hW : ∀ k ∈ range (n + 2),
      (xpad x (k + 1) - xpad x k) * (ypad (coneMap x lam) k + ypad (coneMap x lam) (k + 1)) / 2 =
        ∑ j, lam j / bbCov x j j * ((xpad x (k + 1) - xpad x k) *
          ((xpad x (min ((j : ℕ) + 1) k) - x j * xpad x k) +
            (xpad x (min ((j : ℕ) + 1) (k + 1)) - x j * xpad x (k + 1))) / 2) := by
    intro k hk
    rw [mem_range] at hk
    rw [ypad_coneMap hx h0 h1 lam (by omega), ypad_coneMap hx h0 h1 lam (by omega),
      ← sum_add_distrib, mul_sum, sum_div]
    exact sum_congr rfl fun j _ => by ring
  rw [areaUnder, sum_congr rfl hW, sum_comm, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, area_tent, bbCov_diag]
  have := (bbCov_diag_pos hx h0 h1 j).ne'
  field_simp
  rw [mul_assoc, mul_div_assoc, div_self this, mul_one]

/-! ### (G3) admissible chains = image of the open positive orthant -/

/-- `W` is invertible (all gaps of the padded abscissae are positive). -/
theorem det_bbCovNorm_ne_zero {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) : (bbCovNorm x).det ≠ 0 := by
  rw [det_bbCovNorm, det_bbCov_eq_prod_gaps x hx h0]
  refine div_ne_zero (mul_ne_zero (mul_ne_zero h0.ne' ?_) (sub_pos.mpr h1).ne') ?_
  · exact prod_ne_zero_iff.mpr fun i _ => (sub_pos.mpr (hx Fin.castSucc_lt_succ)).ne'
  · exact prod_ne_zero_iff.mpr fun i _ => (bbCov_diag_pos hx h0 h1 i).ne'

/-- The cone map is injective (the slope drops recover `lam`, by (G1)). -/
theorem coneMap_injective {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) : Function.Injective (coneMap x) := by
  intro a b hab
  funext i
  have h := slopeDrop_coneMap hx h0 h1 a i
  rw [hab, slopeDrop_coneMap hx h0 h1 b i] at h
  exact ((div_left_inj' (bbCov_diag_pos hx h0 h1 i).ne').mp h).symm

/-- The cone map is surjective: `lam = Y ᵥ* W⁻¹` is a preimage of `Y`. -/
theorem coneMap_surjective {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) : Function.Surjective (coneMap x) := by
  intro Y
  refine ⟨Y ᵥ* (bbCovNorm x)⁻¹, ?_⟩
  rw [coneMap_apply, vecMul_vecMul,
    nonsing_inv_mul _ (det_bbCovNorm_ne_zero hx h0 h1).isUnit, vecMul_one]

/-- **(G3)** The strictly concave chains are exactly the images `lam ᵥ* W` of the
open positive orthant `{lam | ∀ i, 0 < lam i}`. -/
theorem admissible_eq_image {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) : Admissible x = coneMap x '' {lam | ∀ i, 0 < lam i} := by
  ext Y
  constructor
  · intro hY
    obtain ⟨lam, rfl⟩ := coneMap_surjective hx h0 h1 Y
    refine ⟨lam, fun i => ?_, rfl⟩
    have hd : 0 < slopeDrop x (coneMap x lam) i := sub_pos.mpr (hY i)
    rw [slopeDrop_coneMap hx h0 h1] at hd
    exact (div_pos_iff_of_pos_right (bbCov_diag_pos hx h0 h1 i)).mp hd
  · rintro ⟨lam, hlam, rfl⟩ i
    have h := slopeDrop_coneMap hx h0 h1 lam i
    have hp : 0 < lam i / (x i * (1 - x i)) := div_pos (hlam i) (bbCov_diag_pos hx h0 h1 i)
    rw [slopeDrop] at h
    linarith

/-- **(G3), area part** On the admissible set, `area (lam ᵥ* W) = (∑ i, lam i) / 2`;
restated with the explicit matrix product. -/
theorem areaUnder_vecMul {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (lam : Fin (n + 1) → ℝ) :
    areaUnder x (lam ᵥ* bbCovNorm x) = (∑ i, lam i) / 2 :=
  areaUnder_coneMap hx h0 h1 lam

end KHoles
