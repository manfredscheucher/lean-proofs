/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.ConeGeometry

/-!
# Discrete concavity of admissible chains

Step 5b of `doc/kholes/kholes.md` (first part). For sorted abscissae
`0 < x 0 < … < x n < 1` and heights `Y`, the padded chain is `P_j = (xpad x j, ypad Y j)`,
`j ≤ n + 2` (`ConeGeometry.lean`), and the `k`-th edge line is
`ℓ_k(t) = ypad Y k + slope x Y k * (t - xpad x k)` (`k ≤ n + 1`).

* `slope_lt_slope`: on admissible heights the slopes strictly decrease;
* `ypad_succ_eq`: the edge `k` goes through `P_k` and `P_{k+1}`;
* `ypad_le_edge`, `ypad_lt_edge` (DCF): every chain vertex lies below every edge line,
  strictly unless it is an endpoint of that edge;
* `admissible_pos`: admissible heights are positive;
* `range_baseCfg_zip2`: the points of `baseCfg (zip2 x Y)` are exactly the padded chain.

These lemmas are used by `ChainConvex.lean` and `ChainArea.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

variable {n : ℕ} {x Y : Fin (n + 1) → ℝ}

lemma ypad_succ_fin (Y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ypad Y ((i : ℕ) + 1) = Y i := by
  simp [ypad, xNat_fin]

lemma ypad_last (Y : Fin (n + 1) → ℝ) : ypad Y (n + 2) = 0 := by
  simp [ypad, xNat]

/-- On admissible heights the slopes strictly decrease. -/
theorem slope_lt_slope (hY : Y ∈ Admissible x) {k l : ℕ} (hkl : k < l) (hl : l ≤ n + 1) :
    slope x Y l < slope x Y k := by
  have step : ∀ t, t < n + 1 → slope x Y (t + 1) < slope x Y t := fun t ht => hY ⟨t, ht⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  induction d with
  | zero => exact step k (by omega)
  | succ d ih => exact (step (k + d + 1) (by omega)).trans (ih (by omega) (by omega))

/-- The edge `k` goes through `P_k` and `P_{k+1}`. -/
theorem ypad_succ_eq (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1) {k : ℕ}
    (hk : k ≤ n + 1) :
    ypad Y (k + 1) = ypad Y k + slope x Y k * (xpad x (k + 1) - xpad x k) := by
  have hpos := sub_pos.mpr (xpad_lt_succ hx h0 h1 (show k < n + 2 by omega))
  rw [slope, div_mul_cancel₀ _ hpos.ne']
  ring

/-- Height of the edge line `ℓ_k` above the vertex `P_j`. -/
private noncomputable def edgeGap (x Y : Fin (n + 1) → ℝ) (k j : ℕ) : ℝ :=
  ypad Y k + slope x Y k * (xpad x j - xpad x k) - ypad Y j

private lemma edgeGap_self (k : ℕ) : edgeGap x Y k k = 0 := by
  simp [edgeGap]

private lemma edgeGap_succ_self (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    {k : ℕ} (hk : k ≤ n + 1) : edgeGap x Y k (k + 1) = 0 := by
  rw [edgeGap, ypad_succ_eq hx h0 h1 hk]
  ring

private lemma edgeGap_succ (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    {j k : ℕ} (hj : j ≤ n + 1) :
    edgeGap x Y k (j + 1) =
      edgeGap x Y k j + (slope x Y k - slope x Y j) * (xpad x (j + 1) - xpad x j) := by
  rw [edgeGap, edgeGap, ypad_succ_eq hx h0 h1 hj]
  ring

/-- Vertices to the right of the edge `k` lie strictly below its line. -/
private lemma edgeGap_pos_above (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) {k : ℕ} (hk : k ≤ n + 1) :
    ∀ d : ℕ, k + 2 + d ≤ n + 2 → 0 < edgeGap x Y k (k + 2 + d) := by
  intro d
  induction d with
  | zero =>
    intro hd
    have e := edgeGap_succ (Y := Y) (k := k) hx h0 h1 (j := k + 1) (by omega)
    rw [edgeGap_succ_self hx h0 h1 hk] at e
    have hs := sub_pos.mpr (slope_lt_slope hY (lt_add_one k) (by omega))
    have hd' := sub_pos.mpr (xpad_lt_succ hx h0 h1 (show k + 1 < n + 2 by omega))
    rw [show k + 2 + 0 = k + 1 + 1 by omega, e]
    linarith [mul_pos hs hd']
  | succ d ih =>
    intro hd
    have e := edgeGap_succ (Y := Y) (k := k) hx h0 h1 (j := k + 2 + d) (by omega)
    have hs := sub_pos.mpr (slope_lt_slope hY (show k < k + 2 + d by omega) (by omega))
    have hd' := sub_pos.mpr (xpad_lt_succ hx h0 h1 (show k + 2 + d < n + 2 by omega))
    rw [show k + 2 + (d + 1) = k + 2 + d + 1 by omega, e]
    linarith [mul_pos hs hd', ih (by omega)]

/-- Vertices to the left of the edge `k` lie strictly below its line. -/
private lemma edgeGap_pos_below (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) {k : ℕ} (hk : k ≤ n + 1) :
    ∀ d j : ℕ, j + d + 1 = k → 0 < edgeGap x Y k j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have e := edgeGap_succ (Y := Y) (k := k) hx h0 h1 (j := j) (by omega)
    obtain rfl : k = j + 1 := by omega
    rw [edgeGap_self] at e
    have hs := sub_neg.mpr (slope_lt_slope hY (show j < j + 1 by omega) hk)
    have hd' := sub_pos.mpr (xpad_lt_succ hx h0 h1 (show j < n + 2 by omega))
    linarith [mul_neg_of_neg_of_pos hs hd']
  | succ d ih =>
    intro j hj
    have e := edgeGap_succ (Y := Y) (k := k) hx h0 h1 (j := j) (by omega)
    have hs := sub_neg.mpr (slope_lt_slope hY (show j < k by omega) hk)
    have hd' := sub_pos.mpr (xpad_lt_succ hx h0 h1 (show j < n + 2 by omega))
    linarith [mul_neg_of_neg_of_pos hs hd', ih (j + 1) (by omega)]

/-- (DCF, strict) Every chain vertex other than `P_k`, `P_{k+1}` lies strictly below the
line of the edge `k`. -/
theorem ypad_lt_edge (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) {j k : ℕ} (hj : j ≤ n + 2) (hk : k ≤ n + 1) (hjk : j ≠ k)
    (hjk' : j ≠ k + 1) :
    ypad Y j < ypad Y k + slope x Y k * (xpad x j - xpad x k) := by
  have h : 0 < edgeGap x Y k j := by
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · exact edgeGap_pos_below hx h0 h1 hY hk (k - j - 1) j (by omega)
    · obtain ⟨d, rfl⟩ : ∃ d, j = k + 2 + d := ⟨j - (k + 2), by omega⟩
      exact edgeGap_pos_above hx h0 h1 hY hk d hj
  rw [edgeGap] at h
  linarith

/-- (DCF, weak) Every chain vertex lies on or below the line of every edge. -/
theorem ypad_le_edge (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) {j k : ℕ} (hj : j ≤ n + 2) (hk : k ≤ n + 1) :
    ypad Y j ≤ ypad Y k + slope x Y k * (xpad x j - xpad x k) := by
  by_cases hjk : j = k
  · subst hjk
    simp
  by_cases hjk' : j = k + 1
  · subst hjk'
    exact (ypad_succ_eq hx h0 h1 hk).le
  exact (ypad_lt_edge hx h0 h1 hY hj hk hjk hjk').le

/-- Admissible heights are positive: `Y i` is a positive combination of the tents
`min (x j) (x i) - x j * x i > 0` (`admissible_eq_image`, `ypad_coneMap`). -/
theorem admissible_pos (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) (i : Fin (n + 1)) : 0 < Y i := by
  rw [admissible_eq_image hx h0 h1] at hY
  obtain ⟨lam, hlam, rfl⟩ := hY
  have h := ypad_coneMap hx h0 h1 lam (k := (i : ℕ) + 1) (by omega)
  rw [ypad_succ_fin] at h
  rw [h]
  refine Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty
  rw [(xpad_mono hx h0 h1).map_min, xpad_succ_fin, xpad_succ_fin]
  refine mul_pos (div_pos (hlam j) ?_) ?_
  · rw [bbCov_diag]
    exact bbCov_diag_pos hx h0 h1 j
  · have hj0 := x_pos hx h0 j
    have hi0 := x_pos hx h0 i
    have hj1 := x_lt_one hx h1 j
    have hi1 := x_lt_one hx h1 i
    rcases le_total (x j) (x i) with hji | hji
    · rw [min_eq_left hji]
      nlinarith
    · rw [min_eq_right hji]
      nlinarith

/-- The points of `baseCfg (zip2 x Y)` are exactly the padded chain `P_0, …, P_{n+2}`. -/
theorem range_baseCfg_zip2 (x Y : Fin (n + 1) → ℝ) :
    range (baseCfg (zip2 x Y)) = (fun j : ℕ => (xpad x j, ypad Y j)) '' Iic (n + 2) := by
  rw [range_baseCfg]
  ext p
  simp only [mem_insert_iff, mem_range, zip2_apply, mem_image, mem_Iic]
  constructor
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨0, by omega, by simp [xpad, ypad]⟩
    · exact ⟨n + 2, le_rfl, by rw [xpad_last, ypad_last]⟩
    · exact ⟨i + 1, by omega, by rw [xpad_succ_fin, ypad_succ_fin]⟩
  · rintro ⟨j, hj, rfl⟩
    rcases j with _ | j
    · left
      simp [xpad, ypad]
    · by_cases hjn : j < n + 1
      · right; right
        exact ⟨⟨j, hjn⟩, by simp [xpad, ypad, xNat, hjn]⟩
      · obtain rfl : j = n + 1 := by omega
        right; left
        simp [xpad, ypad, xNat]

end KHoles
