/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.ChainSlopes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Area of the convex hull of an admissible chain

Step 5b of `doc/kholes/kholes.md` (area part). For sorted abscissae
`0 < x 0 < … < x n < 1` and admissible heights `Y`, the convex hull of the padded chain
`P_j = (xpad x j, ypad Y j)`, `j ≤ n + 2`, is the region
`R = {(t, y) | 0 ≤ t ≤ 1, 0 ≤ y, ∀ k ≤ n + 1, y ≤ ℓ_k t}` below all edge lines, and its area
is the trapezoid sum `areaUnder x Y`:

* `hullArea_eq_areaUnder`: `hullArea (baseCfg (zip2 x Y)) = ofReal (areaUnder x Y)`;
* `areaUnder_nonneg`.

The geometry is first done for an abstract padded chain `X Y : ℕ → ℝ` with `N` edges
(`ChainAreaHyp`: increasing abscissae from `0` to `1`, nonnegative heights vanishing at both
ends, every vertex below every edge line). The hull is identified with `chainAreaRegion`
(`ChainAreaHyp.convexHull_eq`); its volume is computed with `Measure.prod_apply`: the
vertical slice over `t ∈ (X k, X (k+1)]` is `[0, ℓ_k t]` (`ℓ_k` is the minimum of all edge
lines there), and the integral of `ℓ_k` over `[X k, X (k+1)]` is the trapezoid
(`ChainAreaHyp.volume_chainAreaRegion`). The weak discrete concavity `ypad_le_edge` and
`admissible_pos` from `ChainSlopes.lean` provide the hypotheses for the actual chain.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### An abstract padded chain -/

/-- The line through `(X k, Y k)` and `(X (k+1), Y (k+1))`. -/
noncomputable def chainAreaLine (X Y : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Y k + (Y (k + 1) - Y k) / (X (k + 1) - X k) * (t - X k)

/-- The region below all edge lines and above the `x`-axis, over `[0, 1]`. -/
def chainAreaRegion (X Y : ℕ → ℝ) (N : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ ∀ k < N, p.2 ≤ chainAreaLine X Y k p.1}

variable {X Y : ℕ → ℝ} {N : ℕ}

lemma chainAreaLine_left (k : ℕ) : chainAreaLine X Y k (X k) = Y k := by
  simp [chainAreaLine]

lemma chainAreaLine_right {k : ℕ} (h : X k < X (k + 1)) : chainAreaLine X Y k (X (k + 1)) = Y (k + 1) := by
  have h' : X (k + 1) - X k ≠ 0 := (sub_pos.mpr h).ne'
  rw [chainAreaLine, div_mul_cancel₀ _ h']
  ring

lemma chainAreaLine_interp (k k' : ℕ) (t : ℝ) :
    (X (k + 1) - X k) * chainAreaLine X Y k' t =
      (X (k + 1) - t) * chainAreaLine X Y k' (X k) + (t - X k) * chainAreaLine X Y k' (X (k + 1)) := by
  simp only [chainAreaLine]
  ring

lemma chainAreaLine_interp_self {k : ℕ} (h : X k < X (k + 1)) (t : ℝ) :
    (X (k + 1) - X k) * chainAreaLine X Y k t = (X (k + 1) - t) * Y k + (t - X k) * Y (k + 1) := by
  rw [chainAreaLine_interp k k t, chainAreaLine_left, chainAreaLine_right h]

lemma continuous_chainAreaLine (k : ℕ) : Continuous (chainAreaLine X Y k) := by
  unfold chainAreaLine
  fun_prop

lemma isClosed_chainAreaRegion : IsClosed (chainAreaRegion X Y N) := by
  have e : chainAreaRegion X Y N = {p : ℝ × ℝ | 0 ≤ p.1} ∩ ({p | p.1 ≤ 1} ∩ ({p | 0 ≤ p.2} ∩
      ⋂ k, ⋂ (_ : k < N), {p | p.2 ≤ chainAreaLine X Y k p.1})) := by
    ext p
    simp [chainAreaRegion]
  rw [e]
  refine (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_const continuous_snd).inter
    (isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le continuous_snd ((continuous_chainAreaLine k).comp continuous_fst))))

lemma convex_chainAreaRegion : Convex ℝ (chainAreaRegion X Y N) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  simp only [chainAreaRegion, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by nlinarith, by positivity, fun k hk => ?_⟩
  have hl : chainAreaLine X Y k (a * p.1 + b * q.1) =
      a * chainAreaLine X Y k p.1 + b * chainAreaLine X Y k q.1 := by
    simp only [chainAreaLine]
    rw [show b = 1 - a by linarith]
    ring
  rw [hl]
  exact add_le_add (mul_le_mul_of_nonneg_left (hp4 k hk) ha)
    (mul_le_mul_of_nonneg_left (hq4 k hk) hb)

/-- Hypotheses on the padded chain. -/
structure ChainAreaHyp (X Y : ℕ → ℝ) (N : ℕ) : Prop where
  pos : 0 < N
  mono : Monotone X
  lt : ∀ k < N, X k < X (k + 1)
  x0 : X 0 = 0
  xN : X N = 1
  y0 : Y 0 = 0
  yN : Y N = 0
  ynn : ∀ j ≤ N, 0 ≤ Y j
  dcf : ∀ j ≤ N, ∀ k < N, Y j ≤ chainAreaLine X Y k (X j)

namespace ChainAreaHyp

variable (h : ChainAreaHyp X Y N)
include h

lemma line_le {k k' : ℕ} (hk : k < N) (hk' : k' < N) {t : ℝ} (ht1 : X k ≤ t)
    (ht2 : t ≤ X (k + 1)) : chainAreaLine X Y k t ≤ chainAreaLine X Y k' t := by
  have hd := sub_pos.mpr (h.lt k hk)
  have e1 := chainAreaLine_interp (X := X) (Y := Y) k k' t
  have e2 := chainAreaLine_interp_self (Y := Y) (h.lt k hk) t
  have a1 := h.dcf k hk.le k' hk'
  have a2 := h.dcf (k + 1) hk k' hk'
  have m1 := mul_le_mul_of_nonneg_left a1 (sub_nonneg.mpr ht2)
  have m2 := mul_le_mul_of_nonneg_left a2 (sub_nonneg.mpr ht1)
  refine le_of_mul_le_mul_left ?_ hd
  linarith

lemma line_nonneg {k : ℕ} (hk : k < N) {t : ℝ} (ht1 : X k ≤ t) (ht2 : t ≤ X (k + 1)) :
    0 ≤ chainAreaLine X Y k t := by
  have hd := sub_pos.mpr (h.lt k hk)
  have e2 := chainAreaLine_interp_self (Y := Y) (h.lt k hk) t
  have m1 := mul_nonneg (sub_nonneg.mpr ht2) (h.ynn k hk.le)
  have m2 := mul_nonneg (sub_nonneg.mpr ht1) (h.ynn (k + 1) hk)
  refine nonneg_of_mul_nonneg_right ?_ hd
  linarith

lemma exists_piece {t : ℝ} (ht : t ≤ 1) :
    ∃ k < N, (X k < t ∨ k = 0) ∧ t ≤ X (k + 1) := by
  have hex : ∃ k, t ≤ X (k + 1) := ⟨N - 1, by rw [Nat.sub_add_cancel h.pos, h.xN]; exact ht⟩
  classical
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show t ≤ X (N - 1 + 1) by
      rw [Nat.sub_add_cancel h.pos, h.xN]; exact ht)
    have := h.pos
    omega
  · rcases hk : Nat.find hex with _ | k
    · exact Or.inr rfl
    · left
      have := Nat.find_min hex (show k < Nat.find hex by omega)
      exact lt_of_not_ge this

lemma x_nonneg (j : ℕ) : 0 ≤ X j := h.x0 ▸ h.mono (Nat.zero_le j)

lemma x_le_one {j : ℕ} (hj : j ≤ N) : X j ≤ 1 := h.xN ▸ h.mono hj

lemma convexHull_eq :
    convexHull ℝ ((fun j : ℕ => (X j, Y j)) '' Iic N) = chainAreaRegion X Y N := by
  apply Subset.antisymm
  · refine convexHull_min ?_ convex_chainAreaRegion
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨h.x_nonneg j, h.x_le_one hj, h.ynn j hj, fun k hk => h.dcf j hj k hk⟩
  · rintro ⟨t, y⟩ ⟨ht0, ht1, hy0, hy⟩
    have mem : ∀ j ≤ N, (X j, Y j) ∈ (fun j : ℕ => (X j, Y j)) '' Iic N :=
      fun j hj => ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hk1, hk2⟩ := h.exists_piece ht1
    have hk1' : X k ≤ t := by
      rcases hk1 with hk1 | rfl
      · exact hk1.le
      · rw [h.x0]; exact ht0
    have hd := sub_pos.mpr (h.lt k hk)
    set c := chainAreaLine X Y k t with hc
    have hA : (t, c) ∈ convexHull ℝ ((fun j : ℕ => (X j, Y j)) '' Iic N) := by
      refine segment_subset_convexHull (mem k hk.le) (mem (k + 1) hk) ?_
      refine ⟨(X (k + 1) - t) / (X (k + 1) - X k), (t - X k) / (X (k + 1) - X k),
        div_nonneg (sub_nonneg.mpr hk2) hd.le, div_nonneg (sub_nonneg.mpr hk1') hd.le, ?_, ?_⟩
      · field_simp
        ring
      · have e2 := chainAreaLine_interp_self (Y := Y) (h.lt k hk) t
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          field_simp
          ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          field_simp
          linarith
    have hB : (t, (0 : ℝ)) ∈ convexHull ℝ ((fun j : ℕ => (X j, Y j)) '' Iic N) := by
      refine segment_subset_convexHull (mem 0 (Nat.zero_le N)) (mem N le_rfl) ?_
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      ext
      · simp [h.x0, h.xN]
      · simp [h.y0, h.yN]
    have hc0 : 0 ≤ c := h.line_nonneg hk hk1' hk2
    have hyc : y ≤ c := hy k hk
    rcases hc0.eq_or_lt with hc0 | hc0
    · obtain rfl : y = 0 := le_antisymm (hc0 ▸ hyc) hy0
      exact hB
    · refine (convex_convexHull ℝ _).segment_subset hB hA ?_
      refine ⟨1 - y / c, y / c, by rw [sub_nonneg, div_le_one hc0]; exact hyc,
        div_nonneg hy0 hc0.le, by ring, ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp
        ring

lemma slice_eq {k : ℕ} (hk : k < N) {t : ℝ} (ht1 : X k < t) (ht2 : t ≤ X (k + 1)) :
    Prod.mk t ⁻¹' chainAreaRegion X Y N = Icc 0 (chainAreaLine X Y k t) := by
  ext y
  simp only [chainAreaRegion, mem_preimage, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨-, -, hy0, hy⟩
    exact ⟨hy0, hy k hk⟩
  · rintro ⟨hy0, hy⟩
    exact ⟨(h.x_nonneg k).trans ht1.le, ht2.trans (h.x_le_one hk), hy0,
      fun k' hk' => hy.trans (h.line_le hk hk' ht1.le ht2)⟩

lemma volume_slice_of_notMem {t : ℝ} (ht : t ∉ Ioc 0 1) :
    volume (Prod.mk t ⁻¹' chainAreaRegion X Y N) = 0 := by
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · have e : Prod.mk t ⁻¹' chainAreaRegion X Y N = ∅ := eq_empty_of_forall_notMem fun y hy =>
      absurd (show 0 ≤ t from hy.1) (not_le.2 ht0)
    rw [e, measure_empty]
  · refine measure_mono_null (t := {0}) ?_ (Real.volume_singleton)
    rintro y ⟨-, -, hy0, hy⟩
    have e := chainAreaLine_left (X := X) (Y := Y) 0
    rw [h.x0, h.y0] at e
    have := hy 0 h.pos
    simp only [e] at this
    exact le_antisymm this hy0
  · have h1 : 1 < t := by
      by_contra hc
      exact ht ⟨ht0, not_lt.mp hc⟩
    have e : Prod.mk t ⁻¹' chainAreaRegion X Y N = ∅ := eq_empty_of_forall_notMem fun y hy =>
      absurd (show t ≤ 1 from hy.2.1) (not_le.2 h1)
    rw [e, measure_empty]

lemma volume_slice (t : ℝ) :
    volume (Prod.mk t ⁻¹' chainAreaRegion X Y N) =
      ∑ k ∈ Finset.range N,
        (Ioc (X k) (X (k + 1))).indicator (fun t => ENNReal.ofReal (chainAreaLine X Y k t)) t := by
  by_cases ht : t ∈ Ioc 0 1
  · obtain ⟨k, hk, hk1, hk2⟩ := h.exists_piece ht.2
    have hk1' : X k < t := by
      rcases hk1 with hk1 | rfl
      · exact hk1
      · rw [h.x0]; exact ht.1
    rw [h.slice_eq hk hk1' hk2, Real.volume_Icc, sub_zero,
      Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk)]
    · rw [indicator_of_mem (show t ∈ Ioc (X k) (X (k + 1)) from ⟨hk1', hk2⟩)]
    · intro k' _ hne
      have hnot : t ∉ Ioc (X k') (X (k' + 1)) := by
        rintro ⟨a, b⟩
        rcases lt_or_gt_of_ne hne with hl | hl
        · linarith [h.mono (show k' + 1 ≤ k by omega)]
        · linarith [h.mono (show k + 1 ≤ k' by omega)]
      exact indicator_of_notMem hnot _
  · rw [h.volume_slice_of_notMem ht]
    symm
    refine Finset.sum_eq_zero fun k hk => indicator_of_notMem ?_ _
    rintro (⟨a, b⟩ : t ∈ Ioc (X k) (X (k + 1)))
    exact ht ⟨(h.x_nonneg k).trans_lt a, b.trans (h.x_le_one (Finset.mem_range.1 hk))⟩

lemma lintegral_piece {k : ℕ} (hk : k < N) :
    ∫⁻ t in Ioc (X k) (X (k + 1)), ENNReal.ofReal (chainAreaLine X Y k t) =
      ENNReal.ofReal ((X (k + 1) - X k) * (Y k + Y (k + 1)) / 2) := by
  have hlt := h.lt k hk
  have hd : X (k + 1) - X k ≠ 0 := (sub_pos.mpr hlt).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal (continuous_chainAreaLine k).integrableOn_Ioc
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => h.line_nonneg hk ht.1.le ht.2)]
  congr 1
  set s := (Y (k + 1) - Y k) / (X (k + 1) - X k) with hs
  rw [← intervalIntegral.integral_of_le hlt.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => Y k * (t - X k) + s / 2 * (t - X k) ^ 2) (fun t _ => ?_)
      ((continuous_chainAreaLine k).intervalIntegrable _ _)]
  · simp only [sub_self]
    rw [hs]
    field_simp
    ring
  · have := (((hasDerivAt_id t).sub_const (X k)).const_mul (Y k)).add
      ((((hasDerivAt_id t).sub_const (X k)).pow 2).const_mul (s / 2))
    convert this using 1
    · funext y
      simp only [Pi.add_apply, Pi.pow_apply, id]
    · simp only [chainAreaLine, id]
      rw [← hs]
      norm_num
      ring

/-- The area of the region below a concave chain is the trapezoid sum. -/
lemma volume_chainAreaRegion :
    volume (chainAreaRegion X Y N) =
      ENNReal.ofReal (∑ k ∈ Finset.range N, (X (k + 1) - X k) * (Y k + Y (k + 1)) / 2) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply isClosed_chainAreaRegion.measurableSet]
  simp_rw [h.volume_slice]
  rw [lintegral_finsetSum (f := fun k t =>
      (Ioc (X k) (X (k + 1))).indicator (fun t => ENNReal.ofReal (chainAreaLine X Y k t)) t) _
      fun k _ => (ENNReal.measurable_ofReal.comp (continuous_chainAreaLine k).measurable).indicator
        measurableSet_Ioc,
    ENNReal.ofReal_sum_of_nonneg fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [lintegral_indicator measurableSet_Ioc]
    exact h.lintegral_piece (Finset.mem_range.1 hk)
  · have hk' := Finset.mem_range.1 hk
    have := (h.lt k hk').le
    have := h.ynn k hk'.le
    have := h.ynn (k + 1) hk'
    have : 0 ≤ (X (k + 1) - X k) * (Y k + Y (k + 1)) := by nlinarith
    exact div_nonneg this zero_le_two

end ChainAreaHyp

/-! ### The admissible chain -/

variable {n : ℕ} {x Y : Fin (n + 1) → ℝ}

lemma ypad_nonneg (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) (j : ℕ) : 0 ≤ ypad Y j := by
  rcases j with _ | j
  · simp [ypad]
  · simp only [ypad, xNat]
    split_ifs with hj
    · exact (admissible_pos hx h0 h1 hY _).le
    · exact le_rfl

lemma chainAreaHyp_of_admissible (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) : ChainAreaHyp (xpad x) (ypad Y) (n + 2) where
  pos := by omega
  mono := xpad_mono hx h0 h1
  lt := fun _ hk => xpad_lt_succ hx h0 h1 hk
  x0 := rfl
  xN := xpad_last x
  y0 := rfl
  yN := ypad_last Y
  ynn := fun j _ => ypad_nonneg hx h0 h1 hY j
  dcf := fun _ hj _ hk => ypad_le_edge hx h0 h1 hY hj (by omega)

/-- The area of the convex hull of an admissible chain is the trapezoid sum under it. -/
theorem hullArea_eq_areaUnder {n : ℕ} {x Y : Fin (n + 1) → ℝ} (hx : StrictMono x)
    (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1) (hY : Y ∈ Admissible x) :
    hullArea (baseCfg (zip2 x Y)) = ENNReal.ofReal (areaUnder x Y) := by
  have h := chainAreaHyp_of_admissible hx h0 h1 hY
  rw [hullArea, range_baseCfg_zip2, h.convexHull_eq, h.volume_chainAreaRegion, areaUnder]

theorem areaUnder_nonneg {n : ℕ} {x Y : Fin (n + 1) → ℝ} (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) (hY : Y ∈ Admissible x) : 0 ≤ areaUnder x Y := by
  refine Finset.sum_nonneg fun k hk => ?_
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (xpad_mono hx h0 h1 (Nat.le_succ k)))
    (add_nonneg (ypad_nonneg hx h0 h1 hY k) (ypad_nonneg hx h0 h1 hY (k + 1)))) zero_le_two

end KHoles
