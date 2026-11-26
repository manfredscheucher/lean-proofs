/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Elementary limits and diameter inequalities (stage 4)

Auxiliary real-analysis facts and elementary properties of diameter pairs used in Steps 3,
4 and 6 of `doc/kholes/kholes.md`:

* `tendsto_one_sub_div_pow`: `(1 - B/n)^(n-k) → exp(-B)` in `ℝ≥0∞` (`B ≠ ⊤`);
* `one_sub_div_pow_le`: the uniform bound `(1 - B/n)^(n-k) ≤ exp(-B/2)` for `2k ≤ n`;
* `tendsto_choose_div_pow`: `choose n k / n^k → 1/k!`;
* `IsDiamLT.isDiamLE`, `fst_mem_Icc_of_isDiamLE`, `eventually_isDiamLT`,
  `isDiamLE_iff_of_sqDist`, `isDiamLT_iff_of_sqDist`: diameter pairs;
* `tendsto_pairEps_sq`: `pairEps p₁ p₂ n ^ 2 → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Real limits -/

/-- For `0 < n` and `B ≠ ⊤`: `1 - B/n = ofReal (1 - B.toReal/n)`. -/
lemma one_sub_div_eq_ofReal {B : ℝ≥0∞} (hB : B ≠ ⊤) {n : ℕ} (hn : 0 < n) :
    1 - B / n = ENNReal.ofReal (1 - B.toReal / n) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [ENNReal.ofReal_sub _ (div_nonneg ENNReal.toReal_nonneg hnr.le), ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos hnr, ENNReal.ofReal_toReal hB, ENNReal.ofReal_natCast]

/-- The real version: `(1 - b/n)^(n-k) → exp(-b)`. -/
lemma tendsto_one_sub_div_pow_real (b : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (1 - b / n) ^ (n - k)) atTop (𝓝 (Real.exp (-b))) := by
  have h1 : Tendsto (fun n : ℕ => (1 - b / n) ^ n) atTop (𝓝 (Real.exp (-b))) := by
    convert Real.tendsto_one_add_div_pow_exp (-b) using 2 with n
    ring
  have h0 : Tendsto (fun n : ℕ => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat b
  have h2 : Tendsto (fun n : ℕ => (1 - b / n) ^ k) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).pow k
    simpa using this
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  have hlt : ∀ᶠ n : ℕ in atTop, b / (n : ℝ) < 1 := h0.eventually_lt_const one_pos
  filter_upwards [hlt, eventually_ge_atTop k] with n hn hkn
  have hne : (1 - b / n) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  simp only [Pi.div_apply]
  rw [div_eq_iff hne, ← pow_add, Nat.sub_add_cancel hkn]

theorem tendsto_one_sub_div_pow (B : ℝ≥0∞) (hB : B ≠ ⊤) (k : ℕ) :
    Tendsto (fun n : ℕ => (1 - B / n) ^ (n - k)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-B.toReal)))) := by
  have h := ENNReal.tendsto_ofReal (tendsto_one_sub_div_pow_real B.toReal k)
  refine h.congr' ?_
  have h0 : Tendsto (fun n : ℕ => B.toReal / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [h0.eventually_lt_const one_pos, eventually_ge_atTop 1] with n hn hn1
  rw [one_sub_div_eq_ofReal hB hn1, ENNReal.ofReal_pow (by linarith)]

theorem one_sub_div_pow_le (B : ℝ≥0∞) {n k : ℕ} (hn0 : 0 < n) (hn : 2 * k ≤ n) :
    (1 - B / n) ^ (n - k) ≤ ENNReal.ofReal (Real.exp (-B.toReal / 2)) := by
  by_cases hB : B = ⊤
  · subst hB
    have hk : 0 < n - k := by omega
    rw [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n), tsub_eq_zero_of_le le_top,
      zero_pow hk.ne']
    exact zero_le
  set b := B.toReal with hb
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hstep : 1 - B / n ≤ ENNReal.ofReal (Real.exp (-b / n)) := by
    rw [one_sub_div_eq_ofReal hB hn0]
    apply ENNReal.ofReal_le_ofReal
    have := Real.add_one_le_exp (-b / n)
    rw [neg_div] at this ⊢
    linarith
  calc (1 - B / n) ^ (n - k) ≤ ENNReal.ofReal (Real.exp (-b / n)) ^ (n - k) :=
        pow_le_pow_left₀ zero_le hstep _
    _ = ENNReal.ofReal (Real.exp ((n - k : ℕ) * (-b / n))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, Real.exp_nat_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-b / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have hc : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          have : (2 * k : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hkey : b / 2 ≤ ((n - k : ℕ) : ℝ) * b / n := by
          rw [le_div_iff₀ hnr]
          nlinarith
        have : ((n - k : ℕ) : ℝ) * (-b / n) = -(((n - k : ℕ) : ℝ) * b / n) := by ring
        rw [this, neg_div]
        linarith

theorem tendsto_choose_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  have h := (isEquivalent_choose k).div
    (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ) ^ k) (l := atTop))
  refine (h.tendsto_nhds_iff).2 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  simp only [Pi.div_apply]
  field_simp

/-! ### Diameter pairs -/

theorem IsDiamLT.isDiamLE {k : ℕ} {c : ℝ} (hc : 0 ≤ c) {q : Fin k → ℝ × ℝ} {i j : Fin k}
    (_hij : i ≠ j) (h : IsDiamLT c q i j) : IsDiamLE c q i j := by
  intro a b
  by_cases hab : a = b
  · subst hab
    rw [sqDist_self]
    exact sqDist_nonneg hc _ _
  by_cases h1 : (a, b) = (i, j)
  · simp only [Prod.mk.injEq] at h1
    rw [h1.1, h1.2]
  by_cases h2 : (a, b) = (j, i)
  · simp only [Prod.mk.injEq] at h2
    rw [h2.1, h2.2, sqDist_comm]
  exact (h a b hab h1 h2).le

theorem fst_mem_Icc_of_isDiamLE {m : ℕ} {c : ℝ} (hc : 0 ≤ c) {z : Fin m → ℝ × ℝ}
    (h : IsDiamLE c (baseCfg z) 0 1) (i : Fin m) : 0 ≤ (z i).1 ∧ (z i).1 ≤ 1 := by
  have h0 := h i.succ.succ 0
  have h1 := h i.succ.succ 1
  simp only [baseCfg_succ_succ, baseCfg_zero, baseCfg_one, sqDist] at h0 h1
  have hy : 0 ≤ c * ((z i).2 - 0) ^ 2 := by positivity
  constructor <;> nlinarith

/-- Every index of `Fin (m + 2)` is `0`, `1` or `i.succ.succ`. -/
lemma fin_cases_two {m : ℕ} (a : Fin (m + 2)) : a = 0 ∨ a = 1 ∨ ∃ i : Fin m, a = i.succ.succ := by
  refine Fin.cases (Or.inl rfl) (fun a' => ?_) a
  refine Fin.cases (Or.inr (Or.inl rfl)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) a'

/-- Horizontal distances in `baseCfg z` other than the base pair are `< 1`. -/
lemma fst_sub_sq_lt_one {m : ℕ} {z : Fin m → ℝ × ℝ} (hz : ∀ i, 0 < (z i).1 ∧ (z i).1 < 1)
    {a b : Fin (m + 2)} (hab : a ≠ b) (h1 : (a, b) ≠ (0, 1)) (h2 : (a, b) ≠ (1, 0)) :
    ((baseCfg z a).1 - (baseCfg z b).1) ^ 2 < 1 := by
  rcases fin_cases_two a with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases fin_cases_two b with rfl | rfl | ⟨j, rfl⟩
  all_goals first
    | exact absurd rfl hab
    | exact absurd rfl h1
    | exact absurd rfl h2
    | skip
  all_goals simp only [baseCfg_zero, baseCfg_one, baseCfg_succ_succ]
  · have := hz j; nlinarith
  · have := hz j; nlinarith
  · have := hz i; nlinarith
  · have := hz i; nlinarith
  · have := hz i; have := hz j; nlinarith

theorem eventually_isDiamLT {m : ℕ} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    {z : Fin m → ℝ × ℝ} (hz : ∀ i, 0 < (z i).1 ∧ (z i).1 < 1) :
    ∀ᶠ n in atTop, IsDiamLT (c n) (baseCfg z) 0 1 := by
  have hpair : ∀ a b : Fin (m + 2), ∀ᶠ n in atTop, a ≠ b → (a, b) ≠ (0, 1) →
      (a, b) ≠ (1, 0) → sqDist (c n) (baseCfg z a) (baseCfg z b) < 1 := by
    intro a b
    by_cases hcond : a ≠ b ∧ (a, b) ≠ (0, 1) ∧ (a, b) ≠ (1, 0)
    · have hlt := fst_sub_sq_lt_one hz hcond.1 hcond.2.1 hcond.2.2
      have ht : Tendsto (fun n => sqDist (c n) (baseCfg z a) (baseCfg z b)) atTop
          (𝓝 (((baseCfg z a).1 - (baseCfg z b).1) ^ 2 +
            0 * ((baseCfg z a).2 - (baseCfg z b).2) ^ 2)) :=
        tendsto_const_nhds.add (hc.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at ht
      filter_upwards [ht.eventually_lt_const hlt] with n hn _ _ _ using hn
    · refine Eventually.of_forall fun n h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond
  filter_upwards [eventually_all.2 fun a => eventually_all.2 fun b => hpair a b] with n hn
  intro a b hab h1 h2
  have : sqDist (c n) (baseCfg z 0) (baseCfg z 1) = 1 := by simp [sqDist]
  rw [this]
  exact hn a b hab h1 h2

theorem isDiamLE_iff_of_sqDist {k : ℕ} {c c' s : ℝ} (hs : 0 < s) {q q' : Fin k → ℝ × ℝ}
    (h : ∀ a b, sqDist c (q a) (q b) = s * sqDist c' (q' a) (q' b)) (i j : Fin k) :
    IsDiamLE c q i j ↔ IsDiamLE c' q' i j := by
  simp only [IsDiamLE, h, mul_le_mul_iff_right₀ hs]

theorem isDiamLT_iff_of_sqDist {k : ℕ} {c c' s : ℝ} (hs : 0 < s) {q q' : Fin k → ℝ × ℝ}
    (h : ∀ a b, sqDist c (q a) (q b) = s * sqDist c' (q' a) (q' b)) (i j : Fin k) :
    IsDiamLT c q i j ↔ IsDiamLT c' q' i j := by
  simp only [IsDiamLT, h, mul_lt_mul_iff_right₀ hs]

theorem tendsto_pairEps_sq (p₁ p₂ : ℝ × ℝ) :
    Tendsto (fun n : ℕ => pairEps p₁ p₂ n ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (sqDist 1 p₁ p₂)⁻¹ * ((n : ℝ))⁻¹) atTop
      (𝓝 ((sqDist 1 p₁ p₂)⁻¹ * 0)) :=
    tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mul_zero] at h
  have h2 := h.pow 2
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun n => ?_
  rw [pairEps, one_div, mul_inv, mul_comm]

end KHoles
