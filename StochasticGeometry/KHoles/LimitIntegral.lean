/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapSplit
import KHoles.PiLinear
import KHoles.ConvexInvariance
import KHoles.Symmetrize
import KHoles.HullMeasurable
import KHoles.UpperCap
import KHoles.Main
import Mathlib.Data.Nat.Choose.Sum

/-!
# Step 5d: the limit integral `limInt m = m! · 2 · C (m+2)`

Step 5d of `doc/kholes/kholes.md`. The limit integral
`limInt m = ∫_{limSet m} exp(-area conv(baseCfg z)) dz` splits into upper and lower caps:

* `limInt_eq_sum`: `limInt m = Σ_j choose(m, j) · upperInt j · upperInt (m - j)`;
* `limInt_eq`: `limInt m = ofReal (m! · (2 · C (m+2)))`;
* `limInt_ne_top`, `limInt_toReal`.

Proof of `limInt_eq_sum`: a.e. no point lies on the base line (`ae_snd_ne`), so the integrand
is the sum over `M : Finset (Fin m)` of the integrand restricted to the sign pattern
"`(z i).2 > 0` iff `i ∈ M`". For fixed `M` with `#M = j`, an equivalence
`Fin j ⊕ Fin (m - j) ≃ Fin m` (points of `M` first) and `sumPiEquivProdPi` split the
coordinates into the upper points `u` and the lower points `l` (measure preserving). By
CapSplit (`convexIndependent_baseCfg_split`, `hullArea_baseCfg_split`) the integrand is the
product of the upper-cap integrand of `u` and that of the reflected `vscale (-1) l`; Tonelli
(`lintegral_prod_mul`) and the reflection (`lintegral_comp_vscale`) give
`upperInt j · upperInt (m - j)`. Grouping the sets `M` by cardinality
(`Finset.sum_powerset_apply_card`) gives the binomial sum.

`limInt_eq` then follows from `upperInt_eq` (`upperInt j = j! · a j`, UpperCap), `choose(m,j)
j! (m-j)! = m!` and `Σ_j a j · a (m - j) = 2 · Cconv (m+2) = 2 · C (m+2)` (`Cconv_eq_C_all`).
Sanity: `limInt 0 = 1`, `limInt 1 = 4`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Splitting the limit integral by the sign pattern -/

/-- The weight `exp(-area)` of the configuration `baseCfg z`. -/
private noncomputable def expW {m : ℕ} (z : Fin m → ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal))

private lemma measurable_expW (m : ℕ) :
    Measurable (expW : (Fin m → ℝ × ℝ) → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (measurable_hullArea_baseCfg m).ennreal_toReal.neg)

/-- Sign pattern: the points indexed by `M` are above the base, the others below. -/
private def sgnPat {m : ℕ} (M : Finset (Fin m)) : Set (Fin m → ℝ × ℝ) :=
  {z | ∀ i, (i ∈ M → 0 < (z i).2) ∧ (i ∉ M → (z i).2 < 0)}

private lemma measurableSet_sgnPat {m : ℕ} (M : Finset (Fin m)) : MeasurableSet (sgnPat M) := by
  have : sgnPat M =
      ⋂ i, {z : Fin m → ℝ × ℝ | (i ∈ M → 0 < (z i).2) ∧ (i ∉ M → (z i).2 < 0)} := by
    ext z; simp [sgnPat]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun z : Fin m → ℝ × ℝ => (z i).2 :=
    measurable_snd.comp (measurable_pi_apply i)
  by_cases hi : i ∈ M
  · simpa [hi] using measurableSet_lt measurable_const hm
  · simpa [hi] using measurableSet_lt hm measurable_const

private lemma limInt_eq_sum_pat (m : ℕ) :
    limInt m = ∑ M : Finset (Fin m), ∫⁻ z, (limSet m ∩ sgnPat M).indicator expW z := by
  classical
  rw [limInt, ← lintegral_indicator (measurableSet_limSet m),
    ← lintegral_finsetSum _ fun M _ =>
      (measurable_expW m).indicator ((measurableSet_limSet m).inter (measurableSet_sgnPat M))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_snd_ne m 0] with z hz
  set M0 := Finset.univ.filter fun i => 0 < (z i).2 with hM0
  have hM : ∀ M, z ∈ sgnPat M ↔ M = M0 := by
    intro M
    constructor
    · intro h
      ext i
      by_cases hi : i ∈ M
      · simp [hM0, hi, (h i).1 hi]
      · simp [hM0, hi, ((h i).2 hi).le]
    · rintro rfl i
      refine ⟨fun hi => by simpa [hM0] using hi, fun hi => ?_⟩
      simp only [hM0, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact lt_of_le_of_ne hi (hz i)
  have hterm : ∀ M, (limSet m ∩ sgnPat M).indicator expW z =
      if M = M0 then (limSet m).indicator expW z else 0 := by
    intro M
    by_cases h : M = M0
    · simp [indicator, mem_inter_iff, hM, h]
    · simp [indicator, mem_inter_iff, hM, h]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ M0, if_pos (Finset.mem_univ _)]
  rfl

private lemma forall_sum_split {m na nb : ℕ} (e : Fin na ⊕ Fin nb ≃ Fin m)
    (P : Fin m → Prop) :
    (∀ i, P i) ↔ (∀ i, P (e (.inl i))) ∧ (∀ i, P (e (.inr i))) := by
  exact ⟨fun h => (Sum.forall (p := fun s => P (e s))).1 fun s => h _,
    fun h i => by simpa using (Sum.forall (p := fun s => P (e s))).2 h (e.symm i)⟩

/-- Pointwise factorisation of the integrand for a fixed sign pattern. -/
private lemma indicator_pat_eq {m na nb : ℕ} (M : Finset (Fin m))
    (e : Fin na ⊕ Fin nb ≃ Fin m) (heu : ∀ i, e (.inl i) ∈ M) (hel : ∀ i, e (.inr i) ∉ M)
    (z : Fin m → ℝ × ℝ) (u : Fin na → ℝ × ℝ) (l : Fin nb → ℝ × ℝ) (hzu : ∀ i, z (e (.inl i)) = u i)
    (hzl : ∀ i, z (e (.inr i)) = l i) :
    (limSet m ∩ sgnPat M).indicator expW z =
      (upperSet na).indicator expW u * (upperSet nb).indicator expW (vscale (-1) l) := by
  have hm : m = na + nb := by simpa using (Fintype.card_congr e).symm
  have hz : range z = range u ∪ range l := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨s, rfl⟩ := e.surjective i
      rcases s with s | s
      · exact Or.inl ⟨s, (hzu s).symm⟩
      · exact Or.inr ⟨s, (hzl s).symm⟩
    · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
      · exact ⟨_, hzu s⟩
      · exact ⟨_, hzl s⟩
  have hpat : z ∈ sgnPat M ↔ (∀ i, 0 < (u i).2) ∧ (∀ i, (l i).2 < 0) := by
    simp only [sgnPat, mem_ofPred_eq]
    rw [forall_sum_split e]
    simp [heu, hel, hzu, hzl]
  have hx : (∀ i, 0 < (z i).1 ∧ (z i).1 < 1) ↔
      (∀ i, 0 < (u i).1 ∧ (u i).1 < 1) ∧ (∀ i, 0 < (l i).1 ∧ (l i).1 < 1) := by
    rw [forall_sum_split e]
    simp [hzu, hzl]
  have hci_l :
      ConvexIndependent ℝ (baseCfg (vscale (-1) l)) ↔ ConvexIndependent ℝ (baseCfg l) :=
    convexIndependent_baseCfg_vscale (by norm_num) l
  by_cases hP : (∀ i, 0 < (u i).2) ∧ (∀ i, (l i).2 < 0)
  · by_cases hX : (∀ i, 0 < (u i).1 ∧ (u i).1 < 1) ∧ (∀ i, 0 < (l i).1 ∧ (l i).1 < 1)
    · have hu : ∀ i, 0 < (u i).1 ∧ (u i).1 < 1 ∧ 0 < (u i).2 :=
        fun i => ⟨(hX.1 i).1, (hX.1 i).2, hP.1 i⟩
      have hl : ∀ i, 0 < (l i).1 ∧ (l i).1 < 1 ∧ (l i).2 < 0 :=
        fun i => ⟨(hX.2 i).1, (hX.2 i).2, hP.2 i⟩
      have hci := convexIndependent_baseCfg_split z u l hm hz hu hl
      by_cases hc : ConvexIndependent ℝ (baseCfg u) ∧ ConvexIndependent ℝ (baseCfg l)
      · have hzm : z ∈ limSet m ∩ sgnPat M := ⟨⟨hci.2 hc, hx.2 hX⟩, hpat.2 hP⟩
        have hum : u ∈ upperSet na := ⟨hc.1, hu⟩
        have hlm : vscale (-1) l ∈ upperSet nb :=
          ⟨hci_l.2 hc.2, fun i => ⟨(hl i).1, (hl i).2.1, by simpa using (hl i).2.2⟩⟩
        rw [indicator_of_mem hzm, indicator_of_mem hum, indicator_of_mem hlm, expW, expW, expW,
          hullArea_baseCfg_split z u l hz hu hl, hullArea_baseCfg_vscale]
        rw [ENNReal.toReal_add (hullArea_lt_top _).ne (hullArea_lt_top _).ne]
        simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul, neg_add, Real.exp_add]
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      · have hzm : z ∉ limSet m ∩ sgnPat M := fun h => hc (hci.1 h.1.1)
        rw [indicator_of_notMem hzm]
        by_cases hcu : ConvexIndependent ℝ (baseCfg u)
        · have hlm : vscale (-1) l ∉ upperSet nb := fun h => hc ⟨hcu, hci_l.1 h.1⟩
          rw [indicator_of_notMem hlm, mul_zero]
        · have hum : u ∉ upperSet na := fun h => hcu h.1
          rw [indicator_of_notMem hum, zero_mul]
    · have hzm : z ∉ limSet m ∩ sgnPat M := fun h => hX (hx.1 h.1.2)
      rw [indicator_of_notMem hzm]
      by_cases hXu : ∀ i, 0 < (u i).1 ∧ (u i).1 < 1
      · have hlm : vscale (-1) l ∉ upperSet nb := fun h =>
          hX ⟨hXu, fun i => ⟨(h.2 i).1, by simpa using (h.2 i).2.1⟩⟩
        rw [indicator_of_notMem hlm, mul_zero]
      · have hum : u ∉ upperSet na := fun h => hXu fun i => ⟨(h.2 i).1, (h.2 i).2.1⟩
        rw [indicator_of_notMem hum, zero_mul]
  · have hzm : z ∉ limSet m ∩ sgnPat M := fun h => hP (hpat.1 h.2)
    rw [indicator_of_notMem hzm]
    by_cases hPu : ∀ i, 0 < (u i).2
    · have hlm : vscale (-1) l ∉ upperSet nb := fun h =>
        hP ⟨hPu, fun i => by simpa using (h.2 i).2.2⟩
      rw [indicator_of_notMem hlm, mul_zero]
    · have hum : u ∉ upperSet na := fun h => hPu fun i => (h.2 i).2.2
      rw [indicator_of_notMem hum, zero_mul]


private lemma measurable_vscale (k : ℕ) (s : ℝ) :
    Measurable (vscale s : (Fin k → ℝ × ℝ) → Fin k → ℝ × ℝ) :=
  measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i).fst.prodMk (measurable_const.mul (measurable_pi_apply i).snd)

private lemma lintegral_pat {m na nb : ℕ} (M : Finset (Fin m)) (e : Fin na ⊕ Fin nb ≃ Fin m)
    (heu : ∀ i, e (.inl i) ∈ M) (hel : ∀ i, e (.inr i) ∉ M) :
    ∫⁻ z, (limSet m ∩ sgnPat M).indicator expW z = upperInt na * upperInt nb := by
  let Φ := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin na ⊕ Fin nb => ℝ × ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ × ℝ) e)
  have hΦ : MeasurePreserving Φ ((volume : Measure (Fin na → ℝ × ℝ)).prod
      (volume : Measure (Fin nb → ℝ × ℝ))) volume :=
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin na ⊕ Fin nb => (volume : Measure (ℝ × ℝ)))).trans
      (measurePreserving_piCongrLeft (fun _ : Fin m => (volume : Measure (ℝ × ℝ))) e)
  have hΦu : ∀ p i, Φ p (e (.inl i)) = p.1 i := by
    intro p i
    simp [Φ, MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  have hΦl : ∀ p i, Φ p (e (.inr i)) = p.2 i := by
    intro p i
    simp [Φ, MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  rw [← hΦ.lintegral_comp_emb Φ.measurableEmbedding]
  simp_rw [fun p => indicator_pat_eq M e heu hel (Φ p) p.1 p.2 (hΦu p) (hΦl p)]
  have hmeas :
      ∀ k, Measurable ((upperSet k).indicator (expW : (Fin k → ℝ × ℝ) → ℝ≥0∞)) :=
    fun k => (measurable_expW k).indicator (measurableSet_upperSet k)
  rw [lintegral_prod_mul (f := (upperSet na).indicator expW)
    (g := fun l => (upperSet nb).indicator expW (vscale (-1) l)) (hmeas na).aemeasurable
    ((hmeas nb).comp (measurable_vscale nb (-1))).aemeasurable,
    lintegral_comp_vscale nb (by norm_num : (-1 : ℝ) ≠ 0) ((upperSet nb).indicator expW)]
  simp only [inv_neg, inv_one, abs_neg, abs_one, ENNReal.ofReal_one, one_pow, one_mul]
  rw [lintegral_indicator (measurableSet_upperSet na),
    lintegral_indicator (measurableSet_upperSet nb)]
  rfl

private lemma lintegral_pat_card {m : ℕ} (M : Finset (Fin m)) :
    ∫⁻ z, (limSet m ∩ sgnPat M).indicator expW z =
      upperInt M.card * upperInt (m - M.card) := by
  classical
  have hc : Fintype.card {i // i ∉ M} = m - M.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  let fM : Fin M.card ≃ {i // i ∈ M} := (M.equivFin).symm
  let fMc : Fin (m - M.card) ≃ {i // i ∉ M} := (Fintype.equivFinOfCardEq hc).symm
  let e : Fin M.card ⊕ Fin (m - M.card) ≃ Fin m :=
    (Equiv.sumCongr fM fMc).trans (Equiv.sumCompl (· ∈ M))
  exact lintegral_pat M e (fun i => by simp [e]) (fun i => by simpa [e] using (fMc i).2)

theorem limInt_eq_sum (m : ℕ) :
    limInt m = ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ≥0∞) * (upperInt j * upperInt (m - j)) := by
  rw [limInt_eq_sum_pat]
  simp_rw [lintegral_pat_card]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
    (fun j => upperInt j * upperInt (m - j)), Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]


/-! ### Closed form -/

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  rw [a_eq_capIntegral]
  split_ifs
  · exact zero_le_one
  · exact ENNReal.toReal_nonneg

lemma sum_a_mul_a (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), a j * a (m - j) = 2 * C (m + 2) := by
  rw [← Cconv_eq_C_all, Cconv, show m + 2 - 1 = m + 1 by omega, ← mul_assoc]
  norm_num

lemma C_add_two_nonneg (m : ℕ) : 0 ≤ C (m + 2) := by
  have h := sum_a_mul_a m
  have : 0 ≤ ∑ j ∈ Finset.range (m + 1), a j * a (m - j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (a_nonneg j) (a_nonneg (m - j))
  linarith

theorem limInt_eq (m : ℕ) : limInt m = ENNReal.ofReal (m.factorial * (2 * C (m + 2))) := by
  rw [limInt_eq_sum, ← sum_a_mul_a, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (a_nonneg j) (a_nonneg (m - j)))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hreal : (m.factorial : ℝ) * (a j * a (m - j)) =
      (m.choose j : ℝ) * (((j.factorial : ℝ) * a j) * ((m - j).factorial * a (m - j))) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hjm]
    push_cast
    ring
  rw [hreal, upperInt_eq, upperInt_eq,
    ENNReal.ofReal_mul (Nat.cast_nonneg _ : (0 : ℝ) ≤ m.choose j),
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (a_nonneg j)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _ : (0 : ℝ) ≤ j.factorial),
    ENNReal.ofReal_mul (Nat.cast_nonneg _ : (0 : ℝ) ≤ (m - j).factorial)]
  simp only [ENNReal.ofReal_natCast]

theorem limInt_ne_top (m : ℕ) : limInt m ≠ ⊤ := by
  rw [limInt_eq]
  exact ENNReal.ofReal_ne_top

theorem limInt_toReal (m : ℕ) : (limInt m).toReal = m.factorial * (2 * C (m + 2)) := by
  rw [limInt_eq, ENNReal.toReal_ofReal]
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two (C_add_two_nonneg m))

end KHoles
