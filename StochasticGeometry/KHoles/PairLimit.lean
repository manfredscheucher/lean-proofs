/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.Elementary
import KHoles.PiLinear
import KHoles.Symmetrize
import KHoles.HullMeasurable
import KHoles.ConvexInvariance
import KHoles.PairScaling
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The limit of the diameter probabilities (stage 4, Step 4b)

Step 4b of `doc/kholes/kholes.md`: for `k = m + 2` points,
`n^m · diamProb K m (D 1) (n - k) → limInt m`, for the weak and the strict diameter event.

* `lintegral_limSet_exp_half`: `∫_{limSet} exp(-B/2) = 2^m · limInt m` (vertical scaling by 2);
  this is the integral of the dominating function of the inner dominated convergence.
* Inner dominated convergence (fixed `p₁ ≠ p₂` in `interior K`, integrating over the scaled
  coordinates `z`): `∫ scaledIntegrand → limInt m`.
* Outer dominated convergence over `μ_K ⊗ μ_K` with the constant bound `2^m · limInt m`
  (the frontier of a convex set and the diagonal are null).
* `tendsto_diamProb` (abstract diameter event), `tendsto_diamProb_le`, `tendsto_diamProb_lt`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### The dominating integral -/

theorem lintegral_limSet_exp_half (m : ℕ) :
    ∫⁻ z in limSet m, ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal / 2)) =
      2 ^ m * limInt m := by
  set f : (Fin m → ℝ × ℝ) → ℝ≥0∞ := (limSet m).indicator
    (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal / 2))) with hf
  have hcomp : ∀ w, f (vscale 2 w) = (limSet m).indicator
      (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal))) w := by
    intro w
    have hmem : vscale 2 w ∈ limSet m ↔ w ∈ limSet m := by
      simp only [limSet, mem_ofPred_eq, convexIndependent_baseCfg_vscale two_ne_zero,
        vscale_apply]
    by_cases hw : w ∈ limSet m
    · rw [hf, indicator_of_mem (hmem.2 hw), indicator_of_mem hw, hullArea_baseCfg_vscale,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_two]
      congr 2
      ring
    · rw [hf, indicator_of_notMem (mt hmem.1 hw), indicator_of_notMem hw]
  have h := lintegral_comp_vscale m two_ne_zero f
  simp only [hcomp] at h
  rw [limInt, ← lintegral_indicator (measurableSet_limSet m),
    ← lintegral_indicator (measurableSet_limSet m), ← hf, h, ← mul_assoc, ← mul_pow,
    abs_inv, abs_two, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-! ### The inner integrand -/

lemma tendsto_pairEps (p₁ p₂ : ℝ × ℝ) :
    Tendsto (fun n : ℕ => pairEps p₁ p₂ n) atTop (𝓝 0) := by
  refine (tendsto_const_div_atTop_nhds_zero_nat (1 / sqDist 1 p₁ p₂)).congr fun n => ?_
  show 1 / sqDist 1 p₁ p₂ / (n : ℝ) = 1 / ((n : ℝ) * sqDist 1 p₁ p₂)
  rw [div_div, mul_comm]

lemma measurable_scaledIntegrand (K : Set (ℝ × ℝ)) (hKm : MeasurableSet K) {m : ℕ}
    (D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop) (hDm : ∀ c, MeasurableSet {q | D c q})
    (p₁ p₂ : ℝ × ℝ) (n N : ℕ) : Measurable (scaledIntegrand K D p₁ p₂ n N) := by
  unfold scaledIntegrand
  refine Measurable.indicator ?_ ?_
  · exact (((measurable_hullArea_baseCfg m).div_const _).const_sub 1).pow_const N
  · have hc : Continuous fun w : ℝ × ℝ => pairMap p₁ p₂ (pairEps p₁ p₂ n) w := by
      unfold pairMap perp
      fun_prop
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · have : {z : Fin m → ℝ × ℝ | ∀ i, pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i) ∈ K} =
          ⋂ i, (fun z : Fin m → ℝ × ℝ => pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i)) ⁻¹' K := by
        ext z; simp
      have h : MeasurableSet (⋂ i, (fun z : Fin m → ℝ × ℝ =>
          pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i)) ⁻¹' K) :=
        MeasurableSet.iInter fun i => hKm.preimage (hc.measurable.comp (measurable_pi_apply i))
      rw [← this] at h
      exact h
    · exact (continuous_baseCfg m).measurable (measurableSet_ciSet _)
    · exact (continuous_baseCfg m).measurable (hDm _)

/-- Off the null set `{∃ i, (z i).1 ∈ {0, 1}}`, the diameter event forces `z ∈ limSet m`. -/
lemma mem_limSet_of_D {m : ℕ} {D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop}
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    {c : ℝ} (hc : 0 ≤ c) {z : Fin m → ℝ × ℝ} (h0 : ∀ i, (z i).1 ≠ 0) (h1 : ∀ i, (z i).1 ≠ 1)
    (hci : baseCfg z ∈ ciSet (Fin (m + 2))) (hDz : D c (baseCfg z)) : z ∈ limSet m := by
  refine ⟨hci, fun i => ?_⟩
  have := fst_mem_Icc_of_isDiamLE hc (hD_le c hc z hDz) i
  exact ⟨lt_of_le_of_ne this.1 (h0 i).symm, lt_of_le_of_ne this.2 (h1 i)⟩

lemma scaledIntegrand_le {K : Set (ℝ × ℝ)} {m : ℕ} {D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop}
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    (p₁ p₂ : ℝ × ℝ) {n : ℕ} (hn0 : 0 < n) (hn : 2 * (m + 2) ≤ n) {z : Fin m → ℝ × ℝ}
    (h0 : ∀ i, (z i).1 ≠ 0) (h1 : ∀ i, (z i).1 ≠ 1) :
    scaledIntegrand K D p₁ p₂ n (n - (m + 2)) z ≤ (limSet m).indicator
      (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal / 2))) z := by
  unfold scaledIntegrand
  by_cases hz : z ∈ {z : Fin m → ℝ × ℝ | (∀ i, pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i) ∈ K) ∧
      baseCfg z ∈ ciSet (Fin (m + 2)) ∧ D (pairEps p₁ p₂ n ^ 2) (baseCfg z)}
  · rw [indicator_of_mem hz,
      indicator_of_mem (mem_limSet_of_D hD_le (sq_nonneg _) h0 h1 hz.2.1 hz.2.2)]
    exact one_sub_div_pow_le _ hn0 hn
  · rw [indicator_of_notMem hz]
    exact zero_le

lemma tendsto_scaledIntegrand {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {m : ℕ}
    {D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop}
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    (hD_ev : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → Tendsto c atTop (𝓝 0) → ∀ z : Fin m → ℝ × ℝ,
      (∀ i, 0 < (z i).1 ∧ (z i).1 < 1) → ∀ᶠ n in atTop, D (c n) (baseCfg z))
    {p₁ p₂ : ℝ × ℝ} (hp₁ : p₁ ∈ interior K) (hp₂ : p₂ ∈ interior K) {z : Fin m → ℝ × ℝ}
    (h0 : ∀ i, (z i).1 ≠ 0) (h1 : ∀ i, (z i).1 ≠ 1) :
    Tendsto (fun n : ℕ => scaledIntegrand K D p₁ p₂ n (n - (m + 2)) z) atTop
      (𝓝 ((limSet m).indicator
        (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal))) z)) := by
  by_cases hz : z ∈ limSet m
  · rw [indicator_of_mem hz]
    have hK' : ∀ᶠ n : ℕ in atTop, ∀ i, pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i) ∈ K := by
      rw [eventually_all]
      intro i
      have hseg : pairMap p₁ p₂ 0 (z i) ∈ interior K := by
        have : pairMap p₁ p₂ 0 (z i) = (1 - (z i).1) • p₁ + (z i).1 • p₂ := by
          simp only [pairMap, zero_mul, zero_smul, add_zero, smul_sub, sub_smul, one_smul]
          abel
        rw [this]
        exact hK.interior hp₁ hp₂ (by linarith [(hz.2 i).2]) (hz.2 i).1.le (by ring)
      have hc : Continuous fun ε : ℝ => pairMap p₁ p₂ ε (z i) := by
        unfold pairMap perp
        fun_prop
      have ht := (hc.tendsto 0).comp (tendsto_pairEps p₁ p₂)
      exact (ht.eventually (isOpen_interior.mem_nhds hseg)).mono fun n hn => interior_subset hn
    have hDev := hD_ev (fun n => pairEps p₁ p₂ n ^ 2) (fun n => sq_nonneg _)
      (tendsto_pairEps_sq p₁ p₂) z hz.2
    refine (tendsto_one_sub_div_pow (hullArea (baseCfg z)) (hullArea_lt_top _).ne
      (m + 2)).congr' ?_
    filter_upwards [hK', hDev] with n hn hd
    unfold scaledIntegrand
    rw [indicator_of_mem]
    exact ⟨hn, hz.1, hd⟩
  · rw [indicator_of_notMem hz]
    refine tendsto_const_nhds.congr fun n => ?_
    unfold scaledIntegrand
    rw [indicator_of_notMem]
    rintro ⟨_, hci, hd⟩
    exact hz (mem_limSet_of_D hD_le (sq_nonneg _) h0 h1 hci hd)

lemma lintegral_scaledIntegrand_le {K : Set (ℝ × ℝ)} {m : ℕ}
    {D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop}
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    (p₁ p₂ : ℝ × ℝ) {n : ℕ} (hn : 2 * (m + 2) ≤ n) :
    ∫⁻ z, scaledIntegrand K D p₁ p₂ n (n - (m + 2)) z ≤ 2 ^ m * limInt m := by
  rw [← lintegral_limSet_exp_half, ← lintegral_indicator (measurableSet_limSet m)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_fst_ne m 0, ae_fst_ne m 1] with z hz0 hz1
  exact scaledIntegrand_le hD_le p₁ p₂ (by omega) hn hz0 hz1

/-- Inner dominated convergence, for fixed `p₁, p₂ ∈ interior K`. -/
lemma tendsto_lintegral_scaledIntegrand {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) {m : ℕ} {D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop}
    (hDm : ∀ c, MeasurableSet {q | D c q})
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    (hD_ev : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → Tendsto c atTop (𝓝 0) → ∀ z : Fin m → ℝ × ℝ,
      (∀ i, 0 < (z i).1 ∧ (z i).1 < 1) → ∀ᶠ n in atTop, D (c n) (baseCfg z))
    (hJ : limInt m ≠ ⊤) {p₁ p₂ : ℝ × ℝ} (hp₁ : p₁ ∈ interior K) (hp₂ : p₂ ∈ interior K) :
    Tendsto (fun n : ℕ => ∫⁻ z, scaledIntegrand K D p₁ p₂ n (n - (m + 2)) z) atTop
      (𝓝 (limInt m)) := by
  have hlim : limInt m = ∫⁻ z, (limSet m).indicator
      (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal))) z := by
    rw [limInt, lintegral_indicator (measurableSet_limSet m)]
  rw [hlim]
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((limSet m).indicator
      (fun z => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal / 2))))
    (Eventually.of_forall fun n => measurable_scaledIntegrand K hKm D hDm p₁ p₂ n _) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 * (m + 2))] with n hn
    filter_upwards [ae_fst_ne m 0, ae_fst_ne m 1] with z hz0 hz1
    exact scaledIntegrand_le hD_le p₁ p₂ (by omega) hn hz0 hz1
  · rw [lintegral_indicator (measurableSet_limSet m), lintegral_limSet_exp_half]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hJ
  · filter_upwards [ae_fst_ne m 0, ae_fst_ne m 1] with z hz0 hz1
    exact tendsto_scaledIntegrand hK hD_le hD_ev hp₁ hp₂ hz0 hz1

/-! ### Null sets for the outer integral -/

lemma ae_restrict_mem_interior {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKm : MeasurableSet K) :
    ∀ᵐ x ∂(volume.restrict K), x ∈ interior K := by
  rw [ae_restrict_iff' hKm, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (hK.addHaar_frontier volume)
  have hx' : ¬(x ∈ K → x ∈ interior K) := hx
  exact ⟨subset_closure (Classical.not_imp.1 hx').1, (Classical.not_imp.1 hx').2⟩

lemma ae_prod_ne (K : Set (ℝ × ℝ)) :
    ∀ᵐ p ∂((volume.restrict K).prod (volume.restrict K)), p.1 ≠ p.2 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [Measure.measure_prod_null (isClosed_eq continuous_fst continuous_snd).measurableSet]
  refine Eventually.of_forall fun x => ?_
  refine measure_mono_null (fun y hy => ?_) (measure_singleton (μ := volume.restrict K) x)
  simp only [mem_preimage, mem_ofPred_eq] at hy
  exact hy.symm

/-! ### The main limit -/

theorem tendsto_diamProb (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) {m : ℕ} (D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop)
    (hD : ∀ (c c' s : ℝ), 0 < s → ∀ q q' : Fin (m + 2) → ℝ × ℝ,
      (∀ a b, sqDist c (q a) (q b) = s * sqDist c' (q' a) (q' b)) → (D c q ↔ D c' q'))
    (hDm : ∀ c, MeasurableSet {q | D c q})
    (hD_le : ∀ c, 0 ≤ c → ∀ z : Fin m → ℝ × ℝ, D c (baseCfg z) → IsDiamLE c (baseCfg z) 0 1)
    (hD_ev : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → Tendsto c atTop (𝓝 0) → ∀ z : Fin m → ℝ × ℝ,
      (∀ i, 0 < (z i).1 ∧ (z i).1 < 1) → ∀ᶠ n in atTop, D (c n) (baseCfg z))
    (hJ : limInt m ≠ ⊤) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ m * diamProb K m (D 1) (n - (m + 2))) atTop
      (𝓝 (limInt m)) := by
  set μ := (volume.restrict K).prod (volume.restrict K) with hμdef
  have hμ : μ univ = 1 := by
    rw [hμdef, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, hK1, one_mul]
  have hrw : ∀ n : ℕ, (n : ℝ≥0∞) ^ m * diamProb K m (D 1) (n - (m + 2)) =
      ∫⁻ p, (n : ℝ≥0∞) ^ m * pairSection K (D 1) p.1 p.2 (n - (m + 2)) ∂μ := by
    intro n
    rw [diamProb_eq_lintegral_pairSection K hKm (D 1) (hDm 1),
      lintegral_const_mul _ (measurable_pairSection K hKm (D 1) (hDm 1) _)]
  simp_rw [hrw]
  have hint := ae_restrict_mem_interior hK hKm
  have hgood : ∀ᵐ p ∂μ, p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hint,
      Measure.quasiMeasurePreserving_snd.ae hint, ae_prod_ne K] with p h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have key : Tendsto (fun n : ℕ => ∫⁻ p,
      (n : ℝ≥0∞) ^ m * pairSection K (D 1) p.1 p.2 (n - (m + 2)) ∂μ) atTop
      (𝓝 (∫⁻ _, limInt m ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 2 ^ m * limInt m)
      (Eventually.of_forall fun n =>
        (measurable_pairSection K hKm (D 1) (hDm 1) _).const_mul _) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 * (m + 2))] with n hn
      filter_upwards [hgood] with p hp
      rw [pow_mul_pairSection_eq K hKm D hD hp.2.2 (by omega : 0 < n)]
      exact lintegral_scaledIntegrand_le hD_le p.1 p.2 hn
    · rw [lintegral_const, hμ, mul_one]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hJ
    · filter_upwards [hgood] with p hp
      refine (tendsto_lintegral_scaledIntegrand hK hKm hDm hD_le hD_ev hJ hp.1 hp.2.1).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [pow_mul_pairSection_eq K hKm D hD hp.2.2 (by omega : 0 < n)]
  rwa [lintegral_const, hμ, mul_one] at key

theorem tendsto_diamProb_le (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) (m : ℕ) (hJ : limInt m ≠ ⊤) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ m *
      diamProb K m (fun q => IsDiamLE 1 q 0 1) (n - (m + 2))) atTop (𝓝 (limInt m)) :=
  tendsto_diamProb K hK hKm hK1 (fun c q => IsDiamLE c q 0 1)
    (fun _ _ _ hs _ _ h => isDiamLE_iff_of_sqDist hs h 0 1)
    (fun c => measurableSet_isDiamLE c 0 1)
    (fun _ _ _ h => h)
    (fun _ hc0 hc _ hz => (eventually_isDiamLT hc hz).mono fun n hn =>
      hn.isDiamLE (hc0 n) (by simp))
    hJ

theorem tendsto_diamProb_lt (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) (m : ℕ) (hJ : limInt m ≠ ⊤) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ m *
      diamProb K m (fun q => IsDiamLT 1 q 0 1) (n - (m + 2))) atTop (𝓝 (limInt m)) :=
  tendsto_diamProb K hK hKm hK1 (fun c q => IsDiamLT c q 0 1)
    (fun _ _ _ hs _ _ h => isDiamLT_iff_of_sqDist hs h 0 1)
    (fun c => measurableSet_isDiamLT c 0 1)
    (fun _ hc _ h => h.isDiamLE hc (by simp))
    (fun _ _ hc _ hz => eventually_isDiamLT hc hz)
    hJ

end KHoles
