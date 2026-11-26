/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.HullMeasurable
import KHoles.ConvexInvariance
import KHoles.PiLinear
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Fubini over the first two points and the per-pair scaling

Step 4a of `doc/kholes/kholes.md` (wave 2, §3.2 `PairScaling.lean`).

* `diamProb_eq_lintegral_pairSection`: `diamProb K m D N` is the integral over the first two
  points `(p₁, p₂) ∈ K²` of `pairSection K D p₁ p₂ N` (Fubini, splitting off coordinates `0`
  and `1` with `measurePreserving_piFinSuccAbove`).
* `measurable_pairSection`: the section is measurable in `(p₁, p₂)`.
* `pow_mul_pairSection_eq`: for `p₁ ≠ p₂` and `0 < n`, the substitution
  `r i = pairMap p₁ p₂ ε (z i)`, `ε = pairEps p₁ p₂ n`, turns `n^m * pairSection` into
  `∫ scaledIntegrand K D p₁ p₂ n N`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-- The integrand of `diamProb`. -/
private noncomputable def diamFun {k : ℕ} (D : (Fin k → ℝ × ℝ) → Prop) (N : ℕ) :
    (Fin k → ℝ × ℝ) → ℝ≥0∞ :=
  {q | q ∈ ciSet (Fin k) ∧ D q}.indicator (fun q => (1 - hullArea q) ^ N)

private lemma measurable_diamFun {k : ℕ} (D : (Fin k → ℝ × ℝ) → Prop)
    (hDm : MeasurableSet {q | D q}) (N : ℕ) : Measurable (diamFun D N) := by
  refine Measurable.indicator ?_ ((measurableSet_ciSet _).inter hDm)
  exact (measurable_const.sub (measurable_hullArea _)).pow_const N

private lemma pairSection_eq (K : Set (ℝ × ℝ)) {m : ℕ} (D : (Fin (m + 2) → ℝ × ℝ) → Prop)
    (p₁ p₂ : ℝ × ℝ) (N : ℕ) :
    pairSection K D p₁ p₂ N = ∫⁻ r, diamFun D N (cons2 p₁ p₂ r) ∂ptLaw K m := rfl

private instance sigmaFinite_ptLaw (K : Set (ℝ × ℝ)) (n : ℕ) : SigmaFinite (ptLaw K n) := by
  rw [ptLaw_def]; infer_instance

/-- Splitting off the first coordinate of a `ptLaw` integral. -/
private lemma lintegral_ptLaw_succ (K : Set (ℝ × ℝ)) (n : ℕ) (f : (Fin (n + 1) → ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ q, f q ∂ptLaw K (n + 1) =
      ∫⁻ x, ∫⁻ r, f (Fin.cons x r) ∂ptLaw K n ∂(volume.restrict K) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => volume.restrict K)
    0).symm
  have h1 := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f
  rw [ptLaw_def, ← h1, lintegral_prod]
  · refine lintegral_congr fun x => lintegral_congr fun r => ?_
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp [Fin.insertNth_zero']
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

/-- (The hypothesis `MeasurableSet K` of plan §3 is not needed; it is kept, as `_hKm`, so that
the signature matches the plan.) -/
theorem measurable_pairSection (K : Set (ℝ × ℝ)) (_hKm : MeasurableSet K) {m : ℕ}
    (D : (Fin (m + 2) → ℝ × ℝ) → Prop) (hDm : MeasurableSet {q | D q}) (N : ℕ) :
    Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => pairSection K D p.1 p.2 N := by
  simp only [pairSection_eq]
  have hc : Measurable fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × (Fin m → ℝ × ℝ) =>
      cons2 x.1.1 x.1.2 x.2 :=
    ((continuous_cons2 m).comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).measurable
  exact ((measurable_diamFun D hDm N).comp hc).lintegral_prod_right'

theorem diamProb_eq_lintegral_pairSection (K : Set (ℝ × ℝ)) (hKm : MeasurableSet K) {m : ℕ}
    (D : (Fin (m + 2) → ℝ × ℝ) → Prop) (hDm : MeasurableSet {q | D q}) (N : ℕ) :
    diamProb K m D N = ∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ), pairSection K D p.1 p.2 N
      ∂((volume.restrict K).prod (volume.restrict K)) := by
  rw [lintegral_prod _ (measurable_pairSection K hKm D hDm N).aemeasurable]
  have h0 : diamProb K m D N = ∫⁻ q, diamFun D N q ∂ptLaw K (m + 2) := rfl
  rw [h0, lintegral_ptLaw_succ K (m + 1) _ (measurable_diamFun D hDm N)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_ptLaw_succ K m (fun r => diamFun D N (Fin.cons x r))
    ((measurable_diamFun D hDm N).comp
    (continuous_const.finCons continuous_id).measurable)]
  rfl

theorem pow_mul_pairSection_eq (K : Set (ℝ × ℝ)) (hKm : MeasurableSet K) {m : ℕ}
    (D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop)
    (hD : ∀ (c c' s : ℝ), 0 < s → ∀ q q' : Fin (m + 2) → ℝ × ℝ,
      (∀ a b, sqDist c (q a) (q b) = s * sqDist c' (q' a) (q' b)) → (D c q ↔ D c' q'))
    {p₁ p₂ : ℝ × ℝ} (hp : p₁ ≠ p₂) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    (n : ℝ≥0∞) ^ m * pairSection K (D 1) p₁ p₂ N = ∫⁻ z, scaledIntegrand K D p₁ p₂ n N z := by
  set ε := pairEps p₁ p₂ n with hε
  set F : (Fin m → ℝ × ℝ) → ℝ≥0∞ :=
    (univ.pi fun _ => K).indicator fun r => diamFun (D 1) N (cons2 p₁ p₂ r) with hF
  have hpi : MeasurableSet (univ.pi fun _ : Fin m => K) :=
    MeasurableSet.univ_pi fun _ => hKm
  have hsec : pairSection K (D 1) p₁ p₂ N = ∫⁻ r, F r := by
    rw [pairSection_eq, ptLaw_def, ← Measure.restrict_pi_pi, lintegral_indicator hpi]
    rfl
  rw [hsec, ← lintegral_comp_pairMap_pairEps m hp hn F]
  refine lintegral_congr fun z => ?_
  -- the configuration in the original coordinates
  have hcfg0 : cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i)) =
      fun i => pairMap p₁ p₂ ε (baseCfg z i) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp [baseCfg, cons2]
    · simp [baseCfg, cons2]
    · rfl
  have hcfg : cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i)) =
      fun i => p₁ + pairLin p₁ p₂ ε (baseCfg z i) := by
    rw [hcfg0]
    simp only [pairMap_eq_add_pairLin]
  have hεpos : 0 < ε := pairEps_pos hp hn
  have hCI : ConvexIndependent ℝ (cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i))) ↔
      ConvexIndependent ℝ (baseCfg z) := by
    rw [hcfg]
    exact convexIndependent_affine_iff _ (pairLin_injective hp hεpos.ne') _ _
  have hDiam : D 1 (cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i))) ↔ D (ε ^ 2) (baseCfg z) := by
    refine hD 1 (ε ^ 2) (sqDist 1 p₁ p₂) (sqDist_one_pos hp) _ _ fun i j => ?_
    rw [hcfg0]
    exact sqDist_pairMap _ _ _ _ _
  have hArea : hullArea (cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i))) =
      hullArea (baseCfg z) / n := by
    rw [hcfg, hullArea_affine, det_pairLin_pairEps hp hn, abs_of_nonneg (by positivity),
      one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
      div_eq_mul_inv, mul_comm]
  have hS : z ∈ {z : Fin m → ℝ × ℝ | (∀ i, pairMap p₁ p₂ ε (z i) ∈ K) ∧
      baseCfg z ∈ ciSet (Fin (m + 2)) ∧ D (ε ^ 2) (baseCfg z)} ↔
      (fun i => pairMap p₁ p₂ ε (z i)) ∈ univ.pi (fun _ => K) ∧
        cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i)) ∈
          {q | q ∈ ciSet (Fin (m + 2)) ∧ D 1 q} := by
    simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, mem_ciSet, hCI, hDiam,
      forall_const]
  change F (fun i => pairMap p₁ p₂ ε (z i)) = {z : Fin m → ℝ × ℝ | (∀ i, pairMap p₁ p₂ ε (z i) ∈ K) ∧
      baseCfg z ∈ ciSet (Fin (m + 2)) ∧ D (ε ^ 2) (baseCfg z)}.indicator
    (fun z => (1 - hullArea (baseCfg z) / n) ^ N) z
  rw [hF, diamFun]
  by_cases h : (fun i => pairMap p₁ p₂ ε (z i)) ∈ univ.pi (fun _ => K) ∧
      cons2 p₁ p₂ (fun i => pairMap p₁ p₂ ε (z i)) ∈ {q | q ∈ ciSet (Fin (m + 2)) ∧ D 1 q}
  · rw [indicator_of_mem h.1, indicator_of_mem h.2, indicator_of_mem (hS.2 h), hArea]
  · rw [indicator_of_notMem (fun h' => h (hS.1 h'))]
    by_cases h1 : (fun i => pairMap p₁ p₂ ε (z i)) ∈ univ.pi (fun _ => K)
    · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => h ⟨h1, h2⟩)]
    · rw [indicator_of_notMem h1]

end KHoles
