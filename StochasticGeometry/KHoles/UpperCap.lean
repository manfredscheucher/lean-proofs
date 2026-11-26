/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.Symmetrize
import KHoles.ChainSlopes
import KHoles.ChainConvex
import KHoles.ChainArea
import KHoles.HullMeasurable
import KHoles.ConvexInvariance
import KHoles.CapIntegral
import KHoles.Main

/-!
# The labelled upper-cap integral (Step 5c of doc/kholes/kholes.md)

We show `upperInt 0 = 1`, `upperInt (n + 1) = (n + 1)! · capIntegral n`, and hence
`upperInt m = m! · a m`.

Proof of the main identity: the integrand `1[upperSet] · exp(-hullArea (baseCfg w))` is
invariant under permutations of the points, so by `lintegral_eq_factorial_mul_sorted` the
integral is `(n + 1)!` times the integral over tuples with strictly increasing abscissae.
Splitting `w ↔ (x, Y)` (`arrowProdEquivProdArrow`) and using Tonelli, the inner integrand for
`x ∈ simplexFin n` is the indicator of `Admissible x` times `exp (-areaUnder x Y)`
(`convexIndependent_iff_admissible`, `admissible_pos`, `hullArea_eq_areaUnder`), and it
vanishes for `x ∉ simplexFin n`. This is literally `capIntegral n`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### The integrand -/

lemma measurable_expHull (m : ℕ) :
    Measurable fun w : Fin m → ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal)) :=
  (Real.measurable_exp.comp (measurable_hullArea_baseCfg m).ennreal_toReal.neg).ennreal_ofReal

lemma comp_perm_mem_upperSet {m : ℕ} (σ : Equiv.Perm (Fin m)) (w : Fin m → ℝ × ℝ) :
    w ∘ σ ∈ upperSet m ↔ w ∈ upperSet m := by
  simp only [upperSet, mem_ofPred_eq, convexIndependent_baseCfg_comp_perm, Function.comp_apply]
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => h (σ i)⟩
  simpa using h (σ.symm i)

/-- Symmetrisation: the integral over `upperSet` is `m!` times the integral over the tuples
with strictly increasing abscissae. -/
lemma upperInt_eq_factorial_mul_sorted (m : ℕ) :
    upperInt m = m.factorial * ∫⁻ w, ({w : Fin m → ℝ × ℝ | StrictMono fun i => (w i).1} ∩
      upperSet m).indicator
        (fun w => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal))) w := by
  rw [upperInt, ← lintegral_indicator (measurableSet_upperSet m),
    lintegral_eq_factorial_mul_sorted _ ((measurable_expHull m).indicator
      (measurableSet_upperSet m)),
    ← lintegral_indicator (measurableSet_strictMono_fst m), indicator_indicator]
  intro σ z
  by_cases hz : z ∈ upperSet m
  · rw [indicator_of_mem hz, indicator_of_mem ((comp_perm_mem_upperSet σ z).2 hz),
      hullArea_baseCfg_comp_perm]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (fun h => hz ((comp_perm_mem_upperSet σ z).1 h))]

/-- For `x ∈ simplexFin n`, `zip2 x Y` is a sorted upper cap iff `Y` is admissible. -/
lemma zip2_mem_iff {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ∈ simplexFin n) (Y : Fin (n + 1) → ℝ) :
    zip2 x Y ∈ {w : Fin (n + 1) → ℝ × ℝ | StrictMono fun i => (w i).1} ∩ upperSet (n + 1) ↔
      Y ∈ Admissible x := by
  obtain ⟨hmono, h0, h1⟩ := hx
  constructor
  · rintro ⟨-, hci, hb⟩
    exact (convexIndependent_iff_admissible hmono h0 h1 fun i => (hb i).2.2).1 hci
  · intro hY
    have hpos := admissible_pos hmono h0 h1 hY
    refine ⟨hmono, (convexIndependent_iff_admissible hmono h0 h1 hpos).2 hY,
      fun i => ⟨x_pos hmono h0 i, x_lt_one hmono h1 i, hpos i⟩⟩

lemma zip2_mem_imp {n : ℕ} {x Y : Fin (n + 1) → ℝ}
    (h : zip2 x Y ∈ {w : Fin (n + 1) → ℝ × ℝ | StrictMono fun i => (w i).1} ∩ upperSet (n + 1)) :
    x ∈ simplexFin n :=
  ⟨h.1, (h.2.2 0).1, (h.2.2 (Fin.last n)).2.1⟩

/-- The inner integral over the heights. -/
lemma lintegral_zip2 {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∫⁻ Y, ({w : Fin (n + 1) → ℝ × ℝ | StrictMono fun i => (w i).1} ∩ upperSet (n + 1)).indicator
        (fun w => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal))) (zip2 x Y) =
      (simplexFin n).indicator
        (fun x => ∫⁻ Y in Admissible x, ENNReal.ofReal (Real.exp (-areaUnder x Y))) x := by
  set S := {w : Fin (n + 1) → ℝ × ℝ | StrictMono fun i => (w i).1} ∩ upperSet (n + 1) with hS
  by_cases hx : x ∈ simplexFin n
  · rw [indicator_of_mem hx]
    obtain ⟨hmono, h0, h1⟩ := hx
    have hpre : Admissible x = (fun Y => zip2 x Y) ⁻¹' S := by
      ext Y
      exact (zip2_mem_iff ⟨hmono, h0, h1⟩ Y).symm
    have hmeas : MeasurableSet (Admissible x) := by
      rw [hpre]
      refine ((measurableSet_strictMono_fst (n + 1)).inter (measurableSet_upperSet _)).preimage ?_
      exact measurable_pi_lambda _ fun i =>
        measurable_const.prodMk (measurable_pi_apply i)
    rw [← lintegral_indicator hmeas]
    refine lintegral_congr fun Y => ?_
    by_cases hY : Y ∈ Admissible x
    · rw [indicator_of_mem hY, indicator_of_mem ((zip2_mem_iff ⟨hmono, h0, h1⟩ Y).2 hY),
        hullArea_eq_areaUnder hmono h0 h1 hY,
        ENNReal.toReal_ofReal (areaUnder_nonneg hmono h0 h1 hY)]
    · rw [indicator_of_notMem hY,
        indicator_of_notMem fun h => hY ((zip2_mem_iff ⟨hmono, h0, h1⟩ Y).1 h)]
  · rw [indicator_of_notMem hx]
    have h0 : ∀ Y, S.indicator
        (fun w => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal))) (zip2 x Y) = 0 :=
      fun Y => indicator_of_notMem (fun h => hx (zip2_mem_imp h)) _
    simp only [h0, lintegral_zero]

lemma measurable_zip2_prod (n : ℕ) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => zip2 p.1 p.2 :=
  measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

/-! ### Main results -/

theorem upperInt_zero : upperInt 0 = 1 := by
  have hci : ∀ w : Fin 0 → ℝ × ℝ, ConvexIndependent ℝ (baseCfg w) := by
    intro w
    rw [convexIndependent_iff_forall_notMem]
    intro i
    have hc : ∀ j : Fin (0 + 2), ({j}ᶜ : Set (Fin (0 + 2))) = {1 - j} := by
      intro j
      ext l
      fin_cases j <;> fin_cases l <;> simp
    rw [hc, image_singleton, convexHull_singleton, mem_singleton_iff]
    fin_cases i <;> simp
  have hset : upperSet 0 = univ := by
    ext w
    simp [upperSet, hci w]
  have harea : ∀ w : Fin 0 → ℝ × ℝ, hullArea (baseCfg w) = 0 := by
    intro w
    rw [hullArea, range_baseCfg, range_eq_empty, insert_empty_eq, convexHull_pair]
    refine measure_mono_null ?_ (volume_snd_eq 0)
    rw [segment_subset_iff]
    intro s t _ _ _
    simp
  rw [upperInt, hset, Measure.restrict_univ]
  simp only [harea, ENNReal.toReal_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    lintegral_const, one_mul]
  rw [volume_pi, Measure.pi_univ]
  simp

theorem upperInt_succ (n : ℕ) :
    upperInt (n + 1) = ((n + 1).factorial : ℝ≥0∞) * capIntegral n := by
  rw [upperInt_eq_factorial_mul_sorted]
  congr 1
  set S := {w : Fin (n + 1) → ℝ × ℝ | StrictMono fun i => (w i).1} ∩ upperSet (n + 1) with hS
  set F := S.indicator
    (fun w => ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal))) with hF
  have hFm : Measurable F := (measurable_expHull _).indicator
    ((measurableSet_strictMono_fst _).inter (measurableSet_upperSet _))
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (n + 1))
  have hmp : MeasurePreserving e volume volume :=
    volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n + 1))
  have h1 : ∫⁻ w, F w = ∫⁻ p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ), F (zip2 p.1 p.2) := by
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding (fun p => F (zip2 p.1 p.2))]
    rfl
  rw [h1, Measure.volume_eq_prod,
    lintegral_prod (fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => F (zip2 p.1 p.2))
      (hFm.comp (measurable_zip2_prod _)).aemeasurable]
  simp only [hF, hS, lintegral_zip2]
  rw [capIntegral, lintegral_indicator (measurableSet_simplexFin n)]

theorem upperInt_eq (m : ℕ) : upperInt m = (m.factorial : ℝ≥0∞) * ENNReal.ofReal (a m) := by
  cases m with
  | zero => simp [upperInt_zero, a_zero]
  | succ n =>
    rw [upperInt_succ, ← capIntegral_toReal, ENNReal.ofReal_toReal (capIntegral_ne_top n)]

end KHoles
