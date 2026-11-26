/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs

/-!
# Step (i): the simplex integral is the Volterra iteration

`capIntY m y = F m y` for `0 ≤ y ≤ 1` (§2.2 of `doc/kholes/kholes.md`), by induction
on the dimension `m`: the last coordinate `t = x_m` of a point of `simplex (m+1) y` is split
off with `MeasurableEquiv.piFinSuccAbove (Fin.last m)` and Tonelli (`lintegral_prod`).
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace KHoles

/-! ### Measurability -/

theorem measurable_xbar (m : ℕ) (y : ℝ) (k : ℕ) :
    Measurable fun x : Fin m → ℝ => xbar m y x k := by
  unfold xbar
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_capDensity (m : ℕ) (y : ℝ) : Measurable (capDensity m y) := by
  unfold capDensity
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_prod _ fun j _ =>
      (measurable_xbar m y (j + 1)).sub (measurable_xbar m y j)
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_pi_apply i).mul (measurable_const.sub (measurable_pi_apply i))

theorem simplex_eq (m : ℕ) (y : ℝ) :
    simplex m y = (⋂ i : Fin m, ⋂ j : Fin m, {x | i < j → x i < x j}) ∩
      ((⋂ i, {x | 0 < x i}) ∩ ⋂ i, {x | x i < y}) := by
  ext x
  simp [mem_simplex, StrictMono]

theorem measurableSet_simplex (m : ℕ) (y : ℝ) : MeasurableSet (simplex m y) := by
  rw [simplex_eq]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) (MeasurableSet.iInter fun i => ?_))
  · by_cases h : i < j
    · simpa [h] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [h]
  · exact measurableSet_lt measurable_const (measurable_pi_apply i)
  · exact measurableSet_lt (measurable_pi_apply i) measurable_const

/-- The integrand of `capIntY m y` extended by zero off the simplex. -/
noncomputable def capG (m : ℕ) (y : ℝ) (x : Fin m → ℝ) : ℝ≥0∞ :=
  (simplex m y).indicator (fun x => ENNReal.ofReal (capDensity m y x)) x

theorem measurable_capG (m : ℕ) (y : ℝ) : Measurable (capG m y) :=
  (measurable_capDensity m y).ennreal_ofReal.indicator (measurableSet_simplex m y)

theorem capIntY_eq_lintegral_capG (m : ℕ) (y : ℝ) : capIntY m y = ∫⁻ x, capG m y x := by
  rw [capIntY_def, ← lintegral_indicator (measurableSet_simplex m y)]
  rfl

/-! ### Splitting off the last coordinate -/

theorem lintegral_snoc (m : ℕ) {f : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ t : ℝ, ∫⁻ x : Fin m → ℝ, f (Fin.snoc x t) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod (fun p => f ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)).symm p))
      (hf.comp h.measurable).aemeasurable]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

/-! ### The simplex and the density under `Fin.snoc` -/

theorem snoc_mem_simplex_iff {m : ℕ} {y t : ℝ} {x : Fin m → ℝ} :
    (Fin.snoc x t : Fin (m + 1) → ℝ) ∈ simplex (m + 1) y ↔ t ∈ Ioo 0 y ∧ x ∈ simplex m t := by
  constructor
  · rintro ⟨hm, hpos, hlt⟩
    have hlast := hlt (Fin.last m)
    have hp := hpos (Fin.last m)
    simp only [Fin.snoc_last] at hlast hp
    refine ⟨⟨hp, hlast⟩, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · simpa using hm (Fin.castSucc_lt_castSucc_iff.2 hij)
    · simpa using hpos (Fin.castSucc i)
    · simpa using hm (Fin.castSucc_lt_last i)
  · rintro ⟨⟨h0, hy⟩, hm, hpos, hlt⟩
    refine ⟨fun a b hab => ?_, fun i => ?_, fun i => ?_⟩
    · refine Fin.lastCases ?_ (fun b => ?_) b hab
      · refine Fin.lastCases (fun h => absurd h (lt_irrefl _)) (fun a _ => ?_) a
        simpa using hlt a
      · refine Fin.lastCases (fun h => absurd h (not_lt.2 (Fin.le_last _))) (fun a h => ?_) a
        simpa using hm (Fin.castSucc_lt_castSucc_iff.1 h)
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using h0
      · simpa using hpos i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hy
      · simpa using (hlt i).trans hy

theorem xbar_snoc_of_le {m : ℕ} (y t : ℝ) (x : Fin m → ℝ) {k : ℕ} (hk : k ≤ m + 1) :
    xbar (m + 1) y (Fin.snoc x t) k = xbar m t x k := by
  rcases k with _ | k
  · simp
  · rcases Nat.lt_or_ge k m with h | h
    · rw [xbar_of_lt _ _ (by omega), xbar_of_lt _ _ h]
      have : (⟨k, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨k, h⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · have hkm : k = m := by omega
      subst hkm
      rw [xbar_of_lt _ _ (by omega), xbar_of_ge _ _ le_rfl]
      have : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [this, Fin.snoc_last]

theorem capDensity_snoc {m : ℕ} (y t : ℝ) (x : Fin m → ℝ) :
    capDensity (m + 1) y (Fin.snoc x t) = capDensity m t x * ((y - t) / (t * (1 - t))) := by
  unfold capDensity
  rw [prod_range_succ, Fin.prod_univ_castSucc]
  rw [xbar_of_ge _ _ (le_refl (m + 1)), xbar_snoc_of_le y t x le_rfl,
    xbar_of_ge _ _ (le_refl m)]
  rw [Finset.prod_congr rfl fun j hj => by
    rw [xbar_snoc_of_le y t x (by simp at hj; omega), xbar_snoc_of_le y t x (by simp at hj; omega)]]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [mul_div_mul_comm]

/-! ### The integrand under `Fin.snoc` -/

theorem capG_snoc_of_mem {m : ℕ} {y t : ℝ} (hy1 : y ≤ 1) (ht : t ∈ Ioo 0 y) (x : Fin m → ℝ) :
    capG (m + 1) y (Fin.snoc x t) = capG m t x * ENNReal.ofReal ((y - t) / (t * (1 - t))) := by
  have hc : 0 ≤ (y - t) / (t * (1 - t)) :=
    div_nonneg (by linarith [ht.2]) (mul_nonneg ht.1.le (by linarith [ht.2]))
  unfold capG
  by_cases hx : x ∈ simplex m t
  · rw [indicator_of_mem (snoc_mem_simplex_iff.2 ⟨ht, hx⟩), indicator_of_mem hx,
      capDensity_snoc, ENNReal.ofReal_mul' hc]
  · rw [indicator_of_notMem (fun h => hx (snoc_mem_simplex_iff.1 h).2), indicator_of_notMem hx,
      zero_mul]

theorem capG_snoc_of_notMem {m : ℕ} {y t : ℝ} (ht : t ∉ Ioo 0 y) (x : Fin m → ℝ) :
    capG (m + 1) y (Fin.snoc x t) = 0 := by
  unfold capG
  exact indicator_of_notMem (fun h => ht (snoc_mem_simplex_iff.1 h).1) _

/-! ### The Volterra identity -/

theorem capIntY_zero (y : ℝ) : capIntY 0 y = ENNReal.ofReal y := by
  have hs : simplex 0 y = univ := by
    ext x
    simp [mem_simplex, StrictMono]
  have hd : ∀ x : Fin 0 → ℝ, capDensity 0 y x = y := by
    intro x
    simp [capDensity, xbar]
  simp [capIntY_def, hs, hd, lintegral_const, volume_pi]

theorem capIntY_eq_F (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : capIntY m y = F m y := by
  induction m generalizing y with
  | zero => rw [capIntY_zero, F_zero]
  | succ m ih =>
    have hin : ∀ t, ∫⁻ x : Fin m → ℝ, capG (m + 1) y (Fin.snoc x t) =
        (Ioo 0 y).indicator
          (fun t => capIntY m t * ENNReal.ofReal ((y - t) / (t * (1 - t)))) t := by
      intro t
      by_cases ht : t ∈ Ioo 0 y
      · rw [indicator_of_mem ht, capIntY_eq_lintegral_capG,
          ← lintegral_mul_const _ (measurable_capG m t)]
        exact lintegral_congr fun x => capG_snoc_of_mem hy1 ht x
      · rw [indicator_of_notMem ht]
        simp [capG_snoc_of_notMem ht]
    rw [capIntY_eq_lintegral_capG, lintegral_snoc m (measurable_capG _ _), lintegral_congr hin,
      lintegral_indicator measurableSet_Ioo, F_succ]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [ih ht.1.le (ht.2.le.trans hy1)]

theorem capInt_eq_F (m : ℕ) : capInt m = F m 1 :=
  capIntY_eq_F m zero_le_one le_rfl

end KHoles
