/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HullMeasurable
import KHoles.ConvexInvariance

/-!
# Steps 1+2: the expected number of `k`-holes as `choose n k * emptyProb`

Step 1+2 of `doc/kholes/kholes.md`. For `n` i.i.d. uniform points in a convex measurable
set `K` with `volume K = 1` (law `ptLaw K n`):

* `isProbabilityMeasure_ptLaw`: `ptLaw K n` is a probability measure;
* `measurableSet_isHole`: `{p | IsHole k p T}` is measurable;
* `ptLaw_isHole`: for `#T = k`, `P(T is a k-hole) = emptyProb K k (n - k)`;
* `EH_eq_choose_mul`: `EH K n k = n.choose k * emptyProb K k (n - k)`.

Proof of `ptLaw_isHole`: split `Fin n → X ≃ (T → X) × (Tᶜ → X)`
(`measurePreserving_piEquivPiSubtypeProd`), compute the measure of the event by Tonelli
(`Measure.prod_apply`) and `Measure.pi_pi`: the section over `a : T → X` is
`1[CI a] · μ_K(conv(a)ᶜ)^{#Tᶜ}`; a.e. all `a i ∈ K`, so `conv a ⊆ K` and
`μ_K(conv(a)ᶜ) = 1 - hullArea a`; finally reindex `T ≃ Fin k`
(`measurePreserving_piCongrLeft`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

lemma isProbabilityMeasure_restrict_of_volume_eq_one {K : Set (ℝ × ℝ)} (hK1 : volume K = 1) :
    IsProbabilityMeasure (volume.restrict K) :=
  ⟨by rw [Measure.restrict_apply_univ, hK1]⟩

theorem isProbabilityMeasure_ptLaw {K : Set (ℝ × ℝ)} (hK1 : volume K = 1) (n : ℕ) :
    IsProbabilityMeasure (ptLaw K n) := by
  have := isProbabilityMeasure_restrict_of_volume_eq_one hK1
  rw [ptLaw_def]
  infer_instance

theorem measurableSet_isHole {n : ℕ} (k : ℕ) (T : Finset (Fin n)) :
    MeasurableSet {p : Fin n → ℝ × ℝ | IsHole k p T} := by
  classical
  have h1 : MeasurableSet {p : Fin n → ℝ × ℝ | ConvexIndependent ℝ (fun i : T => p i)} :=
    (measurableSet_ciSet T).preimage (by fun_prop)
  have h2 : ∀ j : Fin n,
      MeasurableSet {p : Fin n → ℝ × ℝ | p j ∉ convexHull ℝ (p '' (T : Set (Fin n)))} := by
    intro j
    have hc : Measurable fun p : Fin n → ℝ × ℝ => ((fun i : T => p i), p j) := by fun_prop
    have := ((measurableSet_mem_convexHull_range T).preimage hc).compl
    convert this using 1
    ext p
    simp [image_eq_range]
  have : {p : Fin n → ℝ × ℝ | IsHole k p T} =
      {_p | T.card = k} ∩ ({p | ConvexIndependent ℝ (fun i : T => p i)} ∩
        ⋂ j ∈ Tᶜ, {p | p j ∉ convexHull ℝ (p '' (T : Set (Fin n)))}) := by
    ext p
    simp [IsHole]
  rw [this]
  exact (MeasurableSet.const _).inter (h1.inter (Finset.measurableSet_biInter _ fun j _ => h2 j))

/-- For `a` with all points in the convex set `K` (`volume K = 1`), the uniform measure of the
complement of the hull is `1 - hullArea a`. -/
lemma restrict_compl_convexHull {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hK1 : volume K = 1)
    {ι : Type*} [Finite ι] {a : ι → ℝ × ℝ} (ha : ∀ i, a i ∈ K) :
    volume.restrict K (convexHull ℝ (range a))ᶜ = 1 - hullArea a := by
  have hc := (isCompact_convexHull_range a).isClosed.measurableSet
  rw [Measure.restrict_apply hc.compl, inter_comm, ← sdiff_eq,
    measure_sdiff (convexHull_range_subset hK ha) hc.nullMeasurableSet (hullArea_lt_top a).ne,
    hK1, hullArea]

theorem ptLaw_isHole {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) {n k : ℕ} (T : Finset (Fin n)) (hT : T.card = k) :
    ptLaw K n {p | IsHole k p T} = emptyProb K k (n - k) := by
  classical
  set μ : Measure (ℝ × ℝ) := volume.restrict K with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_restrict_of_volume_eq_one hK1
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ × ℝ) (· ∈ T)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (· ∈ T)
  let S : Set ((T → ℝ × ℝ) × ({j // j ∉ T} → ℝ × ℝ)) :=
    {x | ConvexIndependent ℝ x.1 ∧ ∀ j, x.2 j ∉ convexHull ℝ (range x.1)}
  have hS : {p | IsHole k p T} = e ⁻¹' S := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, IsHole, hT, true_and, S, e,
      MeasurableEquiv.piEquivPiSubtypeProd_apply, image_eq_range, Subtype.forall]
    exact Iff.rfl
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet
        {x : (T → ℝ × ℝ) × ({j // j ∉ T} → ℝ × ℝ) | ConvexIndependent ℝ x.1} :=
      (measurableSet_ciSet T).preimage measurable_fst
    have h2 : ∀ j : {j // j ∉ T}, MeasurableSet
        {x : (T → ℝ × ℝ) × ({j // j ∉ T} → ℝ × ℝ) | x.2 j ∉ convexHull ℝ (range x.1)} :=
      fun j => ((measurableSet_mem_convexHull_range T).preimage
        (by fun_prop : Measurable fun x : (T → ℝ × ℝ) × ({j // j ∉ T} → ℝ × ℝ) =>
          (x.1, x.2 j))).compl
    have : S = {x | ConvexIndependent ℝ x.1} ∩
        ⋂ j, {x | x.2 j ∉ convexHull ℝ (range x.1)} := by
      ext x
      simp [S]
    rw [this]
    exact h1.inter (MeasurableSet.iInter h2)
  have hsec : ∀ a : T → ℝ × ℝ, (Measure.pi fun _ : {j // j ∉ T} => μ) (Prod.mk a ⁻¹' S) =
      (ciSet T).indicator (fun a => μ (convexHull ℝ (range a))ᶜ ^ (n - k)) a := by
    intro a
    by_cases ha : ConvexIndependent ℝ a
    · have : Prod.mk a ⁻¹' S = univ.pi fun _ => (convexHull ℝ (range a))ᶜ := by
        ext b
        simp [S, ha]
      rw [this, Measure.pi_pi, Finset.prod_const, Finset.card_univ, indicator_of_mem ha]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp [hT]
    · have : Prod.mk a ⁻¹' S = ∅ := by
        ext b
        simp [S, ha]
      rw [this, measure_empty, indicator_of_notMem ha]
  have hae : ∀ᵐ a ∂(Measure.pi fun _ : T => μ), ∀ i, a i ∈ K := by
    rw [hμ, ← Measure.restrict_pi_pi]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => hKm)] with a ha
    simpa using ha
  rw [ptLaw_def, hS, he.measure_preimage_equiv, Measure.prod_apply hSm]
  simp_rw [hsec]
  have h1 : ∫⁻ a, (ciSet T).indicator (fun a => μ (convexHull ℝ (range a))ᶜ ^ (n - k)) a
        ∂(Measure.pi fun _ : T => μ) =
      ∫⁻ a, (ciSet T).indicator (fun a => (1 - hullArea a) ^ (n - k)) a
        ∂(Measure.pi fun _ : T => μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with a ha
    simp only [indicator, hμ, restrict_compl_convexHull hK hK1 ha]
  have h2 : ∫⁻ a, (ciSet T).indicator (fun a => (1 - hullArea a) ^ (n - k)) a
      ∂(Measure.pi fun _ : T => μ) = emptyProb K k (n - k) := by
    -- reindex `Fin k ≃ T`
    let f : Fin k ≃ T := (T.equivFinOfCardEq hT).symm
    let E := MeasurableEquiv.piCongrLeft (fun _ : T => ℝ × ℝ) f
    have hf : MeasurePreserving E (Measure.pi fun _ : Fin k => μ)
        (Measure.pi fun _ : T => μ) :=
      measurePreserving_piCongrLeft (fun _ : T => μ) f
    have hE : ∀ q : Fin k → ℝ × ℝ, E q = q ∘ f.symm := by
      intro q
      funext i
      obtain ⟨i', rfl⟩ := f.surjective i
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    rw [← hf.lintegral_comp_emb E.measurableEmbedding, emptyProb, ptLaw_def]
    congr 1
    funext q
    simp only [hE, indicator, mem_ciSet, convexIndependent_comp_equiv_iff, hullArea_comp_equiv]
  convert h1.trans h2 using 3

theorem EH_eq_choose_mul {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK1 : volume K = 1) (n k : ℕ) :
    EH K n k = n.choose k * emptyProb K k (n - k) := by
  classical
  have hcount : ∀ p : Fin n → ℝ × ℝ, (holeCount k p : ℝ≥0∞) =
      ∑ T : Finset (Fin n), {p | IsHole k p T}.indicator 1 p := by
    intro p
    rw [holeCount, Finset.card_filter]
    push_cast
    simp [indicator]
  have hT : ∀ T : Finset (Fin n), ptLaw K n {p | IsHole k p T} =
      if T.card = k then emptyProb K k (n - k) else 0 := by
    intro T
    split_ifs with h
    · exact ptLaw_isHole hK hKm hK1 T h
    · have : {p : Fin n → ℝ × ℝ | IsHole k p T} = ∅ := by
        ext p
        simp [IsHole, h]
      rw [this, measure_empty]
  rw [EH]
  simp_rw [hcount]
  rw [lintegral_finsetSum _ fun T _ => measurable_one.indicator (measurableSet_isHole k T)]
  simp_rw [lintegral_indicator_one (measurableSet_isHole k _), hT]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun T : Finset (Fin n) => T.card = k) =
      Finset.powersetCard k Finset.univ := by
    ext T
    simp
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end KHoles
