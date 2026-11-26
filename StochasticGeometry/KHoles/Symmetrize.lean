/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null sets, permutations and sorting of point families

Helper results for Steps 3–5 of `doc/kholes/kholes.md` (file `Symmetrize`, wave 1):

* `lintegral_comp_perm_pi`: integrals over `ι → X` w.r.t. a product measure are invariant
  under permuting the coordinates.
* `ae_fst_ne`, `ae_snd_ne`, `ae_injective_fst`: almost every family `z : Fin m → ℝ × ℝ` avoids
  a given vertical/horizontal line and has pairwise distinct abscissae.
* `measurableSet_strictMono_fst`, `lintegral_eq_factorial_mul_sorted`: the integral of a
  permutation symmetric function is `m!` times the integral over the families with strictly
  increasing abscissae (via `Tuple.sort`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Permuting coordinates -/

theorem lintegral_comp_perm_pi {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (f : (ι → X) → ℝ≥0∞) :
    ∫⁻ z, f (z ∘ σ) ∂Measure.pi (fun _ => μ) = ∫⁻ z, f z ∂Measure.pi (fun _ => μ) := by
  classical
  let E : (ι → X) ≃ᵐ (ι → X) := MeasurableEquiv.piCongrLeft (fun _ => X) σ.symm
  have hE : ∀ z, E z = z ∘ σ := by
    intro z
    funext i
    have := Equiv.piCongrLeft_apply_apply (P := fun _ : ι => X) σ.symm z (σ i)
    simpa [E, MeasurableEquiv.coe_piCongrLeft] using this
  have hmp : MeasurePreserving E (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
    measurePreserving_piCongrLeft (fun _ => μ) σ.symm
  simp_rw [← hE]
  exact hmp.lintegral_comp_emb E.measurableEmbedding f

/-! ### Null sets -/

lemma volume_fst_eq (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.1 = c} = 0 := by
  have : {p : ℝ × ℝ | p.1 = c} = {c} ×ˢ univ := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]
  simp

lemma volume_snd_eq (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.2 = c} = 0 := by
  have : {p : ℝ × ℝ | p.2 = c} = univ ×ˢ {c} := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem ae_fst_ne (m : ℕ) (c : ℝ) : ∀ᵐ z : Fin m → ℝ × ℝ, ∀ i, (z i).1 ≠ c := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact Measure.pi_eval_preimage_null (μ := fun _ : Fin m => (volume : Measure (ℝ × ℝ)))
    (i := i) (volume_fst_eq c)

theorem ae_snd_ne (m : ℕ) (c : ℝ) : ∀ᵐ z : Fin m → ℝ × ℝ, ∀ i, (z i).2 ≠ c := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact Measure.pi_eval_preimage_null (μ := fun _ : Fin m => (volume : Measure (ℝ × ℝ)))
    (i := i) (volume_snd_eq c)

/-- For `i ≠ j`, the hyperplane `{z | (z i).1 = (z j).1}` is null. -/
lemma volume_fst_eq_fst {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (volume : Measure (Fin m → ℝ × ℝ)) {z | (z i).1 = (z j).1} = 0 := by
  classical
  let φ : (Fin m → ℝ × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.proj i) - (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.proj j)
  have hset : {z : Fin m → ℝ × ℝ | (z i).1 = (z j).1} = (LinearMap.ker φ : Set _) := by
    ext z
    simp [φ, sub_eq_zero]
  have hne : LinearMap.ker φ ≠ ⊤ := by
    intro h
    have hz : (Pi.single i ((1 : ℝ), (0 : ℝ)) : Fin m → ℝ × ℝ) ∈ LinearMap.ker φ := by
      rw [h]; exact Submodule.mem_top
    simp [φ, hij.symm] at hz
  rw [hset]
  exact Measure.addHaar_submodule _ _ hne

theorem ae_injective_fst (m : ℕ) :
    ∀ᵐ z : Fin m → ℝ × ℝ, Function.Injective fun i => (z i).1 := by
  have h : ∀ᵐ z : Fin m → ℝ × ℝ, ∀ i j, i ≠ j → (z i).1 ≠ (z j).1 := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) (volume_fst_eq_fst hij)
      simp only [mem_ofPred_eq, not_forall, ne_eq, not_not, exists_prop] at hz
      exact hz.2
  filter_upwards [h] with z hz i j hij
  by_contra hne
  exact hz i j hne hij

/-! ### Sorting -/

lemma measurableSet_strictMono_fst_comp {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    MeasurableSet {z : Fin m → ℝ × ℝ | StrictMono fun i => (z (σ i)).1} := by
  have : {z : Fin m → ℝ × ℝ | StrictMono fun i => (z (σ i)).1} =
      ⋂ i, ⋂ j, {z | i < j → (z (σ i)).1 < (z (σ j)).1} := by
    ext z
    simp [StrictMono]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i < j
  · simp only [hij, true_imp_iff]
    exact measurableSet_lt (measurable_fst.comp (measurable_pi_apply _))
      (measurable_fst.comp (measurable_pi_apply _))
  · simp [hij]

theorem measurableSet_strictMono_fst (m : ℕ) :
    MeasurableSet {z : Fin m → ℝ × ℝ | StrictMono fun i => (z i).1} :=
  measurableSet_strictMono_fst_comp (Equiv.refl _)

/-- An injective tuple is sorted by exactly one permutation, namely `Tuple.sort`. -/
lemma strictMono_comp_iff_eq_sort {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin m)) : StrictMono (x ∘ σ) ↔ σ = Tuple.sort x := by
  constructor
  · intro h
    rw [Tuple.eq_sort_iff]
    refine ⟨h.monotone, fun i j hij hfij => ?_⟩
    exact absurd hfij (h hij).ne
  · rintro rfl
    exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Equiv.injective _))

theorem lintegral_eq_factorial_mul_sorted {m : ℕ} (f : (Fin m → ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable f)
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) (z : Fin m → ℝ × ℝ), f (z ∘ σ) = f z) :
    ∫⁻ z, f z = m.factorial * ∫⁻ z in {z | StrictMono fun i => (z i).1}, f z := by
  classical
  set S : Set (Fin m → ℝ × ℝ) := {z | StrictMono fun i => (z i).1} with hS
  let A : Equiv.Perm (Fin m) → Set (Fin m → ℝ × ℝ) :=
    fun σ => {z | StrictMono fun i => (z (σ i)).1}
  have hA : ∀ σ, MeasurableSet (A σ) := measurableSet_strictMono_fst_comp
  -- pointwise: for injective abscissae, exactly one piece contains `z`
  have hsum : ∀ᵐ z : Fin m → ℝ × ℝ, f z = ∑ σ, (A σ).indicator f z := by
    filter_upwards [ae_injective_fst m] with z hz
    have : ∀ σ, (A σ).indicator f z = if σ = Tuple.sort (fun i => (z i).1) then f z else 0 := by
      intro σ
      by_cases h : σ = Tuple.sort (fun i => (z i).1)
      · have hmem : z ∈ A σ := (strictMono_comp_iff_eq_sort hz σ).2 h
        rw [indicator_of_mem hmem, if_pos h]
      · have hmem : z ∉ A σ := fun hm => h ((strictMono_comp_iff_eq_sort hz σ).1 hm)
        rw [indicator_of_notMem hmem, if_neg h]
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- each piece is the sorted piece after permuting the coordinates
  have hpiece : ∀ σ, ∫⁻ z, (A σ).indicator f z = ∫⁻ z, S.indicator f z := by
    intro σ
    have h1 : ∀ z, (A σ).indicator f z = S.indicator f (z ∘ σ) := by
      intro z
      by_cases h : z ∈ A σ
      · have h' : z ∘ σ ∈ S := h
        rw [indicator_of_mem h, indicator_of_mem h', hsymm]
      · have h' : z ∘ σ ∉ S := h
        rw [indicator_of_notMem h, indicator_of_notMem h']
    simp_rw [h1]
    exact lintegral_comp_perm_pi (volume : Measure (ℝ × ℝ)) σ (S.indicator f)
  rw [lintegral_congr_ae hsum, lintegral_finsetSum _ fun σ _ => hf.indicator (hA σ)]
  simp_rw [hpiece]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    lintegral_indicator (measurableSet_strictMono_fst m)]

end KHoles
