/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Measurability and finiteness of convex hulls (stage 4, wave 1)

Basic topological and measure-theoretic facts about convex hulls of finite point families in
`ℝ × ℝ`, used throughout stage 4 of `doc/kholes/kholes.md` (Steps 1–5):

* the hull of `range q` is the image of the standard simplex, and the set
  `{(q, r) | r ∈ convexHull (range q)}` is closed (`isClosed_mem_convexHull_range`);
* convex independence as "no point in the hull of the others", hence `ciSet ι` is open
  (`isOpen_ciSet`) and measurable;
* `hullArea` is measurable, finite, and bounded by `volume K` for points in a convex `K`;
* continuity of `cons2`/`baseCfg`, measurability of the diameter events `IsDiamLE`/`IsDiamLT`,
  and of the sets `limSet m`, `upperSet m` (both are open).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Hull of a finite family as image of the standard simplex -/

theorem convexHull_range_eq_image {ι : Type*} [Fintype ι] (q : ι → ℝ × ℝ) :
    convexHull ℝ (range q) = (fun w : ι → ℝ => ∑ i, w i • q i) '' stdSimplex ℝ ι := by
  classical
  let L : (ι → ℝ) →ₗ[ℝ] ℝ × ℝ := ∑ i, (LinearMap.proj i).smulRight (q i)
  have hL : ∀ w, L w = ∑ i, w i • q i := fun w => by simp [L]
  rw [← convexHull_basis_eq_stdSimplex, ← funext hL, LinearMap.image_convexHull, ← range_comp]
  congr 2
  funext j
  simp [Function.comp, L, Finset.sum_ite_eq]

theorem isClosed_mem_convexHull_range (ι : Type*) [Fintype ι] :
    IsClosed {p : (ι → ℝ × ℝ) × (ℝ × ℝ) | p.2 ∈ convexHull ℝ (range p.1)} := by
  have : CompactSpace (stdSimplex ℝ ι) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)
  have hZ : IsClosed {x : stdSimplex ℝ ι × ((ι → ℝ × ℝ) × (ℝ × ℝ)) |
      ∑ i, (x.1 : ι → ℝ) i • x.2.1 i = x.2.2} :=
    isClosed_eq (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
      (continuous_snd.comp continuous_snd)
  convert isClosedMap_snd_of_compactSpace _ hZ using 1
  ext ⟨q, r⟩
  constructor
  · rintro hr
    rw [mem_ofPred_eq, convexHull_range_eq_image] at hr
    obtain ⟨w, hw, hr⟩ := hr
    exact ⟨(⟨w, hw⟩, (q, r)), hr, rfl⟩
  · rintro ⟨⟨⟨w, hw⟩, ⟨q', r'⟩⟩, h, h'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    rw [mem_ofPred_eq, convexHull_range_eq_image]
    exact ⟨w, hw, h⟩

theorem measurableSet_mem_convexHull_range (ι : Type*) [Fintype ι] :
    MeasurableSet {p : (ι → ℝ × ℝ) × (ℝ × ℝ) | p.2 ∈ convexHull ℝ (range p.1)} :=
  (isClosed_mem_convexHull_range ι).measurableSet

/-! ### Convex independence is an open condition -/

theorem convexIndependent_iff_forall_notMem {ι : Type*} (q : ι → ℝ × ℝ) :
    ConvexIndependent ℝ q ↔ ∀ i, q i ∉ convexHull ℝ (q '' {i}ᶜ) := by
  rw [convexIndependent_iff_notMem_convexHull_sdiff]
  constructor
  · intro h i
    simpa [compl_eq_univ_sdiff] using h i univ
  · intro h i s hs
    exact h i (convexHull_mono (image_mono fun j hj => hj.2) hs)

/-- For fixed `i`, the set of families whose `i`-th point lies in the hull of the others is
closed. -/
lemma isClosed_mem_convexHull_compl (ι : Type*) [Fintype ι] (i : ι) :
    IsClosed {q : ι → ℝ × ℝ | q i ∈ convexHull ℝ (q '' {i}ᶜ)} := by
  classical
  have hc : Continuous fun q : ι → ℝ × ℝ =>
      ((fun j : ({i}ᶜ : Set ι) => q j), q i) := by
    fun_prop
  have := (isClosed_mem_convexHull_range ({i}ᶜ : Set ι)).preimage hc
  convert this using 1
  ext q
  simp only [mem_ofPred_eq, mem_preimage, image_eq_range]

theorem isOpen_ciSet (ι : Type*) [Fintype ι] : IsOpen (ciSet ι) := by
  have : ciSet ι = ⋂ i, {q : ι → ℝ × ℝ | q i ∈ convexHull ℝ (q '' {i}ᶜ)}ᶜ := by
    ext q
    simp [convexIndependent_iff_forall_notMem]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isClosed_mem_convexHull_compl ι i).isOpen_compl

theorem measurableSet_ciSet (ι : Type*) [Fintype ι] : MeasurableSet (ciSet ι) :=
  (isOpen_ciSet ι).measurableSet

/-! ### `hullArea`: compactness, measurability, bounds -/

theorem isCompact_convexHull_range {ι : Type*} [Finite ι] (q : ι → ℝ × ℝ) :
    IsCompact (convexHull ℝ (range q)) :=
  (finite_range q).isCompact_convexHull ℝ

theorem measurable_hullArea (ι : Type*) [Fintype ι] :
    Measurable (hullArea : (ι → ℝ × ℝ) → ℝ≥0∞) :=
  measurable_measure_prodMk_left (measurableSet_mem_convexHull_range ι)

theorem hullArea_lt_top {ι : Type*} [Finite ι] (q : ι → ℝ × ℝ) : hullArea q < ⊤ :=
  (isCompact_convexHull_range q).measure_lt_top

theorem convexHull_range_subset {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {ι : Type*}
    {q : ι → ℝ × ℝ} (hq : ∀ i, q i ∈ K) : convexHull ℝ (range q) ⊆ K :=
  convexHull_min (range_subset_iff.2 hq) hK

theorem hullArea_le {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {ι : Type*} {q : ι → ℝ × ℝ}
    (hq : ∀ i, q i ∈ K) : hullArea q ≤ volume K :=
  measure_mono (convexHull_range_subset hK hq)

/-! ### `cons2` and `baseCfg` -/

theorem continuous_cons2 (m : ℕ) :
    Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) × (Fin m → ℝ × ℝ) => cons2 p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => exact continuous_fst
  | succ j =>
    induction j using Fin.cases with
    | zero => exact continuous_snd.fst
    | succ k => exact (continuous_apply k).comp continuous_snd.snd

theorem continuous_baseCfg (m : ℕ) : Continuous (baseCfg : (Fin m → ℝ × ℝ) → _) :=
  (continuous_cons2 m).comp (f := fun z : Fin m → ℝ × ℝ => (((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), z))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))

theorem measurable_hullArea_baseCfg (m : ℕ) :
    Measurable fun z : Fin m → ℝ × ℝ => hullArea (baseCfg z) :=
  (measurable_hullArea _).comp (continuous_baseCfg m).measurable

/-! ### Diameter events -/

lemma continuous_sqDist_apply {k : ℕ} (c : ℝ) (a b : Fin k) :
    Continuous fun q : Fin k → ℝ × ℝ => sqDist c (q a) (q b) := by
  unfold sqDist
  fun_prop

theorem measurableSet_isDiamLE {k : ℕ} (c : ℝ) (i j : Fin k) :
    MeasurableSet {q : Fin k → ℝ × ℝ | IsDiamLE c q i j} := by
  have : {q : Fin k → ℝ × ℝ | IsDiamLE c q i j} =
      ⋂ a, ⋂ b, {q | sqDist c (q a) (q b) ≤ sqDist c (q i) (q j)} := by
    ext q
    simp only [IsDiamLE, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_le (continuous_sqDist_apply c a b).measurable
      (continuous_sqDist_apply c i j).measurable

theorem measurableSet_isDiamLT {k : ℕ} (c : ℝ) (i j : Fin k) :
    MeasurableSet {q : Fin k → ℝ × ℝ | IsDiamLT c q i j} := by
  have : {q : Fin k → ℝ × ℝ | IsDiamLT c q i j} =
      ⋂ a, ⋂ b, {q | a ≠ b → (a, b) ≠ (i, j) → (a, b) ≠ (j, i) →
        sqDist c (q a) (q b) < sqDist c (q i) (q j)} := by
    ext q
    simp only [IsDiamLT, mem_iInter, mem_ofPred_eq]
  rw [this]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  by_cases h : a ≠ b ∧ (a, b) ≠ (i, j) ∧ (a, b) ≠ (j, i)
  · obtain ⟨h1, h2, h3⟩ := h
    have hs : {q : Fin k → ℝ × ℝ | a ≠ b → (a, b) ≠ (i, j) → (a, b) ≠ (j, i) →
        sqDist c (q a) (q b) < sqDist c (q i) (q j)} =
        {q | sqDist c (q a) (q b) < sqDist c (q i) (q j)} := by
      ext q
      exact ⟨fun hq => hq h1 h2 h3, fun hq _ _ _ => hq⟩
    rw [hs]
    exact measurableSet_lt (continuous_sqDist_apply c a b).measurable
      (continuous_sqDist_apply c i j).measurable
  · have hs : {q : Fin k → ℝ × ℝ | a ≠ b → (a, b) ≠ (i, j) → (a, b) ≠ (j, i) →
        sqDist c (q a) (q b) < sqDist c (q i) (q j)} = univ := by
      ext q
      exact ⟨fun _ => trivial, fun _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
    rw [hs]
    exact MeasurableSet.univ

/-! ### The sets `limSet` and `upperSet` are open -/

lemma isOpen_limSet (m : ℕ) : IsOpen (limSet m) := by
  have : limSet m = baseCfg ⁻¹' ciSet (Fin (m + 2)) ∩
      ⋂ i, ({z : Fin m → ℝ × ℝ | 0 < (z i).1} ∩ {z | (z i).1 < 1}) := by
    ext z
    simp [limSet, forall_and]
  rw [this]
  refine ((isOpen_ciSet _).preimage (continuous_baseCfg m)).inter
    (isOpen_iInter_of_finite fun i => ?_)
  have hx : Continuous fun z : Fin m → ℝ × ℝ => (z i).1 := by fun_prop
  exact (isOpen_lt continuous_const hx).inter (isOpen_lt hx continuous_const)

lemma isOpen_upperSet (m : ℕ) : IsOpen (upperSet m) := by
  have : upperSet m = baseCfg ⁻¹' ciSet (Fin (m + 2)) ∩
      ⋂ i, ({z : Fin m → ℝ × ℝ | 0 < (z i).1} ∩ {z | (z i).1 < 1} ∩ {z | 0 < (z i).2}) := by
    ext z
    simp [upperSet, forall_and, and_assoc]
  rw [this]
  refine ((isOpen_ciSet _).preimage (continuous_baseCfg m)).inter
    (isOpen_iInter_of_finite fun i => ?_)
  have hx : Continuous fun z : Fin m → ℝ × ℝ => (z i).1 := by fun_prop
  have hy : Continuous fun z : Fin m → ℝ × ℝ => (z i).2 := by fun_prop
  exact ((isOpen_lt continuous_const hx).inter (isOpen_lt hx continuous_const)).inter
    (isOpen_lt continuous_const hy)

theorem measurableSet_limSet (m : ℕ) : MeasurableSet (limSet m) :=
  (isOpen_limSet m).measurableSet

theorem measurableSet_upperSet (m : ℕ) : MeasurableSet (upperSet m) :=
  (isOpen_upperSet m).measurableSet

end KHoles
