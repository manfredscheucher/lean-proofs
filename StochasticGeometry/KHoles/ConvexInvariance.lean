/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.Analysis.Convex.Independent
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.GroupTheory.Perm.Fin

/-!
# Invariance of convex independence and hull area

Step 1 support of `doc/kholes/kholes.md` (wave 1, §3.1 `ConvexInvariance.lean`):
convex independence (`ConvexIndependent ℝ`) and the hull area `hullArea` of a finite family of
points are invariant under reindexing by an equivalence, and behave as expected under
injective affine maps `x ↦ c + L x` (convex independence is preserved, the area is multiplied
by `|det L|`). Specialisations to the base configuration `baseCfg z = ((0,0), (1,0), z …)`:
permuting `z` and the vertical scaling `vscale s z`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Reindexing -/

theorem convexIndependent_comp_equiv_iff {ι ι' : Type*} (e : ι' ≃ ι) (q : ι → ℝ × ℝ) :
    ConvexIndependent ℝ (q ∘ e) ↔ ConvexIndependent ℝ q := by
  refine ⟨fun h => ?_, fun h => h.comp_embedding e.toEmbedding⟩
  have := h.comp_embedding e.symm.toEmbedding
  convert this using 1
  funext i
  simp

theorem hullArea_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (q : ι → ℝ × ℝ) :
    hullArea (q ∘ e) = hullArea q := by
  simp only [hullArea, EquivLike.range_comp]

theorem convexIndependent_iff_set {ι : Type*} (q : ι → ℝ × ℝ) :
    ConvexIndependent ℝ q ↔
      Function.Injective q ∧ ∀ x ∈ range q, x ∉ convexHull ℝ (range q \ {x}) := by
  constructor
  · intro h
    exact ⟨h.injective, convexIndependent_set_iff_notMem_convexHull_sdiff.mp h.range⟩
  · rintro ⟨hi, h⟩
    exact hi.convexIndependent_iff_set.mp (convexIndependent_set_iff_notMem_convexHull_sdiff.mpr h)

/-! ### Affine maps -/

/-- The affine map `x ↦ c + L x`. -/
private noncomputable def affOf (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  (AffineEquiv.constVAdd ℝ (ℝ × ℝ) c).toAffineMap.comp L.toAffineMap

private lemma affOf_apply (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (c x : ℝ × ℝ) :
    affOf L c x = c + L x := rfl

theorem convexIndependent_affine_iff {ι : Type*} (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hL : Function.Injective L) (c : ℝ × ℝ) (q : ι → ℝ × ℝ) :
    ConvexIndependent ℝ (fun i => c + L (q i)) ↔ ConvexIndependent ℝ q := by
  set f := affOf L c
  have hf : Function.Injective f := fun x y hxy => hL (add_left_cancel hxy)
  have himg : ∀ s : Set ι, convexHull ℝ ((fun i => c + L (q i)) '' s) =
      f '' convexHull ℝ (q '' s) := fun s => by
    rw [AffineMap.image_convexHull, image_image]
    rfl
  constructor
  · intro h s i hi
    apply h s i
    rw [himg]
    exact mem_image_of_mem f hi
  · intro h s i hi
    apply h s i
    rw [himg] at hi
    exact hf.mem_set_image.mp hi

theorem hullArea_affine {ι : Type*} (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (c : ℝ × ℝ) (q : ι → ℝ × ℝ) :
    hullArea (fun i => c + L (q i)) = ENNReal.ofReal |LinearMap.det L| * hullArea q := by
  have hr : range (fun i => c + L (q i)) = affOf L c '' range q := by
    rw [← range_comp]
    rfl
  have hS : affOf L c '' convexHull ℝ (range q) =
      (fun x => c + x) '' (L '' convexHull ℝ (range q)) := by
    rw [image_image]
    rfl
  rw [hullArea, hr, ← AffineMap.image_convexHull, hS, image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, hullArea]

/-! ### The base configuration -/

/-- The permutation of `Fin (m + 2)` fixing `0` and `1` and acting as `σ` on the rest. -/
private def liftPerm2 {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))

private lemma baseCfg_comp_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : Fin m → ℝ × ℝ) :
    baseCfg (z ∘ σ) = baseCfg z ∘ liftPerm2 σ := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp [liftPerm2]
  · simp [liftPerm2, Equiv.Perm.decomposeFin_symm_apply_zero]
  · simp [liftPerm2, Equiv.Perm.decomposeFin_symm_apply_succ]

theorem convexIndependent_baseCfg_comp_perm {m : ℕ} (σ : Equiv.Perm (Fin m))
    (z : Fin m → ℝ × ℝ) :
    ConvexIndependent ℝ (baseCfg (z ∘ σ)) ↔ ConvexIndependent ℝ (baseCfg z) := by
  rw [baseCfg_comp_perm]
  exact convexIndependent_comp_equiv_iff _ _

theorem hullArea_baseCfg_comp_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : Fin m → ℝ × ℝ) :
    hullArea (baseCfg (z ∘ σ)) = hullArea (baseCfg z) := by
  rw [baseCfg_comp_perm]
  exact hullArea_comp_equiv _ _

/-- Local copy of `det_vscaleLin` (the exported one lives in `PiLinear.lean`). -/
private lemma det_vscaleLin_local (s : ℝ) : LinearMap.det (vscaleLin s) = s := by
  rw [vscaleLin, LinearMap.det_prodMap]
  simp

private lemma baseCfg_vscale {m : ℕ} (s : ℝ) (z : Fin m → ℝ × ℝ) :
    baseCfg (vscale s z) = fun i => 0 + vscaleLin s (baseCfg z i) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
    simp [vscaleLin_apply, baseCfg, cons2]

theorem convexIndependent_baseCfg_vscale {m : ℕ} {s : ℝ} (hs : s ≠ 0) (z : Fin m → ℝ × ℝ) :
    ConvexIndependent ℝ (baseCfg (vscale s z)) ↔ ConvexIndependent ℝ (baseCfg z) := by
  rw [baseCfg_vscale]
  refine convexIndependent_affine_iff _ (fun x y hxy => ?_) 0 _
  rw [vscaleLin_apply, vscaleLin_apply] at hxy
  obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
  exact Prod.ext h1 (mul_left_cancel₀ hs h2)

theorem hullArea_baseCfg_vscale {m : ℕ} (s : ℝ) (z : Fin m → ℝ × ℝ) :
    hullArea (baseCfg (vscale s z)) = ENNReal.ofReal |s| * hullArea (baseCfg z) := by
  rw [baseCfg_vscale, hullArea_affine, det_vscaleLin_local]

end KHoles
