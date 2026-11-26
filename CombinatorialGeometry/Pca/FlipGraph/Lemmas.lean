/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): basic facts on interiors, flips and isomorphisms

* `inside_iff`: `Inside` via any side function.
* `inside_α`: crossing a segment changes the interior status exactly for the curve of the segment.
* `flip_inside`: after the flip of a triangle `T`, every cell `f ≠ T` keeps its interior status for
  every curve, and `T` switches it exactly for its three curves (FROS: a triangle flip moves a
  pseudocircle over the crossing of two others).
* `flipStep_symm`: the flip graph is undirected (flipping the flipped triangle gives back `M`).
* isomorphisms: equivalence relation, flips can be transported along isomorphisms.
-/
import Pca.FlipGraph.FlipSide
import Pca.FlipGraph.FlipSymm
import Pca.FlipGraph.IsoMap

open Equiv Finset

namespace Pca.FlipGraph

universe u v w

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Marked

variable (M : Marked n D)

theorem inside_iff {C : Fin n} {s : M.A.Cell → ZMod 2} (hs : M.A.IsSide C s) (f : M.A.Cell) :
    M.Inside C f ↔ s f ≠ s M.z := by
  refine ⟨fun h => h s hs, fun h s' hs' => ?_⟩
  rcases hs.eq_or_eq_add_one hs' with rfl | rfl
  · exact h
  · intro h'
    exact h (add_right_cancel h')

theorem not_inside_z (C : Fin n) : ¬ M.Inside C M.z := by
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  exact fun h => h s hs rfl

/-- Crossing the segment of `y` changes the interior status exactly for the curve of `y`. -/
theorem inside_α (C : Fin n) (y : D) :
    M.Inside C (M.A.cellOf (M.A.α y)) ↔ (M.Inside C (M.A.cellOf y) ↔ M.A.curve y ≠ C) := by
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  rw [M.inside_iff hs, M.inside_iff hs]
  have h := hs y
  have h' := Arrangement.zmod2_eq_add_of_add_eq h
  rw [h']
  generalize s (M.A.cellOf y) = a
  generalize s M.z = b
  by_cases hc : M.A.curve y = C
  · rw [if_pos hc]; simp only [hc, ne_eq, not_true_eq_false, iff_false, not_not]; revert a b; decide
  · rw [if_neg hc]; simp [hc]

end Marked

/-- The marked arrangement after the flip of the triangle `cellOf d` (only meaningful for
`cellOf d ≠ M.z`). -/
def Marked.flip (M : Marked n D) (d : D) (hT : M.A.IsTriangle (M.A.cellOf d)) : Marked n D :=
  ⟨M.A.flip d hT, Arrangement.flipCellEquiv hT M.z⟩

/-- **Interiors after a flip.** A cell `f ≠ T` keeps its interior status for every curve; the
triangle `T` switches it exactly for the curves of its sides. -/
theorem flip_inside (M : Marked n D) {d : D} (hT : M.A.IsTriangle (M.A.cellOf d))
    (hz : M.A.cellOf d ≠ M.z) (C : Fin n) (f : M.A.Cell) :
    (M.flip d hT).Inside C (Arrangement.flipCellEquiv hT f) ↔
      (M.Inside C f ↔ ¬ (f = M.A.cellOf d ∧ M.HasSideOn C (M.A.cellOf d))) := by
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  have hs' := flip_isSide hT hs
  refine ((M.flip d hT).inside_iff hs' _).trans ?_
  rw [M.inside_iff hs]
  change flipSide hT C s _ ≠ flipSide hT C s (Arrangement.flipCellEquiv hT M.z) ↔ _
  simp only [flipSide, Equiv.symm_apply_apply, flipCorr]
  rw [if_neg (show ¬ (M.z = M.A.cellOf d ∧ ∃ y ∈ (M.A.cellOf d).darts, M.A.curve y = C) from
    fun h => hz h.1.symm), add_zero]
  unfold Marked.HasSideOn
  by_cases hc : f = M.A.cellOf d ∧ ∃ y ∈ (M.A.cellOf d).darts, M.A.curve y = C
  · rw [if_pos hc]
    simp only [hc, not_true_eq_false, iff_false, ne_eq, not_not, and_self]
    generalize s (M.A.cellOf d) = a; generalize s M.z = b; revert a b; decide
  · rw [if_neg hc, add_zero]
    simp only [hc, not_false_eq_true, iff_true]

/-- Two marked arrangements are equal if the arrangements are and the marked cells share a dart. -/
theorem Marked.ext_cellOf {M N : Marked n D} (h : M.A = N.A)
    (hz : ∃ y, M.A.cellOf y = M.z ∧ N.A.cellOf y = N.z) : M = N := by
  obtain ⟨A, z⟩ := M
  obtain ⟨B, w⟩ := N
  obtain ⟨y, hy, hy'⟩ := hz
  change A = B at h
  subst h
  change A.cellOf y = z at hy
  change A.cellOf y = w at hy'
  rw [← hy, ← hy']

/-- **The flip graph is undirected**: flipping the flipped triangle gives back the arrangement. -/
theorem flipStep_symm {M M' : Marked n D} (h : FlipStep M M') : FlipStep M' M := by
  obtain ⟨d, hT, hz, rfl⟩ := h
  refine ⟨M.A.σ (M.A.σ d), flip_tri' hT, ?_, ?_⟩
  · change (M.A.flip d hT).cellOf (M.A.σ (M.A.σ d)) ≠ Arrangement.flipCellEquiv hT M.z
    rw [Arrangement.flip_cellOf_σσ]
    exact fun h => hz ((Arrangement.flipCellEquiv hT).injective h)
  · obtain ⟨y, hy⟩ := M.z.exists_mk
    refine Marked.ext_cellOf (flip_flip hT).symm ⟨y, hy, ?_⟩
    rw [flip_flip_cellOf hT y]
    exact congrArg _ (congrArg _ hy)

theorem cylStep_symm {M M' : Marked n D} (h : CylStep M M') : CylStep M' M :=
  ⟨flipStep_symm h.1, h.2.2, h.2.1⟩

theorem reach_symm {M M' : Marked n D} (h : Reach M M') : Reach M' M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (flipStep_symm hs)).trans ih

theorem cylReach_symm {M M' : Marked n D} (h : CylReach M M') : CylReach M' M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (cylStep_symm hs)).trans ih

/-! ## Isomorphisms -/

section Iso

variable {D' : Type v} [Fintype D'] [DecidableEq D'] {D'' : Type w} [Fintype D'']
  [DecidableEq D'']

theorem IsIso.refl (M : Marked n D) : IsIso M M :=
  ⟨⟨Equiv.refl D, 1, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h⟩⟩

/-- The marked cell of `M'` consists of the images of the darts of the marked cell of `M`. -/
theorem Iso.cellOf_eq_z {M : Marked n D} {M' : Marked n D'} (I : Iso M M') (y : D) :
    M'.A.cellOf (I.e y) = M'.z ↔ M.A.cellOf y = M.z := by
  obtain ⟨y₀, hy₀⟩ := M.z.exists_mk
  have h₀ : M'.A.cellOf (I.e y₀) = M'.z := I.map_z y₀ hy₀
  change M.A.cellOf y₀ = M.z at hy₀
  rw [← h₀, ← hy₀]
  exact map_cellOf_eq_iff I.e I.map_σ I.map_α

theorem IsIso.symm {M : Marked n D} {M' : Marked n D'} (h : IsIso M M') : IsIso M' M := by
  obtain ⟨I⟩ := h
  have hσ : ∀ d, I.e.symm (M'.A.σ d) = M.A.σ (I.e.symm d) := fun d => I.e.injective (by
    rw [Equiv.apply_symm_apply, I.map_σ, Equiv.apply_symm_apply])
  have hα : ∀ d, I.e.symm (M'.A.α d) = M.A.α (I.e.symm d) := fun d => I.e.injective (by
    rw [Equiv.apply_symm_apply, I.map_α, Equiv.apply_symm_apply])
  refine ⟨⟨I.e.symm, I.π.symm, hσ, hα, fun d => ?_, fun d hd => ?_⟩⟩
  · rw [Equiv.eq_symm_apply, ← I.map_curve, Equiv.apply_symm_apply]
  · rw [← I.cellOf_eq_z, Equiv.apply_symm_apply]; exact hd

theorem IsIso.trans {M : Marked n D} {M' : Marked n D'} {M'' : Marked n D''} (h : IsIso M M')
    (h' : IsIso M' M'') : IsIso M M'' := by
  obtain ⟨I⟩ := h
  obtain ⟨J⟩ := h'
  refine ⟨⟨I.e.trans J.e, I.π.trans J.π, fun d => ?_, fun d => ?_, fun d => ?_, fun d hd => ?_⟩⟩
  · simp only [Equiv.trans_apply, I.map_σ, J.map_σ]
  · simp only [Equiv.trans_apply, I.map_α, J.map_α]
  · simp only [Equiv.trans_apply, I.map_curve, J.map_curve]
  · exact J.map_z _ (I.map_z d hd)

/-- Isomorphisms preserve cylindricity. -/
theorem IsIso.cylindrical {M : Marked n D} {M' : Marked n D'} (h : IsIso M M')
    (hc : M.Cylindrical) : M'.Cylindrical := by
  obtain ⟨I⟩ := h
  obtain ⟨p, hp⟩ := hc
  obtain ⟨y, rfl⟩ := p.exists_mk
  refine ⟨M'.A.cellOf (I.e y), fun C' s' hs' => ?_⟩
  set s : M.A.Cell → ZMod 2 := fun f => s' (cellMap I.e (map_φ I.e I.map_σ I.map_α) f)
  have hs : M.A.IsSide (I.π.symm C') s := by
    intro x
    change s' (M'.A.cellOf (I.e x)) + s' (M'.A.cellOf (I.e (M.A.α x))) = _
    rw [I.map_α, hs' (I.e x), I.map_curve]
    simp only [Equiv.eq_symm_apply]
  obtain ⟨y₀, hy₀⟩ := M.z.exists_mk
  have hz : s M.z = s' M'.z := by
    rw [← hy₀]; exact congrArg s' (I.map_z y₀ hy₀)
  have := hp _ s hs
  rw [hz] at this
  exact this

/-- **Flips can be transported along isomorphisms.** -/
theorem IsIso.flipStep {M : Marked n D} {N N' : Marked n D'} (h : IsIso M N)
    (hs : FlipStep N N') : ∃ M', FlipStep M M' ∧ IsIso M' N' := by
  obtain ⟨I⟩ := h
  obtain ⟨d', hT', hz', rfl⟩ := hs
  obtain ⟨d, rfl⟩ := I.e.surjective d'
  have hT : M.A.IsTriangle (M.A.cellOf d) := by
    unfold Arrangement.IsTriangle Arrangement.IsKCell
    rw [← size_cellOf_map I.e I.map_σ I.map_α]; exact hT'
  have hz : M.A.cellOf d ≠ M.z := fun h => hz' ((I.cellOf_eq_z d).2 h)
  refine ⟨M.flip d hT, ⟨d, hT, hz, rfl⟩, ⟨⟨I.e, I.π, I.map_σ, fun y => ?_, I.map_curve,
    fun y hy => ?_⟩⟩⟩
  · exact flipα_map I.e I.map_σ I.map_α hT y
  · change (M.A.flip d hT).cellOf y = Arrangement.flipCellEquiv hT M.z at hy
    change (N.A.flip (I.e d) hT').cellOf (I.e y) = Arrangement.flipCellEquiv hT' N.z
    rw [Arrangement.flip_cellOf] at hy ⊢
    rw [← flipG'_map I.e I.map_σ I.map_α]
    have := (Arrangement.flipCellEquiv hT).injective hy
    rw [(I.cellOf_eq_z _).2 this]

theorem IsIso.reach {M : Marked n D} {N N' : Marked n D'} (h : IsIso M N) (hr : Reach N N') :
    ∃ M', Reach M M' ∧ IsIso M' N' := by
  induction hr with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, h⟩
  | tail _ hs ih =>
    obtain ⟨M₁, hM₁, hi⟩ := ih
    obtain ⟨M₂, hM₂, hi₂⟩ := hi.flipStep hs
    exact ⟨M₂, hM₁.tail hM₂, hi₂⟩

theorem IsIso.cylReach {M : Marked n D} {N N' : Marked n D'} (h : IsIso M N)
    (hr : CylReach N N') : ∃ M', CylReach M M' ∧ IsIso M' N' := by
  induction hr with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, h⟩
  | tail _ hs ih =>
    obtain ⟨M₁, hM₁, hi⟩ := ih
    obtain ⟨M₂, hM₂, hi₂⟩ := hi.flipStep hs.1
    have hc₁ : M₁.Cylindrical := hi.symm.cylindrical hs.2.1
    have hc₂ : M₂.Cylindrical := hi₂.symm.cylindrical hs.2.2
    exact ⟨M₂, hM₁.tail ⟨hM₂, hc₁, hc₂⟩, hi₂⟩

end Iso

end Pca.FlipGraph
