/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): cycles from predecessors, and shortcuts

* `cyc_of_pred`: following a predecessor map from a vertex gives a simple directed cycle (first
  repetition) that follows the map.
* `exists_smaller` (FROS: "a directed cycle such that the enclosed area is minimal"): a cycle that
  is not tight (`Cyc.Good`) has a cycle with a smaller region. A forward dart `y` off the cycle
  arrives at the vertex `v` of the cycle from the region; walking back along its chord, the chord
  enters the region at a vertex `u` of the cycle (the foot is outside the region); the piece from
  `u` to `v` together with the cycle from `v` back to `u` is the new cycle (built with
  `cyc_of_pred`); it uses a dart of the piece, whose cells both lie in the old region, and its
  region lies in the old one (`Cyc.cut_le`).
-/
import Pca.FlipGraph.CycleCell

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} {Λ : Lens A}

/-- **A cycle from a predecessor map.** -/
theorem cyc_of_pred (P : A.Crossing → Prop) (p : A.Crossing → D)
    (hp : ∀ x, P x → Λ.Fwd (p x) ∧ A.crossingOf (A.α (p x)) = x ∧ P (A.crossingOf (p x)) ∧
      Λ.IsVertex x)
    {x₀ : A.Crossing} (h₀ : P x₀) :
    ∃ Z : Λ.Cyc, ∀ i, P (A.crossingOf (A.α (Z.z i))) ∧ Z.z i = p (A.crossingOf (A.α (Z.z i))) := by
  classical
  let f : ℕ → A.Crossing := fun m => Nat.rec x₀ (fun _ x => A.crossingOf (p x)) m
  have f0 : f 0 = x₀ := rfl
  have fs : ∀ m, f (m + 1) = A.crossingOf (p (f m)) := fun m => rfl
  have hf : ∀ m, P (f m) := fun m => by
    induction m with
    | zero => exact h₀
    | succ m ih => rw [fs]; exact (hp _ ih).2.2.1
  have hex : ∃ j, ∃ i < j, f i = f j := by
    obtain ⟨a, b, he, hab⟩ := Function.not_injective_iff.1 (not_injective_infinite_finite f)
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, a, h, he⟩
    · exact ⟨a, b, h, he.symm⟩
  haveI : DecidablePred (fun j => ∃ i < j, f i = f j) := Classical.decPred _
  obtain ⟨i, hij, hfij⟩ := Nat.find_spec hex
  have hmin : ∀ a b, a < b → b < Nat.find hex → f a ≠ f b := fun a b hab hb he =>
    Nat.find_min hex hb ⟨a, hab, he⟩
  generalize Nat.find hex = j at hij hfij hmin
  -- the vertex `f m` is the end of `p (f m)`
  have hend : ∀ m, A.crossingOf (A.α (p (f m))) = f m := fun m => (hp _ (hf m)).2.1
  have hk1 : 1 < j - i := by
    by_contra h
    have : j = i + 1 := by omega
    rw [this, fs] at hfij
    exact A.crossingOf_α_ne _ ((hend i).trans hfij)
  haveI : NeZero (j - i) := ⟨by omega⟩
  haveI : Fact (1 < j - i) := ⟨hk1⟩
  have hval : ∀ t : ZMod (j - i), t.val < j - i := fun t => ZMod.val_lt t
  let z : ZMod (j - i) → D := fun t => p (f (j - 1 - t.val))
  have hzx : ∀ t, A.crossingOf (z t) = f (j - t.val) := fun t => by
    have := hval t
    show A.crossingOf (p (f (j - 1 - t.val))) = _
    rw [← fs, show j - 1 - t.val + 1 = j - t.val by omega]
  have hzα : ∀ t, A.crossingOf (A.α (z t)) = f (j - 1 - t.val) := fun t => hend _
  refine ⟨⟨j - i, hk1, z, fun t => (hp _ (hf _)).1, fun t => ?_, fun t s hts => ?_,
    fun t => ?_⟩, fun t => ⟨?_, ?_⟩⟩
  · rw [hzα, hzx]
    have h1 := hval t
    rw [ZMod.val_add, ZMod.val_one]
    by_cases hlt : t.val + 1 < j - i
    · rw [Nat.mod_eq_of_lt hlt]; congr 1; omega
    · have : t.val + 1 = j - i := by omega
      rw [this, Nat.mod_self, Nat.sub_zero, show j - 1 - t.val = i by omega, hfij]
  · rw [hzx, hzx] at hts
    have ht1 := hval t
    have hs1 := hval s
    apply ZMod.val_injective
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rcases Nat.eq_zero_or_pos t.val with h0 | h0
      · rw [h0, Nat.sub_zero, ← hfij] at hts
        exact hmin i (j - s.val) (by omega) (by omega) hts
      · exact hmin (j - s.val) (j - t.val) (by omega) (by omega) hts.symm
    · rcases Nat.eq_zero_or_pos s.val with h0 | h0
      · rw [h0, Nat.sub_zero, ← hfij] at hts
        exact hmin i (j - t.val) (by omega) (by omega) hts.symm
      · exact hmin (j - t.val) (j - s.val) (by omega) (by omega) hts
  · rw [hzx]; exact (hp _ (hf _)).2.2.2
  · rw [hzα]; exact hf _
  · rw [hzα]

end Lens

end Pca.FlipGraph
