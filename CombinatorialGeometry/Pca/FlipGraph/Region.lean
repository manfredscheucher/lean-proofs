/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): regions of sides (Jordan-type facts)

Combinatorial replacements for the topological facts that FROS use without comment:

* `side_connected`: the cells on one side of a curve are connected in the dual graph by segments
  not on that curve (a side of a pseudocircle is connected).
* `digon_side_run`: if `g` is a digon with sides on `C` and `C'`, then the part of `C` on the side
  of `C'` containing `g` is exactly the side of `g` on `C` (one segment).
* `digon_region`: if `g` is a digon with sides on `C` and `C'`, then `g` is the only cell on its
  sides of `C` and `C'` (the region of the two-curve subarrangement containing `g` is the digon).
-/
import Pca.FlipGraph.Lemmas
import Pca.FlipGraph.SConfOf

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The cells `f` and `g` are adjacent across the segment of a dart `y` with `P y`. -/
def AdjBy (A : Arrangement n D) (P : D → Prop) (f g : A.Cell) : Prop :=
  ∃ y, P y ∧ A.cellOf y = f ∧ A.cellOf (A.α y) = g

variable {A : Arrangement n D}

open Arrangement

/-- An orbit of a permutation of period at most two. -/
theorem two_cycle {f : Perm D} {a y : D} (h : f (f a) = a) (hs : f.SameCycle a y) :
    y = a ∨ y = f a := by
  obtain ⟨k, rfl⟩ := hs.exists_nat_pow_eq
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih (Perm.SameCycle.refl f a |>.trans ⟨k, by simp⟩) with h' | h'
    · right; rw [h']
    · left; rw [h', h]

theorem eq_or_eq_α_of_segmentOf {y a : D} (h : A.segmentOf y = A.segmentOf a) :
    y = a ∨ y = A.α a :=
  two_cycle (A.α_α a) (Orbit.mk_eq_mk.1 h).symm

/-- **Cuts along one curve**: a function on the cells that changes only across segments of `C` is
constant or a side function of `C` (the segments of `C` across which it changes form a closed
walk, hence all of `C` or nothing). -/
theorem const_or_isSide (C : Fin n) (r : A.Cell → ZMod 2)
    (hr : ∀ y, A.curve y ≠ C → r (A.cellOf y) = r (A.cellOf (A.α y))) :
    (∀ f g, r f = r g) ∨ A.IsSide C r := by
  set t : D → ZMod 2 := fun y => r (A.cellOf y) + r (A.cellOf (A.α y)) with ht
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have ht0 : ∀ y, A.curve y ≠ C → t y = 0 := fun y hy => by
    simp only [ht, hr y hy, h2]
  have hσ : ∀ y, r (A.cellOf (A.σ y)) = r (A.cellOf y) + t y := fun y => by
    simp only [ht, A.cellOf_σ]
    rw [← add_assoc, h2, zero_add]
  have hα : ∀ y, t (A.α y) = t y := fun y => by simp only [ht, A.α_α, add_comm]
  have hσσ : ∀ y, A.curve y = C → t (A.σ (A.σ y)) = t y := by
    intro y hy
    have h1 := hσ y
    have h2' := hσ (A.σ y)
    have h3 := hσ (A.σ (A.σ y))
    have h4 := hσ (A.σ (A.σ (A.σ y)))
    rw [A.σ_σ_σ_σ] at h4
    have c1 : A.curve (A.σ y) ≠ C := fun h => A.isArrangement.curve_σ y (h.trans hy.symm)
    have c3 : A.curve (A.σ (A.σ (A.σ y))) ≠ C := by rw [A.curve_σσσ]; exact c1
    rw [ht0 _ c1] at h2'
    rw [ht0 _ c3] at h4
    rw [h3, h2', h1] at h4
    have key : ∀ a b c : ZMod 2, a = a + b + 0 + c + 0 → c = b := by decide
    exact key _ _ _ h4
  have hstr : ∀ y, A.curve y = C → t (A.straight y) = t y := fun y hy => by
    rw [straight_apply, hσσ _ (by rw [A.curve_α]; exact hy), hα]
  have hpow : ∀ y, A.curve y = C → ∀ k : ℕ, t ((A.straight ^ k) y) = t y := by
    intro y hy k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hc : A.curve ((A.straight ^ k) y) = C := by
        clear ih
        induction k with
        | zero => exact hy
        | succ k ihk => rw [pow_succ', Perm.mul_apply, straight_apply, A.curve_σσ, A.curve_α, ihk]
      rw [pow_succ', Perm.mul_apply, hstr _ hc, ih]
  have hconst : ∀ d e, A.curve d = C → A.curve e = C → t d = t e := by
    intro d e hd he
    rcases A.isArrangement.straight d e (hd.trans he.symm) with h | h
    · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      have hk' : (A.straight ^ k) d = e := hk
      rw [← hk', hpow d hd]
    · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      have hk' : (A.straight ^ k) d = A.σ (A.σ e) := hk
      have := hpow d hd k
      rw [hk'] at this
      rw [hσσ e he] at this
      exact this.symm
  obtain ⟨d₀, hd₀⟩ := A.exists_dart_on C
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (t d₀) with h0 | h1
  · left
    have hall : ∀ y, t y = 0 := fun y => by
      by_cases hy : A.curve y = C
      · rw [hconst y d₀ hy hd₀, h0]
      · exact ht0 y hy
    have hG := A.const_of_invariant (fun y => r (A.cellOf y))
      (fun y => by simp only [hσ, hall, add_zero])
      (fun y => by
        have := hall y
        simp only [ht] at this
        have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
        exact key _ _ this)
    intro f g
    obtain ⟨x, rfl⟩ := f.exists_mk
    obtain ⟨w, rfl⟩ := g.exists_mk
    exact hG x w
  · right
    intro y
    by_cases hy : A.curve y = C
    · rw [if_pos hy]; exact (hconst y d₀ hy hd₀).trans h1
    · rw [if_neg hy]; exact ht0 y hy

/-- **A side of a curve is connected**: two cells on the same side of `C` are joined by a dual
path that does not cross `C`. -/
theorem side_connected {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {f g : A.Cell}
    (hfg : s f = s g) : Relation.EqvGen (AdjBy A (fun y => A.curve y ≠ C)) f g := by
  classical
  set R := Relation.EqvGen (AdjBy A (fun y => A.curve y ≠ C)) f with hR
  let r : A.Cell → ZMod 2 := fun h => if R h then 1 else 0
  have hr : ∀ y, A.curve y ≠ C → r (A.cellOf y) = r (A.cellOf (A.α y)) := by
    intro y hy
    have hadj : Relation.EqvGen (AdjBy A (fun y => A.curve y ≠ C)) (A.cellOf y)
        (A.cellOf (A.α y)) := Relation.EqvGen.rel _ _ ⟨y, hy, rfl, rfl⟩
    have : R (A.cellOf y) ↔ R (A.cellOf (A.α y)) :=
      ⟨fun h => h.trans _ _ _ hadj, fun h => h.trans _ _ _ hadj.symm⟩
    simp only [r, this]
  have hf : r f = 1 := if_pos (Relation.EqvGen.refl f)
  suffices hg : r g = 1 by
    by_contra h
    simp only [r, if_neg h] at hg
    exact absurd hg (by decide)
  rcases const_or_isSide C r hr with hc | hs'
  · rw [hc g f, hf]
  · rcases hs.eq_or_eq_add_one hs' with h | h
    · rw [h] at hf ⊢; rw [← hfg]; exact hf
    · rw [h] at hf ⊢; simp only at hf ⊢; rw [← hfg]; exact hf

/-- **The side of `C'` containing a digon `g` meets `C` in the side of `g` on `C`.** Here `a` is
the dart of `g` on `C` (so `φ a` is the dart of `g` on `C'`). -/
theorem digon_side_run {a : D} (hg : A.IsDigon (A.cellOf a)) {s' : A.Cell → ZMod 2}
    (hs' : A.IsSide (A.curve (A.φ a)) s') {y : D} (hy : A.curve y = A.curve a)
    (hys : s' (A.cellOf y) = s' (A.cellOf a)) :
    A.segmentOf y = A.segmentOf a := by
  set C' := A.curve (A.φ a)
  have hCC : A.curve a ≠ C' := (A.curve_φ_ne a).symm
  have hφφ : A.φ (A.φ a) = a := A.φ_φ_of_digon hg
  set Γ := sconfOf A C' s' hs' (s' (A.cellOf a)) (A.φ a) rfl (by rw [A.cellOf_φ])
  have hab : ∀ w, Γ.Above w ↔ A.curve w ≠ C' ∧ s' (A.cellOf w) = s' (A.cellOf a) :=
    fun w => sconfOf_above
  have ha : Γ.Above a := (hab a).2 ⟨hCC, rfl⟩
  have hy' : Γ.Above y := (hab y).2 ⟨by rw [hy]; exact hCC, hys⟩
  -- the darts next to `a` along its curve are not above
  have hnext : ¬ Γ.Above (A.straight a) := by
    rw [hab]
    rintro ⟨-, h⟩
    rw [A.side_straight hs' hCC, ← φ_apply, if_pos rfl] at h
    exact absurd h (by generalize s' (A.cellOf a) = c; revert c; decide)
  have hprev : ∀ w, A.straight w = a → ¬ Γ.Above w := by
    intro w hw hwA
    obtain ⟨hwc, hws⟩ := (hab w).1 hwA
    have h := A.side_straight hs' hwc
    rw [hw, hws] at h
    have hend : A.curve (A.σ (A.α w)) = C' := by
      rw [← A.mem_curves_end_iff hwc, ← crossingOf_straight, hw, ← hφφ,
        show A.φ (A.φ a) = A.σ (A.α (A.φ a)) from rfl, A.crossingOf_σ]
      have := A.mem_curves_crossingOf (A.α (A.φ a))
      rwa [A.curve_α] at this
    rw [if_pos hend] at h
    exact absurd h (by generalize s' (A.cellOf a) = c; revert c; decide)
  have hwalk : ∀ u v : D, Γ.Above u → Γ.UpperWalk u v → (u = a ∨ v = a) → u = v := by
    rintro u v - ⟨k, hk, rfl⟩ huv
    rcases k with _ | k
    · rfl
    · exfalso
      rcases huv with rfl | h
      · exact hnext (by have h := hk 1 (by omega); rw [pow_one] at h; exact h)
      · have hw := hk k (by omega)
        apply hprev _ ?_ hw
        rw [← h, pow_succ', Perm.mul_apply]
        rfl
  have hseg : A.segmentOf (A.α a) = A.segmentOf a :=
    Orbit.mk_eq_mk.2 (Perm.SameCycle.symm ⟨1, by simp⟩)
  rcases Sweep.SConf.upper_arc ha hy' hy.symm with h | h | h | h
  · rw [← hwalk _ _ ha h (Or.inl rfl)]
  · rw [hwalk _ _ hy' h (Or.inr rfl)]
  · have h3 : a = A.α y := hwalk _ _ ha h (Or.inl rfl)
    have e : y = A.α a := by rw [h3, A.α_α]
    rw [e, hseg]
  · have hαy : Γ.Above (A.α y) := (hab _).2 ⟨by rw [A.curve_α, hy]; exact hCC, by
      rw [← hys]; have := hs' y; rw [if_neg (by rw [hy]; exact hCC)] at this
      have key : ∀ u v : ZMod 2, u + v = 0 → v = u := by decide
      exact key _ _ this⟩
    have h4 : A.α y = a := hwalk _ _ hαy h (Or.inr rfl)
    have e : y = A.α a := by rw [← h4, A.α_α]
    rw [e, hseg]

/-- **A digon is the whole region of the two-curve subarrangement containing it**: every cell on
the same sides of the two curves of the digon `cellOf a` is the digon. -/
theorem digon_region {a : D} (hg : A.IsDigon (A.cellOf a)) {s s' : A.Cell → ZMod 2}
    (hs : A.IsSide (A.curve a) s) (hs' : A.IsSide (A.curve (A.φ a)) s') {f : A.Cell}
    (hf : s f = s (A.cellOf a)) (hf' : s' f = s' (A.cellOf a)) : f = A.cellOf a := by
  classical
  have hφφ : A.φ (A.φ a) = a := A.φ_φ_of_digon hg
  have hg' : A.IsDigon (A.cellOf (A.φ a)) := by rw [A.cellOf_φ]; exact hg
  have hs2 : A.IsSide (A.curve (A.φ (A.φ a))) s := by rw [hφφ]; exact hs
  have hcφ : A.cellOf (A.φ a) = A.cellOf a := A.cellOf_φ a
  -- the darts of the digon
  have hmem : ∀ y, A.cellOf y = A.cellOf a → y = a ∨ y = A.φ a := fun y hy =>
    two_cycle hφφ ((cellOf_eq_iff A).1 hy.symm)
  -- crossing a segment of `C` or `C'` leaves the region (`flip1`, `flip2`)
  have flip1 : ∀ y, A.curve y = A.curve a → s (A.cellOf (A.α y)) ≠ s (A.cellOf y) := by
    intro y hy h
    have := hs y
    rw [if_pos hy, h] at this
    exact absurd this (by generalize s (A.cellOf y) = c; revert c; decide)
  have flip2 : ∀ y, A.curve y = A.curve (A.φ a) →
      s' (A.cellOf (A.α y)) ≠ s' (A.cellOf y) := by
    intro y hy h
    have := hs' y
    rw [if_pos hy, h] at this
    exact absurd this (by generalize s' (A.cellOf y) = c; revert c; decide)
  set P : A.Cell → Prop := fun h => s h = s (A.cellOf a) ∧ s' h = s' (A.cellOf a) ∧
    h ≠ A.cellOf a with hP
  -- no dart leaves `P` across its segment
  have hstay : ∀ y, P (A.cellOf y) → P (A.cellOf (A.α y)) := by
    rintro y ⟨h1, h2, h3⟩
    by_cases hc : A.curve y = A.curve a
    · exfalso
      have hk' := eq_or_eq_α_of_segmentOf (digon_side_run hg hs' hc h2)
      rcases hk' with rfl | rfl
      · exact h3 rfl
      · exact flip1 a rfl (by rw [h1])
    by_cases hc' : A.curve y = A.curve (A.φ a)
    · exfalso
      have h1' : s (A.cellOf y) = s (A.cellOf (A.φ a)) := by rw [hcφ]; exact h1
      rcases eq_or_eq_α_of_segmentOf (digon_side_run hg' hs2 hc' h1') with rfl | rfl
      · exact h3 hcφ
      · apply flip2 (A.φ a) rfl
        rw [hcφ]; exact h2
    have hs1 := hs y
    have hs1' := hs' y
    rw [if_neg hc] at hs1
    rw [if_neg hc'] at hs1'
    have key : ∀ u v : ZMod 2, u + v = 0 → v = u := by decide
    refine ⟨(key _ _ hs1).trans h1, (key _ _ hs1').trans h2, fun h => ?_⟩
    rcases hmem _ h with h' | h'
    · apply hc; rw [← h', A.curve_α]
    · apply hc'; rw [← h', A.curve_α]
  let r : A.Cell → ZMod 2 := fun h => if P h then 1 else 0
  have hr : ∀ y, r (A.cellOf (A.α y)) = r (A.cellOf y) := by
    intro y
    by_cases h : P (A.cellOf y)
    · simp only [r, if_pos h, if_pos (hstay y h)]
    · have h' : ¬ P (A.cellOf (A.α y)) := fun h' => h (by
        have := hstay _ h'; rwa [A.α_α] at this)
      simp only [r, if_neg h, if_neg h']
  have hc := A.const_of_invariant (fun y => r (A.cellOf y))
    (fun y => by simp only [A.cellOf_σ, hr]) (fun y => hr y)
  by_contra hne
  obtain ⟨x, rfl⟩ := f.exists_mk
  have h1 : r (A.cellOf x) = 1 := by simp only [r, if_pos (show P (A.cellOf x) from ⟨hf, hf', hne⟩)]
  have h2 : r (A.cellOf a) = 0 := by simp only [r, P, ne_eq, not_true_eq_false, and_false,
    if_false]
  have := hc x a
  rw [h1, h2] at this
  exact absurd this (by decide)

end Pca.FlipGraph
