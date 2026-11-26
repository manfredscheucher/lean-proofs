/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): root chains of forward darts

For a forward dart `y` with foot dart `z₀` (`y = straight^k z₀`), the **root chain** `root y` is the
path from the base of `L` along `L` to the foot and up the chord to the start of `y` (as a chain:
`walk base i₀ + walk z₀ k`, `σ z₀ = straight^i₀ base`). FROS' regions "bounded by the subarcs of `a`
and `a'` from `L` to `p` and the corresponding part of `L`" are the cuts of the even chains
`root y + root y'` for two forward darts `y`, `y'` at `p` (`bd_root`). The foot is unique
(`foot_unique`), so `root (straight^k z₀) = walk z₀ k + walk base i₀` (`root_eq`).
-/
import Pca.FlipGraph.Chord

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- The index of an `L`-dart along the run `L`. -/
noncomputable def lidx (d : D) : ℕ := by
  classical exact if h : ∃ i, d = (A.straight ^ i) Λ.base then Nat.find h else 0

/-- Foot data of `y`: `y = straight^k z₀` with `σ z₀ ∈ L` and chord darts on the way. -/
def IsFoot (z₀ : D) (k : ℕ) (y : D) : Prop :=
  Λ.L (A.σ z₀) ∧ (∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) ∧ (A.straight ^ k) z₀ = y

open Classical in
/-- The root chain of `y` (zero if `y` has no foot). -/
noncomputable def root (y : D) : A.Segment → ZMod 2 :=
  if h : ∃ z₀ k, Λ.IsFoot z₀ k y then
    walk (Classical.choose h) (Classical.choose (Classical.choose_spec h)) +
      walk Λ.base (Λ.lidx (A.σ (Classical.choose h)))
  else 0

variable {Λ}

theorem lidx_spec {d : D} (hd : Λ.L d) : d = (A.straight ^ Λ.lidx d) Λ.base ∧ Λ.lidx d ≤ Λ.kL := by
  classical
  obtain ⟨i, hi, hd'⟩ := (Λ.L_iff' d).1 hd
  have ex : ∃ i, d = (A.straight ^ i) Λ.base := ⟨i, hd'⟩
  have e : Λ.lidx d = Nat.find ex := by unfold lidx; rw [dif_pos ex]
  rw [e]
  exact ⟨Nat.find_spec ex, (Nat.find_min' ex hd').trans hi⟩

/-- The dart before a foot dart is not a chord dart. -/
theorem not_chord_before_foot {z₀ w : D} (hz : Λ.L (A.σ z₀)) (hw : A.straight w = z₀) :
    ¬ Λ.Chord w := by
  intro hc
  have hα : A.α w = A.σ (A.σ z₀) := by
    rw [← hw, A.straight_apply, A.σ_σ_σ_σ]
  have := hc.2
  rw [hα, A.cellOf_σ] at this
  exact (Λ.L_bd _ hz).2 this

/-- **The foot is unique.** -/
theorem foot_unique {z₀ z₁ y : D} {k k₁ : ℕ} (h₀ : Λ.IsFoot z₀ k y) (h₁ : Λ.IsFoot z₁ k₁ y) :
    z₀ = z₁ ∧ k = k₁ := by
  wlog hle : k ≤ k₁ generalizing z₀ z₁ k k₁
  · obtain ⟨a, b⟩ := this h₁ h₀ (by omega); exact ⟨a.symm, b.symm⟩
  obtain ⟨hz₀, hc₀, e₀⟩ := h₀
  obtain ⟨hz₁, hc₁, e₁⟩ := h₁
  have e : z₀ = (A.straight ^ (k₁ - k)) z₁ := by
    apply (A.straight ^ k).injective
    rw [e₀, ← Perm.mul_apply, ← pow_add, show k + (k₁ - k) = k₁ by omega, e₁]
  rcases Nat.eq_zero_or_pos (k₁ - k) with h0 | h0
  · rw [h0, pow_zero, Perm.one_apply] at e; exact ⟨e, by omega⟩
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d, k₁ - k = d + 1 := ⟨k₁ - k - 1, by omega⟩
    rw [hd, Walk.pow_succ_apply] at e
    exact not_chord_before_foot hz₀ e.symm (hc₁ d (by omega))

theorem root_eq {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀)) (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) :
    Λ.root ((A.straight ^ k) z₀) = walk z₀ k + walk Λ.base (Λ.lidx (A.σ z₀)) := by
  classical
  have ex : ∃ z₀' k', Λ.IsFoot z₀' k' ((A.straight ^ k) z₀) := ⟨z₀, k, hz, hc, rfl⟩
  unfold root
  rw [dif_pos ex]
  obtain ⟨a, b⟩ := foot_unique (Classical.choose_spec (Classical.choose_spec ex))
    (⟨hz, hc, rfl⟩ : Λ.IsFoot z₀ k ((A.straight ^ k) z₀))
  have key : ∀ z₁ k₁, z₁ = z₀ → k₁ = k →
      (walk z₁ k₁ + walk Λ.base (Λ.lidx (A.σ z₁)) : A.Segment → ZMod 2) =
        walk z₀ k + walk Λ.base (Λ.lidx (A.σ z₀)) := by
    rintro _ _ rfl rfl; rfl
  exact key _ _ a b

/-- The root chain grows by one segment along the chord. -/
theorem root_succ {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k + 1, Λ.Chord ((A.straight ^ i) z₀)) :
    Λ.root ((A.straight ^ (k + 1)) z₀) =
      Λ.root ((A.straight ^ k) z₀) + δ (A.segmentOf ((A.straight ^ k) z₀)) := by
  rw [root_eq hz hc, root_eq hz fun i hi => hc i (by omega)]
  simp only [walk, sum_range_succ]
  abel

/-- **Boundary of a root chain**: its two ends, the base of `L` and the start of `y`. -/
theorem bd_root {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀)) (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀))
    (x : A.Crossing) :
    Chain.bd (Λ.root ((A.straight ^ k) z₀)) x =
      δx (A.crossingOf ((A.straight ^ k) z₀)) x + δx (A.crossingOf Λ.base) x := by
  rw [root_eq hz hc, bd_add, bd_walk, bd_walk, ← (lidx_spec hz).1, A.crossingOf_σ]
  have key : ∀ a b c : ZMod 2, a + b + (c + a) = b + c := by decide
  exact key _ _ _

/-- A nonzero value of a walk chain is on one of its segments. -/
theorem walk_ne_zero {z : D} {k : ℕ} {s : A.Segment} (h : walk z k s ≠ 0) :
    ∃ i < k, s = A.segmentOf ((A.straight ^ i) z) := by
  by_contra hn
  push_neg at hn
  apply h
  rw [walk_apply]
  exact sum_eq_zero fun i hi => if_neg (hn i (mem_range.1 hi))

/-- The segments of a root chain are chord segments of the chord or `L`-segments. -/
theorem root_ne_zero {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) {w : D}
    (h : Λ.root ((A.straight ^ k) z₀) (A.segmentOf w) ≠ 0) :
    (∃ i < k, w = (A.straight ^ i) z₀ ∨ w = A.α ((A.straight ^ i) z₀)) ∨
      (∃ i < Λ.lidx (A.σ z₀), w = (A.straight ^ i) Λ.base ∨ w = A.α ((A.straight ^ i) Λ.base)) := by
  rw [root_eq hz hc, Pi.add_apply] at h
  by_cases h1 : walk z₀ k (A.segmentOf w) = 0
  · rw [h1, zero_add] at h
    obtain ⟨i, hi, e⟩ := walk_ne_zero h
    exact Or.inr ⟨i, hi, eq_or_eq_α_of_segmentOf e⟩
  · obtain ⟨i, hi, e⟩ := walk_ne_zero h1
    exact Or.inl ⟨i, hi, eq_or_eq_α_of_segmentOf e⟩

theorem L_of_lt_lidx {d : D} (hd : Λ.L d) {i : ℕ} (hi : i < Λ.lidx d) :
    Λ.L ((A.straight ^ i) Λ.base) :=
  (Λ.L_iff' _).2 ⟨i, by have := (lidx_spec hd).2; omega, rfl⟩

/-- Root chains are supported in the lens. -/
theorem root_supp {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) : Supp Λ (Λ.root ((A.straight ^ k) z₀)) := by
  intro w h
  rcases root_ne_zero hz hc h with ⟨i, hi, rfl | rfl⟩ | ⟨i, hi, rfl | rfl⟩
  · exact Or.inl (hc i hi.le).1
  · exact Or.inl (hc i hi.le).2
  · exact Or.inl (Λ.L_bd _ (L_of_lt_lidx hz hi)).1
  · rw [A.α_α]; exact Or.inr (Λ.L_bd _ (L_of_lt_lidx hz hi)).1

/-- The value of a root chain on a dart of another curve, not on `S`, is `0`. -/
theorem root_other {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) {w : D} (hw : A.curve w ≠ A.curve z₀)
    (hwS : A.curve w ≠ Λ.S) : Λ.root ((A.straight ^ k) z₀) (A.segmentOf w) = 0 := by
  by_contra h
  rcases root_ne_zero hz hc h with ⟨i, -, rfl | rfl⟩ | ⟨i, hi, rfl | rfl⟩
  · exact hw (Walk.curve_pow A z₀ i)
  · exact hw (by rw [A.curve_α, Walk.curve_pow])
  · exact hwS (Λ.L_curve _ (L_of_lt_lidx hz hi))
  · exact hwS (by rw [A.curve_α]; exact Λ.L_curve _ (L_of_lt_lidx hz hi))

/-- The value of a root chain on a chord dart of another curve is `0` (under `Sep`). -/
theorem root_other_chord (hs : Λ.Sep) {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) {w : D} (hw : A.curve w ≠ A.curve z₀)
    (hwc : Λ.Chord w) : Λ.root ((A.straight ^ k) z₀) (A.segmentOf w) = 0 :=
  root_other hz hc hw fun h => S_not_chord hs h hwc

/-- The value of a root chain on an `R`-dart is `0`. -/
theorem root_R {z₀ : D} {k : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) {w : D} (hw : Λ.R w) :
    Λ.root ((A.straight ^ k) z₀) (A.segmentOf w) = 0 := by
  by_contra h
  have hb : Λ.Bd w := Or.inr hw
  rcases root_ne_zero hz hc h with ⟨i, hi, rfl | rfl⟩ | ⟨i, hi, rfl | rfl⟩
  · exact hb.not_chord (hc i hi.le)
  · exact hb.not_chord (chord_α (hc i hi.le))
  · exact Λ.disj _ ⟨L_of_lt_lidx hz hi, hw⟩
  · exact (Λ.R_bd _ hw).2 (by rw [A.α_α]; exact (Λ.L_bd _ (L_of_lt_lidx hz hi)).1)

/-- The value of a root chain on the chord itself: `1` exactly on the segments before `y`. -/
theorem root_self {z₀ : D} {k m i : ℕ} (hz : Λ.L (A.σ z₀))
    (hc : ∀ i ≤ m, Λ.Chord ((A.straight ^ i) z₀)) (hlt : m < period A.straight z₀) (hk : k ≤ m)
    (hi : i ≤ m) :
    Λ.root ((A.straight ^ k) z₀) (A.segmentOf ((A.straight ^ i) z₀)) = if i < k then 1 else 0 := by
  have hc' : ∀ j ≤ k, Λ.Chord ((A.straight ^ j) z₀) := fun j hj => hc j (by omega)
  rw [root_eq hz hc', Pi.add_apply]
  have hL : walk Λ.base (Λ.lidx (A.σ z₀)) (A.segmentOf ((A.straight ^ i) z₀)) = 0 := by
    by_contra h
    obtain ⟨j, hj, e⟩ := walk_ne_zero h
    rcases eq_or_eq_α_of_segmentOf e with e | e
    · exact Bd.not_chord (show Λ.Bd _ from Or.inl (L_of_lt_lidx hz hj)) (e ▸ hc i hi)
    · exact Bd.not_chord (show Λ.Bd _ from Or.inl (L_of_lt_lidx hz hj))
        (by rw [← A.α_α ((A.straight ^ j) Λ.base), ← e]; exact chord_α (hc i hi))
  rw [hL, add_zero, walk_apply]
  have : ∀ j ∈ range k, (if A.segmentOf ((A.straight ^ i) z₀) = A.segmentOf ((A.straight ^ j) z₀)
      then (1 : ZMod 2) else 0) = if j = i then 1 else 0 := by
    intro j hj
    rw [mem_range] at hj
    by_cases e : j = i
    · rw [if_pos e, if_pos (by rw [e])]
    · rw [if_neg e, if_neg fun h => e (seg_inj hlt hi (by omega) h).symm]
  rw [sum_congr rfl this, sum_ite_eq' (range k) i (fun _ => (1 : ZMod 2))]
  simp only [mem_range]

end Lens

end Pca.FlipGraph
