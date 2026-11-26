/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): a cycle that is not tight has a smaller one

`Cyc.exists_smaller` (see `CycleShort.lean` for the construction in words). Helpers: the four cells
at a crossing off the cycle have the same value (`cells_at`); a crossing all of whose cells lie in
the region is off the cycle (`off_of_all`); the cells at a foot dart are outside the region
(`foot_zero`).
-/
import Pca.FlipGraph.CycleShort

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} {Λ : Lens A}

namespace Cyc

variable (Z : Λ.Cyc) (hs : Λ.Sep) (ht : Λ.Transversal)
include hs ht

/-- At a crossing off the cycle the four cells have the same value. -/
theorem cells_at {w : D} (hno : ¬ ∃ i, A.crossingOf (A.α w) = A.crossingOf (Z.z i)) :
    Z.cut (A.cellOf w) = Z.cut (A.cellOf (A.α w)) ∧
      Z.cut (A.cellOf (A.straight w)) = Z.cut (A.cellOf (A.α w)) ∧
      Z.cut (A.cellOf (A.α (A.straight w))) = Z.cut (A.cellOf (A.α w)) := by
  have h0 : ∀ e, A.crossingOf e = A.crossingOf (A.α w) →
      Z.cut (A.cellOf (A.σ e)) = Z.cut (A.cellOf e) := fun e he => by
    rw [cut_σ Z.cut_isCut, Z.chain_not hs ht (fun hz => hno (by
      obtain ⟨i, hi⟩ := Z.inZ_vertex hz; exact ⟨i, he.symm.trans hi⟩)), add_zero]
  have e1 := h0 (A.α w) rfl
  have e2 := h0 (A.σ (A.α w)) (A.crossingOf_σ _)
  have e3 := h0 (A.σ (A.σ (A.α w))) (A.crossingOf_σσ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [← e1, A.cellOf_σ, A.α_α]
  · rw [A.straight_apply, e2, e1]
  · rw [← A.cellOf_σ, A.straight_apply, e3, e2, e1]

/-- A crossing all of whose cells lie in the region is off the cycle. -/
theorem off_of_all {w : D} (h1 : Z.cut (A.cellOf w) = 1) (h2 : Z.cut (A.cellOf (A.α w)) = 1)
    (h3 : Z.cut (A.cellOf (A.straight w)) = 1) (h4 : Z.cut (A.cellOf (A.α (A.straight w))) = 1) :
    ¬ ∃ i, A.crossingOf (A.α w) = A.crossingOf (Z.z i) := by
  rintro ⟨i, hi⟩
  have hall : ∀ e, A.crossingOf e = A.crossingOf (A.α w) → Z.cut (A.cellOf e) = 1 := by
    intro e he
    have hm := (A.crossingOf_eq_iff).1 he.symm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact h2
    · rw [A.cellOf_σ, A.α_α]; exact h1
    · rw [← A.straight_apply]; exact h3
    · rw [A.cellOf_σ, ← A.straight_apply]; exact h4
  have a1 := hall (Z.z i) hi.symm
  have a2 := hall (A.σ (Z.z i)) (by rw [A.crossingOf_σ]; exact hi.symm)
  rw [A.cellOf_σ, Z.cut_z hs ht, a1] at a2
  exact absurd a2 (by decide)

/-- The cells of a foot dart are outside the region. -/
theorem foot_zero {z₀ : D} (hz : Λ.L (A.σ z₀)) :
    Z.cut (A.cellOf z₀) = 0 ∧ Z.cut (A.cellOf (A.α z₀)) = 0 := by
  have hσ : Z.cut (A.cellOf (A.σ z₀)) = 0 := by
    rw [norm_L Λ Z.cut_isCut Z.cut_norm hz,
      Z.chain_not hs ht fun h => (show Λ.Bd _ from Or.inl hz).not_chord (Z.inZ_chord h)]
  have hz0 : ¬ Z.InZ z₀ := fun h => by
    obtain ⟨i, hi⟩ := Z.inZ_vertex h
    exact foot_not_vertex hz (by rw [hi]; exact Z.vert i)
  refine ⟨?_, by rw [← A.cellOf_σ]; exact hσ⟩
  rw [cut_σ Z.cut_isCut, Z.chain_not hs ht hz0, add_zero] at hσ
  exact hσ

/-- **A cycle that is not tight has a cycle with a smaller region.** -/
theorem exists_smaller (hG : ¬ Z.Good) : ∃ Z' : Λ.Cyc, Z'.size < Z.size := by
  classical
  simp only [Good, not_forall] at hG
  obtain ⟨y, hy, hyZ, ⟨iv, hyv⟩, hy1⟩ := hG
  have hy1' : Z.cut (A.cellOf y) = 1 := (Chain.zmod2_cases _).resolve_left hy1
  have hy2 : Z.cut (A.cellOf (A.α y)) = 1 := by rw [Z.cut_not hs ht hyZ]; exact hy1'
  obtain ⟨z₀, K, hz, hc, hK⟩ := exists_foot ht hy
  let good : ℕ → Prop := fun m => Z.cut (A.cellOf ((A.straight ^ m) z₀)) = 1 ∧
    Z.cut (A.cellOf (A.α ((A.straight ^ m) z₀))) = 1
  have gK : good K := by show _ ∧ _; rw [hK]; exact ⟨hy1', hy2⟩
  have g0 : ¬ good 0 := fun h => by
    have := (Z.foot_zero hs ht hz).1
    have h1 : Z.cut (A.cellOf ((A.straight ^ 0) z₀)) = 1 := h.1
    rw [show (A.straight ^ 0) z₀ = z₀ by simp] at h1
    rw [h1] at this; exact absurd this (by decide)
  set m₁ := Nat.findGreatest (fun m => ¬ good m) K with hm₁def
  have hm₁ : ¬ good m₁ := Nat.findGreatest_spec (P := fun m => ¬ good m) (Nat.zero_le K) g0
  have hm₁K : m₁ ≤ K := Nat.findGreatest_le K
  have hm₁lt : m₁ < K := lt_of_le_of_ne hm₁K (fun h => hm₁ (h ▸ gK))
  have hgood : ∀ m, m₁ < m → m ≤ K → good m := fun m h1 h2 =>
    not_not.1 (Nat.findGreatest_is_greatest h1 h2)
  have hfw : ∀ m ≤ K, Λ.Fwd ((A.straight ^ m) z₀) := by
    have : ∀ d ≤ K, Λ.Fwd ((A.straight ^ (K - d)) z₀) := by
      intro d hd
      induction d with
      | zero => rw [Nat.sub_zero, hK]; exact hy
      | succ d ih =>
        have h' := ih (by omega)
        rw [show K - d = (K - (d + 1)) + 1 by omega, Walk.pow_succ_apply] at h'
        exact Fwd.of_straight h' (hc _ (by omega))
    intro m hm
    have := this (K - m) (by omega)
    rwa [show K - (K - m) = m by omega] at this
  -- the vertex `u` where the chord enters the region
  have hu : ∃ iu, A.crossingOf ((A.straight ^ (m₁ + 1)) z₀) = A.crossingOf (Z.z iu) := by
    by_contra hno
    rw [← crossingOf_α_pow] at hno
    obtain ⟨c1, c2, c3⟩ := Z.cells_at hs ht hno
    obtain ⟨g1, g2⟩ := hgood (m₁ + 1) (by omega) (by omega)
    rw [Walk.pow_succ_apply] at g1 g2
    rw [g1] at c2; rw [g2] at c3
    exact hm₁ ⟨c1.trans c2.symm, c2.symm⟩
  obtain ⟨iu, hiu⟩ := hu
  -- the inner crossings of the piece
  let Int : A.Crossing → Prop := fun x =>
    ∃ m, m₁ + 1 < m ∧ m ≤ K ∧ x = A.crossingOf ((A.straight ^ m) z₀)
  have hint : ∀ x, Int x → ¬ ∃ i, x = A.crossingOf (Z.z i) := by
    rintro x ⟨m, h1, h2, rfl⟩ hx
    obtain ⟨g1, g2⟩ := hgood (m - 1) (by omega) (by omega)
    obtain ⟨g3, g4⟩ := hgood m (by omega) (by omega)
    rw [show m = (m - 1) + 1 by omega, Walk.pow_succ_apply] at g3 g4
    apply Z.off_of_all hs ht g1 g2 g3 g4
    rw [crossingOf_α_pow, show m - 1 + 1 = m by omega]; exact hx
  set v := A.crossingOf (Z.z iv) with hvdef
  have hvint : ¬ Int v := fun h => hint v h ⟨iv, rfl⟩
  -- the predecessor map
  let p : A.Crossing → D := fun x =>
    if x = v then y else if h : Int x then (A.straight ^ (Classical.choose h - 1)) z₀
      else if h' : ∃ i, x = A.crossingOf (Z.z i) then Z.z (Classical.choose h' - 1) else y
  have hp_v : p v = y := if_pos rfl
  have hp_int : ∀ x, Int x → ∃ m, m₁ + 1 < m ∧ m ≤ K ∧ x = A.crossingOf ((A.straight ^ m) z₀) ∧
      p x = (A.straight ^ (m - 1)) z₀ := by
    intro x hx
    have hxv : x ≠ v := fun h => hvint (h ▸ hx)
    obtain ⟨a, b, c⟩ := Classical.choose_spec hx
    exact ⟨_, a, b, c, by simp only [p, if_neg hxv, dif_pos hx]⟩
  have hp_Z : ∀ x i, x ≠ v → ¬ Int x → x = A.crossingOf (Z.z i) → p x = Z.z (i - 1) := by
    intro x i hxv hxi hx
    have h' : ∃ i, x = A.crossingOf (Z.z i) := ⟨i, hx⟩
    simp only [p, if_neg hxv, dif_neg hxi, dif_pos h']
    rw [Z.inj _ _ ((Classical.choose_spec h').symm.trans hx)]
  let Pdom : A.Crossing → Prop := fun x => x = v ∨ Int x ∨ ∃ i, x = A.crossingOf (Z.z i)
  have hstart : ∀ m, m₁ < m → m ≤ K → Pdom (A.crossingOf ((A.straight ^ m) z₀)) := by
    intro m h1 h2
    rcases Nat.lt_or_ge (m₁ + 1) m with h | h
    · exact Or.inr (Or.inl ⟨m, h, h2, rfl⟩)
    · rw [show m = m₁ + 1 by omega]; exact Or.inr (Or.inr ⟨iu, hiu⟩)
  have hp : ∀ x, Pdom x → Λ.Fwd (p x) ∧ A.crossingOf (A.α (p x)) = x ∧
      Pdom (A.crossingOf (p x)) ∧ Λ.IsVertex x := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      rw [hp_v]
      refine ⟨hy, hyv, ?_, Z.vert iv⟩
      rw [← hK]; exact hstart K hm₁lt le_rfl
    by_cases hxi : Int x
    · obtain ⟨m, h1, h2, rfl, hpx⟩ := hp_int x hxi
      rw [hpx]
      refine ⟨hfw _ (by omega), by rw [crossingOf_α_pow, show m - 1 + 1 = m by omega],
        hstart _ (by omega) (by omega), ?_⟩
      have := isVertex_passed (Λ := Λ) (hc (m - 1) (by omega))
        (by rw [← Walk.pow_succ_apply, show m - 1 + 1 = m by omega]; exact hc m h2)
      rwa [← Walk.pow_succ_apply, show m - 1 + 1 = m by omega] at this
    · obtain ⟨i, rfl⟩ : ∃ i, x = A.crossingOf (Z.z i) := by
        rcases hx with h | h | h
        · exact absurd h hxv
        · exact absurd h hxi
        · exact h
      rw [hp_Z _ i hxv hxi rfl]
      exact ⟨Z.fwd _, Z.crossing_α i, Or.inr (Or.inr ⟨_, rfl⟩), Z.vert i⟩
  obtain ⟨Z', hZ'⟩ := cyc_of_pred Pdom p hp (Or.inl rfl)
  -- the darts of the new cycle
  let PD : D → Prop := fun d => ∃ m, m₁ < m ∧ m ≤ K ∧ d = (A.straight ^ m) z₀
  have dart_cases : ∀ τ, PD (Z'.z τ) ∨ ∃ i, A.crossingOf (A.α (Z'.z τ)) = A.crossingOf (Z.z i) ∧
      Z'.z τ = Z.z (i - 1) ∧ A.crossingOf (A.α (Z'.z τ)) ≠ v := by
    intro τ
    obtain ⟨hd, he⟩ := hZ' τ
    set e := A.crossingOf (A.α (Z'.z τ))
    by_cases hev : e = v
    · left; rw [he, hev, hp_v, ← hK]; exact ⟨K, hm₁lt, le_rfl, rfl⟩
    by_cases hei : Int e
    · left
      obtain ⟨m, h1, h2, -, hpx⟩ := hp_int e hei
      rw [he, hpx]; exact ⟨m - 1, by omega, by omega, rfl⟩
    · right
      obtain ⟨i, hi⟩ : ∃ i, e = A.crossingOf (Z.z i) := by
        rcases hd with h | h | h
        · exact absurd h hev
        · exact absurd h hei
        · exact h
      exact ⟨i, hi, by rw [he, hp_Z e i hev hei hi], hev⟩
  have some_PD : ∃ τ, PD (Z'.z τ) := by
    by_contra hno
    have hno' : ∀ τ, ¬ PD (Z'.z τ) := fun τ h => hno ⟨τ, h⟩
    let T : ZMod Z.k → Prop := fun i => ∃ τ, A.crossingOf (A.α (Z'.z τ)) = A.crossingOf (Z.z i)
    have hT0 : ∃ i, T i := by
      rcases dart_cases 0 with h | ⟨i, hi, -, -⟩
      · exact absurd h (hno' 0)
      · exact ⟨i, 0, hi⟩
    have hTs : ∀ i, T (i + 1) → T i := by
      rintro i ⟨τ, hτ⟩
      rcases dart_cases τ with h | ⟨i', hi', hz', -⟩
      · exact absurd h (hno' τ)
      · have : i' = i + 1 := Z.inj _ _ (hi'.symm.trans hτ)
        rw [this, add_sub_cancel_right] at hz'
        refine ⟨τ - 1, ?_⟩
        rw [Z'.link, sub_add_cancel, hz']
    obtain ⟨i₀, hi₀⟩ := hT0
    obtain ⟨τ, hτ⟩ := zmod_induct_down T hTs hi₀ iv
    rcases dart_cases τ with h | ⟨-, -, -, hne⟩
    · exact hno' τ h
    · exact hne hτ
  -- the new region lies in the old one
  have hsupp : ∀ d, Z'.chain (A.segmentOf d) ≠ 0 →
      Z.cut (A.cellOf d) = 1 ∨ Z.cut (A.cellOf (A.α d)) = 1 := by
    intro d hd
    have hin : Z'.InZ d := by
      by_contra h; rw [Z'.chain_not hs ht h] at hd; exact hd rfl
    have key : ∀ τ, Z.cut (A.cellOf (Z'.z τ)) = 1 ∨ Z.cut (A.cellOf (A.α (Z'.z τ))) = 1 := by
      intro τ
      rcases dart_cases τ with ⟨m, h1, h2, h3⟩ | ⟨i, -, hz', -⟩
      · left; rw [h3]; exact (hgood m h1 h2).1
      · rw [hz', Z.cut_z hs ht]
        rcases Chain.zmod2_cases (Z.cut (A.cellOf (Z.z (i - 1)))) with h | h
        · right; rw [h]; rfl
        · left; exact h
    obtain ⟨τ, rfl | rfl⟩ := Z'.inZ_cases hin
    · exact key τ
    · rw [A.α_α]; exact (key τ).symm
  have hle : ∀ g, Z.cut g = 0 → Z'.cut g = 0 := fun g hg =>
    Z.cut_le hs ht Z'.cut_isCut Z'.cut_norm hsupp hg
  obtain ⟨τ₀, m, h1, h2, h3⟩ := some_PD
  obtain ⟨g, hg1, hg2⟩ : ∃ g, Z.cut g = 1 ∧ Z'.cut g ≠ 1 := by
    have e := Z'.cut_z hs ht τ₀
    obtain ⟨c1, c2⟩ := hgood m h1 h2
    rw [← h3] at c1 c2
    rcases Chain.zmod2_cases (Z'.cut (A.cellOf (Z'.z τ₀))) with h | h
    · exact ⟨_, c1, by rw [h]; decide⟩
    · exact ⟨_, c2, by rw [e, h]; decide⟩
  refine ⟨Z', ?_⟩
  unfold size
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨g, by simp [hg1], by simp [hg2]⟩
  · intro g' hg'
    simp only [mem_filter, mem_univ, true_and] at hg' ⊢
    rcases Chain.zmod2_cases (Z.cut g') with h | h
    · rw [hle g' h] at hg'; exact absurd hg' (by decide)
    · exact h

end Cyc

end Lens

end Pca.FlipGraph
