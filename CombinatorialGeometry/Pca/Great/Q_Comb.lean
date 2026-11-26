/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma, combinatorial core (`doc/pca/great.md` section 3.3)

A **chord system** abstracts the chords of a great arrangement in the hemisphere `H` of a frame:
`P e` is the position of the start of chord `e` on the frame curve, `H e f` the position of the
crossing with `f` along `e` (`0 < H e f < m`). `Rt x t k` says that the cell at position `k` on `t`
lies right of `x`; the relation `rel` says that the two ways of computing the side of the
crossing of `f` and `g` with respect to `e` agree.

For a chord `ℓ` and a side `Nq` of it, the quarter `Q` is the part of `H` on side `Nq`. The lemma
`exists_tri`: if two chords of `T` cross in `Q`, there are `i, j ∈ T` crossing in `Q` such that
along `ℓ`, `i` and `j` no other chord of `T` crosses between the three crossings (the three sides
of the triangle of `ℓ, i, j`). Proof by the fewest-chords-in-between argument (section 3.3).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

open Finset

namespace Pca.Great.Comb

theorem iff_of_not_iff_iff {X p q : Prop} (h : ¬ (X ↔ p) ↔ ¬ (X ↔ q)) : p ↔ q := by tauto

/-- Strictly between. -/
def Bet (k a b : ℕ) : Prop := (a < k ∧ k < b) ∨ (b < k ∧ k < a)

instance (k a b : ℕ) : Decidable (Bet k a b) := by unfold Bet; infer_instance

/-- A chord system. -/
structure ChordSys (ι : Type*) where
  P : ι → ℕ
  H : ι → ι → ℕ
  m : ℕ
  P_inj : Function.Injective P
  H_inj : ∀ e f g, f ≠ e → g ≠ e → H e f = H e g → f = g
  H_pos : ∀ e f, f ≠ e → 0 < H e f
  H_lt : ∀ e f, f ≠ e → H e f < m
  rel : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    ((P e < P f ↔ H f e ≤ H f g) ↔ (P e < P g ↔ H g e ≤ H g f))

variable {ι : Type*} [DecidableEq ι] (S : ChordSys ι)

namespace ChordSys

/-- The cell at position `k` on chord `t` lies right of `x`. -/
def Rt (x t : ι) (k : ℕ) : Prop := ¬ (S.P x < S.P t ↔ S.H t x ≤ k)

theorem rel' {e f g : ι} (h1 : e ≠ f) (h2 : e ≠ g) (h3 : f ≠ g) :
    S.Rt e f (S.H f g) ↔ S.Rt e g (S.H g f) := by
  have := S.rel e f g h1 h2 h3
  unfold Rt; tauto

theorem Rt_congr {x t : ι} {k k' : ℕ} (h : S.H t x ≤ k ↔ S.H t x ≤ k') :
    S.Rt x t k ↔ S.Rt x t k' := by
  unfold Rt; rw [h]

variable (ℓ : ι) (Nq : Prop) [Decidable Nq] (T : Finset ι)

/-- The cell at position `k` on `t` lies in the quarter. -/
def InQ (t : ι) (k : ℕ) : Prop := S.Rt ℓ t k ↔ Nq

/-- `f` is a candidate for the first crossing of `e` in the quarter. -/
def Cand (e f : ι) : Prop := f ∈ T ∧ f ≠ ℓ ∧ f ≠ e ∧ S.InQ ℓ Nq e (S.H e f)

/-- `f` is the first crossing of `e` with a chord of `T` in the quarter. -/
def IsFirst (e f : ι) : Prop :=
  S.Cand ℓ Nq T e f ∧ ∀ g, S.Cand ℓ Nq T e g → g ≠ f → Bet (S.H e f) (S.H e ℓ) (S.H e g)

/-- The number of chords of `T` crossing `ℓ` strictly between `i` and `j`. -/
noncomputable def gap (i j : ι) : ℕ := by
  classical
  exact (T.filter fun t => t ≠ ℓ ∧ t ≠ i ∧ t ≠ j ∧ Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)).card

variable {S ℓ Nq T}

/-- The quarter side on a chord is one side of the crossing with `ℓ`. -/
theorem inQ_iff {t : ι} (htℓ : t ≠ ℓ) {k : ℕ} :
    S.InQ ℓ Nq t k ↔ (S.H t ℓ ≤ k ↔ (¬ (S.P ℓ < S.P t) ↔ Nq)) := by
  unfold InQ Rt; tauto

theorem exists_first {e f : ι} (he : e ≠ ℓ) (h : S.Cand ℓ Nq T e f) :
    ∃ f', S.IsFirst ℓ Nq T e f' := by
  classical
  set C := T.filter fun g => S.Cand ℓ Nq T e g
  have hC : f ∈ C := mem_filter.2 ⟨h.1, h⟩
  obtain ⟨g, hg, hmin⟩ := C.exists_min_image
    (fun g => (S.H e g - S.H e ℓ) + (S.H e ℓ - S.H e g)) ⟨f, hC⟩
  have hgc := (mem_filter.1 hg).2
  refine ⟨g, hgc, fun g' hg' hne => ?_⟩
  have hle := hmin g' (mem_filter.2 ⟨hg'.1, hg'⟩)
  have hneH : S.H e g ≠ S.H e g' := fun h => hne (S.H_inj e g g' hgc.2.2.1 hg'.2.2.1 h).symm
  have h1 : S.H e g ≠ S.H e ℓ := fun h => hgc.2.1 (S.H_inj e g ℓ hgc.2.2.1 he.symm h)
  have h2 : S.H e g' ≠ S.H e ℓ := fun h => hg'.2.1 (S.H_inj e g' ℓ hg'.2.2.1 he.symm h)
  have q1 := (inQ_iff he).1 hgc.2.2.2
  have q2 := (inQ_iff he).1 hg'.2.2.2
  unfold Bet
  by_cases hN : (¬ (S.P ℓ < S.P e) ↔ Nq)
  · have := q1.2 hN; have := q2.2 hN; omega
  · have := mt q1.1 hN; have := mt q2.1 hN; omega


theorem Rt_of_not_bet {x t : ι} {k k' : ℕ} (h1 : S.H t x ≠ k) (h2 : S.H t x ≠ k')
    (hb : ¬ Bet (S.H t x) k k') : S.Rt x t k ↔ S.Rt x t k' :=
  S.Rt_congr (by unfold Bet at hb; omega)

theorem inQ_of_bet {t : ι} (htℓ : t ≠ ℓ) {k k' : ℕ} (hk' : S.InQ ℓ Nq t k')
    (hb : Bet k (S.H t ℓ) k') : S.InQ ℓ Nq t k := by
  rw [inQ_iff htℓ] at hk' ⊢
  unfold Bet at hb
  by_cases hX : (¬ (S.P ℓ < S.P t) ↔ Nq)
  · have := hk'.2 hX; exact iff_of_true (by omega) hX
  · have := mt hk'.1 hX; exact iff_of_false (by omega) hX

/-- Two positions in the quarter are on the same side of the crossing with `ℓ`. -/
theorem inQ_same {t : ι} (htℓ : t ≠ ℓ) {k k' : ℕ} (hk : S.InQ ℓ Nq t k) (hk' : S.InQ ℓ Nq t k')
    (h1 : k ≠ S.H t ℓ) (h2 : k' ≠ S.H t ℓ) :
    (S.H t ℓ < k ∧ S.H t ℓ < k') ∨ (k < S.H t ℓ ∧ k' < S.H t ℓ) := by
  rw [inQ_iff htℓ] at hk hk'
  by_cases hX : (¬ (S.P ℓ < S.P t) ↔ Nq)
  · have := hk.2 hX; have := hk'.2 hX; omega
  · have := mt hk.1 hX; have := mt hk'.1 hX; omega

section Main

variable {i j : ι} (hij : S.IsFirst ℓ Nq T i j) (hiℓ : i ≠ ℓ)
include hij hiℓ

theorem first_ne : j ≠ ℓ ∧ j ≠ i ∧ j ∈ T := ⟨hij.1.2.1, hij.1.2.2.1, hij.1.1⟩

/-- No chord of `T` crosses `i` in the quarter before `j` (on the side of the triangle). -/
theorem not_cross_i {t : ι} (ht : t ∈ T) (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hQ : S.InQ ℓ Nq t (S.H t i)) (hs : S.Rt j t (S.H t i) ↔ S.Rt j ℓ (S.H ℓ i)) : False := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have r1 := S.rel' (e := j) (f := t) (g := i) (Ne.symm htj) hji hti
  have r2 := S.rel' (e := j) (f := ℓ) (g := i) hjℓ hji (Ne.symm hiℓ)
  have r3 := S.rel' (e := ℓ) (f := t) (g := i) (Ne.symm htℓ) (Ne.symm hiℓ) hti
  have hc : S.Cand ℓ Nq T i t := ⟨ht, htℓ, hti, by unfold InQ; rw [← r3]; exact hQ⟩
  have hb := hij.2 t hc htj
  have key : S.Rt j i (S.H i t) ↔ S.Rt j i (S.H i ℓ) := by rw [← r1, ← r2]; exact hs
  unfold Rt at key
  have key' : S.H i j ≤ S.H i t ↔ S.H i j ≤ S.H i ℓ := by tauto
  unfold Bet at hb
  omega

/-- The end of the quarter part of a chord is not in the triangle region. -/
theorem not_end {t : ι} (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j) {E : ℕ}
    (hE : (∀ x, x ≠ t → S.H t x ≤ E) ∨ (∀ x, x ≠ t → ¬ S.H t x ≤ E))
    (h1 : S.InQ ℓ Nq t E) (h2 : S.Rt i t E ↔ S.Rt i ℓ (S.H ℓ j))
    (h3 : S.Rt j t E ↔ S.Rt j ℓ (S.H ℓ i)) : False := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have hQ := hij.1.2.2.2
  have r1 := S.rel ℓ i j (Ne.symm hiℓ) (Ne.symm hjℓ) (Ne.symm hji)
  have r2 := S.rel i ℓ j hiℓ (Ne.symm hji) (Ne.symm hjℓ)
  have r3 := S.rel j ℓ i hjℓ hji (Ne.symm hiℓ)
  have d1 : S.P ℓ ≠ S.P i := fun h => hiℓ (S.P_inj h).symm
  have d2 : S.P ℓ ≠ S.P j := fun h => hjℓ (S.P_inj h).symm
  have d3 : S.P i ≠ S.P j := fun h => hji (S.P_inj h).symm
  have d4 : S.P ℓ ≠ S.P t := fun h => htℓ (S.P_inj h).symm
  have d5 : S.P i ≠ S.P t := fun h => hti (S.P_inj h).symm
  have d6 : S.P j ≠ S.P t := fun h => htj (S.P_inj h).symm
  have e1 : S.H ℓ i ≠ S.H ℓ j := fun h => hji (S.H_inj ℓ i j hiℓ hjℓ h).symm
  have e2 : S.H i ℓ ≠ S.H i j := fun h => hjℓ (S.H_inj i ℓ j (Ne.symm hiℓ) hji h).symm
  have e3 : S.H j ℓ ≠ S.H j i := fun h => hiℓ (S.H_inj j ℓ i (Ne.symm hjℓ) (Ne.symm hji) h).symm
  simp only [InQ, Rt] at hQ h1 h2 h3
  rcases hE with hE | hE
  · simp only [hE ℓ (Ne.symm htℓ), hE i (Ne.symm hti), hE j (Ne.symm htj), iff_true] at h1 h2 h3
    by_cases hN : Nq <;> simp only [hN, iff_true, iff_false] at hQ h1 <;> omega
  · simp only [hE ℓ (Ne.symm htℓ), hE i (Ne.symm hti), hE j (Ne.symm htj), iff_false] at h1 h2 h3
    by_cases hN : Nq <;> simp only [hN, iff_true, iff_false] at hQ h1 <;> omega

/-- The end of the quarter part of the chord `t`: the side of `x` there is the side at the crossing
position `k` unless `x` crosses `t` in the quarter beyond `k`. -/
theorem exists_end {t : ι} (htℓ : t ≠ ℓ) : ∃ E : ℕ,
    ((∀ x, x ≠ t → S.H t x ≤ E) ∨ (∀ x, x ≠ t → ¬ S.H t x ≤ E)) ∧ S.InQ ℓ Nq t E ∧
      (∀ k, S.InQ ℓ Nq t k → k ≠ S.H t ℓ → ∀ x, x ≠ t → S.H t x ≠ k →
        ((S.H t x ≤ k ↔ S.H t x ≤ E) ↔
          ¬ (S.InQ ℓ Nq t (S.H t x) ∧ Bet k (S.H t ℓ) (S.H t x)))) ∧
      (∀ x, x ≠ t → S.H t x ≠ S.H t ℓ →
        ((S.H t x ≤ S.H t ℓ ↔ S.H t x ≤ E) ↔ ¬ S.InQ ℓ Nq t (S.H t x))) := by
  by_cases hX : (¬ (S.P ℓ < S.P t) ↔ Nq)
  · refine ⟨S.m - 1, Or.inl fun x hx => by have := S.H_lt t x hx; omega,
      (inQ_iff htℓ).2 (iff_of_true (by have := S.H_lt t ℓ (Ne.symm htℓ); omega) hX), ?_⟩
    refine ⟨fun k hk hka x hx hne => ?_, fun x hx hne => ?_⟩
    · have hk' := ((inQ_iff htℓ).1 hk).2 hX
      have := S.H_lt t x hx
      rw [inQ_iff htℓ]
      simp only [hX, iff_true]
      unfold Bet
      constructor
      · intro h; omega
      · intro h; omega
    · have := S.H_lt t x hx
      rw [inQ_iff htℓ]
      simp only [hX, iff_true]
      constructor
      · intro h; omega
      · intro h; omega
  · refine ⟨0, Or.inr fun x hx => by have := S.H_pos t x hx; omega,
      (inQ_iff htℓ).2 (iff_of_false (by have := S.H_pos t ℓ (Ne.symm htℓ); omega) hX), ?_⟩
    refine ⟨fun k hk hka x hx hne => ?_, fun x hx hne => ?_⟩
    · have hk' := mt ((inQ_iff htℓ).1 hk).1 hX
      have := S.H_pos t x hx
      rw [inQ_iff htℓ]
      simp only [hX, iff_false]
      unfold Bet
      constructor
      · intro h; omega
      · intro h; omega
    · have := S.H_pos t x hx
      rw [inQ_iff htℓ]
      simp only [hX, iff_false]
      constructor
      · intro h; omega
      · intro h; omega

end Main

end ChordSys

end Pca.Great.Comb
