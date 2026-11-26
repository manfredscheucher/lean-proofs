/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma, combinatorial form (`doc/pca/great.md` section 3.3)
-/
import Pca.Great.Q_Step
import Mathlib.Data.Finset.Prod

open Finset

namespace Pca.Great.Comb

namespace ChordSys

variable {ι : Type*} [DecidableEq ι] {S : ChordSys ι} {ℓ : ι} {Nq : Prop} [Decidable Nq]
  {T : Finset ι}

theorem flip_helper {X p q σ : Prop} (h1 : ¬ (p ↔ q)) (h2 : ¬ (¬ (X ↔ p) ↔ σ)) :
    ¬ (X ↔ q) ↔ σ := by tauto

section Main

variable {i j : ι} (hij : S.IsFirst ℓ Nq T i j) (hiℓ : i ≠ ℓ)
include hij hiℓ

theorem gap_lt {t s : ι} (ht : t ∈ T) (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hb : Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)) (hst : s ≠ t)
    (hs : s = j ∨ (s ≠ i ∧ s ≠ ℓ ∧ s ≠ t ∧ Bet (S.H ℓ s) (S.H ℓ i) (S.H ℓ j))) :
    S.gap ℓ T t s < S.gap ℓ T i j := by
  classical
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have Hne : ∀ {x y : ι}, x ≠ ℓ → y ≠ ℓ → x ≠ y → S.H ℓ x ≠ S.H ℓ y :=
    fun hx hy hxy h => hxy (S.H_inj _ _ _ hx hy h)
  unfold gap
  apply card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · obtain ⟨huT, huℓ, hut, hus, hbu⟩ := mem_filter.1 hu
    have h1 := Hne huℓ hiℓ
    have h2 := Hne huℓ hjℓ
    refine mem_filter.2 ⟨huT, huℓ, ?_, ?_, ?_⟩
    · rintro rfl
      rcases hs with rfl | ⟨-, -, -, hs'⟩ <;> unfold Bet at hb hbu <;> try unfold Bet at hs'
      all_goals omega
    · rintro rfl
      rcases hs with rfl | ⟨-, hsℓ, -, hs'⟩
      · exact hus rfl
      · unfold Bet at hb hbu hs'; omega
    · rcases hs with rfl | ⟨-, -, -, hs'⟩ <;> unfold Bet at hb hbu ⊢ <;> try unfold Bet at hs'
      all_goals omega
  · have := hsub (mem_filter.2 ⟨ht, htℓ, hti, htj, hb⟩)
    obtain ⟨-, -, h, -⟩ := mem_filter.1 this
    exact h rfl

/-- Along `j`, no chord of `T` crosses between `ℓ` and `i` (given the statement along `ℓ`). -/
theorem no_cross_j
    (hC1 : ∀ t ∈ T, t ≠ ℓ → t ≠ i → t ≠ j → ¬ Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j))
    {t : ι} (ht : t ∈ T) (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hb : Bet (S.H j t) (S.H j ℓ) (S.H j i)) : False := by
  obtain ⟨hjℓ, hji, hjT⟩ := first_ne hij hiℓ
  have Hne : ∀ {e x y : ι}, x ≠ e → y ≠ e → x ≠ y → S.H e x ≠ S.H e y :=
    fun hx hy hxy h => hxy (S.H_inj _ _ _ hx hy h)
  have hQji : S.InQ ℓ Nq j (S.H j i) := by
    have := hij.1.2.2.2
    unfold InQ at this ⊢
    rwa [S.rel' (Ne.symm hiℓ) (Ne.symm hjℓ) (Ne.symm hji)] at this
  have hQjt : S.InQ ℓ Nq j (S.H j t) := inQ_of_bet hjℓ hQji hb
  have vi : S.Rt i j (S.H j t) ↔ S.Rt i ℓ (S.H ℓ j) :=
    (S.Rt_of_not_bet (Hne (Ne.symm hji) htj (Ne.symm hti)) (Hne (Ne.symm hji) (Ne.symm hjℓ) hiℓ)
      (by unfold Bet at hb ⊢; omega)).trans (S.rel' (Ne.symm hji) hiℓ hjℓ)
  have ci : S.Rt i t (S.H t j) ↔ S.Rt i ℓ (S.H ℓ j) :=
    (S.rel' (Ne.symm hti) (Ne.symm hji) htj).trans vi
  have qc : S.InQ ℓ Nq t (S.H t j) := by
    unfold InQ; rw [S.rel' (Ne.symm htℓ) (Ne.symm hjℓ) htj]; exact hQjt
  obtain ⟨E, hE, hEQ, hEk, hEa⟩ := exists_end hij hiℓ (t := t) htℓ
  have DL := not_cross_i hij hiℓ ht htℓ hti htj
  have BL := not_end hij hiℓ htℓ hti htj hE hEQ
  have hab : S.H t ℓ ≠ S.H t i := Hne htℓ.symm hti.symm hiℓ.symm
  have hac : S.H t ℓ ≠ S.H t j := Hne htℓ.symm htj.symm hjℓ.symm
  have hbc : S.H t i ≠ S.H t j := Hne hti.symm htj.symm hji.symm
  by_cases hX : S.Rt j t (S.H t ℓ) ↔ S.Rt j ℓ (S.H ℓ i)
  · by_cases hb' : Bet (S.H t i) (S.H t ℓ) (S.H t j)
    · exact DL (inQ_of_bet htℓ qc hb')
        ((S.Rt_of_not_bet hbc.symm hac.symm (by unfold Bet at hb' ⊢; omega)).trans hX)
    · have ia : S.Rt i t (S.H t ℓ) ↔ S.Rt i ℓ (S.H ℓ j) :=
        (S.Rt_of_not_bet hab.symm hbc hb').trans ci
      have u1 := iff_of_not_iff_iff ((S.rel' hiℓ (Ne.symm hti) (Ne.symm htℓ)).trans ia)
      have u2 := iff_of_not_iff_iff ((S.rel' hjℓ (Ne.symm htj) (Ne.symm htℓ)).trans hX)
      apply hC1 t ht htℓ hti htj
      have w1 : S.H ℓ t ≠ S.H ℓ i := Hne htℓ hiℓ hti
      have w2 : S.H ℓ t ≠ S.H ℓ j := Hne htℓ hjℓ htj
      have w3 : S.H ℓ i ≠ S.H ℓ j := Hne hiℓ hjℓ (Ne.symm hji)
      unfold Bet; omega
  · have hj1 := (hEa j htj.symm hac.symm).not.2 (not_not.2 qc)
    have jE : S.Rt j t E ↔ S.Rt j ℓ (S.H ℓ i) := flip_helper hj1 hX
    by_cases hb2 : S.InQ ℓ Nq t (S.H t i) ∧ Bet (S.H t j) (S.H t ℓ) (S.H t i)
    · refine DL hb2.1 ((S.Rt_congr ((hEk _ hb2.1 hab.symm j htj.symm hbc.symm).2 ?_)).trans jE)
      rintro ⟨-, h⟩; have := hb2.2; unfold Bet at h this; omega
    · exact BL ((S.Rt_congr ((hEk _ qc hac.symm i hti.symm hbc).2 hb2)).symm.trans ci) jE

end Main

/-- **Quarter lemma, combinatorial form.** -/
theorem exists_tri_aux (hTℓ : ℓ ∈ T) (hex : ∃ e f, e ∈ T ∧ e ≠ ℓ ∧ S.Cand ℓ Nq T e f) :
    ∃ i j, i ∈ T ∧ i ≠ ℓ ∧ S.IsFirst ℓ Nq T i j ∧
      (∀ t ∈ T, t ≠ ℓ → t ≠ i → t ≠ j → ¬ Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)) ∧
      (∀ t ∈ T, t ≠ ℓ → t ≠ i → t ≠ j → ¬ Bet (S.H j t) (S.H j ℓ) (S.H j i)) := by
  classical
  set Pairs := (T ×ˢ T).filter fun q : ι × ι => q.1 ≠ ℓ ∧ S.IsFirst ℓ Nq T q.1 q.2
  obtain ⟨e, f, he, heℓ, hc⟩ := hex
  obtain ⟨f', hf'⟩ := exists_first heℓ hc
  have hne : Pairs.Nonempty := ⟨(e, f'), mem_filter.2 ⟨mem_product.2 ⟨he, hf'.1.1⟩, heℓ, hf'⟩⟩
  obtain ⟨⟨i, j⟩, hmem, hmin⟩ := Pairs.exists_min_image (fun q => S.gap ℓ T q.1 q.2) hne
  obtain ⟨hprod, hiℓ, hij⟩ := mem_filter.1 hmem
  have hiT := (mem_product.1 hprod).1
  have hC1 : ∀ t ∈ T, t ≠ ℓ → t ≠ i → t ≠ j → ¬ Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j) := by
    intro t ht htℓ hti htj hb
    obtain ⟨s, hs, hs'⟩ := step hij hiℓ hiT ht htℓ hti htj hb
    have hst : s ≠ t := hs.1.2.2.1
    have hlt := gap_lt hij hiℓ ht htℓ hti htj hb hst hs'
    exact absurd (hmin (t, s) (mem_filter.2 ⟨mem_product.2 ⟨ht, hs.1.1⟩, htℓ, hs⟩))
      (not_le.2 hlt)
  exact ⟨i, j, hiT, hiℓ, hij, hC1, fun t ht htℓ hti htj hb =>
    no_cross_j hij hiℓ hC1 ht htℓ hti htj hb⟩


end ChordSys

end Pca.Great.Comb
