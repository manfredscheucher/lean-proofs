/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma, combinatorial core: the main step (`doc/pca/great.md` section 3.3)
-/
import Pca.Great.Q_Comb

open Finset

namespace Pca.Great.Comb

namespace ChordSys

variable {ι : Type*} [DecidableEq ι] {S : ChordSys ι} {ℓ : ι} {Nq : Prop} [Decidable Nq]
  {T : Finset ι}

theorem Hne' {e x y : ι} (hx : x ≠ e) (hy : y ≠ e) (hxy : x ≠ y) : S.H e x ≠ S.H e y :=
  fun h => hxy (S.H_inj _ _ _ hx hy h)

section Main

variable {i j : ι} (hij : S.IsFirst ℓ Nq T i j) (hiℓ : i ≠ ℓ)
include hij hiℓ

/-- A chord `t` crossing `ℓ` between `i` and `j` starts in the triangle region. -/
theorem start_signs {t : ι} (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hb : Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)) :
    (S.Rt i t (S.H t ℓ) ↔ S.Rt i ℓ (S.H ℓ j)) ∧ (S.Rt j t (S.H t ℓ) ↔ S.Rt j ℓ (S.H ℓ i)) := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have hℓi : S.H ℓ i ≠ S.H ℓ j := Hne' hiℓ hjℓ hji.symm
  constructor
  · rw [S.rel' (Ne.symm hti) hiℓ htℓ]
    exact S.Rt_of_not_bet (Hne' htℓ hiℓ hti).symm hℓi (by unfold Bet at hb ⊢; omega)
  · rw [S.rel' (Ne.symm htj) hjℓ htℓ]
    exact S.Rt_of_not_bet (Hne' htℓ hjℓ htj).symm hℓi.symm (by unfold Bet at hb ⊢; omega)

/-- Claim A: `t` crosses `j` in the quarter, and before `i` if it crosses `i` there. -/
theorem claimA {t : ι} (ht : t ∈ T) (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hb : Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)) :
    S.InQ ℓ Nq t (S.H t j) ∧
      (¬ S.InQ ℓ Nq t (S.H t i) ∨ Bet (S.H t j) (S.H t ℓ) (S.H t i)) := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  obtain ⟨st_i, st_j⟩ := start_signs hij hiℓ htℓ hti htj hb
  have hab : S.H t ℓ ≠ S.H t i := Hne' htℓ.symm hti.symm hiℓ.symm
  have hac : S.H t ℓ ≠ S.H t j := Hne' htℓ.symm htj.symm hjℓ.symm
  have hbc : S.H t i ≠ S.H t j := Hne' hti.symm htj.symm hji.symm
  obtain ⟨E, hE, hEQ, -, hEa⟩ := exists_end hij hiℓ (t := t) htℓ
  by_cases hQb : S.InQ ℓ Nq t (S.H t i)
  · by_cases hcl : S.InQ ℓ Nq t (S.H t j) ∧ Bet (S.H t j) (S.H t ℓ) (S.H t i)
    · exact ⟨hcl.1, Or.inr hcl.2⟩
    · exfalso
      refine not_cross_i hij hiℓ ht htℓ hti htj hQb ?_
      rw [← st_j]
      refine S.Rt_of_not_bet hbc.symm hac.symm ?_
      intro hbet
      apply hcl
      refine ⟨inQ_of_bet htℓ hQb (by unfold Bet at hbet ⊢; omega), ?_⟩
      unfold Bet at hbet ⊢; omega
  · by_cases hQc : S.InQ ℓ Nq t (S.H t j)
    · exact ⟨hQc, Or.inl hQb⟩
    · exfalso
      refine not_end hij hiℓ htℓ hti htj hE hEQ ?_ ?_
      · rw [← st_i]; exact S.Rt_congr ((hEa i hti.symm hab.symm).2 hQb).symm
      · rw [← st_j]; exact S.Rt_congr ((hEa j htj.symm hac.symm).2 hQc).symm

/-- A chord `s` of `T` that is in the triangle region at its position `d'` starts there too. -/
theorem start_of_mid {s : ι} (hsT : s ∈ T) (hsℓ : s ≠ ℓ) (hsi : s ≠ i) (hsj : s ≠ j) {d' : ℕ}
    (hd'ℓ : d' ≠ S.H s ℓ) (hd'i : S.H s i ≠ d') (hd'j : S.H s j ≠ d')
    (q1 : S.InQ ℓ Nq s d') (i1 : S.Rt i s d' ↔ S.Rt i ℓ (S.H ℓ j))
    (j1 : S.Rt j s d' ↔ S.Rt j ℓ (S.H ℓ i)) :
    (S.Rt i s (S.H s ℓ) ↔ S.Rt i ℓ (S.H ℓ j)) ∧ (S.Rt j s (S.H s ℓ) ↔ S.Rt j ℓ (S.H ℓ i)) := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have ha'b' : S.H s ℓ ≠ S.H s i := Hne' hsℓ.symm hsi.symm hiℓ.symm
  have ha'c' : S.H s ℓ ≠ S.H s j := Hne' hsℓ.symm hsj.symm hjℓ.symm
  have hb'c' : S.H s i ≠ S.H s j := Hne' hsi.symm hsj.symm hji.symm
  obtain ⟨E', hE', hEQ', hEk', -⟩ := exists_end hij hiℓ (t := s) hsℓ
  have DL : S.InQ ℓ Nq s (S.H s i) → (S.Rt j s (S.H s i) ↔ S.Rt j ℓ (S.H ℓ i)) → False :=
    not_cross_i hij hiℓ hsT hsℓ hsi hsj
  have BL : (S.Rt i s E' ↔ S.Rt i ℓ (S.H ℓ j)) → (S.Rt j s E' ↔ S.Rt j ℓ (S.H ℓ i)) → False :=
    not_end hij hiℓ hsℓ hsi hsj hE' hEQ'
  have toE : ∀ x, x ≠ s → S.H s x ≠ d' → ¬ (S.InQ ℓ Nq s (S.H s x) ∧ Bet d' (S.H s ℓ) (S.H s x)) →
      (S.Rt x s d' ↔ S.Rt x s E') := fun x hx hne h =>
    S.Rt_congr ((hEk' d' q1 hd'ℓ x hx hne).2 h)
  constructor
  · rw [← i1]
    refine S.Rt_of_not_bet ha'b'.symm hd'i ?_
    intro hb1
    have hQb' : S.InQ ℓ Nq s (S.H s i) := inQ_of_bet hsℓ q1 hb1
    by_cases hc1 : Bet (S.H s j) (S.H s i) d'
    · refine BL ?_ ?_
      · rw [← i1, toE i hsi.symm hd'i ?_]
        rintro ⟨-, h⟩; unfold Bet at h hb1; omega
      · rw [← j1, toE j hsj.symm hd'j ?_]
        rintro ⟨-, h⟩; unfold Bet at h hb1 hc1; omega
    · exact DL hQb' ((S.Rt_of_not_bet hb'c'.symm hd'j hc1).trans j1)
  · rw [← j1]
    refine S.Rt_of_not_bet ha'c'.symm hd'j ?_
    intro hc1
    by_cases hb2 : S.InQ ℓ Nq s (S.H s i) ∧ Bet d' (S.H s ℓ) (S.H s i)
    · refine DL hb2.1 ((S.Rt_of_not_bet hb'c'.symm hd'j ?_).trans j1)
      have := hb2.2; unfold Bet at this hc1 ⊢; omega
    · refine BL ?_ ?_
      · rw [← i1, toE i hsi.symm hd'i hb2]
      · rw [← j1, toE j hsj.symm hd'j ?_]
        rintro ⟨-, h⟩; unfold Bet at h hc1; omega

/-- A chord starting in the triangle region crosses `ℓ` between `i` and `j`. -/
theorem bet_of_start {s : ι} (hsℓ : s ≠ ℓ) (hsi : s ≠ i) (hsj : s ≠ j)
    (hxi : S.Rt i s (S.H s ℓ) ↔ S.Rt i ℓ (S.H ℓ j))
    (hxj : S.Rt j s (S.H s ℓ) ↔ S.Rt j ℓ (S.H ℓ i)) :
    Bet (S.H ℓ s) (S.H ℓ i) (S.H ℓ j) := by
  obtain ⟨hjℓ, hji, -⟩ := first_ne hij hiℓ
  have v1 := iff_of_not_iff_iff ((S.rel' hiℓ (Ne.symm hsi) hsℓ.symm).trans hxi)
  have v2 := iff_of_not_iff_iff ((S.rel' hjℓ (Ne.symm hsj) hsℓ.symm).trans hxj)
  have w1 : S.H ℓ s ≠ S.H ℓ i := Hne' hsℓ hiℓ hsi
  have w2 : S.H ℓ s ≠ S.H ℓ j := Hne' hsℓ hjℓ hsj
  have w3 : S.H ℓ i ≠ S.H ℓ j := Hne' hiℓ hjℓ (Ne.symm hji)
  unfold Bet; omega

/-- **Main step**: a chord `t` crossing `ℓ` strictly between `i` and `j` has a first crossing `s`
which is `j` or again crosses `ℓ` strictly between `i` and `j`. -/
theorem step (hi : i ∈ T) {t : ι} (ht : t ∈ T) (htℓ : t ≠ ℓ) (hti : t ≠ i) (htj : t ≠ j)
    (hb : Bet (S.H ℓ t) (S.H ℓ i) (S.H ℓ j)) :
    ∃ s, S.IsFirst ℓ Nq T t s ∧
      (s = j ∨ (s ≠ i ∧ s ≠ ℓ ∧ s ≠ t ∧ Bet (S.H ℓ s) (S.H ℓ i) (S.H ℓ j))) := by
  obtain ⟨hjℓ, hji, hjT⟩ := first_ne hij hiℓ
  obtain ⟨st_i, st_j⟩ := start_signs hij hiℓ htℓ hti htj hb
  have hA := claimA hij hiℓ ht htℓ hti htj hb
  have hcand : S.Cand ℓ Nq T t j := ⟨hjT, hjℓ, Ne.symm htj, hA.1⟩
  obtain ⟨s, hs⟩ := exists_first htℓ hcand
  refine ⟨s, hs, ?_⟩
  by_cases hsj : s = j
  · exact Or.inl hsj
  right
  obtain ⟨hsT, hsℓ, hst, hsQ⟩ := hs.1
  have hbs : Bet (S.H t s) (S.H t ℓ) (S.H t j) := hs.2 j hcand (Ne.symm hsj)
  have hsi : s ≠ i := by
    rintro rfl
    rcases hA.2 with h | h
    · exact h hsQ
    · unfold Bet at h hbs; omega
  have hab : S.H t ℓ ≠ S.H t i := Hne' htℓ.symm hti.symm hiℓ.symm
  have hac : S.H t ℓ ≠ S.H t j := Hne' htℓ.symm htj.symm hjℓ.symm
  have hbd : S.H t i ≠ S.H t s := Hne' hti.symm hst (Ne.symm hsi)
  have hcd : S.H t j ≠ S.H t s := Hne' htj.symm hst (Ne.symm hsj)
  have sd_i : S.Rt i t (S.H t s) ↔ S.Rt i ℓ (S.H ℓ j) := by
    rw [← st_i]
    refine S.Rt_of_not_bet hbd hab.symm ?_
    intro hb'
    rcases hA.2 with h | h
    · exact h (inQ_of_bet htℓ hsQ (by unfold Bet at hb' ⊢; omega))
    · unfold Bet at h hb' hbs; omega
  have sd_j : S.Rt j t (S.H t s) ↔ S.Rt j ℓ (S.H ℓ i) := by
    rw [← st_j]
    exact S.Rt_of_not_bet hcd hac.symm (by unfold Bet at hbs ⊢; omega)
  have i1 : S.Rt i s (S.H s t) ↔ S.Rt i ℓ (S.H ℓ j) := by
    rw [← S.rel' (Ne.symm hti) (Ne.symm hsi) (Ne.symm hst)]; exact sd_i
  have j1 : S.Rt j s (S.H s t) ↔ S.Rt j ℓ (S.H ℓ i) := by
    rw [← S.rel' (Ne.symm htj) (Ne.symm hsj) (Ne.symm hst)]; exact sd_j
  have q1 : S.InQ ℓ Nq s (S.H s t) := by
    unfold InQ; rw [← S.rel' (Ne.symm htℓ) (Ne.symm hsℓ) (Ne.symm hst)]; exact hsQ
  obtain ⟨xi, xj⟩ := start_of_mid hij hiℓ hsT hsℓ hsi hsj
    (Hne' hsℓ.symm hst.symm htℓ.symm).symm (Hne' hsi.symm hst.symm hti.symm)
    (Hne' (Ne.symm hsj) hst.symm htj.symm) q1 i1 j1
  exact ⟨hsi, hsℓ, hst, bet_of_start hij hiℓ hsℓ hsi hsj xi xj⟩

end Main

end ChordSys

end Pca.Great.Comb
