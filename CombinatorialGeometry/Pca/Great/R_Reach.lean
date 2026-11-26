/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: every great arrangement flips to the canonical form (`doc/pca/great.md` section 3.4)
-/
import Pca.Great.R_Exist

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

/-- Two sorted triples with the same set of curves are equal. -/
theorem sorted_eq {p : Fin n → ℕ} {t t' : Fin n × Fin n × Fin n} (h1 : p t.1 < p t.2.1)
    (h2 : p t.2.1 < p t.2.2) (h1' : p t'.1 < p t'.2.1) (h2' : p t'.2.1 < p t'.2.2)
    (h : ({t.1, t.2.1, t.2.2} : Finset (Fin n)) = {t'.1, t'.2.1, t'.2.2}) : t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  simp only at h1 h2 h1' h2' h
  have ha : a ∈ ({a', b', c'} : Finset (Fin n)) := h ▸ by simp
  have hb : b ∈ ({a', b', c'} : Finset (Fin n)) := h ▸ by simp
  have hc : c ∈ ({a', b', c'} : Finset (Fin n)) := h ▸ by simp
  have ha' : a' ∈ ({a, b, c} : Finset (Fin n)) := h.symm ▸ by simp
  have hb' : b' ∈ ({a, b, c} : Finset (Fin n)) := h.symm ▸ by simp
  have hc' : c' ∈ ({a, b, c} : Finset (Fin n)) := h.symm ▸ by simp
  simp only [mem_insert, mem_singleton] at ha hb hc ha' hb' hc'
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> first | rfl | omega |
    (rcases ha' with h | h | h <;> rcases hb' with h' | h' | h' <;>
      rcases hc' with h'' | h'' | h'' <;> subst_vars <;> omega)

variable (F : Frame A) (hA : A.IsGreat)
include hA

/-- **Reaching the canonical form**: antipodal flips bring every great arrangement to potential
`0` (for the same frame curve and base dart). -/
theorem reach_cf : ∃ (C : Arrangement n D) (FC : Frame C), Relation.ReflTransGen Arrangement.AFlip A C ∧
    C.IsGreat ∧ FC.pot = 0 ∧ FC.c0 = F.c0 ∧ FC.β0 = F.β0 := by
  classical
  induction h : F.pot using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    by_cases hk : k = 0
    · exact ⟨A, F, .refl, hA, h.trans hk, rfl, rfl⟩
    obtain ⟨d, hT, hc0, hH, t0, hbad, hset⟩ := F.exists_bad_tri hA (by omega)
    obtain ⟨hT', hc0', hneg⟩ := F.neg_aflip hA hT hc0 hH
    set B := (A.flip d hT).flip (A.α (ant A d)) hT'
    set FB := (F.flipF hT).flipF hT'
    have hanti := isAntipodalTri_ant hA hT
    have hAB : A.AFlip B := ⟨d, A.α (ant A d), hT, hanti, hT', rfl⟩
    have hB := AFlip.isGreat hA hAB
    have hp : ∀ e, FB.p e = F.p e := fun e => by
      rw [(F.flipF hT).flip_p hT' hc0' e, F.flip_p hT hc0 e]
    have hbad' : ∀ t, FB.Bad t ↔ F.Bad t ∧ t ≠ t0 := by
      intro t
      unfold Bad
      rw [hp, hp, hp]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6⟩
        have hab : t.1 ≠ t.2.1 := fun e => by rw [e] at h4; omega
        have hac : t.1 ≠ t.2.2 := fun e => by rw [e] at h4; omega
        have hbc : t.2.1 ≠ t.2.2 := fun e => by rw [e] at h5; omega
        have := (hneg _ _ _ h1 h2 h3 hab hac hbc).1 h6
        by_cases hs : ({t.1, t.2.1, t.2.2} : Finset (Fin n)) =
            Arrangement.Cell.curves A (A.cellOf d)
        · exfalso
          have ht : t = t0 := sorted_eq h4 h5 hbad.2.2.2.1 hbad.2.2.2.2.1 (hs.trans hset.symm)
          subst ht
          exact (this.1 hbad.2.2.2.2.2) hs
        · exact ⟨⟨h1, h2, h3, h4, h5, this.2 hs⟩, fun e => hs (e ▸ hset)⟩
      · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, hne⟩
        have hab : t.1 ≠ t.2.1 := fun e => by rw [e] at h4; omega
        have hac : t.1 ≠ t.2.2 := fun e => by rw [e] at h4; omega
        have hbc : t.2.1 ≠ t.2.2 := fun e => by rw [e] at h5; omega
        refine ⟨h1, h2, h3, h4, h5, (hneg _ _ _ h1 h2 h3 hab hac hbc).2 ⟨fun _ => ?_, fun _ => h6⟩⟩
        intro hs
        exact hne (sorted_eq h4 h5 hbad.2.2.2.1 hbad.2.2.2.2.1 (hs.trans hset.symm))
    have hpot : FB.pot + 1 = k := by
      rw [← h]
      unfold pot
      have : univ.filter FB.Bad = (univ.filter F.Bad).erase t0 := by
        ext t; simp only [mem_filter, mem_univ, true_and, mem_erase, hbad']; tauto
      rw [this, card_erase_of_mem (mem_filter.2 ⟨mem_univ _, hbad⟩)]
      have := card_pos.2 ⟨t0, mem_filter.2 ⟨mem_univ _, hbad⟩⟩
      omega
    obtain ⟨C, FC, hBC, hC, hFC, h1, h2⟩ := ih FB.pot (by omega) FB hB rfl
    exact ⟨C, FC, .head hAB hBC, hC, hFC, h1, h2⟩

end Frame

end Pca.Great
