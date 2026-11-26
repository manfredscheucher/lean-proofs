/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: the canonical form is unique up to isomorphism (`doc/pca/great.md` section 3.4)

In the canonical form the positions along the chords are determined by the positions `p` on the
frame curve (`hpos_count`), hence so is the rotation table (`R_Table`). Two canonical arrangements
are isomorphic (`cf_iso`): relabel the curves by their positions on the frame curve.
-/
import Pca.Great.R_Order

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

/-- The curve at a position of a chord in `H`. -/
theorem curveAt_spec {c : Fin n} (hc : c ≠ F.c0) {k : ℕ} (hk0 : 0 < k) (hk : k < n - 1) :
    F.data.curveAt c k ≠ F.c0 ∧ F.data.curveAt c k ≠ c ∧ F.hpos c (F.data.curveAt c k) = k := by
  rw [data_curveAt]
  set u := A.curve (A.σ ((A.straight ^ k) (F.β c)))
  have hcu : c ≠ u := by
    intro h
    apply A.isArrangement.curve_σ ((A.straight ^ k) (F.β c))
    rw [curve_straight_pow, F.curve_β hA hc]; exact h.symm
  have hu0 : u ≠ F.c0 := by
    intro h
    have := A.mem_curves_crossingOf_σ ((A.straight ^ k) (F.β c))
    rw [show A.curve (A.σ ((A.straight ^ k) (F.β c))) = F.c0 from h] at this
    rcases (F.c0_mem_chord_iff hA hc (k := k) (by omega)).1 this with h' | h' <;> omega
  exact ⟨hu0, Ne.symm hcu, (F.hpos_unique hA hc hcu hk (A.mem_curves_crossingOf_σ _)).symm⟩

/-- Every position `k < n - 1` of the frame curve is the start of a chord. -/
theorem exists_p {k : ℕ} (hk : k < n - 1) : ∃ e, e ≠ F.c0 ∧ F.p e = k := by
  set e := A.curve (A.σ ((A.straight ^ k) F.β0))
  have he0 : e ≠ F.c0 := by
    rw [← F.curve_β0, ← curve_straight_pow k F.β0]; exact A.isArrangement.curve_σ _
  have h := (F.mem_curves_c0_iff hA he0 (k := k) (by omega)).1 (A.mem_curves_crossingOf_σ _)
  have := F.p_lt hA he0
  exact ⟨e, he0, by omega⟩

/-- **The positions in the canonical form.** -/
theorem hpos_count (hpot : F.pot = 0) {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hef : e ≠ f) :
    F.hpos e f = 1 + (univ.filter fun g => g ≠ F.c0 ∧ g ≠ e ∧ F.p f < F.p g).card := by
  classical
  have hn := A.two_le_n
  obtain ⟨hf0, hfm, -⟩ := F.hpos_spec hA he hf hef
  have hS : (univ.filter fun g => g ≠ F.c0 ∧ g ≠ e ∧ F.p f < F.p g) =
      univ.filter fun g => g ≠ F.c0 ∧ g ≠ e ∧ F.hpos e g < F.hpos e f := by
    ext g
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hg0, hge, hlt⟩
      have hgf : g ≠ f := fun h => by rw [h] at hlt; omega
      exact ⟨hg0, hge, F.cf_order hA hpot he hg0 hf (Ne.symm hge) hef hgf hlt⟩
    · rintro ⟨hg0, hge, hlt⟩
      refine ⟨hg0, hge, ?_⟩
      have hgf : g ≠ f := fun h => by rw [h] at hlt; omega
      by_contra hc
      have hne : F.p g ≠ F.p f := fun h => hgf (F.p_inj hA hg0 hf h)
      have := F.cf_order hA hpot he hf hg0 hef (Ne.symm hge) (Ne.symm hgf) (by omega)
      omega
  rw [hS]
  have himg : (univ.filter fun g => g ≠ F.c0 ∧ g ≠ e ∧ F.hpos e g < F.hpos e f).image (F.hpos e) =
      Ioo 0 (F.hpos e f) := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_Ioo]
    constructor
    · rintro ⟨g, ⟨hg0, hge, hlt⟩, rfl⟩
      exact ⟨(F.hpos_spec hA he hg0 (Ne.symm hge)).1, hlt⟩
    · rintro ⟨hk0, hk⟩
      obtain ⟨h1, h2, h3⟩ := F.curveAt_spec hA he hk0 (by omega)
      exact ⟨_, ⟨h1, h2, by rw [h3]; exact hk⟩, h3⟩
  have hinj : Set.InjOn (F.hpos e)
      (univ.filter fun g => g ≠ F.c0 ∧ g ≠ e ∧ F.hpos e g < F.hpos e f : Set (Fin n)) := by
    intro x hx y hy h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    exact F.hpos_inj hA he hx.1 hy.1 (Ne.symm hx.2.1) (Ne.symm hy.2.1) h
  rw [← card_image_of_injOn hinj, himg, Nat.card_Ioo]
  omega

end Frame

end Pca.Great
