/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package E (SH Lemma 3.7), the pieces of the darts of a removal

For a removal `X` of the curves `R`, a dart `e'` of `Γ − R` is the joined segment of the darts
`ePc e' t = straight^t (ι e')`, `t ≤ eJ e'` (its **pieces**) of `Γ`; the ends of the pieces
`t < eJ e'` are deleted crossings (the **ports**). `eNxt` walks along the pieces and turns at the
kept crossings like `φ` of `Γ − R`, so that its orbits through first pieces are the cells of `Γ − R`
seen in `Γ`.
-/
import Pca.Sweep.E_Basic
import Pca.Sweep.Removal

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)}

variable (Γ R) in
open Classical in
/-- The next piece: straight on at a deleted crossing, turn like `φ` at a kept one. -/
noncomputable def eNxt (f : D) : D := if Γ.rK R (Γ.α f) then Γ.φ f else Γ.straight f

theorem e_crossing_nxt (f : D) : Γ.crossingOf (Γ.eNxt R f) = Γ.crossingOf (Γ.α f) := by
  unfold eNxt
  split_ifs
  · rw [j_φ_apply, j_crossingOf_σ]
  · exact r_crossingOf_straight Γ _

namespace Removal

variable (X : Γ.Removal R)

/-- The number of deleted crossings on the joined segment of `e'`. -/
noncomputable def eJ (e' : X.D') : ℕ := Γ.rJ R (X.ι e')

/-- The `t`-th piece of `e'`. -/
def ePc (e' : X.D') (t : ℕ) : D := (Γ.straight ^ t) (X.ι e')

variable {X}

theorem e_rK (e' : X.D') : Γ.rK R (X.ι e') := (r_keep X e').1

theorem e_pc_zero (e' : X.D') : X.ePc e' 0 = X.ι e' := rfl

theorem e_pc_succ (e' : X.D') (t : ℕ) : X.ePc e' (t + 1) = Γ.straight (X.ePc e' t) :=
  r_pow_succ Γ _ _

theorem e_ι_α (e' : X.D') : X.ι (X.Γ'.α e') = Γ.rHit R (X.ι e') := by
  obtain ⟨e, hp, hnd, he⟩ := X.isRemoval.α e'
  rw [he, r_hit_eq (e_rK e'), ← r_piece_eq (e_rK e') hp hnd]

theorem e_ι_α' (e' : X.D') : X.ι (X.Γ'.α e') = Γ.α (X.ePc e' (X.eJ e')) := by
  rw [e_ι_α, r_hit_eq (e_rK e')]; rfl

theorem e_ι_φ (e' : X.D') : X.ι (X.Γ'.φ e') = Γ.φ (X.ePc e' (X.eJ e')) := by
  rw [j_φ_apply, X.isRemoval.σ, e_ι_α', j_φ_apply]

theorem e_eJ_α (e' : X.D') : X.eJ (X.Γ'.α e') = X.eJ e' := by
  unfold eJ; rw [e_ι_α, r_J_hit (e_rK e')]

theorem e_α_pc (e' : X.D') {t : ℕ} (ht : t ≤ X.eJ e') :
    Γ.α (X.ePc e' t) = X.ePc (X.Γ'.α e') (X.eJ e' - t) := by
  have h1 : Γ.rHit R (X.ι (X.Γ'.α e')) = X.ι e' := by rw [e_ι_α, r_hit_hit (e_rK e')]
  have h2 : Γ.rJ R (X.ι (X.Γ'.α e')) = X.eJ e' := e_eJ_α e'
  have := r_rev (e_rK (X.Γ'.α e')) (i := t) (by rw [h2]; exact ht)
  rw [h1, h2] at this
  exact this

theorem e_pc_unique {e1 e2 : X.D'} {a b : ℕ} (ha : a ≤ X.eJ e1) (hb : b ≤ X.eJ e2)
    (h : X.ePc e1 a = X.ePc e2 b) : e1 = e2 :=
  X.isRemoval.inj (r_piece_unique (e_rK e1) (e_rK e2) ha hb h)

theorem e_pc_idx {e' : X.D'} {a b : ℕ} (ha : a ≤ X.eJ e') (hb : b ≤ X.eJ e')
    (h : X.ePc e' a = X.ePc e' b) : a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha h.symm (by omega)).symm
  rcases Nat.eq_or_lt_of_le hab with h0 | h0
  · exact h0
  exfalso
  have h2 : X.ι e' = (Γ.straight ^ (b - a)) (X.ι e') := by
    have := congrArg (⇑((Γ.straight ^ a)⁻¹)) h
    unfold ePc at this
    rw [Pca.MapFacts.pow_inv_pow_apply _ hab, Pca.MapFacts.pow_inv_pow_apply _ le_rfl, Nat.sub_self,
      pow_zero, Perm.one_apply] at this
    exact this
  exact r_notK_pow (e_rK e') (t := b - a) (by omega) (by unfold eJ at hb; omega) (h2 ▸ e_rK e')

theorem e_pc_rK {e' : X.D'} {t : ℕ} (ht : t ≤ X.eJ e') :
    Γ.rK R (Γ.α (X.ePc e' t)) ↔ t = X.eJ e' := by
  constructor
  · intro h
    by_contra hne
    exact r_notK_lt (e_rK e') (show t < Γ.rJ R (X.ι e') by unfold eJ at ht hne; omega) h
  · rintro rfl; exact r_K_end (e_rK e')

theorem e_curve_pc (e' : X.D') (t : ℕ) : Γ.curve (X.ePc e' t) = X.Γ'.curve e' := by
  unfold ePc; rw [r_curve_pow, X.isRemoval.curve]

theorem e_curve_pc_nmem (e' : X.D') (t : ℕ) : Γ.curve (X.ePc e' t) ∉ R := by
  unfold ePc; rw [r_curve_pow]; exact Γ.r_curve_not_mem R (e_rK e')

theorem e_cell_pc {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) (e' : X.D') {t : ℕ}
    (ht : t ≤ X.eJ e') : r (Γ.cellOf (X.ePc e' t)) = r (Γ.cellOf (X.ι e')) :=
  r_cell_pow r hr (e_rK e') ht

theorem e_side_pc (e' : X.D') {t : ℕ} (ht : t ≤ X.eJ e') :
    Γ.side (Γ.cellOf (X.ePc e' t)) = X.Γ'.side (X.Γ'.cellOf e') := by
  rw [e_cell_pc Γ.side (r_side_R (r_S_not_mem X e')) e' ht]
  exact (X.isRemoval.side e').symm

theorem e_crossing_pc_succ (e' : X.D') (t : ℕ) :
    Γ.crossingOf (X.ePc e' (t + 1)) = Γ.crossingOf (Γ.α (X.ePc e' t)) := by
  rw [e_pc_succ]; exact r_crossingOf_straight Γ _

theorem e_nxt_lt {e' : X.D'} {t : ℕ} (ht : t < X.eJ e') :
    Γ.eNxt R (X.ePc e' t) = X.ePc e' (t + 1) := by
  unfold eNxt
  rw [if_neg (fun h => by have := (e_pc_rK ht.le).1 h; omega), e_pc_succ]

theorem e_nxt_last (e' : X.D') : Γ.eNxt R (X.ePc e' (X.eJ e')) = X.ι (X.Γ'.φ e') := by
  unfold eNxt
  rw [if_pos ((e_pc_rK le_rfl).2 rfl), e_ι_φ]

/-- The pieces of `e'` along `eNxt`, then the first piece of `φ' e'`. -/
theorem e_nxt_iter (e' : X.D') {t : ℕ} (ht : t ≤ X.eJ e') :
    (Γ.eNxt R)^[t] (X.ι e') = X.ePc e' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), e_nxt_lt (by omega)]

theorem e_nxt_iter_succ (e' : X.D') :
    (Γ.eNxt R)^[X.eJ e' + 1] (X.ι e') = X.ι (X.Γ'.φ e') := by
  rw [Function.iterate_succ_apply', e_nxt_iter e' le_rfl, e_nxt_last]

/-! ## Every dart of `Γ` above the sweep, not on a removed curve, is a piece -/

/-- The straight walk from a surviving dart runs through pieces. -/
theorem e_piece_of_keep {w : D} (hw : Γ.Keep R w) (m : ℕ) :
    ∃ e' t, t ≤ X.eJ e' ∧ X.ePc e' t = (Γ.straight ^ m) w := by
  induction m with
  | zero =>
    obtain ⟨e', he'⟩ := (X.isRemoval.range w).2 hw
    exact ⟨e', 0, Nat.zero_le _, he'⟩
  | succ m ih =>
    obtain ⟨e', t, ht, he⟩ := ih
    rw [r_pow_succ, ← he]
    rcases Nat.lt_or_ge t (X.eJ e') with hlt | hge
    · exact ⟨e', t + 1, hlt, e_pc_succ e' t⟩
    · have hteq : t = X.eJ e' := le_antisymm ht hge
      subst hteq
      have hk : Γ.Keep R (Γ.straight (X.ePc e' (X.eJ e'))) := by
        rw [j_straight_apply, ← e_ι_α']
        exact r_keep_σ (r_keep_σ (r_keep X _))
      obtain ⟨e2, he2⟩ := (X.isRemoval.range _).2 hk
      exact ⟨e2, 0, Nat.zero_le _, he2⟩

/-- A dart above the sweep whose curve is not removed is a piece, provided every curve with a
part above the sweep has a vertex on the sweep (SH Lemma 3.4). -/
theorem e_piece_exists (h34 : ∀ δ, Γ.Present δ → Γ.MeetsSweep δ) [Nonempty X.D'] {e : D}
    (hR : Γ.curve e ∉ R) (hup : Γ.Up (Γ.cellOf e)) :
    ∃ e' t, t ≤ X.eJ e' ∧ X.ePc e' t = e := by
  have hSR : Γ.S ∉ R := r_S_not_mem X (Classical.arbitrary _)
  obtain ⟨y0, hy0, hk0⟩ : ∃ y0, Γ.curve y0 = Γ.curve e ∧ Γ.Keep R y0 := by
    by_cases hS : Γ.curve e = Γ.S
    · obtain ⟨d0, hd0⟩ := X.Γ'.isSConf.S_mem inferInstance
      refine ⟨X.ι d0, ?_, r_keep X d0⟩
      rw [← X.isRemoval.curve, hd0, X.isRemoval.S, hS]
    · obtain ⟨x, hx, hon⟩ := h34 _ ⟨hS, e, rfl, hS, hup⟩
      obtain ⟨y, rfl⟩ := x.exists_mk
      have hc := j_curves_crossingOf Γ y
      have hSm : Γ.S ∈ Γ.curves (Γ.crossingOf y) := hx.1
      have hδm : Γ.curve e ∈ Γ.curves (Γ.crossingOf y) := hon
      obtain ⟨y0, hy0, hσ, hx0⟩ : ∃ y0, Γ.curve y0 = Γ.curve e ∧
          Γ.curve (Γ.σ y0) = Γ.S ∧ Γ.crossingOf y0 = Γ.crossingOf y := by
        rw [hc, mem_insert, mem_singleton] at hSm hδm
        rcases hδm with h1 | h1
        · refine ⟨y, h1.symm, ?_, rfl⟩
          rcases hSm with h2 | h2
          · exact absurd (h1.trans h2.symm) hS
          · exact h2.symm
        · refine ⟨Γ.σ y, h1.symm, ?_, j_crossingOf_σ _ _⟩
          rcases hSm with h2 | h2
          · rw [j_curve_σσ]; exact h2.symm
          · exact absurd (h1.trans h2.symm) hS
      have hK : Γ.rK R y0 := by
        intro hdel
        rw [r_deleted_iff, hy0, hσ] at hdel
        rcases hdel with h | h
        · exact hR h
        · exact hSR h
      have hKσ : Γ.rK R (Γ.σ y0) := (Γ.r_rK_σ R y0).2 hK
      exact ⟨y0, hy0, hK, Γ.σ y0, hσ, .rel _ _ ⟨hK, hKσ, Or.inl rfl⟩⟩
  have hk1 : Γ.Keep R (Γ.σ (Γ.σ y0)) := r_keep_σ (r_keep_σ hk0)
  obtain ⟨k, hk, hsc⟩ : ∃ k, Γ.Keep R k ∧ Γ.straight.SameCycle k e := by
    rcases Γ.isSConf.straight e y0 hy0.symm with h | h
    · exact ⟨y0, hk0, h.symm⟩
    · exact ⟨_, hk1, h.symm⟩
  obtain ⟨m, hm⟩ := hsc.exists_nat_pow_eq
  rw [← hm]
  exact e_piece_of_keep hk m

/-! ## Ports on a finite edge are vertices on the sweep -/

/-- The dart of `Γ` of a finite edge of `Γ − R` is a sweep dart. -/
theorem e_sweep_ι {d' : X.D'} (hd : X.Γ'.IsSweepDart d') : Γ.IsSweepDart (X.ι d') := by
  have hc : Γ.curve (X.ι d') = Γ.S := by rw [← X.isRemoval.curve, hd.1, X.isRemoval.S]
  rw [no_sweep_iff hc]
  rw [← X.isRemoval.side]
  exact (no_sweep_iff hd.1).1 hd

/-- The deleted crossings on a finite edge of `Γ − R` are not inside the ∞-arc of `Γ`. -/
theorem e_port_not_inf {d' : X.D'} (hd : X.Γ'.IsFinSeg d') {s : ℕ} (hs : s < X.eJ d') :
    ¬ Γ.IsInfVertex (Γ.crossingOf (Γ.α (X.ePc d' s))) := by
  rintro ⟨z, hz, i, hi, hx⟩
  have hz' : Γ.infStart = some z := hz
  have hA : Γ.IsSweepDart ((Γ.straight ^ (i + 1)) z) := no_sweep_pow (no_z_sweep hz') _
  have hB : Γ.IsSweepDart (X.ePc d' (s + 1)) := no_sweep_pow (e_sweep_ι hd.1) _
  have hAB : (Γ.straight ^ (i + 1)) z = X.ePc d' (s + 1) := by
    refine no_sweep_unique hB hA ?_
    rw [no_pow_succ, r_crossingOf_straight, e_crossing_pc_succ, hx]
  rcases Nat.lt_or_ge s i with hsi | hsi
  · -- `ι d'` starts at an inner crossing of the ∞-arc
    have h1 : X.ι d' = (Γ.straight ^ (i - s)) z := by
      have := congrArg (⇑((Γ.straight ^ (s + 1))⁻¹)) hAB
      unfold ePc at this
      rw [Pca.MapFacts.pow_inv_pow_apply _ (by omega), Pca.MapFacts.pow_inv_pow_apply _ le_rfl,
        Nat.sub_self, pow_zero, Perm.one_apply] at this
      rw [← this]; congr 2; omega
    have hinf : Γ.IsInfVertex (Γ.crossingOf (X.ι d')) := by
      obtain ⟨q, hq⟩ : ∃ q, i - s = q + 1 := ⟨i - s - 1, by omega⟩
      refine ⟨z, hz, q, by omega, ?_⟩
      rw [h1, hq, no_pow_succ, r_crossingOf_straight]
    have := (X.isRemoval.infVertex d').2 hinf
    exact (e_finSeg_fin hd).1.2 this
  · -- `z` is a piece of `d'`, so `d'` is the start of the ∞-arc of `Γ − R`
    have h1 : z = X.ePc d' (s - i) := by
      have := congrArg (⇑((Γ.straight ^ (i + 1))⁻¹)) hAB
      unfold ePc at this
      rw [Pca.MapFacts.pow_inv_pow_apply _ le_rfl, Pca.MapFacts.pow_inv_pow_apply _ (by omega),
        Nat.sub_self, pow_zero, Perm.one_apply] at this
      rw [this]; unfold ePc; congr 2; omega
    obtain ⟨z', hz'm⟩ : ∃ z', X.Γ'.infStart = some z' :=
      Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
    obtain ⟨z0, hz0, hp⟩ := X.isRemoval.infStart z' (by rw [hz'm]; rfl)
    have hz0' : z0 = z := by rw [hz'] at hz0; exact (Option.some_inj.1 hz0).symm
    subst hz0'
    obtain ⟨k, hk, hkz⟩ := (Γ.r_piece_iff R).1 hp
    have hkJ : k ≤ X.eJ z' := by
      by_contra hlt
      exact hk _ (show Γ.rJ R (X.ι z') < k by unfold eJ at hlt; omega) (r_K_end (e_rK z'))
    have heq : d' = z' := e_pc_unique (a := s - i) (b := k) (by omega) hkJ
      (by rw [← h1]; exact hkz.symm)
    subst heq
    apply hd.2
    show d' ∈ arcOf X.Γ'.σ X.Γ'.α X.Γ'.infStart X.Γ'.infLen
    rw [hz'm]
    exact mem_image.2 ⟨0, mem_range.2 (Nat.succ_pos _), rfl⟩

end Removal

end SConf

end Pca.Sweep
