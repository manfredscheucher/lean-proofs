/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), basic facts on removing curves

Helper file for `Pca/Sweep/Removal.lean`. For a set `R` of curves:

* `rK R d`: the crossing of `d` is kept (not deleted);
* `rP R`: the involution `σ²` on the darts at deleted crossings (identity elsewhere);
* `rJ R k`, `rHit R k`: the joined segment starting with `k` (at a kept crossing) has the pieces
  `straight^i k`, `i ≤ rJ R k`, and ends with `rHit R k = α (straight^(rJ R k) k)` (the chains
  `x ↦ α (rP x)` of `Pca/Great/Map_Perm.lean`);
* the darts that survive (`Keep`), the reverse of a joined segment, and functions on cells that are
  constant across the segments of removed curves.
-/
import Pca.Sweep.R_Defs
import Pca.Sweep.R_Gen
import Pca.Great.Map_Perm

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}


namespace SConf

variable (Γ : SConf n D) (R : Finset (Fin n))

/-- The crossing of `d` is kept. -/
def rK (d : D) : Prop := ¬ Γ.Deleted R (Γ.crossingOf d)

open Classical in
noncomputable instance (d : D) : Decidable (Γ.rK R d) := inferInstance

open Classical in
noncomputable def rPf (d : D) : D := if Γ.rK R d then d else Γ.σ (Γ.σ d)

/-! ## Rewriting -/

theorem r_crossingOf_σσ (d : D) : Γ.crossingOf (Γ.σ (Γ.σ d)) = Γ.crossingOf d := by
  rw [j_crossingOf_σ, j_crossingOf_σ]

theorem r_crossingOf_straight (d : D) : Γ.crossingOf (Γ.straight d) = Γ.crossingOf (Γ.α d) := by
  rw [j_straight_apply, r_crossingOf_σσ]

theorem r_deleted_iff (d : D) :
    Γ.Deleted R (Γ.crossingOf d) ↔ Γ.curve d ∈ R ∨ Γ.curve (Γ.σ d) ∈ R := by
  unfold Deleted OnCurve
  rw [j_curves_crossingOf]
  constructor
  · rintro ⟨γ, hγ, hm⟩
    rw [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Or.inl hγ
    · exact Or.inr hγ
  · rintro (h | h)
    · exact ⟨_, h, mem_insert_self _ _⟩
    · exact ⟨_, h, mem_insert_of_mem (mem_singleton_self _)⟩

theorem r_rK_σ (d : D) : Γ.rK R (Γ.σ d) ↔ Γ.rK R d := by
  unfold rK; rw [j_crossingOf_σ]

theorem r_rK_σσ (d : D) : Γ.rK R (Γ.σ (Γ.σ d)) ↔ Γ.rK R d := by
  rw [r_rK_σ, r_rK_σ]

theorem r_rK_straight (d : D) : Γ.rK R (Γ.straight d) ↔ Γ.rK R (Γ.α d) := by
  unfold rK; rw [r_crossingOf_straight]

theorem r_curve_not_mem {d : D} (h : Γ.rK R d) : Γ.curve d ∉ R :=
  fun hm => h ((Γ.r_deleted_iff R d).2 (Or.inl hm))

theorem r_curve_pow (d : D) (i : ℕ) : Γ.curve ((Γ.straight ^ i) d) = Γ.curve d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ', Perm.mul_apply, j_curve_straight, ih]

theorem r_pow_succ (d : D) (i : ℕ) :
    (Γ.straight ^ (i + 1)) d = Γ.straight ((Γ.straight ^ i) d) := by
  rw [pow_succ', Perm.mul_apply]

theorem r_piece_iff {d e : D} : Γ.Piece R d e ↔
    ∃ k : ℕ, (∀ i < k, ¬ Γ.rK R (Γ.α ((Γ.straight ^ i) d))) ∧ (Γ.straight ^ k) d = e := by
  unfold Piece rK
  simp only [not_not]

/-! ## The involution `rP` and the chains -/

theorem r_rPf_inv (d : D) : Γ.rPf R (Γ.rPf R d) = d := by
  unfold rPf
  by_cases h : Γ.rK R d
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg (by rw [r_rK_σσ]; exact h), Γ.j_σ4]

noncomputable def rP : Perm D := Function.Involutive.toPerm _ (Γ.r_rPf_inv R)

theorem r_rP_apply (d : D) : Γ.rP R d = Γ.rPf R d := rfl

theorem r_rP_of_not {d : D} (h : ¬ Γ.rK R d) : Γ.rP R d = Γ.σ (Γ.σ d) := by
  rw [r_rP_apply, rPf, if_neg h]

theorem r_hitHyp : MapFacts.HitHyp Γ.α (Γ.rP R) (Γ.rK R) (fun _ => True) where
  aa := Γ.j_α_α
  ane := Γ.isSConf.α_ne
  pp := Γ.r_rPf_inv R
  pK d h := by rw [r_rP_apply, rPf, if_pos h]
  Kp d := by
    rw [r_rP_apply, rPf]
    split_ifs with h
    · rfl
    · exact Γ.r_rK_σσ R d
  Qa _ := Iff.rfl
  Qp _ := Iff.rfl
  KQ _ _ := trivial
  pne d _ h := by rw [r_rP_of_not _ _ h]; exact Γ.j_σσ_ne d

open Classical in
/-- The number of deleted crossings on the joined segment starting with `k`. -/
noncomputable def rJ (k : D) : ℕ := MapFacts.hitIdx Γ.α (Γ.rP R) (Γ.rK R) k

open Classical in
/-- The reverse dart of the joined segment starting with `k`. -/
noncomputable def rHit (k : D) : D := MapFacts.hit Γ.α (Γ.rP R) (Γ.rK R) k

variable {Γ R}

theorem r_chain {k : D} (hk : Γ.rK R k) :
    ∀ i ≤ Γ.rJ R k, ((Γ.α * Γ.rP R) ^ i) (Γ.α k) = Γ.α ((Γ.straight ^ i) k) := by
  classical
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply, r_pow_succ, j_straight_apply]
    have hn := (Γ.r_hitHyp R).not_mem_lt hk (i := i) (by unfold rJ at hi; omega)
    rw [ih (by omega)] at hn
    rw [r_rP_of_not _ _ hn]

theorem r_hit_eq {k : D} (hk : Γ.rK R k) :
    Γ.rHit R k = Γ.α ((Γ.straight ^ Γ.rJ R k) k) := by
  classical
  rw [← r_chain hk _ le_rfl]
  unfold rHit rJ
  convert (Γ.r_hitHyp R).hit_eq hk

theorem r_K_end {k : D} (hk : Γ.rK R k) : Γ.rK R (Γ.α ((Γ.straight ^ Γ.rJ R k) k)) := by
  classical
  rw [← r_hit_eq hk]
  unfold rHit
  convert (Γ.r_hitHyp R).hit_mem hk

theorem r_notK_lt {k : D} (hk : Γ.rK R k) {i : ℕ} (hi : i < Γ.rJ R k) :
    ¬ Γ.rK R (Γ.α ((Γ.straight ^ i) k)) := by
  classical
  rw [← r_chain hk _ hi.le]
  have := (Γ.r_hitHyp R).not_mem_lt hk (i := i) (by unfold rJ at hi; omega)
  convert this

theorem r_J_eq_of {k : D} (hk : Γ.rK R k) {m : ℕ} (hm : Γ.rK R (Γ.α ((Γ.straight ^ m) k)))
    (hlt : ∀ i < m, ¬ Γ.rK R (Γ.α ((Γ.straight ^ i) k))) : Γ.rJ R k = m := by
  rcases lt_trichotomy (Γ.rJ R k) m with h | h | h
  · exact absurd (r_K_end hk) (hlt _ h)
  · exact h
  · exact absurd hm (r_notK_lt hk h)

/-- The darts `straight^t k` for `0 < t ≤ rJ k` lie at deleted crossings. -/
theorem r_notK_pow {k : D} (hk : Γ.rK R k) {t : ℕ} (h0 : 0 < t) (ht : t ≤ Γ.rJ R k) :
    ¬ Γ.rK R ((Γ.straight ^ t) k) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [r_pow_succ, r_rK_straight]
  exact r_notK_lt hk (by omega)

theorem r_piece_J {k : D} (hk : Γ.rK R k) : Γ.Piece R k ((Γ.straight ^ Γ.rJ R k) k) :=
  (Γ.r_piece_iff R).2 ⟨_, fun _ hi => r_notK_lt hk hi, rfl⟩

/-- A piece followed by a kept crossing is the last piece. -/
theorem r_piece_eq {k e : D} (hk : Γ.rK R k) (hp : Γ.Piece R k e) (he : Γ.rK R (Γ.α e)) :
    e = (Γ.straight ^ Γ.rJ R k) k := by
  obtain ⟨m, hm, rfl⟩ := (Γ.r_piece_iff R).1 hp
  rw [r_J_eq_of hk he hm]

theorem r_straight_α (y : D) : Γ.straight (Γ.α y) = Γ.α (Γ.straight⁻¹ y) := by
  obtain ⟨z, rfl⟩ := Γ.straight.surjective y
  rw [Perm.inv_def, Equiv.symm_apply_apply]
  simp only [j_straight_apply, j_α_α, Γ.j_σ4]

theorem r_straight_pow_α (i : ℕ) (y : D) :
    (Γ.straight ^ i) (Γ.α y) = Γ.α ((Γ.straight ^ i)⁻¹ y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [r_pow_succ, ih, r_straight_α, pow_succ, mul_inv_rev, Perm.mul_apply]

/-- The reverse of a joined segment: its pieces in the other direction. -/
theorem r_rev {k : D} (hk : Γ.rK R k) {i : ℕ} (hi : i ≤ Γ.rJ R k) :
    Γ.α ((Γ.straight ^ i) (Γ.rHit R k)) = (Γ.straight ^ (Γ.rJ R k - i)) k := by
  rw [r_hit_eq hk, r_straight_pow_α, j_α_α, MapFacts.pow_inv_pow_apply _ hi]

theorem r_K_hit {k : D} (hk : Γ.rK R k) : Γ.rK R (Γ.rHit R k) := by
  rw [r_hit_eq hk]; exact r_K_end hk

theorem r_J_hit {k : D} (hk : Γ.rK R k) : Γ.rJ R (Γ.rHit R k) = Γ.rJ R k := by
  refine r_J_eq_of (r_K_hit hk) ?_ fun i hi => ?_
  · rw [r_rev hk le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]; exact hk
  · rw [r_rev hk hi.le]
    obtain ⟨s, hs⟩ : ∃ s, Γ.rJ R k - i = s + 1 := ⟨Γ.rJ R k - i - 1, by omega⟩
    rw [hs, r_pow_succ, r_rK_straight]
    exact r_notK_lt hk (by omega)

theorem r_hit_hit {k : D} (hk : Γ.rK R k) : Γ.rHit R (Γ.rHit R k) = k := by
  classical
  unfold rHit
  convert (Γ.r_hitHyp R).hit_hit hk

theorem r_hit_ne {k : D} (hk : Γ.rK R k) : Γ.rHit R k ≠ k := by
  classical
  unfold rHit
  convert (Γ.r_hitHyp R).hit_ne hk

theorem r_curve_hit {k : D} (hk : Γ.rK R k) : Γ.curve (Γ.rHit R k) = Γ.curve k := by
  rw [r_hit_eq hk, j_curve_α, r_curve_pow]

/-- `σ² (rHit k)` is the first return of `straight` to a kept crossing. -/
theorem r_σσ_hit {k : D} (hk : Γ.rK R k) :
    Γ.σ (Γ.σ (Γ.rHit R k)) = (Γ.straight ^ (Γ.rJ R k + 1)) k := by
  rw [r_hit_eq hk, r_pow_succ, j_straight_apply]

/-- Two joined segments with a common piece are equal. -/
theorem r_piece_unique {a b : D} (ha : Γ.rK R a) (hb : Γ.rK R b) {i m : ℕ} (hi : i ≤ Γ.rJ R a)
    (hm : m ≤ Γ.rJ R b) (h : (Γ.straight ^ i) a = (Γ.straight ^ m) b) : a = b := by
  wlog him : i ≤ m generalizing a b i m
  · exact (this hb ha hm hi h.symm (by omega)).symm
  have h2 : a = (Γ.straight ^ (m - i)) b := by
    have := congrArg (⇑((Γ.straight ^ i)⁻¹)) h
    rw [MapFacts.pow_inv_pow_apply _ him] at this
    simpa using this
  rcases Nat.eq_zero_or_pos (m - i) with h0 | h0
  · rw [h0, pow_zero, Perm.one_apply] at h2; exact h2
  · exact absurd (h2 ▸ ha) (r_notK_pow hb h0 (by omega))

/-! ## The surviving darts -/

theorem r_keep_K {d : D} (h : Γ.Keep R d) : Γ.rK R d := h.1

theorem r_keptStep_K {a b : D} (h : Γ.KeptStep R a b) : Γ.rK R a ∧ Γ.rK R b := ⟨h.1, h.2.1⟩

theorem r_eqvGen_K {a b : D} (h : Relation.EqvGen (Γ.KeptStep R) a b) :
    a = b ∨ (Γ.rK R a ∧ Γ.rK R b) := by
  induction h with
  | rel a b h => exact Or.inr (r_keptStep_K h)
  | refl => exact Or.inl rfl
  | symm a b _ ih => rcases ih with rfl | ⟨h1, h2⟩
                     · exact Or.inl rfl
                     · exact Or.inr ⟨h2, h1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨h1, h2⟩
    · exact ih2
    · rcases ih2 with rfl | ⟨h3, h4⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h4⟩

theorem r_keep_of_eqvGen {a b : D} (ha : Γ.Keep R a) (h : Relation.EqvGen (Γ.KeptStep R) a b) :
    Γ.Keep R b := by
  obtain ⟨e, he, hae⟩ := ha.2
  refine ⟨?_, e, he, (h.symm).trans _ _ _ hae⟩
  rcases r_eqvGen_K h with rfl | ⟨-, h2⟩
  · exact ha.1
  · exact h2

theorem r_keep_σ {d : D} (h : Γ.Keep R d) : Γ.Keep R (Γ.σ d) :=
  r_keep_of_eqvGen h (.rel _ _ ⟨h.1, (Γ.r_rK_σ R d).2 h.1, Or.inl rfl⟩)

theorem r_keep_σ_iff (d : D) : Γ.Keep R (Γ.σ d) ↔ Γ.Keep R d := by
  refine ⟨fun h => ?_, r_keep_σ⟩
  have := r_keep_σ (r_keep_σ (r_keep_σ h))
  rwa [Γ.j_σ4] at this

theorem r_keep_hit {k : D} (hk : Γ.Keep R k) : Γ.Keep R (Γ.rHit R k) := by
  refine r_keep_of_eqvGen hk (.rel _ _ ⟨hk.1, r_K_hit hk.1, Or.inr ⟨_, r_piece_J hk.1, ?_⟩⟩)
  exact r_hit_eq hk.1

theorem r_keep_S {d : D} (hS : Γ.curve d = Γ.S) (hK : Γ.rK R d) : Γ.Keep R d :=
  ⟨hK, d, hS, .refl _⟩

theorem r_keep_pow {w : D} (hw : Γ.Keep R w) {t : ℕ} (ht : Γ.rK R ((Γ.straight ^ t) w)) :
    Γ.Keep R ((Γ.straight ^ t) w) := by
  induction t using Nat.strong_induction_on generalizing w with
  | _ t ih =>
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · exact hw
  by_cases hex : ∃ s, 0 < s ∧ s < t ∧ Γ.rK R ((Γ.straight ^ s) w)
  · obtain ⟨s, hs0, hst, hs⟩ := hex
    have h1 := ih s hst hw hs
    have h2 : (Γ.straight ^ t) w = (Γ.straight ^ (t - s)) ((Γ.straight ^ s) w) := by
      rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hst.le]
    rw [h2] at ht ⊢
    exact ih (t - s) (by omega) h1 ht
  · push Not at hex
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hJ : Γ.rJ R w = s := by
      refine r_J_eq_of hw.1 (by rw [← r_rK_straight, ← r_pow_succ]; exact ht) fun i hi => ?_
      rw [← r_rK_straight, ← r_pow_succ]
      exact hex (i + 1) (by omega) (by omega)
    have := r_keep_σ (r_keep_σ (r_keep_hit hw))
    rwa [r_σσ_hit hw.1, hJ] at this

/-- A step of the kept map from a surviving dart is `σ` or `rHit`. -/
theorem r_keptStep_cases {a b : D} (ha : Γ.rK R a) (h : Γ.KeptStep R a b) :
    b = Γ.σ a ∨ b = Γ.rHit R a := by
  rcases h.2.2 with h1 | ⟨e, hp, rfl⟩
  · exact Or.inl h1
  · right
    rw [r_hit_eq ha, ← r_piece_eq ha hp h.2.1]

/-! ## Functions on cells across removed segments -/

/-- A function on cells that does not change across the segments of removed curves does not
change along a joined segment. -/
theorem r_cell_straight {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) {y : D}
    (hy : Γ.curve y ∉ R) (hd : ¬ Γ.rK R (Γ.α y)) :
    r (Γ.cellOf (Γ.straight y)) = r (Γ.cellOf y) := by
  set w := Γ.σ (Γ.α y)
  have hw : Γ.curve w ∈ R := by
    rcases (Γ.r_deleted_iff R (Γ.α y)).1 (not_not.1 hd) with h | h
    · rw [j_curve_α] at h; exact absurd h hy
    · exact h
  have h1 : Γ.cellOf (Γ.straight y) = Γ.cellOf (Γ.α w) := by
    rw [j_straight_apply, j_cellOf_σ]
  have h2 : Γ.cellOf w = Γ.cellOf y := Γ.j_cellOf_φ y
  rw [h1, hr w hw, h2]

theorem r_cell_pow {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) {k : D}
    (hk : Γ.rK R k) {i : ℕ} (hi : i ≤ Γ.rJ R k) :
    r (Γ.cellOf ((Γ.straight ^ i) k)) = r (Γ.cellOf k) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [r_pow_succ, r_cell_straight r hr (by rw [r_curve_pow]; exact Γ.r_curve_not_mem R hk)
      (r_notK_lt hk (by omega)), ih (by omega)]

theorem r_side_R (hS : Γ.S ∉ R) (w : D) (hw : Γ.curve w ∈ R) :
    Γ.side (Γ.cellOf (Γ.α w)) = Γ.side (Γ.cellOf w) := by
  have h := Γ.isSide w
  rw [if_neg (fun h' : Γ.curve w = Γ.S => hS (h' ▸ hw))] at h
  change Γ.side (Γ.cellOf w) + Γ.side (Γ.cellOf (Γ.α w)) = 0 at h
  rw [j_zmod2_eq_add_of_add_eq h, add_zero]

/-- Along `S` the upper side stays on the left. -/
theorem r_sweep_straight {y : D} (hy : Γ.curve y = Γ.S) :
    Γ.side (Γ.cellOf (Γ.α (Γ.straight y))) = Γ.side (Γ.cellOf (Γ.α y)) := by
  set w := Γ.α y
  have h1 : Γ.cellOf (Γ.α (Γ.straight y)) = Γ.cellOf (Γ.σ (Γ.σ (Γ.σ w))) := by
    rw [j_straight_apply, ← j_cellOf_σ]
  have h2 : Γ.cellOf (Γ.α (Γ.σ (Γ.σ (Γ.σ w)))) = Γ.cellOf w := by
    rw [← j_cellOf_σ, Γ.j_σ4]
  have hc : Γ.curve (Γ.σ (Γ.σ (Γ.σ w))) ≠ Γ.S := by
    rw [j_curve_σσ, ← hy, ← j_curve_α Γ y]
    exact Γ.isSConf.curve_σ _
  have h := Γ.isSide (Γ.σ (Γ.σ (Γ.σ w)))
  rw [if_neg hc] at h
  change Γ.side (Γ.cellOf _) + Γ.side (Γ.cellOf _) = 0 at h
  rw [h2] at h
  rw [h1, j_zmod2_eq_add_of_add_eq h, add_zero]

theorem r_sweep_pow {y : D} (hy : Γ.curve y = Γ.S) (i : ℕ) :
    Γ.side (Γ.cellOf (Γ.α ((Γ.straight ^ i) y))) = Γ.side (Γ.cellOf (Γ.α y)) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [r_pow_succ, r_sweep_straight (by rw [r_curve_pow]; exact hy), ih]

end SConf

end Pca.Sweep
