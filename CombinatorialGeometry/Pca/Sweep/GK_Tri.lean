/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Packages G and K: the empty triangle left by a removal, seen in `Γ`

`GKTri Γ γ d a b k₁ k₂` records, in `Γ`, the empty triangle `Δ(i, v, i + 1)` of `Γ − γ` above the
finite edge `d` (from `i` to `i + 1`, a segment of `Γ` by Lemma 3.7): the first leg starts with `a`
(from `i`), consists of `k₁ + 1` pieces and ends at `v` as `α (straight^k₁ a)`; the second leg
starts with `b` (from `v`), has `k₂ + 1` pieces and ends at `i + 1`; the crossings passed are the
crossings with `γ` on the legs (SH: "`γ` intersects the leg `k` times"). `gk_tri` builds it from a
removal.

Facts (all in `Γ`, with Jordan cuts of single curves):
* `parity`: `k₁ ≡ k₂ (mod 2)` (`γ` is a closed curve; walk around the triangle against the side
  of `γ`).
* `cell_b_of_zero`: if one leg is not hit, `v` is a corner of the face above `[i, i + 1]`.
* `cell_b_of_vis`: if `v` is a corner of that face at all, then at the corner of the triangle
  (the dart `b`): the four corners at `v` are told apart by the sides of the two leg curves.
* `even_of_vis`: then the first leg is hit an even number of times (side of `γ`).
* `not_two_two`: then not both legs are hit twice. The part of `γ` on the triangle's side of the
  first leg's curve is one arc (`no_upper_arc` for that curve as sweeping curve, `gkInst`), and so
  for the second; the two arcs force `γ` to run `u₁ → u₂' → u₂ → u₁'` (the two chords of
  Figure 10), and the region cut out by `[i, u₁]`, the first chord and `[u₂', i + 1]` separates the
  corner at `v` from the face above `[i, i + 1]`.
-/
import Pca.Sweep.GK_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The empty triangle of `Γ − γ` above the finite edge `d`, seen in `Γ` (module doc). -/
structure GKTri (Γ : SConf n D) (γ : Fin n) (d a b : D) (k₁ k₂ : ℕ) : Prop where
  ha : a = Γ.σ d
  hb : b = Γ.σ (Γ.α ((Γ.straight ^ k₁) a))
  hc : Γ.σ (Γ.α ((Γ.straight ^ k₂) b)) = Γ.α d
  del1 : ∀ t < k₁, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ t) a))) = γ
  del2 : ∀ t < k₂, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ t) b))) = γ
  c1γ : Γ.curve a ≠ γ
  c2γ : Γ.curve b ≠ γ
  dS : Γ.curve d = Γ.S
  γS : γ ≠ Γ.S
  k1le : k₁ ≤ 2
  k2le : k₂ ≤ 2
  k1P : k₁ < period Γ.straight a
  k2P : k₂ < period Γ.straight b

/-- The triangle of a removal, from Lemma 3.7 (`h37`: the finite edge is a segment of `Γ`). -/
theorem gk_tri {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'} (h : X.Γ'.EmptyTriAt d')
    (h37 : X.ι (X.Γ'.α d') = Γ.α (X.ι d')) :
    GKTri Γ γ (X.ι d') (X.ι (X.Γ'.σ d')) (X.ι (X.Γ'.φ (X.Γ'.σ d')))
      (X.hits (X.Γ'.σ d')) (X.hits (X.Γ'.φ (X.Γ'.σ d'))) := by
  obtain ⟨del1, -, hα1⟩ := gk_hits_spec X (X.Γ'.σ d')
  obtain ⟨del2, -, hα2⟩ := gk_hits_spec X (X.Γ'.φ (X.Γ'.σ d'))
  have hφ := f_φ_three (Γ := X.Γ') (x := X.Γ'.α d') h.2
  simp only [j_φ_apply, j_α_α] at hφ
  have c1 := gk_curve_ne X (X.Γ'.σ d')
  have c2 := gk_curve_ne X (X.Γ'.φ (X.Γ'.σ d'))
  refine ⟨X.isRemoval.σ d', ?_, ?_, ?_, ?_, c1, c2, ?_, ?_, gk_hits_le_two X _,
    gk_hits_le_two X _, gk_hits_lt_period X _, gk_hits_lt_period X _⟩
  · rw [j_φ_apply, X.isRemoval.σ, hα1]
  · rw [← hα2, ← X.isRemoval.σ, j_φ_apply, hφ, h37]
  · intro t ht
    exact gk_del_curve (by rw [no_curve_pow]; exact c1) (del1 t ht)
  · intro t ht
    exact gk_del_curve (by rw [no_curve_pow]; exact c2) (del2 t ht)
  · rw [← X.isRemoval.curve, h.1.1.1, X.isRemoval.S]
  · intro h'
    exact X.r_S_not_mem d' (h' ▸ mem_singleton_self γ)

theorem gk_zmod2_eq_self_add {x c : ZMod 2} (h : x = x + c) : c = 0 := by
  revert x c; decide

theorem gk_cell_σα (y : D) : Γ.cellOf (Γ.σ (Γ.α y)) = Γ.cellOf y := by
  rw [j_cellOf_σ, j_α_α]

namespace GKTri

variable {γ : Fin n} {d a b : D} {k₁ k₂ : ℕ} (T : GKTri Γ γ d a b k₁ k₂)
include T

theorem cell_a : Γ.cellOf a = Γ.cellOf (Γ.α d) := by rw [T.ha, j_cellOf_σ]

theorem cell_b : Γ.cellOf b = Γ.cellOf ((Γ.straight ^ k₁) a) := by rw [T.hb, gk_cell_σα]

theorem cell_αd : Γ.cellOf (Γ.α d) = Γ.cellOf ((Γ.straight ^ k₂) b) := by
  rw [← T.hc, gk_cell_σα]

theorem c12 : Γ.curve a ≠ Γ.curve b := by
  rw [T.hb]
  have := no_curve_σ_ne (Γ := Γ) (Γ.α ((Γ.straight ^ k₁) a))
  rw [j_curve_α, no_curve_pow] at this
  exact fun h => this h.symm

theorem c1S : Γ.curve a ≠ Γ.S := by
  rw [T.ha, ← T.dS]; exact no_curve_σ_ne d

theorem c2S : Γ.curve b ≠ Γ.S := by
  have := no_curve_σ_ne (Γ := Γ) (Γ.α ((Γ.straight ^ k₂) b))
  rw [T.hc, j_curve_α, T.dS, j_curve_α, no_curve_pow] at this
  exact fun h => this h.symm

/-- `γ` is a closed curve: the legs are hit with the same parity. -/
theorem parity : k₁ % 2 = k₂ % 2 := by
  obtain ⟨r, hr⟩ := gk_curve_cut (Γ := Γ) γ
  have h1 := gk_walk_flip hr a k₁ T.del1
  have h2 := gk_walk_flip hr b k₂ T.del2
  rw [← T.cell_b, T.cell_a] at h1
  rw [← T.cell_αd] at h2
  have h3 : ((k₁ : ZMod 2) + k₂) = 0 := by
    rw [h2, add_assoc, add_comm (k₂ : ZMod 2)] at h1; exact gk_zmod2_eq_self_add h1
  have := T.k1le
  have := T.k2le
  interval_cases k₁ <;> interval_cases k₂ <;> first | rfl | (exfalso; revert h3; decide)

/-- One leg not hit: `v` is a corner of the face above `[i, i + 1]`, at `b`. -/
theorem cell_b_of_zero (h : k₁ = 0 ∨ k₂ = 0) : Γ.cellOf b = Γ.cellOf (Γ.α d) := by
  rcases h with rfl | rfl
  · rw [T.cell_b, pow_zero, Perm.one_apply, T.cell_a]
  · rw [T.cell_αd, pow_zero, Perm.one_apply]

/-- If `v` is a corner of the face above `[i, i + 1]`, it is so at `b`. -/
theorem cell_b_of_vis {e : D} (he : Γ.cellOf e = Γ.cellOf (Γ.α d))
    (hx : Γ.crossingOf e = Γ.crossingOf b) : Γ.cellOf b = Γ.cellOf (Γ.α d) := by
  set y := (Γ.straight ^ k₁) a with hy
  obtain ⟨r1, hr1⟩ := gk_curve_cut (Γ := Γ) (Γ.curve a)
  obtain ⟨r2, hr2⟩ := gk_curve_cut (Γ := Γ) (Γ.curve b)
  have hr1b : r1 (Γ.cellOf b) = r1 (Γ.cellOf (Γ.α d)) := by
    rw [T.cell_b, gk_walk hr1 a k₁ (fun t ht => by rw [T.del1 t ht]; exact T.c1γ.symm),
      T.cell_a]
  have hr2b : r2 (Γ.cellOf b) = r2 (Γ.cellOf (Γ.α d)) := by
    rw [T.cell_b, gk_walk hr2 a k₁ (fun t ht => by rw [T.del1 t ht]; exact T.c2γ.symm),
      T.cell_a]
  have hcy : Γ.curve y = Γ.curve a := no_curve_pow a k₁
  have hb : b = Γ.σ (Γ.α y) := T.hb
  have hx' : Γ.crossingOf e = Γ.crossingOf (Γ.α y) := by rw [hx, hb, j_crossingOf_σ]
  have hcon : ∀ x : ZMod 2, x + x = 1 → False := fun x h => by
    rw [j_zmod2_add_self] at h; exact absurd h (by decide)
  rcases no_mem_crossing hx' with h | h | h | h
  · have := hr1 y
    rw [if_pos hcy, ← T.cell_b, ← h, he, ← hr1b] at this
    exact (hcon _ this).elim
  · rw [hb, ← h, he]
  · have := hr2 b
    rw [if_pos rfl, hb, ← j_cellOf_σ, ← h, he, ← hb, ← hr2b] at this
    exact (hcon _ this).elim
  · have h1 := hr1 (Γ.σ (Γ.σ (Γ.α y)))
    have h2 := hr1 b
    rw [if_pos (by rw [j_curve_σσ, j_curve_α, hcy])] at h1
    rw [if_neg (fun h' => T.c12 h'.symm)] at h2
    rw [← j_cellOf_σ Γ (Γ.σ (Γ.σ (Γ.α y))), ← h, he, j_cellOf_σ Γ (Γ.σ (Γ.α y)), ← hb] at h1
    have h3 : r1 (Γ.cellOf (Γ.α b)) = r1 (Γ.cellOf b) := by
      rw [j_zmod2_eq_add_of_add_eq h2, add_zero]
    rw [h3, hr1b] at h1
    exact (hcon _ h1).elim

/-- If `v` is a corner of the face above `[i, i + 1]` at `b`, the first leg is hit an even number
of times. -/
theorem even_of_vis (h : Γ.cellOf b = Γ.cellOf (Γ.α d)) : k₁ % 2 = 0 := by
  obtain ⟨r, hr⟩ := gk_curve_cut (Γ := Γ) γ
  have h1 := gk_walk_flip hr a k₁ T.del1
  rw [← T.cell_b, T.cell_a, h] at h1
  have h3 : (k₁ : ZMod 2) = 0 := gk_zmod2_eq_self_add h1
  have := T.k1le
  interval_cases k₁ <;> first | rfl | (exfalso; revert h3; decide)

/-- `v` is not a corner of the face above `[i, i + 1]` at `b` when both legs are hit twice
(module doc). -/
theorem not_two_two (h1 : k₁ = 2) (h2 : k₂ = 2) (hbF : Γ.cellOf b = Γ.cellOf (Γ.α d)) :
    False := by
  subst h1 h2
  set F := Γ.cellOf (Γ.α d) with hF
  set g0 := Γ.σ (Γ.α ((Γ.straight ^ 0) a)) with hg0
  set g1 := Γ.σ (Γ.α ((Γ.straight ^ 1) a)) with hg1
  set g2 := Γ.σ (Γ.α ((Γ.straight ^ 0) b)) with hg2
  set g2' := Γ.σ (Γ.α ((Γ.straight ^ 1) b)) with hg2'
  have cg0 : Γ.curve g0 = γ := T.del1 0 (by norm_num)
  have cg1 : Γ.curve g1 = γ := T.del1 1 (by norm_num)
  have cg2 : Γ.curve g2 = γ := T.del2 0 (by norm_num)
  have cg2' : Γ.curve g2' = γ := T.del2 1 (by norm_num)
  have hca : Γ.cellOf a = F := T.cell_a
  have cell_g0 : Γ.cellOf g0 = F := by rw [hg0, gk_cell_σα, pow_zero, Perm.one_apply, hca]
  have cell_g1 : Γ.cellOf g1 = Γ.cellOf ((Γ.straight ^ 1) a) := gk_cell_σα _
  have cell_g2 : Γ.cellOf g2 = F := by rw [hg2, gk_cell_σα, pow_zero, Perm.one_apply, hbF]
  have cell_g2' : Γ.cellOf g2' = Γ.cellOf ((Γ.straight ^ 1) b) := gk_cell_σα _
  obtain ⟨rg, hrg⟩ := gk_curve_cut (Γ := Γ) γ
  obtain ⟨r1, hr1, hr1F⟩ := gk_curve_cut' (Γ := Γ) (Γ.curve a) F
  obtain ⟨r2, hr2, hr2F⟩ := gk_curve_cut' (Γ := Γ) (Γ.curve b) F
  have hrgα : ∀ y, Γ.curve y = γ → rg (Γ.cellOf (Γ.α y)) = rg (Γ.cellOf y) + 1 := by
    intro y hy
    have := hrg y
    rw [if_pos hy] at this
    exact j_zmod2_eq_add_of_add_eq this
  have hr1a1 : r1 (Γ.cellOf ((Γ.straight ^ 1) a)) = 1 := by
    rw [gk_walk hr1 a 1 (fun t ht => by rw [T.del1 t (by omega)]; exact T.c1γ.symm), hca, hr1F]
  have hr2b1 : r2 (Γ.cellOf ((Γ.straight ^ 1) b)) = 1 := by
    rw [gk_walk hr2 b 1 (fun t ht => by rw [T.del2 t (by omega)]; exact T.c2γ.symm), hbF, hr2F]
  have hP1 : 1 < period Γ.straight a := by have := T.k1P; omega
  have hP2 : 1 < period Γ.straight b := by have := T.k2P; omega
  -- the part of `γ` on the triangle's side of the curve of the first leg is one arc
  have hz1 : r1 (Γ.cellOf (Γ.α (Γ.α a))) = 1 := by rw [j_α_α, hca, hr1F]
  have hz2 : r2 (Γ.cellOf (Γ.α (Γ.α b))) = 1 := by rw [j_α_α, hbF, hr2F]
  set Γ1 := Γ.gkInst (Γ.curve a) r1 hr1 (Γ.α a) (j_curve_α Γ a) hz1 with hΓ1
  set Γ2 := Γ.gkInst (Γ.curve b) r2 hr2 (Γ.α b) (j_curve_α Γ b) hz2 with hΓ2
  obtain ⟨L, -, hL, hLP, -, hcov1⟩ := no_upper_arc (Γ := Γ1) (a := g0) (b := g1)
    (gkInst_above.2 ⟨by rw [cg0]; exact T.c1γ.symm, by rw [cell_g0]; exact hr1F⟩)
    (gkInst_above.2 ⟨by rw [cg1]; exact T.c1γ.symm, by rw [cell_g1]; exact hr1a1⟩)
    (show Γ.curve g0 = Γ.curve g1 by rw [cg0, cg1])
    (show Γ.curve a ∈ Γ.curves (Γ.crossingOf g0) by
      rw [j_curves_crossingOf, hg0, j_curve_σσ, j_curve_α, no_curve_pow]
      exact mem_insert_of_mem (mem_singleton_self _))
    (show Γ.curve a ∈ Γ.curves (Γ.crossingOf g1) by
      rw [j_curves_crossingOf, hg1, j_curve_σσ, j_curve_α, no_curve_pow]
      exact mem_insert_of_mem (mem_singleton_self _))
    (show Γ.crossingOf g0 ≠ Γ.crossingOf g1 by
      rw [hg0, hg1, j_crossingOf_σ, j_crossingOf_σ]; exact f_cross_ne (by norm_num) hP1)
  obtain ⟨L2, -, hL2, hL2P, -, hcov2⟩ := no_upper_arc (Γ := Γ2) (a := g2) (b := g2')
    (gkInst_above.2 ⟨by rw [cg2]; exact T.c2γ.symm, by rw [cell_g2]; exact hr2F⟩)
    (gkInst_above.2 ⟨by rw [cg2']; exact T.c2γ.symm, by rw [cell_g2']; exact hr2b1⟩)
    (show Γ.curve g2 = Γ.curve g2' by rw [cg2, cg2'])
    (show Γ.curve b ∈ Γ.curves (Γ.crossingOf g2) by
      rw [j_curves_crossingOf, hg2, j_curve_σσ, j_curve_α, no_curve_pow]
      exact mem_insert_of_mem (mem_singleton_self _))
    (show Γ.curve b ∈ Γ.curves (Γ.crossingOf g2') by
      rw [j_curves_crossingOf, hg2', j_curve_σσ, j_curve_α, no_curve_pow]
      exact mem_insert_of_mem (mem_singleton_self _))
    (show Γ.crossingOf g2 ≠ Γ.crossingOf g2' by
      rw [hg2, hg2', j_crossingOf_σ, j_crossingOf_σ]; exact f_cross_ne (by norm_num) hP2)
  change (Γ.straight ^ L) g0 = Γ.α g1 at hL
  change L < period Γ.straight g0 at hLP
  change (Γ.straight ^ L2) g2 = Γ.α g2' at hL2
  change L2 < period Γ.straight g2 at hL2P
  -- `g2` lies on the arc of `g0`, `g0` on the arc of `g2`, both in the same direction
  obtain ⟨q, hqL, hq⟩ := hcov1 g2
    (gkInst_above.2 ⟨by rw [cg2]; exact T.c1γ.symm, by rw [cell_g2]; exact hr1F⟩)
    (show Γ.curve g2 = Γ.curve g0 by rw [cg2, cg0])
  have hq' : (Γ.straight ^ q) g0 = g2 := by
    rcases hq with hq | hq
    · exact hq
    · exfalso
      have e1 := gk_walk_own hrg g0 cg0 q
      change (Γ.straight ^ q) g0 = Γ.α g2 at hq
      rw [hq, hrgα g2 cg2, cell_g2, cell_g0] at e1
      exact gk_zmod2_ne_add_one _ e1.symm
  obtain ⟨p, hpL, hp⟩ := hcov2 g0
    (gkInst_above.2 ⟨by rw [cg0]; exact T.c2γ.symm, by rw [cell_g0]; exact hr2F⟩)
    (show Γ.curve g0 = Γ.curve g2 by rw [cg2, cg0])
  have hp' : (Γ.straight ^ p) g2 = g0 := by
    rcases hp with hp | hp
    · exact hp
    · exfalso
      have e1 := gk_walk_own hrg g2 cg2 p
      change (Γ.straight ^ p) g2 = Γ.α g0 at hp
      rw [hp, hrgα g0 cg0, cell_g2, cell_g0] at e1
      exact gk_zmod2_ne_add_one _ e1.symm
  -- positions along `γ`: `u₁` (0), `u₂'` (after step `m`), `u₂` (step `q`), `u₁'` (after `L`)
  set P := period Γ.straight g0 with hPdef
  have hPpos : 0 < P := period_pos Γ.straight g0
  have hL2P' : L2 < P := by rw [← hq', no_period_pow] at hL2P; exact hL2P
  have hpq : (Γ.straight ^ (p + q)) g0 = g0 := by rw [no_pow_add, hq', hp']
  have hne02 : g2 ≠ g0 := by
    intro h
    apply T.c12
    have := Γ.α.injective (Γ.σ.injective h)
    simp only [pow_zero, Perm.one_apply] at this
    rw [this]
  have hsum : p + q = P := by
    by_cases hlt : p + q < P
    · exfalso
      have := no_pow_inj hlt hPpos (by rw [hpq, pow_zero, Perm.one_apply])
      apply hne02
      rw [← hq', show q = 0 by omega, pow_zero, Perm.one_apply]
    · have h3 : (Γ.straight ^ (p + q - P)) g0 = (Γ.straight ^ 0) g0 := by
        rw [← no_pow_period, Nat.sub_add_cancel (by omega), hpq, pow_zero, Perm.one_apply]
      have := no_pow_inj (show p + q - P < P by omega) hPpos h3
      omega
  set m := q + L2 - P with hmdef
  have hmq : m < q := by omega
  have hm : (Γ.straight ^ m) g0 = Γ.α g2' := by
    rw [← hL2, ← hq', ← no_pow_add, show L2 + q = m + P by omega, no_pow_period]
  -- the closed walk `[i, u₁]`, `γ` from `u₁` to `u₂'`, `[u₂', i + 1]`, `[i + 1, i]`
  set M := m + 4 with hM
  set w : ℕ → D := fun i => if i = 0 then a else if i ≤ m + 1 then (Γ.straight ^ (i - 1)) g0
    else if i = m + 2 then (Γ.straight ^ 2) b else Γ.α d with hw
  have hwc : ∀ i < M, (i = 0 ∧ w i = a) ∨
      (1 ≤ i ∧ i ≤ m + 1 ∧ w i = (Γ.straight ^ (i - 1)) g0) ∨
      (i = m + 2 ∧ w i = (Γ.straight ^ 2) b) ∨ (i = m + 3 ∧ w i = Γ.α d) := by
    intro i hi
    by_cases h0 : i = 0
    · exact Or.inl ⟨h0, by simp only [hw, if_pos h0]⟩
    by_cases h1 : i ≤ m + 1
    · exact Or.inr (Or.inl ⟨by omega, h1, by simp only [hw, if_neg h0, if_pos h1]⟩)
    by_cases h2 : i = m + 2
    · exact Or.inr (Or.inr (Or.inl ⟨h2, by simp only [hw, if_neg h0, if_neg h1, if_pos h2]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [hw, if_neg h0, if_neg h1, if_neg h2]⟩))
  have cγt : ∀ t, Γ.curve ((Γ.straight ^ t) g0) = γ := fun t => by rw [no_curve_pow, cg0]
  have cb2 : Γ.curve ((Γ.straight ^ 2) b) = Γ.curve b := no_curve_pow b 2
  have cαd : Γ.curve (Γ.α d) = Γ.S := by rw [j_curve_α, T.dS]
  have hinj : ∀ i < M, ∀ j < M, Γ.segmentOf (w i) = Γ.segmentOf (w j) → i = j := by
    intro i hi j hj hs
    have hc := gk_curve_seg hs
    rcases hwc i hi with ⟨hi0, hwi⟩ | ⟨hi1, hi2, hwi⟩ | ⟨hi0, hwi⟩ | ⟨hi0, hwi⟩ <;>
    rcases hwc j hj with ⟨hj0, hwj⟩ | ⟨hj1, hj2, hwj⟩ | ⟨hj0, hwj⟩ | ⟨hj0, hwj⟩ <;>
    rw [hwi, hwj] at hc hs <;>
    simp only [cγt, cb2, cαd] at hc <;>
    first
      | omega
      | exact absurd hc T.c1γ | exact absurd hc.symm T.c1γ
      | exact absurd hc T.c2γ | exact absurd hc.symm T.c2γ
      | exact absurd hc T.c12 | exact absurd hc.symm T.c12
      | exact absurd hc T.c1S | exact absurd hc.symm T.c1S
      | exact absurd hc T.c2S | exact absurd hc.symm T.c2S
      | exact absurd hc T.γS | exact absurd hc.symm T.γS
      | (have := gk_seg_pow_inj (x := g0) (by omega) (by omega) hs; omega)
  have hwalk : ∀ i < M, Γ.crossingOf (Γ.α (w i)) = Γ.crossingOf (w ((i + 1) % M)) := by
    intro i hi
    rcases hwc i hi with ⟨rfl, hwi⟩ | ⟨hi1, hi2, hwi⟩ | ⟨rfl, hwi⟩ | ⟨rfl, hwi⟩
    · rw [hwi, Nat.mod_eq_of_lt (by omega)]
      rcases hwc 1 (by omega) with h | ⟨-, -, h⟩ | h | h
      · omega
      · simp only [h, hg0, Nat.sub_self, pow_zero, Perm.one_apply, j_crossingOf_σ]
      · omega
      · omega
    · rw [hwi, Nat.mod_eq_of_lt (by omega)]
      rcases hwc (i + 1) (by omega) with h | ⟨-, h3, h⟩ | ⟨h3, h⟩ | h
      · omega
      · rw [h, show i + 1 - 1 = i - 1 + 1 by omega, no_pow_succ, no_crossingOf_α_straight]
      · rw [h, show i - 1 = m by omega, hm, j_α_α, hg2', j_crossingOf_σ,
          ← no_crossingOf_α_straight, ← no_pow_succ]
      · omega
    · rw [hwi, Nat.mod_eq_of_lt (by omega)]
      rcases hwc (m + 2 + 1) (by omega) with h | h | h | ⟨-, h⟩
      · omega
      · omega
      · omega
      · rw [h, ← T.hc, j_crossingOf_σ]
    · rw [hwi, show m + 3 + 1 = M by omega, Nat.mod_self]
      rcases hwc 0 (by omega) with ⟨-, h⟩ | h | h | h
      · rw [h, j_α_α, T.ha, j_crossingOf_σ]
      · omega
      · omega
      · omega
  set E := (range M).image (fun i => Γ.segmentOf (w i)) with hE
  obtain ⟨rW, hrW⟩ := exists_cut E (gk_even_walk (by omega) w hwalk hinj)
  have hf0 : Γ.segmentOf g0 ∈ E := by
    rcases hwc 1 (by omega) with h | ⟨-, -, h⟩ | h | h
    · omega
    · rw [hE, mem_image]
      refine ⟨1, mem_range.2 (by omega), ?_⟩
      rw [h, pow_zero, Perm.one_apply]
    · omega
    · omega
  have hf1 : Γ.segmentOf g1 ∉ E := by
    have hg1L : Γ.segmentOf g1 = Γ.segmentOf ((Γ.straight ^ L) g0) := by
      rw [hL, j_segmentOf_α]
    rw [hg1L, hE, mem_image]
    rintro ⟨i, hi, hs⟩
    rw [mem_range] at hi
    have hc := gk_curve_seg hs
    rw [cγt] at hc
    rcases hwc i hi with ⟨-, hwi⟩ | ⟨hi1, hi2, hwi⟩ | ⟨-, hwi⟩ | ⟨-, hwi⟩ <;>
      rw [hwi] at hs hc
    · exact T.c1γ hc.symm
    · have := gk_seg_pow_inj (x := g0) (by omega) hLP hs
      omega
    · rw [cb2] at hc; exact T.c2γ hc.symm
    · rw [cαd] at hc; exact T.γS hc
  have s1 := no_walk_straight hrW a
  have s2 := no_walk_straight hrW (Γ.straight a)
  have hσ0 : Γ.σ (Γ.α a) = g0 := by rw [hg0, pow_zero, Perm.one_apply]
  have hσ1 : Γ.σ (Γ.α (Γ.straight a)) = g1 := by rw [hg1, pow_one]
  rw [hσ0, if_pos hf0] at s1
  rw [hσ1, if_neg hf1, add_zero, s1] at s2
  have hb2 : Γ.cellOf (Γ.straight (Γ.straight a)) = Γ.cellOf a := by
    have : (Γ.straight ^ 2) a = Γ.straight (Γ.straight a) := by rw [pow_two, Perm.mul_apply]
    rw [← this, ← T.cell_b, hbF, hca]
  rw [hb2] at s2
  exact gk_zmod2_ne_add_one _ s2

end GKTri

/-- The edge above which `γ₁` leaves its triangle with the first leg hit twice is not the edge
above which `γ₂` leaves its triangle with the second leg hit twice. -/
theorem gk_mixed {γ₁ γ₂ : Fin n} {d a₁ b₁ a₂ b₂ : D} (T1 : GKTri Γ γ₁ d a₁ b₁ 2 0)
    (T2 : GKTri Γ γ₂ d a₂ b₂ 0 2) : False := by
  have hbb : b₁ = (Γ.straight ^ 2) b₂ := by
    have h1 := T1.hc
    rw [pow_zero, Perm.one_apply, ← T2.hc] at h1
    exact Γ.α.injective (Γ.σ.injective h1)
  have e : (Γ.straight ^ 2) b₂ = Γ.straight ((Γ.straight ^ 1) b₂) := no_pow_succ b₂ 1
  have hm : γ₂ ∈ Γ.curves (Γ.crossingOf ((Γ.straight ^ 2) b₂)) := by
    rw [e, no_crossingOf_α_straight, j_curves_crossingOf, T2.del2 1 (by norm_num)]
    exact mem_insert_of_mem (mem_singleton_self _)
  rw [← hbb, T1.hb, j_crossingOf_σ, j_curves_crossingOf, ← T1.hb, j_curve_α, no_curve_pow,
    mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · apply T2.c1γ; rw [T2.ha, ← T1.ha, hm]
  · apply T2.c2γ; rw [hm, hbb, no_curve_pow]

/-- p. 322, "each edge of the sweep is responsible for at most one curve", in `Γ`: two triangles
above the same edge, each with exactly one leg hit (twice), belong to the same curve. -/
theorem gk_unique {γ₁ γ₂ : Fin n} {d a₁ b₁ a₂ b₂ : D} {k₁ k₂ l₁ l₂ : ℕ}
    (T1 : GKTri Γ γ₁ d a₁ b₁ k₁ k₂) (T2 : GKTri Γ γ₂ d a₂ b₂ l₁ l₂)
    (o1 : (k₁ = 2 ∧ k₂ = 0) ∨ (k₁ = 0 ∧ k₂ = 2)) (o2 : (l₁ = 2 ∧ l₂ = 0) ∨ (l₁ = 0 ∧ l₂ = 2)) :
    γ₁ = γ₂ := by
  have haa : a₁ = a₂ := T1.ha.trans T2.ha.symm
  rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [← T1.del1 0 (by norm_num), ← T2.del1 0 (by norm_num), haa]
  · exact (gk_mixed T1 T2).elim
  · exact (gk_mixed T2 T1).elim
  · have hbb : b₁ = b₂ := by rw [T1.hb, T2.hb, haa]
    rw [← T1.del2 0 (by norm_num), ← T2.del2 0 (by norm_num), hbb]

end SConf

end Pca.Sweep
