/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: consequences of the hypotheses `UHyp`

Curves and sides of the darts at `v`, at `i`, `i + 1` and along the legs; the seven cells
`B, L, T, R` (at `v`, above `S`) and `Q, P1, P2` (below the edge `[i, i + 1]`) are pairwise
distinct (by the side function and the cuts of `γ1`, `γ2`); the twelve darts whose segments change
(`uM`) are pairwise distinct.
-/
import Pca.Sweep.U_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- The twelve darts whose segments change: the darts at `v`, the far ends of the segments at
`v`, and the two segments of `Q` at `i` and `i + 1`. -/
def uM (d a : D) : Fin 12 → D
  | 0 => a
  | 1 => Γ.σ a
  | 2 => Γ.σ (Γ.σ a)
  | 3 => Γ.σ (Γ.σ (Γ.σ a))
  | 4 => Γ.α a
  | 5 => Γ.α (Γ.σ a)
  | 6 => Γ.α (Γ.σ (Γ.σ a))
  | 7 => Γ.α (Γ.σ (Γ.σ (Γ.σ a)))
  | 8 => Γ.up1 d
  | 9 => Γ.α (Γ.up1 d)
  | 10 => Γ.up2 d
  | 11 => Γ.α (Γ.up2 d)

/-- `α` on the indices of `uM`. -/
def uAI : Fin 12 → Fin 12
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 0 | 5 => 1 | 6 => 2 | 7 => 3
  | 8 => 9 | 9 => 8 | 10 => 11 | 11 => 10

/-- The new pairing on the indices of `uM`. -/
def uPI : Fin 12 → Fin 12
  | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | 8 => 0 | 0 => 8 | 9 => 1 | 1 => 9
  | 10 => 3 | 3 => 10 | 11 => 2 | 2 => 11

/-- The cell of `uM i`: `0 = B, 1 = L, 2 = T, 3 = R, 4 = Q, 5 = P1, 6 = P2`. -/
def uCI : Fin 12 → Fin 7
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 0
  | 8 => 5 | 9 => 4 | 10 => 4 | 11 => 6

/-- The curve of `uM i`: `false = γ1`, `true = γ2`. -/
def uKI : Fin 12 → Bool
  | 0 => true | 1 => false | 2 => true | 3 => false | 4 => true | 5 => false | 6 => true
  | 7 => false | 8 => false | 9 => false | 10 => true | 11 => true

/-- The seven cells. -/
def uCell (d a : D) : Fin 7 → Γ.Cell
  | 0 => Γ.cellOf a
  | 1 => Γ.cellOf (Γ.σ a)
  | 2 => Γ.cellOf (Γ.σ (Γ.σ a))
  | 3 => Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a)))
  | 4 => Γ.cellOf d
  | 5 => Γ.cellOf (Γ.up1 d)
  | 6 => Γ.cellOf (Γ.α (Γ.up2 d))

theorem uAI_uAI (i : Fin 12) : uAI (uAI i) = i := by revert i; decide
theorem uPI_uPI (i : Fin 12) : uPI (uPI i) = i := by revert i; decide
theorem uPI_ne (i : Fin 12) : uPI i ≠ i := by revert i; decide
/-- The side and the two cut values of the seven cells. -/
def uTab (xB yB xQ yQ : ZMod 2) : Fin 7 → ZMod 2 × ZMod 2 × ZMod 2
  | 0 => (1, xB, yB)
  | 1 => (1, xB, yB + 1)
  | 2 => (1, xB + 1, yB + 1)
  | 3 => (1, xB + 1, yB)
  | 4 => (0, xQ, yQ)
  | 5 => (0, xQ + 1, yQ)
  | 6 => (0, xQ, yQ + 1)

theorem uTab_inj (xB yB xQ yQ : ZMod 2) : Function.Injective (uTab xB yB xQ yQ) := by
  revert xB yB xQ yQ; decide

theorem uSig_inj (i j : Fin 12) (h1 : uCI i = uCI j) (h2 : uKI i = uKI j) : i = j := by
  revert i j; decide

variable {Γ} {d a : D} {k : ℕ} {γ : Fin n}

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

/-! ### Curves -/

theorem UHyp.c_d : Γ.curve d = Γ.S := H.sweep.1

theorem UHyp.c_σa : Γ.curve (Γ.σ a) = Γ.curve (Γ.ub1 d) := by
  rw [← H.leg1, u_curve_pow]

theorem UHyp.c_σσa : Γ.curve (Γ.σ (Γ.σ a)) = Γ.curve (Γ.ub2 d) := by
  rw [← H.leg2, u_curve_pow]

theorem UHyp.c_a : Γ.curve a = Γ.curve (Γ.ub2 d) := by
  rw [← H.c_σσa, j_curve_σσ]

theorem UHyp.c_σσσa : Γ.curve (Γ.σ (Γ.σ (Γ.σ a))) = Γ.curve (Γ.ub1 d) := by
  rw [j_curve_σσ, H.c_σa]

theorem UHyp.c12 : Γ.curve (Γ.ub1 d) ≠ Γ.curve (Γ.ub2 d) := by
  rw [← H.c_σa, ← H.c_σσa]; exact Γ.isSConf.curve_σ _ |>.symm

theorem UHyp.c1S : Γ.curve (Γ.ub1 d) ≠ Γ.S := by
  rw [← H.c_d]; exact Γ.isSConf.curve_σ d

theorem UHyp.c2S : Γ.curve (Γ.ub2 d) ≠ Γ.S := by
  have h : Γ.curve (Γ.ub2 d) = Γ.curve (Γ.σ (Γ.α d)) := Γ.j_curve_σσ _
  rw [h]; intro h'; apply Γ.isSConf.curve_σ (Γ.α d); rw [h', j_curve_α, H.c_d]

theorem UHyp.c_up1 : Γ.curve (Γ.up1 d) = Γ.curve (Γ.ub1 d) := Γ.j_curve_σσ _

theorem UHyp.c_up2 : Γ.curve (Γ.up2 d) = Γ.curve (Γ.ub2 d) := (Γ.j_curve_σσ _).symm

/-- The curve of `uM i`. -/
theorem UHyp.c_uM (i : Fin 12) :
    Γ.curve (Γ.uM d a i) = if uKI i then Γ.curve (Γ.ub2 d) else Γ.curve (Γ.ub1 d) := by
  fin_cases i <;> simp only [uM, uKI, if_true, if_false, Bool.false_eq_true, j_curve_α] <;>
    first | exact H.c_a | exact H.c_σa | exact H.c_σσa | exact H.c_σσσa | exact H.c_up1 | exact H.c_up2

/-! ### Sides -/

theorem UHyp.s_αd : Γ.side (Γ.cellOf (Γ.α d)) = 1 := H.sweep.2

theorem UHyp.s_d : Γ.side (Γ.cellOf d) = 0 := by
  have h := Γ.u_side_α d
  rw [H.s_αd, if_pos H.c_d] at h
  revert h; generalize Γ.side (Γ.cellOf d) = x; revert x; decide

theorem UHyp.s_σd : Γ.side (Γ.cellOf (Γ.σ d)) = 1 := by
  rw [j_cellOf_σ]; exact H.s_αd

theorem UHyp.s_up1 : Γ.side (Γ.cellOf (Γ.up1 d)) = 0 := by
  unfold up1
  rw [Γ.u_side_σ, Γ.u_side_σ, H.s_σd, if_neg (by
    have := H.c1S; unfold ub1 at this; exact this), if_pos (by rw [j_curve_σσ, H.c_d])]
  decide

theorem UHyp.s_αup1 : Γ.side (Γ.cellOf (Γ.α (Γ.up1 d))) = 0 := by
  rw [← j_cellOf_σ]; unfold up1; rw [Γ.j_σ4]; exact H.s_d

theorem UHyp.s_up2 : Γ.side (Γ.cellOf (Γ.up2 d)) = 0 := by
  unfold up2; rw [j_cellOf_σ, j_α_α]; exact H.s_d

theorem UHyp.s_αup2 : Γ.side (Γ.cellOf (Γ.α (Γ.up2 d))) = 0 := by
  rw [← j_cellOf_σ, Γ.u_side_σ, H.s_up2, if_neg (by rw [H.c_up2]; exact H.c2S)]
  rfl

theorem UHyp.s_ub2 : Γ.side (Γ.cellOf (Γ.ub2 d)) = 1 := by
  have h0 : Γ.side (Γ.cellOf (Γ.σ (Γ.up2 d))) = 0 := by rw [j_cellOf_σ]; exact H.s_αup2
  unfold ub2
  rw [Γ.u_side_σ]
  unfold up2 at h0
  rw [h0, if_pos (by rw [j_curve_σσ, j_curve_α, H.c_d])]
  decide

end Hyp

/-- The curve after the next crossing of a straight walk. -/
theorem u_curve_next (x : D) :
    Γ.curve (Γ.σ (Γ.α x)) = Γ.curve (Γ.σ (Γ.straight x)) := by
  rw [Γ.u_α_straight]; exact Γ.u_curve_σσσ _

/-- Two darts at one crossing. -/
theorem u_mem_of_crossing {x y : D} (h : Γ.crossingOf x = Γ.crossingOf y) :
    x = y ∨ x = Γ.σ y ∨ x = Γ.σ (Γ.σ y) ∨ x = Γ.σ (Γ.σ (Γ.σ y)) := by
  have h1 : Γ.σ.SameCycle y x := (Orbit.mk_eq_mk.1 h).symm
  have h2 := mem_orbitList.2 h1
  rw [Γ.j_orbitList_σ] at h2
  simpa using h2

/-- Two darts of one curve at one crossing. -/
theorem u_eq_or_σσ {x y : D} (h : Γ.crossingOf x = Γ.crossingOf y) (hc : Γ.curve x = Γ.curve y) :
    x = y ∨ x = Γ.σ (Γ.σ y) := by
  rcases Γ.u_mem_of_crossing h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hc (Γ.isSConf.curve_σ y)
  · exact Or.inr rfl
  · exact absurd (hc.symm.trans (Γ.u_curve_σσσ y)).symm (Γ.isSConf.curve_σ y)

/-- A leg: the side stays `1` along a straight walk that does not cross `S`. -/
theorem u_leg_side {b e : D} {k : ℕ} (hk : (Γ.straight ^ k) b = e)
    (h0 : Γ.side (Γ.cellOf b) = 1)
    (hmid : ∀ j, 0 < j → j < k → Γ.curve (Γ.σ ((Γ.straight ^ j) b)) ≠ Γ.S)
    (hend : Γ.curve (Γ.σ e) ≠ Γ.S) : ∀ j ≤ k, Γ.side (Γ.cellOf ((Γ.straight ^ j) b)) = 1 := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    rw [u_pow_succ, Γ.u_side_straight, ih (by omega), Γ.u_curve_next, ← u_pow_succ]
    rcases Nat.lt_or_ge (j + 1) k with h | h
    · rw [if_neg (hmid _ (by omega) h)]; rfl
    · rw [show j + 1 = k by omega, hk, if_neg hend]; rfl

/-- A leg ending at a crossing it does not pass before is shorter than its period. -/
theorem u_leg_period {b e : D} {k : ℕ} (hk : (Γ.straight ^ k) b = e)
    (hne : ∀ j < k, Γ.crossingOf ((Γ.straight ^ j) b) ≠ Γ.crossingOf e) :
    k < period Γ.straight b := by
  by_contra hle
  push Not at hle
  have hP := period_pos Γ.straight b
  have h1 := u_pow_mod Γ.straight b k
  rw [hk] at h1
  exact hne _ (lt_of_lt_of_le (Nat.mod_lt _ hP) hle) (by rw [h1])

section Hyp2

variable (H : Γ.UHyp d a k γ)
include H

/-! ### The legs -/

theorem UHyp.oth1 {j : ℕ} (hj : j < k) :
    Γ.curve (Γ.σ ((Γ.straight ^ j) (Γ.ub1 d))) = if j = 0 then Γ.S else γ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos rfl]; exact (Γ.j_curve_σσ d).trans H.c_d
  · rw [if_neg (by omega)]; exact H.mid1 j hj0 hj

theorem UHyp.oth2 {j : ℕ} (hj : j < k) :
    Γ.curve (Γ.σ ((Γ.straight ^ j) (Γ.ub2 d))) = if j = 0 then Γ.S else γ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos rfl]
    show Γ.curve (Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.α d))))) = Γ.S
    rw [Γ.j_σ4, j_curve_α, H.c_d]
  · rw [if_neg (by omega)]; exact H.mid2 j hj0 hj

theorem UHyp.oth_ne1 (j : ℕ) :
    (if j = 0 then Γ.S else γ) ≠ Γ.curve (Γ.ub1 d) := by
  split_ifs
  · exact H.c1S.symm
  · exact H.γ_1

theorem UHyp.oth_ne2 (j : ℕ) :
    (if j = 0 then Γ.S else γ) ≠ Γ.curve (Γ.ub2 d) := by
  split_ifs
  · exact H.c2S.symm
  · exact H.γ_2

theorem UHyp.oth_S {j : ℕ} (hj0 : 0 < j) :
    (if j = 0 then Γ.S else γ) ≠ Γ.S := by
  rw [if_neg (by omega)]; exact H.γ_S

theorem UHyp.curves1 {j : ℕ} (hj : j < k) :
    Γ.curves (Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d))) =
      {Γ.curve (Γ.ub1 d), if j = 0 then Γ.S else γ} := by
  rw [j_curves_crossingOf, u_curve_pow, H.oth1 hj]

theorem UHyp.curves2 {j : ℕ} (hj : j < k) :
    Γ.curves (Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d))) =
      {Γ.curve (Γ.ub2 d), if j = 0 then Γ.S else γ} := by
  rw [j_curves_crossingOf, u_curve_pow, H.oth2 hj]

theorem UHyp.curves_v :
    Γ.curves (Γ.crossingOf a) = {Γ.curve (Γ.ub2 d), Γ.curve (Γ.ub1 d)} := by
  rw [j_curves_crossingOf, H.c_a, H.c_σa]

theorem UHyp.curves_v' (x : D) (hx : Γ.crossingOf x = Γ.crossingOf a) :
    Γ.curves (Γ.crossingOf x) = {Γ.curve (Γ.ub2 d), Γ.curve (Γ.ub1 d)} := by
  rw [hx, H.curves_v]

theorem UHyp.f1_ne_v {j : ℕ} (hj : j < k) :
    Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d)) ≠ Γ.crossingOf a := by
  intro h
  have h1 := H.curves1 hj
  rw [h, H.curves_v] at h1
  have : Γ.curve (Γ.ub2 d) ∈ ({Γ.curve (Γ.ub1 d), if j = 0 then Γ.S else γ} : Finset (Fin n)) := by
    rw [← h1]; exact mem_insert_self _ _
  rw [mem_insert, mem_singleton] at this
  rcases this with h2 | h2
  · exact H.c12 h2.symm
  · exact H.oth_ne2 j h2.symm

theorem UHyp.f2_ne_v {j : ℕ} (hj : j < k) :
    Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d)) ≠ Γ.crossingOf a := by
  intro h
  have h1 := H.curves2 hj
  rw [h, H.curves_v] at h1
  have : Γ.curve (Γ.ub1 d) ∈ ({Γ.curve (Γ.ub2 d), if j = 0 then Γ.S else γ} : Finset (Fin n)) := by
    rw [← h1]; exact mem_insert_of_mem (mem_singleton_self _)
  rw [mem_insert, mem_singleton] at this
  rcases this with h2 | h2
  · exact H.c12 h2
  · exact H.oth_ne1 j h2.symm

theorem UHyp.f1_ne_f2 {i j : ℕ} (hi : i < k) (hj : j < k) :
    Γ.crossingOf ((Γ.straight ^ i) (Γ.ub1 d)) ≠ Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d)) := by
  intro h
  have h1 := H.curves1 hi
  rw [h, H.curves2 hj] at h1
  have : Γ.curve (Γ.ub1 d) ∈ ({Γ.curve (Γ.ub2 d), if j = 0 then Γ.S else γ} : Finset (Fin n)) := by
    rw [h1]; exact mem_insert_self _ _
  rw [mem_insert, mem_singleton] at this
  rcases this with h2 | h2
  · exact H.c12 h2
  · exact H.oth_ne1 j h2.symm

theorem UHyp.k_lt1 : k < period Γ.straight (Γ.ub1 d) := by
  refine Γ.u_leg_period H.leg1 fun j hj => ?_
  rw [j_crossingOf_σ]; exact H.f1_ne_v hj

theorem UHyp.k_lt2 : k < period Γ.straight (Γ.ub2 d) := by
  refine Γ.u_leg_period H.leg2 fun j hj => ?_
  rw [j_crossingOf_σ, j_crossingOf_σ]; exact H.f2_ne_v hj

theorem UHyp.f1_inj {i j : ℕ} (hi : i < k) (hj : j < k)
    (h : Γ.crossingOf ((Γ.straight ^ i) (Γ.ub1 d)) = Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d))) :
    i = j := by
  rcases Γ.u_eq_or_σσ h (by rw [u_curve_pow, u_curve_pow]) with h1 | h1
  · exact u_pow_inj (by have := H.k_lt1; omega) (by have := H.k_lt1; omega) h1
  · exact absurd h1.symm (Γ.u_ne_rev _ j i)

theorem UHyp.f2_inj {i j : ℕ} (hi : i < k) (hj : j < k)
    (h : Γ.crossingOf ((Γ.straight ^ i) (Γ.ub2 d)) = Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d))) :
    i = j := by
  rcases Γ.u_eq_or_σσ h (by rw [u_curve_pow, u_curve_pow]) with h1 | h1
  · exact u_pow_inj (by have := H.k_lt2; omega) (by have := H.k_lt2; omega) h1
  · exact absurd h1.symm (Γ.u_ne_rev _ j i)

/-! ### Sides along the legs and at `v` -/

theorem UHyp.s_leg1 {j : ℕ} (hj : j ≤ k) : Γ.side (Γ.cellOf ((Γ.straight ^ j) (Γ.ub1 d))) = 1 :=
  Γ.u_leg_side H.leg1 H.s_σd (fun j h0 h1 => by rw [H.oth1 h1]; exact H.oth_S h0)
    (by rw [H.c_σσa]; exact H.c2S) j hj

theorem UHyp.s_leg2 {j : ℕ} (hj : j ≤ k) : Γ.side (Γ.cellOf ((Γ.straight ^ j) (Γ.ub2 d))) = 1 :=
  Γ.u_leg_side H.leg2 H.s_ub2 (fun j h0 h1 => by rw [H.oth2 h1]; exact H.oth_S h0)
    (by rw [Γ.u_curve_σσσ, H.c_σa]; exact H.c1S) j hj

theorem UHyp.s_σa : Γ.side (Γ.cellOf (Γ.σ a)) = 1 := by
  have := H.s_leg1 le_rfl; rwa [H.leg1] at this

theorem UHyp.s_σσa : Γ.side (Γ.cellOf (Γ.σ (Γ.σ a))) = 1 := by
  rw [Γ.u_side_σ, H.s_σa, if_neg (by rw [H.c_σa]; exact H.c1S), add_zero]

theorem UHyp.s_σσσa : Γ.side (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a)))) = 1 := by
  rw [Γ.u_side_σ, H.s_σσa, if_neg (by rw [H.c_σσa]; exact H.c2S), add_zero]

theorem UHyp.s_a : Γ.side (Γ.cellOf a) = 1 := by
  have h := Γ.u_side_σ (Γ.σ (Γ.σ (Γ.σ a)))
  rw [Γ.j_σ4, H.s_σσσa, if_neg (by rw [H.c_σσσa]; exact H.c1S), add_zero] at h
  exact h

theorem UHyp.s_v {x : D} (hx : Γ.crossingOf x = Γ.crossingOf a) :
    Γ.side (Γ.cellOf x) = 1 := by
  rcases Γ.u_mem_of_crossing hx with rfl | rfl | rfl | rfl
  · exact H.s_a
  · exact H.s_σa
  · exact H.s_σσa
  · exact H.s_σσσa

/-! ### The seven cells -/

theorem UHyp.cell_uM (i : Fin 12) : Γ.cellOf (Γ.uM d a i) = Γ.uCell d a (uCI i) := by
  fin_cases i <;> simp only [uM, uCI, uCell] <;>
    first
    | rfl
    | exact (j_cellOf_σ _ _).symm
    | (rw [← j_cellOf_σ, Γ.j_σ4])
    | (rw [← j_cellOf_σ]; unfold up1; rw [Γ.j_σ4])
    | (unfold up2; rw [j_cellOf_σ, j_α_α])

theorem UHyp.side_uCell (c : Fin 7) :
    Γ.side (Γ.uCell d a c) = if c.val < 4 then 1 else 0 := by
  fin_cases c <;> simp only [uCell] <;> norm_num
  · exact H.s_a
  · exact H.s_σa
  · exact H.s_σσa
  · exact H.s_σσσa
  · exact H.s_d
  · exact H.s_up1
  · exact H.s_αup2

theorem UHyp.uCell_inj : Function.Injective (Γ.uCell d a) := by
  obtain ⟨g1, hg1⟩ := Γ.u_exists_curveCut (Γ.curve (Γ.ub1 d))
  obtain ⟨g2, hg2⟩ := Γ.u_exists_curveCut (Γ.curve (Γ.ub2 d))
  have e1 := Γ.u_cut_σ hg1
  have e2 := Γ.u_cut_σ hg2
  have c12 := H.c12
  have hS1 : Γ.S ≠ Γ.curve (Γ.ub1 d) := H.c1S.symm
  have hS2 : Γ.S ≠ Γ.curve (Γ.ub2 d) := H.c2S.symm
  -- values of the two cuts on the seven cells, relative to `B` and `Q`
  have vL1 := e1 a; have vL2 := e2 a
  have vT1 := e1 (Γ.σ a); have vT2 := e2 (Γ.σ a)
  have vR1 := e1 (Γ.σ (Γ.σ a)); have vR2 := e2 (Γ.σ (Γ.σ a))
  rw [H.c_a, if_neg c12.symm] at vL1
  rw [H.c_a, if_pos rfl] at vL2
  rw [H.c_σa, if_pos rfl] at vT1
  rw [H.c_σa, if_neg c12] at vT2
  rw [H.c_σσa, if_neg c12.symm] at vR1
  rw [H.c_σσa, if_pos rfl] at vR2
  have q1 := e1 d; have q1' := e1 (Γ.σ d); have q1'' := e1 (Γ.σ (Γ.σ d))
  have q2 := e2 d; have q2' := e2 (Γ.σ d); have q2'' := e2 (Γ.σ (Γ.σ d))
  rw [H.c_d, if_neg hS1] at q1
  rw [H.c_d, if_neg hS2] at q2
  rw [show Γ.curve (Γ.σ d) = Γ.curve (Γ.ub1 d) from rfl, if_pos rfl] at q1'
  rw [show Γ.curve (Γ.σ d) = Γ.curve (Γ.ub1 d) from rfl, if_neg c12] at q2'
  rw [Γ.j_curve_σσ, H.c_d, if_neg hS1] at q1''
  rw [Γ.j_curve_σσ, H.c_d, if_neg hS2] at q2''
  have p2a := e1 (Γ.up2 d); have p2b := e2 (Γ.up2 d)
  rw [H.c_up2, if_neg c12.symm] at p2a
  rw [H.c_up2, if_pos rfl] at p2b
  have hQ : Γ.cellOf (Γ.up2 d) = Γ.cellOf d := by unfold up2; rw [j_cellOf_σ, j_α_α]
  have hP2 : Γ.cellOf (Γ.σ (Γ.up2 d)) = Γ.cellOf (Γ.α (Γ.up2 d)) := j_cellOf_σ _ _
  rw [hQ, hP2] at p2a p2b
  have s := H.side_uCell
  set xB := g1 (Γ.cellOf a)
  set yB := g2 (Γ.cellOf a)
  set xQ := g1 (Γ.cellOf d)
  set yQ := g2 (Γ.cellOf d)
  have hv : ∀ c, (Γ.side (Γ.uCell d a c), g1 (Γ.uCell d a c), g2 (Γ.uCell d a c)) =
      uTab xB yB xQ yQ c := by
    intro c
    rw [s]
    fin_cases c <;> simp only [uCell, uTab, up1, Prod.mk.injEq] <;> norm_num <;>
      (try simp only [vR1, vT1, vL1, vR2, vT2, vL2, q1'', q1', q1, q2'', q2', q2, p2a, p2b]) <;>
      (try ring_nf) <;> (try simp) <;> (try exact ⟨rfl, rfl⟩) <;> (try decide)
  intro i j hij
  have h := (hv i).symm.trans ((congrArg (fun c => (Γ.side c, g1 c, g2 c)) hij).trans (hv j))
  exact uTab_inj xB yB xQ yQ h

theorem UHyp.uM_inj : Function.Injective (Γ.uM d a) := by
  intro i j h
  have hc := congrArg Γ.cellOf h
  rw [H.cell_uM, H.cell_uM] at hc
  have hk := congrArg Γ.curve h
  rw [H.c_uM, H.c_uM] at hk
  refine uSig_inj i j (H.uCell_inj hc) ?_
  cases hi : uKI i <;> cases hj : uKI j <;> rw [hi, hj] at hk <;> simp at hk ⊢
  · exact H.c12 hk
  · exact H.c12 hk.symm

/-! ### Positions of the changed darts on the straight walks -/

theorem UHyp.straight_inj {x y : D} (h : Γ.straight x = Γ.straight y) : x = y :=
  Γ.straight.injective h

theorem UHyp.pos7 : Γ.α (Γ.σ (Γ.σ (Γ.σ a))) = (Γ.straight ^ (k - 1)) (Γ.ub1 d) := by
  apply Γ.straight.injective
  rw [← u_pow_succ, Nat.sub_add_cancel H.k_pos, H.leg1, j_straight_apply, j_α_α, Γ.j_σ4]

theorem UHyp.pos4 : Γ.α a = (Γ.straight ^ (k - 1)) (Γ.ub2 d) := by
  apply Γ.straight.injective
  rw [← u_pow_succ, Nat.sub_add_cancel H.k_pos, H.leg2, j_straight_apply, j_α_α]

theorem UHyp.pos5 : Γ.α (Γ.σ a) = Γ.σ (Γ.σ ((Γ.straight ^ (k + 1)) (Γ.ub1 d))) := by
  rw [u_pow_succ, H.leg1, j_straight_apply, Γ.j_σ4]

theorem UHyp.pos6 : Γ.α (Γ.σ (Γ.σ a)) = Γ.σ (Γ.σ ((Γ.straight ^ (k + 1)) (Γ.ub2 d))) := by
  rw [u_pow_succ, H.leg2, j_straight_apply, Γ.j_σ4]

theorem UHyp.pos3 : Γ.σ (Γ.σ (Γ.σ a)) = Γ.σ (Γ.σ ((Γ.straight ^ k) (Γ.ub1 d))) := by
  rw [H.leg1]

theorem UHyp.pos0 : a = Γ.σ (Γ.σ ((Γ.straight ^ k) (Γ.ub2 d))) := by
  rw [H.leg2, Γ.j_σ4]

theorem UHyp.pos8 : Γ.up1 d = Γ.σ (Γ.σ ((Γ.straight ^ 0) (Γ.ub1 d))) := rfl

theorem UHyp.pos10 : Γ.up2 d = Γ.σ (Γ.σ ((Γ.straight ^ 0) (Γ.ub2 d))) := by
  show Γ.σ (Γ.α d) = Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.α d)))))
  rw [Γ.j_σ4]

theorem UHyp.pos9 :
    Γ.α (Γ.up1 d) = (Γ.straight ^ (period Γ.straight (Γ.ub1 d) - 1)) (Γ.ub1 d) := by
  apply Γ.straight.injective
  rw [u_pow_pred_period, j_straight_apply, j_α_α]
  show Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.σ d)))) = Γ.σ d
  rw [Γ.j_σ4]

theorem UHyp.pos11 :
    Γ.α (Γ.up2 d) = (Γ.straight ^ (period Γ.straight (Γ.ub2 d) - 1)) (Γ.ub2 d) := by
  apply Γ.straight.injective
  rw [u_pow_pred_period, j_straight_apply, j_α_α]
  rfl

theorem UHyp.kP1 : k + 1 < period Γ.straight (Γ.ub1 d) := by
  have h1 := H.k_lt1
  by_contra hle
  have he : period Γ.straight (Γ.ub1 d) = k + 1 := by omega
  have h2 := u_pow_period Γ.straight (Γ.ub1 d)
  rw [he] at h2
  have h5 := H.pos5
  rw [h2] at h5
  have h58 : Γ.uM d a 5 = Γ.uM d a 8 := by simp only [uM]; rw [h5]; rfl
  exact absurd (H.uM_inj h58) (by decide)

theorem UHyp.kP2 : k + 1 < period Γ.straight (Γ.ub2 d) := by
  have h1 := H.k_lt2
  by_contra hle
  have he : period Γ.straight (Γ.ub2 d) = k + 1 := by omega
  have h2 := u_pow_period Γ.straight (Γ.ub2 d)
  rw [he] at h2
  have h6 := H.pos6
  rw [h2] at h6
  have h610 : Γ.uM d a 6 = Γ.uM d a 10 := by
    simp only [uM]; rw [h6, H.pos10, pow_zero, Perm.one_apply]
  exact absurd (H.uM_inj h610) (by decide)

/-- The changed darts on the walk of `γ1` from `σ d`. -/
theorem UHyp.fwd1 {m : Fin 12} {i : ℕ} (hi : i < period Γ.straight (Γ.ub1 d))
    (h : Γ.uM d a m = (Γ.straight ^ i) (Γ.ub1 d)) :
    (m = 1 ∧ i = k) ∨ (m = 7 ∧ i + 1 = k) ∨ (m = 9 ∧ i + 1 = period Γ.straight (Γ.ub1 d)) := by
  have hP := H.kP1
  have hk := H.k_pos
  have hc := congrArg Γ.curve h
  rw [H.c_uM, u_curve_pow] at hc
  fin_cases m <;> simp only [uKI, if_true, if_false, Bool.false_eq_true] at hc
  all_goals first | exact absurd hc.symm H.c12 | skip
  all_goals simp only [uM] at h
  all_goals simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, false_and, true_and, or_false,
    false_or]
  · rw [← H.leg1] at h; exact (u_pow_inj (by omega) hi h).symm
  · rw [H.pos3] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [H.pos5] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [H.pos7] at h; have := u_pow_inj (by omega) hi h; omega
  · rw [H.pos8] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [H.pos9] at h; have := u_pow_inj (by omega) hi h; omega

/-- The changed darts on the walk of `γ2` from `σ³ (α d)`. -/
theorem UHyp.fwd2 {m : Fin 12} {i : ℕ} (hi : i < period Γ.straight (Γ.ub2 d))
    (h : Γ.uM d a m = (Γ.straight ^ i) (Γ.ub2 d)) :
    (m = 2 ∧ i = k) ∨ (m = 4 ∧ i + 1 = k) ∨ (m = 11 ∧ i + 1 = period Γ.straight (Γ.ub2 d)) := by
  have hP := H.kP2
  have hk := H.k_pos
  have hc := congrArg Γ.curve h
  rw [H.c_uM, u_curve_pow] at hc
  fin_cases m <;> simp only [uKI, if_true, if_false, Bool.false_eq_true] at hc
  all_goals first | exact absurd hc H.c12 | skip
  all_goals simp only [uM] at h
  all_goals simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, false_and, true_and, or_false,
    false_or]
  · rw [H.pos0] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [← H.leg2] at h; exact (u_pow_inj (by omega) hi h).symm
  · rw [H.pos4] at h; have := u_pow_inj (by omega) hi h; omega
  · rw [H.pos6] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [H.pos10] at h; exact absurd h (Γ.u_ne_rev _ _ _)
  · rw [H.pos11] at h; have := u_pow_inj (by omega) hi h; omega

end Hyp2

end SConf

end Pca.Sweep
