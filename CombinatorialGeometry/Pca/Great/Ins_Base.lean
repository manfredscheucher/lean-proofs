/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve along a closed walk: the maps (`doc/pca/great.md` section 4.1)

A walk `W` is a cyclic sequence of darts `t 0, …, t (K-1)`: the new curve crosses the segment of
`t i` from the cell right of `t i` into the cell left of it (`cellOf (α (t i))`), which is the
cell right of `t (i+1)`. The visited cells `cellOf (t i)` are pairwise distinct and every old
curve is crossed exactly twice.

The new map has darts `D ⊕ (Fin K × Fin 4)`. At the new crossing `w i` on the segment of `t i`
(from `x` = start of `t i` to `y` = end of `t i`) the four new darts are `(i, 0) = u i` (old curve,
from `w i` back to `x`), `(i, 1) = v i` (old curve, from `w i` to `y`), `(i, 2) = p i` (new curve,
forward, into the cell left of `t i`), `(i, 3) = q i` (new curve, backward), in counter-clockwise
order `v, p, u, q`. The old darts keep `σ`; `α` changes only on `t i` (now `↔ u i`) and `α (t i)`
(now `↔ v i`); the new curve's segments are `p i ↔ q (i+1)`.
-/
import Pca.Great.Defs
import Pca.Excess

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- A closed walk of crossed segments for inserting a new curve. -/
structure InsWalk (A : Arrangement n D) (K : ℕ) where
  t : Fin K → D
  three_le : 3 ≤ K
  adj : ∀ i, A.cellOf (A.α (t i)) = A.cellOf (t (finRotate K i))
  cell_inj : Function.Injective (fun i => A.cellOf (t i))
  twice : ∀ e : Fin n, (univ.filter (fun i => A.curve (t i) = e)).card = 2

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

/-- The next index. -/
abbrev nx (_W : InsWalk A K) (i : Fin K) : Fin K := finRotate K i
/-- The previous index. -/
abbrev pv (_W : InsWalk A K) (i : Fin K) : Fin K := (finRotate K).symm i

theorem nx_pv (i : Fin K) : W.nx (W.pv i) = i := (finRotate K).apply_symm_apply i
theorem pv_nx (i : Fin K) : W.pv (W.nx i) = i := (finRotate K).symm_apply_apply i

theorem t_inj : Function.Injective W.t := fun i j h => W.cell_inj (by simp only [h])

theorem nx_val (i : Fin K) :
    ((W.nx i : Fin K) : ℕ) = if (i : ℕ) + 1 = K then 0 else (i : ℕ) + 1 := by
  have h3 := W.three_le
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  show ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) = _
  rw [coe_finRotate]
  have := i.isLt
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Fin.ext (by simp; omega))

theorem nx_ne (i : Fin K) : W.nx i ≠ i := by
  have h3 := W.three_le
  intro h
  have h1 := congrArg Fin.val h
  rw [W.nx_val] at h1
  have := i.isLt
  split_ifs at h1 <;> omega

theorem nx_nx_ne (i : Fin K) : W.nx (W.nx i) ≠ i := by
  have h3 := W.three_le
  intro h
  have h1 := congrArg Fin.val h
  rw [W.nx_val, W.nx_val] at h1
  have := i.isLt
  split_ifs at h1 <;> omega

/-- The crossed segments are distinct: `t i ≠ α (t j)`. -/
theorem t_ne_α (i j : Fin K) : W.t i ≠ A.α (W.t j) := by
  intro h
  have h1 : A.cellOf (W.t i) = A.cellOf (W.t (W.nx j)) := by rw [h, W.adj]
  have hij : i = W.nx j := W.cell_inj h1
  subst hij
  have h2 : A.cellOf (A.α (W.t (W.nx j))) = A.cellOf (W.t j) := by
    rw [h, A.isArrangement.α_α]
  rw [W.adj] at h2
  exact W.nx_nx_ne j (W.cell_inj h2)

theorem αt_inj : Function.Injective fun i => A.α (W.t i) := fun i j h => W.t_inj (by
  have := congrArg A.α h; simpa [A.isArrangement.α_α] using this)

/-! ## The new maps -/

/-- The rotation on `Fin 4`: `1 ↦ 2 ↦ 0 ↦ 3 ↦ 1` (`v, p, u, q`). -/
def s4 : Fin 4 → Fin 4 := ![3, 2, 0, 1]
/-- Its inverse. -/
def s4inv : Fin 4 → Fin 4 := ![2, 3, 1, 0]

theorem s4_inv (r : Fin 4) : s4inv (s4 r) = r := by fin_cases r <;> rfl
theorem inv_s4 (r : Fin 4) : s4 (s4inv r) = r := by fin_cases r <;> rfl

/-- The new rotation. -/
def σ' (_W : InsWalk A K) : Perm (D ⊕ (Fin K × Fin 4)) where
  toFun
    | .inl d => .inl (A.σ d)
    | .inr (i, r) => .inr (i, s4 r)
  invFun
    | .inl d => .inl (A.σ.symm d)
    | .inr (i, r) => .inr (i, s4inv r)
  left_inv x := by rcases x with d | ⟨i, r⟩ <;> simp [s4_inv]
  right_inv x := by rcases x with d | ⟨i, r⟩ <;> simp [inv_s4]

open Classical in
/-- The new reverse-dart map. -/
noncomputable def αfun : D ⊕ (Fin K × Fin 4) → D ⊕ (Fin K × Fin 4)
  | .inl d =>
    if h : ∃ i, W.t i = d then .inr (Classical.choose h, 0)
    else if h' : ∃ i, A.α (W.t i) = d then .inr (Classical.choose h', 1)
    else .inl (A.α d)
  | .inr (i, r) =>
    if r = 0 then .inl (W.t i)
    else if r = 1 then .inl (A.α (W.t i))
    else if r = 2 then .inr (W.nx i, 3)
    else .inr (W.pv i, 2)

theorem αfun_t (i : Fin K) : W.αfun (.inl (W.t i)) = .inr (i, 0) := by
  have h : ∃ j, W.t j = W.t i := ⟨i, rfl⟩
  simp only [αfun, dif_pos h]
  rw [W.t_inj (Classical.choose_spec h)]

theorem αfun_αt (i : Fin K) : W.αfun (.inl (A.α (W.t i))) = .inr (i, 1) := by
  have h0 : ¬ ∃ j, W.t j = A.α (W.t i) := fun ⟨j, hj⟩ => W.t_ne_α j i hj
  have h : ∃ j, A.α (W.t j) = A.α (W.t i) := ⟨i, rfl⟩
  simp only [αfun, dif_neg h0, dif_pos h]
  rw [W.αt_inj (Classical.choose_spec h)]

theorem αfun_inl {d : D} (h1 : ∀ i, W.t i ≠ d) (h2 : ∀ i, A.α (W.t i) ≠ d) :
    W.αfun (.inl d) = .inl (A.α d) := by
  have h0 : ¬ ∃ j, W.t j = d := fun ⟨j, hj⟩ => h1 j hj
  have h0' : ¬ ∃ j, A.α (W.t j) = d := fun ⟨j, hj⟩ => h2 j hj
  simp only [αfun, dif_neg h0, dif_neg h0']

theorem αfun_u (i : Fin K) : W.αfun (.inr (i, 0)) = .inl (W.t i) := by simp [αfun]
theorem αfun_v (i : Fin K) : W.αfun (.inr (i, 1)) = .inl (A.α (W.t i)) := by simp [αfun]
theorem αfun_p (i : Fin K) : W.αfun (.inr (i, 2)) = .inr (W.nx i, 3) := by simp [αfun]
theorem αfun_q (i : Fin K) : W.αfun (.inr (i, 3)) = .inr (W.pv i, 2) := by simp [αfun]

theorem αfun_αfun (x : D ⊕ (Fin K × Fin 4)) : W.αfun (W.αfun x) = x := by
  rcases x with d | ⟨i, r⟩
  · by_cases h1 : ∃ i, W.t i = d
    · obtain ⟨i, rfl⟩ := h1; rw [W.αfun_t, W.αfun_u]
    by_cases h2 : ∃ i, A.α (W.t i) = d
    · obtain ⟨i, rfl⟩ := h2; rw [W.αfun_αt, W.αfun_v]
    push Not at h1 h2
    rw [W.αfun_inl h1 h2]
    have h1' : ∀ i, W.t i ≠ A.α d := fun i h => h2 i (by rw [h, A.isArrangement.α_α])
    have h2' : ∀ i, A.α (W.t i) ≠ A.α d := fun i h => h1 i (by
      have := congrArg A.α h; simpa [A.isArrangement.α_α] using this)
    rw [W.αfun_inl h1' h2', A.isArrangement.α_α]
  · fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue]; rw [W.αfun_u, W.αfun_t]
    · simp only [Fin.mk_one, Fin.isValue]; rw [W.αfun_v, W.αfun_αt]
    · show W.αfun (W.αfun (.inr (i, 2))) = .inr (i, 2)
      rw [W.αfun_p, W.αfun_q, W.pv_nx]
    · show W.αfun (W.αfun (.inr (i, 3))) = .inr (i, 3)
      rw [W.αfun_q, W.αfun_p, W.nx_pv]

/-- The new reverse-dart permutation. -/
noncomputable def α' : Perm (D ⊕ (Fin K × Fin 4)) :=
  Function.Involutive.toPerm _ W.αfun_αfun

theorem α'_apply (x : D ⊕ (Fin K × Fin 4)) : W.α' x = W.αfun x := rfl

/-- The new curve labels. -/
def curve' : D ⊕ (Fin K × Fin 4) → Fin (n + 1)
  | .inl d => Fin.castSucc (A.curve d)
  | .inr (i, r) => if r.val < 2 then Fin.castSucc (A.curve (W.t i)) else Fin.last n

end InsWalk

end Pca.Great
