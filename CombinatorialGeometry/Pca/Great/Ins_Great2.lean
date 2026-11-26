/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting along an antipodally symmetric walk: the result is great
-/
import Pca.Great.Ins_Great

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

theorem st_pow_p (k : ℕ) (i : Fin K) : (W.st ^ k) (.inr (i, 2)) = .inr ((W.nx)^[k] i, 2) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [pow_succ, Perm.mul_apply, W.st_p, ih, Function.iterate_succ_apply]

theorem st_pow_q (k : ℕ) (i : Fin K) : (W.st ^ k) (.inr (i, 3)) = .inr ((W.pv)^[k] i, 3) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [pow_succ, Perm.mul_apply, W.st_q, ih, Function.iterate_succ_apply]

theorem nx_iter_pv_iter (k : ℕ) (i : Fin K) : (W.nx)^[k] ((W.pv)^[k] i) = i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', W.nx_pv, ih]

theorem ins_curves_inl (d : D) :
    Arrangement.Crossing.curves W.ins (W.ins.crossingOf (.inl d)) =
      (Arrangement.Crossing.curves A (A.crossingOf d)).map Fin.castSuccEmb :=
  W.crossCurves_inl d

theorem ins_curves_inr (i : Fin K) (r : Fin 4) :
    Arrangement.Crossing.curves W.ins (W.ins.crossingOf (.inr (i, r))) =
      {Fin.castSucc (A.curve (W.t i)), Fin.last n} :=
  W.crossCurves_inr i r

variable (hA : A.IsGreat) (hS : W.Sym)
include hA hS

theorem st_pow_old (d : D) : (W.st ^ n) (.inl d) = .inl (ant A d) := by
  have hn := A.two_le_n
  have h := W.st_walk d (n - 1)
  rw [W.hits_half hA hS, show n - 1 + 1 = n by omega] at h
  exact h

omit hA in
theorem curve_sh (i : Fin K) : A.curve (W.t (W.sh i)) = A.curve (W.t i) := by
  rw [hS, A.isArrangement.curve_α, curve_ant]

/-- **The inserted arrangement is great.** -/
theorem ins_isGreat : W.ins.IsGreat := by
  apply isGreat_of_antW
  intro x
  have hant : ∀ y, ant W.ins y = (W.st ^ n) y := fun y => by
    simp only [ant, Nat.add_sub_cancel]; rfl
  rw [hant]
  rcases x with d | ⟨i, r⟩
  · rw [W.st_pow_old hA hS, W.ins_curves_inl, W.ins_curves_inl, curves_ant hA]
  · fin_cases r
    · -- `u i`
      have e : (W.st ^ n) (.inr (i, 0)) = .inr (W.sh i, 1) := by
        rw [← W.st_αt i, ← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply,
          W.st_pow_old hA hS, ant_α, ← hS, W.st_t]
      show Arrangement.Crossing.curves W.ins (W.ins.crossingOf ((W.st ^ n) (.inr (i, 0)))) = _
      rw [e, W.ins_curves_inr, W.ins_curves_inr, W.curve_sh hS]
    · -- `v i`
      have e : (W.st ^ n) (.inr (i, 1)) = .inr (W.sh i, 0) := by
        rw [← W.st_t i, ← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply,
          W.st_pow_old hA hS, show ant A (W.t i) = A.α (W.t (W.sh i)) by
            rw [hS, A.isArrangement.α_α], W.st_αt]
      show Arrangement.Crossing.curves W.ins (W.ins.crossingOf ((W.st ^ n) (.inr (i, 1)))) = _
      rw [e, W.ins_curves_inr, W.ins_curves_inr, W.curve_sh hS]
    · show Arrangement.Crossing.curves W.ins (W.ins.crossingOf ((W.st ^ n) (.inr (i, 2)))) = _
      rw [W.st_pow_p, W.ins_curves_inr, W.ins_curves_inr]
      show _ = {Fin.castSucc (A.curve (W.t i)), Fin.last n}
      rw [← W.curve_sh hS i]; rfl
    · show Arrangement.Crossing.curves W.ins (W.ins.crossingOf ((W.st ^ n) (.inr (i, 3)))) = _
      rw [W.st_pow_q, W.ins_curves_inr, W.ins_curves_inr]
      show _ = {Fin.castSucc (A.curve (W.t i)), Fin.last n}
      have := W.curve_sh hS ((W.pv)^[n] i)
      rw [sh, W.nx_iter_pv_iter] at this
      rw [this]

end InsWalk

end Pca.Great
