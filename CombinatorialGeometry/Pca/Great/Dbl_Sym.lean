/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Doubling a curve: the symmetry `t (i + n) = α (ant (t i))`
-/
import Pca.Great.Dbl_Walk

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace Dbl

variable (A : Arrangement n D) (y0 : D)

theorem ant_y (k : ℕ) : ant A (y A y0 k) = y A y0 (k + (n - 1)) := by
  simp only [ant, y, ← Perm.mul_apply, ← pow_add, add_comm]

theorem y_eq {a b : ℕ} (h : a = b + 2 * (n - 1)) : y A y0 a = y A y0 b := by
  rw [h, y_mod]

variable (hn : 2 ≤ n)
include hn

theorem iter_val (k : ℕ) (i : Fin (2 * n)) :
    (((finRotate (2 * n))^[k] i : Fin (2 * n)) : ℕ) = (i.val + k) % (2 * n) := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', nx_val hn, ih]
    have h1 := Nat.mod_lt (i.val + k) (show 0 < 2 * n by omega)
    rw [← add_assoc, Nat.add_mod (i.val + k) 1, Nat.one_mod_eq_one.2 (by omega)]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact (Nat.mod_eq_of_lt (by omega)).symm

variable (hA : A.IsGreat)
include hA

theorem sym (i : Fin (2 * n)) :
    t A y0 ((finRotate (2 * n))^[n] i) = A.α (ant A (t A y0 i)) := by
  have hi := i.isLt
  have hv := iter_val hn n i
  set j := (finRotate (2 * n))^[n] i
  by_cases h0 : i.val = 0
  · have hj : j.val = n := by rw [hv, h0, zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [t_0 A y0 h0, t_n A y0 (by omega) (by omega) hj, ant_y, zero_add]
  by_cases h1 : i.val ≤ n - 1
  · have hj : j.val = i.val + n := by rw [hv, Nat.mod_eq_of_lt (by omega)]
    rw [t_R A y0 h0 h1, t_L A y0 (by omega) (by omega) (by omega), ant_σ hA, ant_y, hj]
    rw [y_eq A y0 (show 2 * (n - 1) + 1 - i.val + (n - 1) = 2 * n - (i.val + n) + 2 * (n - 1)
      by omega)]
  by_cases h2 : i.val = n
  · have hj : j.val = 0 := by rw [hv, h2, show n + n = 2 * n by omega, Nat.mod_self]
    rw [t_n A y0 h0 h1 h2, t_0 A y0 hj, ant_α, A.isArrangement.α_α, ant_y]
    exact (y_eq A y0 (by omega)).symm
  · have hj : j.val = i.val - n := by
      rw [hv, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [t_L A y0 h0 h1 h2, t_R A y0 (by omega) (by omega), ant_α, A.isArrangement.α_α, hj]
    have e : ∀ z, ant A (A.σ (A.σ (A.σ z))) = A.σ (ant A z) := fun z => by
      rw [ant_σ hA, ant_σσ, A.σ_σ_σ_σ]
    rw [e, ant_y]
    congr 2
    omega

end Dbl

end Pca.Great
