/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Doubling a curve: the walk (`doc/pca/great.md` 4.2)

For a dart `y 0` on the curve `c` with walk `y k = straight^k (y 0)` (`m = n - 1`, the antipode of
`y k` is `y (k + m)`), the new curve runs on the right of `c` backwards from segment `0` to
segment `m` and on the left of `c` backwards from segment `m` to segment `0`:

* `t 0 = y 0` (crossing `c` into the right side),
* `t i = σ (y (2m + 1 - i))` for `1 ≤ i ≤ m` (crossing the curve at `X (2m + 1 - i)`),
* `t n = α (y m)` (crossing `c` back),
* `t i = α (σ³ (y (2n - i)))` for `n < i < 2n`.

It satisfies `t (i + n) = α (ant (t i))`.
-/
import Pca.Great.Ins_Great2

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace Dbl

variable (A : Arrangement n D) (y0 : D)

/-- The walk along the doubled curve. -/
abbrev y (k : ℕ) : D := (A.straight ^ k) y0

/-- The crossed darts. -/
def t (i : Fin (2 * n)) : D :=
  if i.val = 0 then y A y0 0
  else if i.val ≤ n - 1 then A.σ (y A y0 (2 * (n - 1) + 1 - i.val))
  else if i.val = n then A.α (y A y0 (n - 1))
  else A.α (A.σ (A.σ (A.σ (y A y0 (2 * n - i.val)))))

theorem y_succ (k : ℕ) : y A y0 (k + 1) = A.straight (y A y0 k) := by
  simp only [y, pow_succ', Perm.mul_apply]

theorem y_mod (k : ℕ) : y A y0 (k + 2 * (n - 1)) = y A y0 k := by
  simp only [y, pow_add, Perm.mul_apply, straight_pow_period]

theorem σσ_y_succ (k : ℕ) : A.σ (A.σ (y A y0 (k + 1))) = A.α (y A y0 k) := by
  rw [y_succ, A.straight_apply, A.σ_σ_σ_σ]

theorem σσσ_y_succ (k : ℕ) : A.σ (A.σ (A.σ (y A y0 (k + 1)))) = A.φ (y A y0 k) := by
  rw [y_succ, A.straight_apply, A.σ_σ_σ_σ]; rfl

theorem cellOf_α_eq (z : D) : A.cellOf (A.α z) = A.cellOf (A.σ z) := (A.cellOf_σ z).symm

theorem cellOf_ασσσ (z : D) : A.cellOf (A.α (A.σ (A.σ (A.σ z)))) = A.cellOf z := by
  rw [cellOf_α_eq, A.σ_σ_σ_σ]

theorem t_0 {i : Fin (2 * n)} (h : i.val = 0) : t A y0 i = y A y0 0 := by
  simp only [t, if_pos h]

theorem t_R {i : Fin (2 * n)} (h1 : i.val ≠ 0) (h2 : i.val ≤ n - 1) :
    t A y0 i = A.σ (y A y0 (2 * (n - 1) + 1 - i.val)) := by
  simp only [t, if_neg h1, if_pos h2]

theorem t_n {i : Fin (2 * n)} (h1 : i.val ≠ 0) (h2 : ¬ i.val ≤ n - 1) (h3 : i.val = n) :
    t A y0 i = A.α (y A y0 (n - 1)) := by
  simp only [t, if_neg h1, if_neg h2, if_pos h3]

theorem t_L {i : Fin (2 * n)} (h1 : i.val ≠ 0) (h2 : ¬ i.val ≤ n - 1) (h3 : i.val ≠ n) :
    t A y0 i = A.α (A.σ (A.σ (A.σ (y A y0 (2 * n - i.val))))) := by
  simp only [t, if_neg h1, if_neg h2, if_neg h3]

variable (hn : 2 ≤ n)
include hn

theorem nx_val (i : Fin (2 * n)) :
    ((finRotate (2 * n) i : Fin (2 * n)) : ℕ) = if i.val + 1 = 2 * n then 0 else i.val + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  have key : ∀ (K : ℕ) (hK : K = m + 1) (j : Fin K),
      ((finRotate K j : Fin K) : ℕ) = if j.val + 1 = K then 0 else j.val + 1 := by
    intro K hK j
    subst hK
    rw [coe_finRotate]
    by_cases h : j = Fin.last m
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro h'; exact h (Fin.ext (by simp; omega))
  exact key _ hm i

theorem adj (i : Fin (2 * n)) :
    A.cellOf (A.α (t A y0 i)) = A.cellOf (t A y0 (finRotate (2 * n) i)) := by
  have hi := i.isLt
  have hv := nx_val hn i
  set j := finRotate (2 * n) i
  by_cases h0 : i.val = 0
  · have hj : j.val = 1 := by rw [hv, if_neg (by omega), h0]
    rw [t_0 A y0 h0, t_R A y0 (by omega) (by omega), cellOf_α_eq, hj,
      show 2 * (n - 1) + 1 - 1 = 0 + 2 * (n - 1) by omega, y_mod]
  by_cases h1 : i.val ≤ n - 1
  · rw [t_R A y0 h0 h1, cellOf_α_eq]
    by_cases h1' : i.val < n - 1
    · have hj : j.val = i.val + 1 := by rw [hv, if_neg (by omega)]
      rw [t_R A y0 (by omega) (by omega), hj,
        show 2 * (n - 1) + 1 - i.val = (2 * (n - 1) + 1 - (i.val + 1)) + 1 by omega, σσ_y_succ,
        cellOf_α_eq]
    · have hj : j.val = n := by rw [hv, if_neg (by omega)]; omega
      rw [t_n A y0 (by omega) (by omega) hj,
        show 2 * (n - 1) + 1 - i.val = (n - 1) + 1 by omega, σσ_y_succ]
  by_cases h2 : i.val = n
  · have hj : j.val = n + 1 := by rw [hv, if_neg (by omega), h2]
    rw [t_n A y0 h0 h1 h2, A.isArrangement.α_α, t_L A y0 (by omega) (by omega) (by omega),
      cellOf_ασσσ, hj, show 2 * n - (n + 1) = n - 1 by omega]
  rw [t_L A y0 h0 h1 h2, A.isArrangement.α_α,
    show 2 * n - i.val = (2 * n - i.val - 1) + 1 by omega, σσσ_y_succ, A.cellOf_φ]
  by_cases h3 : i.val + 1 = 2 * n
  · have hj : j.val = 0 := by rw [hv, if_pos h3]
    rw [t_0 A y0 hj, show 2 * n - i.val - 1 = 0 by omega]
  · have hj : j.val = i.val + 1 := by rw [hv, if_neg h3]
    rw [t_L A y0 (by omega) (by omega) (by omega), cellOf_ασσσ, hj,
      show 2 * n - (i.val + 1) = 2 * n - i.val - 1 by omega]

end Dbl

end Pca.Great
