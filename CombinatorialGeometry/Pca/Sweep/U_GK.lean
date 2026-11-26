/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: the hypotheses `UHyp` from the triangle of a removal (`GKTri`)

In Lemma 3.9 the legs of the empty triangle `Δ(i, v, i + 1)` of `Γ − γ` are crossed `h` times by
`γ` each (`h = 1`: Case 1, `h = 2`: Case 2); in `Γ` they are straight walks of `h + 1` segments
whose inner crossings are crossings with `γ`.
-/
import Pca.Sweep.U_Basic
import Pca.Sweep.GK_Tri

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Walking back along a curve. -/
theorem u_back (x : D) (m i : ℕ) :
    (Γ.straight ^ m) (Γ.α ((Γ.straight ^ (m + i)) x)) = Γ.α ((Γ.straight ^ i) x) := by
  induction m with
  | zero => rw [zero_add, pow_zero, Perm.one_apply]
  | succ m ih =>
    rw [u_pow_succ', show m + 1 + i = (m + i) + 1 by omega, u_pow_succ, ← ih]
    congr 1
    rw [j_straight_apply, j_α_α, j_straight_apply, Γ.j_σ4]

theorem UHyp.of_gkTri {γ : Fin n} {d a₀ b : D} {h : ℕ} (T : GKTri Γ γ d a₀ b h h)
    (hd : Γ.IsSweepDart d) (hh : 0 < h) : Γ.UHyp d b (h + 1) γ := by
  have hub1 : Γ.ub1 d = a₀ := T.ha.symm
  have hub2 : Γ.ub2 d = Γ.α ((Γ.straight ^ h) b) := by
    unfold ub2; rw [← T.hc, Γ.j_σ4]
  have hpow2 : ∀ j ≤ h, (Γ.straight ^ j) (Γ.ub2 d) = Γ.α ((Γ.straight ^ (h - j)) b) := by
    intro j hj
    rw [hub2, show h = j + (h - j) by omega, u_back, Nat.add_sub_cancel_left]
  have hcb : Γ.curve (Γ.ub2 d) = Γ.curve b := by rw [hub2, j_curve_α, u_curve_pow]
  refine ⟨hd, by omega, ?_, ?_, T.γS, ?_, ?_, ?_, ?_⟩
  · rw [hub1, u_pow_succ, j_straight_apply, T.hb]
  · rw [u_pow_succ, hpow2 h le_rfl, Nat.sub_self, pow_zero, Perm.one_apply, j_straight_apply,
      j_α_α]
  · rw [hub1]; exact T.c1γ.symm
  · rw [hcb]; exact T.c2γ.symm
  · intro j hj0 hj
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    rw [hub1, u_pow_succ, j_straight_apply, Γ.u_curve_σσσ]
    exact T.del1 t (by omega)
  · intro j hj0 hj
    rw [hpow2 j (by omega)]
    exact T.del2 _ (by omega)

end SConf

end Pca.Sweep
