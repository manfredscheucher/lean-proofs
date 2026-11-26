/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package I (SH Lemma 3.9, Case 2): the two minus faces

`T : GKTri Γ γ d a b 2 2` is the triangle `Δ(i, v, i + 1)` of `Γ − γ` seen in `Γ`: first leg
`a, sa, s²a` (`A = γ(i)`, crossing `γ` at `u₁`, `u₂`), second leg `b, sb, s²b` (`β = γ(i+1)`,
crossing `γ` at `w₁`, `w₂`). With the chords (`i_b3`: `σ (α (σ (α b))) = s²a`, the cell between
the legs below `v` is `v, w₁, u₂`):

* `i_case_L`: if the minus face `L = cellOf (σ b)` (beyond the second leg) has four corners and
  lies above the finite edge `e`, it is `w₁, v, y, j` (`v–y` on `A`, `j–w₁` on `γ`); removing `β`
  leaves the empty triangle `Δ(j, u₂, y)` with legs `j–w₁–u₂` and `u₂–v–y`, each crossed once by
  `β`, and `u₂` is not a corner of `L`: Case 1 for `β` (`i_reduce`).
* `i_case_R`: the mirror image for `R = cellOf (σ³ b)`, removing `A`: the triangle
  `Δ(j, w₁, m)` with legs `j–v–w₁` and `w₁–u₂–m`.

This is SH's "without loss of generality, `γ` hits leg `⟨i, v⟩` before leg `⟨i+1, v⟩`" and the
removal of `γ(i+1)` (Figure 10): the face that can become a triangle in the untangled
arrangement is the one where `γ` goes straight to the sweep, and removing the other leg's curve
gives a Case 1 configuration.
-/
import Pca.Sweep.I_Red

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- A cell has at least two corners. -/
theorem i_two_le_size (x : D) : 2 ≤ (Γ.cellOf x).size := by
  rw [c_size]
  have hp := period_pos Γ.φ x
  by_contra hc
  have h1 : period Γ.φ x = 1 := by omega
  have h2 := iterate_period Γ.φ x
  rw [h1] at h2
  have h3 : Γ.σ (Γ.α x) = x := h2
  apply no_curve_σ_ne (Γ := Γ) (Γ.α x)
  rw [h3, j_curve_α]

/-- The darts of a cell with four corners. -/
theorem i_mem_cell4 {x y : D} (hp : (Γ.cellOf x).size = 4)
    (h : Γ.cellOf y = Γ.cellOf x) :
    y = x ∨ y = Γ.φ x ∨ y = Γ.φ (Γ.φ x) ∨ y = Γ.φ (Γ.φ (Γ.φ x)) := by
  rw [c_size] at hp
  have h' : Γ.φ.SameCycle x y := Orbit.mk_eq_mk.1 h.symm
  have := mem_orbitList.2 h'
  simpa [orbitList, hp, List.range_succ] using this

theorem i_φ4 {x : D} (hp : (Γ.cellOf x).size = 4) :
    Γ.φ (Γ.φ (Γ.φ (Γ.φ x))) = x := by
  rw [c_size] at hp
  have := iterate_period Γ.φ x
  rw [hp] at this
  exact this

theorem i_mem_curves {c : Fin n} {x : D} :
    c ∈ Γ.curves (Γ.crossingOf x) ↔ c = Γ.curve x ∨ c = Γ.curve (Γ.σ x) := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton]

/-- The crossings at the darts of a cell with four corners. -/
theorem i_hid4 {x : D} (hp : (Γ.cellOf x).size = 4) {P : Γ.Crossing → Prop}
    (h0 : P (Γ.crossingOf x)) (h1 : P (Γ.crossingOf (Γ.φ x)))
    (h2 : P (Γ.crossingOf (Γ.φ (Γ.φ x)))) (h3 : P (Γ.crossingOf (Γ.φ (Γ.φ (Γ.φ x))))) :
    ∀ y ∈ (Γ.cellOf x).darts, P (Γ.crossingOf y) := by
  intro y hy
  rcases i_mem_cell4 hp (Orbit.mem_darts.1 hy) with rfl | rfl | rfl | rfl <;> assumption

variable {γ : Fin n} {d a b : D}

/-- The crossing `u₂` (end of `sa`, start of `s²a`) lies on `γ` and `A` only. -/
theorem i_u2 (T : GKTri Γ γ d a b 2 2) {c : Fin n}
    (hc : c ∈ Γ.curves (Γ.crossingOf ((Γ.straight ^ 2) a))) : c = γ ∨ c = Γ.curve a := by
  have hg := T.del1 1 (by norm_num)
  rw [pow_one] at hg
  have hs : (Γ.straight ^ 2) a = Γ.σ (Γ.σ (Γ.α (Γ.straight a))) := by
    rw [no_pow_succ, pow_one, j_straight_apply]
  rw [hs, j_crossingOf_σ, i_mem_curves, ← hs, no_curve_pow, hg] at hc
  exact hc

/-- The minus face beyond the second leg (`cellOf (σ b)`). -/
theorem i_case_L (hΓ : Γ.MinCE) (T : GKTri Γ γ d a b 2 2)
    (hb3 : Γ.σ (Γ.α (Γ.σ (Γ.α b))) = (Γ.straight ^ 2) a) (hAb : Γ.Above b) {e : D}
    (he : Γ.IsFinSeg e) (hf : Γ.cellOf (Γ.α e) = Γ.cellOf (Γ.σ b))
    (h4 : (Γ.cellOf (Γ.σ b)).size = 4) : False := by
  set s2 := (Γ.straight ^ 2) a with hs2
  have hbd : b = Γ.σ (Γ.α s2) := T.hb
  have hx0 : Γ.cellOf (Γ.σ b) = Γ.cellOf (Γ.α b) := j_cellOf_σ Γ b
  rw [hx0] at hf h4
  have hφx0 : Γ.φ (Γ.α b) = Γ.σ b := by rw [j_φ_apply, j_α_α]
  have hcs2 : Γ.curve s2 = Γ.curve a := no_curve_pow a 2
  have hcσb : Γ.curve (Γ.σ b) = Γ.curve a := by
    rw [hbd, j_curve_σσ, j_curve_α, hcs2]
  have hcγ : Γ.curve (Γ.σ (Γ.α b)) = γ := by
    have := T.del2 0 (by norm_num); rwa [pow_zero, Perm.one_apply] at this
  have heS : Γ.curve (Γ.α e) = Γ.S := by rw [j_curve_α]; exact he.1.1
  have c12 := T.c12
  rcases i_mem_cell4 h4 hf with h0 | h0 | h0 | h0
  · exact T.c2S (by rw [← j_curve_α, ← h0, heS])
  · rw [hφx0] at h0
    exact T.c1S (by rw [← hcσb, ← h0, heS])
  · -- the face `w₁, v, y, j`
    have hL1 : Γ.σ (Γ.α (Γ.σ b)) = Γ.α e := by rw [h0, hφx0]; rfl
    have h5 := i_φ4 h4
    rw [← h0] at h5
    have hL2 : Γ.σ (Γ.α (Γ.σ e)) = Γ.α b := by
      have : Γ.φ (Γ.α e) = Γ.σ e := by rw [j_φ_apply, j_α_α]
      rw [this, j_φ_apply] at h5; exact h5
    have hst1 : Γ.straight (Γ.σ e) = Γ.σ (Γ.α b) := by rw [j_straight_apply, hL2]
    have hst2 : Γ.straight s2 = Γ.σ b := by rw [j_straight_apply, ← hbd]
    have hu2 : ∀ c ∈ Γ.curves (Γ.crossingOf s2), c ≠ Γ.S ∧ c ≠ Γ.curve b := by
      intro c hc
      rcases i_u2 T hc with rfl | rfl
      · exact ⟨T.γS, fun h => T.c2γ h.symm⟩
      · exact ⟨T.c1S, c12⟩
    have hyb : Γ.curve b ∉ Γ.curves (Γ.crossingOf (Γ.α (Γ.σ b))) := by
      rw [i_mem_curves, j_curve_α, hcσb, hL1, heS]
      rintro (h | h)
      · exact c12 h.symm
      · exact T.c2S h
    have hcey : Γ.crossingOf (Γ.α e) = Γ.crossingOf (Γ.α (Γ.σ b)) := by
      rw [← hL1, j_crossingOf_σ]
    have hsize : (Γ.cellOf (Γ.α e)).size = 4 := by rw [hf]; exact h4
    refine i_reduce hΓ ⟨T.c2S, b, rfl, hAb⟩ he ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [i_mem_curves, he.1.1]
      rintro (h | h)
      · exact T.c2S h
      · have := no_curve_σ_ne (Γ := Γ) (Γ.α (Γ.σ e))
        rw [hL2, j_curve_α, j_curve_α] at this
        exact this h
    · rw [hcey]; exact hyb
    · rw [← j_crossingOf_σ, hL2, i_mem_curves, j_curve_α]; exact Or.inl rfl
    · rw [hst1, ← j_crossingOf_σ, hb3]
      intro h; exact (hu2 _ h).2 rfl
    · rw [hst1, hb3, ← j_crossingOf_σ, ← hbd, i_mem_curves]; exact Or.inl rfl
    · rw [hst1, hb3, hst2]; exact hyb
    · rw [hst1, hb3, hst2, hL1]
    · rw [hst1, hb3]
      have hφe : Γ.φ (Γ.α e) = Γ.σ e := by rw [j_φ_apply, j_α_α]
      have hφσe : Γ.φ (Γ.σ e) = Γ.α b := by rw [j_φ_apply, hL2]
      refine i_hid4 (P := fun x => x ≠ Γ.crossingOf s2) hsize ?_ ?_ ?_ ?_
      · intro h
        have hS : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α e)) := by
          rw [i_mem_curves]; exact Or.inl heS.symm
        rw [h] at hS; exact (hu2 _ hS).1 rfl
      · rw [hφe, j_crossingOf_σ]
        intro h
        have hS : Γ.S ∈ Γ.curves (Γ.crossingOf e) := by
          rw [i_mem_curves]; exact Or.inl he.1.1.symm
        rw [h] at hS; exact (hu2 _ hS).1 rfl
      · rw [hφe, hφσe]
        intro h
        have hS : Γ.curve b ∈ Γ.curves (Γ.crossingOf (Γ.α b)) := by
          rw [i_mem_curves, j_curve_α]; exact Or.inl rfl
        rw [h] at hS; exact (hu2 _ hS).2 rfl
      · rw [hφe, hφσe, hφx0, j_crossingOf_σ]
        intro h
        have hS : Γ.curve b ∈ Γ.curves (Γ.crossingOf b) := by
          rw [i_mem_curves]; exact Or.inl rfl
        rw [h] at hS; exact (hu2 _ hS).2 rfl
  · have h5 := i_φ4 h4
    rw [← h0, j_φ_apply, j_α_α] at h5
    -- `σ e = α b`
    have := j_curve_σσ (Γ := Γ) e
    rw [h5, hcγ, he.1.1] at this
    exact T.γS this

/-- The minus face beyond the first leg (`cellOf (σ³ b)`), the mirror image of `i_case_L`. -/
theorem i_case_R (hΓ : Γ.MinCE) (T : GKTri Γ γ d a b 2 2)
    (hb3 : Γ.σ (Γ.α (Γ.σ (Γ.α b))) = (Γ.straight ^ 2) a) (hd : Γ.IsSweepDart d) {e : D}
    (he : Γ.IsFinSeg e) (hf : Γ.cellOf (Γ.α e) = Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b))))
    (h4 : (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b)))).size = 4) : False := by
  set s2 := (Γ.straight ^ 2) a with hs2
  have hbd : b = Γ.σ (Γ.α s2) := T.hb
  have hx0 : Γ.σ (Γ.σ (Γ.σ b)) = Γ.α s2 := by rw [hbd, j_σ4]
  rw [hx0] at hf h4
  have hφx0 : Γ.φ (Γ.α s2) = Γ.σ s2 := by rw [j_φ_apply, j_α_α]
  have hcs2 : Γ.curve s2 = Γ.curve a := no_curve_pow a 2
  have hcσs2 : Γ.curve (Γ.σ s2) = γ := by
    have h := i_u2 T (c := Γ.curve (Γ.σ s2)) (by rw [i_mem_curves]; exact Or.inr rfl)
    rcases h with h | h
    · exact h
    · exact absurd (h.trans hcs2.symm) (no_curve_σ_ne s2)
  have heS : Γ.curve (Γ.α e) = Γ.S := by rw [j_curve_α]; exact he.1.1
  have hcγ : Γ.curve (Γ.σ (Γ.α b)) = γ := by
    have := T.del2 0 (by norm_num); rwa [pow_zero, Perm.one_apply] at this
  have c12 := T.c12
  have hAa : Γ.Above a := T.ha ▸ no_above_σ hd
  rcases i_mem_cell4 h4 hf with h0 | h0 | h0 | h0
  · exact T.c1S (by rw [← hcs2, ← j_curve_α, ← h0, heS])
  · rw [hφx0] at h0
    exact T.γS (by rw [← hcσs2, ← h0, heS])
  · -- the face `u₂, v, j, m`
    have hR1 : Γ.σ (Γ.α (Γ.σ s2)) = Γ.α e := by rw [h0, hφx0]; rfl
    have h5 := i_φ4 h4
    rw [← h0] at h5
    have hR2 : Γ.σ (Γ.α (Γ.σ e)) = Γ.α s2 := by
      have : Γ.φ (Γ.α e) = Γ.σ e := by rw [j_φ_apply, j_α_α]
      rw [this, j_φ_apply] at h5; exact h5
    have hst1 : Γ.straight (Γ.σ e) = b := by rw [j_straight_apply, hR2, ← hbd]
    have hst2 : Γ.straight (Γ.σ (Γ.α b)) = Γ.σ s2 := by
      rw [j_straight_apply]
      conv_rhs => rw [← hb3]
    have hw1 : ∀ c ∈ Γ.curves (Γ.crossingOf (Γ.α b)), c ≠ Γ.S ∧ c ≠ Γ.curve a := by
      intro c hc
      rw [i_mem_curves, j_curve_α, hcγ] at hc
      rcases hc with rfl | rfl
      · exact ⟨T.c2S, fun h => c12 h.symm⟩
      · exact ⟨T.γS, fun h => T.c1γ h.symm⟩
    have hym : Γ.curve a ∉ Γ.curves (Γ.crossingOf (Γ.α (Γ.σ s2))) := by
      rw [i_mem_curves, j_curve_α, hcσs2, hR1, heS]
      rintro (h | h)
      · exact T.c1γ h
      · exact T.c1S h
    have hcem : Γ.crossingOf (Γ.α e) = Γ.crossingOf (Γ.α (Γ.σ s2)) := by
      rw [← hR1, j_crossingOf_σ]
    have hsize : (Γ.cellOf (Γ.α e)).size = 4 := by rw [hf]; exact h4
    refine i_reduce hΓ ⟨T.c1S, a, rfl, hAa⟩ he ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [i_mem_curves, he.1.1]
      rintro (h | h)
      · exact T.c1S h
      · have := no_curve_σ_ne (Γ := Γ) (Γ.α (Γ.σ e))
        rw [hR2, j_curve_α, j_curve_α, hcs2] at this
        exact this h
    · rw [hcem]; exact hym
    · rw [← j_crossingOf_σ, hR2, i_mem_curves, j_curve_α, hcs2]; exact Or.inl rfl
    · rw [hst1]
      intro h; exact (hw1 _ h).2 rfl
    · rw [hst1, ← j_crossingOf_σ, hb3, i_mem_curves, hcs2]; exact Or.inl rfl
    · rw [hst1, hst2]; exact hym
    · rw [hst1, hst2, hR1]
    · rw [hst1]
      have hφe : Γ.φ (Γ.α e) = Γ.σ e := by rw [j_φ_apply, j_α_α]
      have hφσe : Γ.φ (Γ.σ e) = Γ.α s2 := by rw [j_φ_apply, hR2]
      refine i_hid4 (P := fun x => x ≠ Γ.crossingOf (Γ.σ (Γ.α b))) hsize ?_ ?_ ?_ ?_
      · intro h
        have hS : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α e)) := by
          rw [i_mem_curves]; exact Or.inl heS.symm
        rw [h, j_crossingOf_σ] at hS; exact (hw1 _ hS).1 rfl
      · rw [hφe, j_crossingOf_σ]
        intro h
        have hS : Γ.S ∈ Γ.curves (Γ.crossingOf e) := by
          rw [i_mem_curves]; exact Or.inl he.1.1.symm
        rw [h, j_crossingOf_σ] at hS; exact (hw1 _ hS).1 rfl
      · rw [hφe, hφσe]
        intro h
        have hS : Γ.curve a ∈ Γ.curves (Γ.crossingOf (Γ.α s2)) := by
          rw [i_mem_curves, j_curve_α, hcs2]; exact Or.inl rfl
        rw [h, j_crossingOf_σ] at hS; exact (hw1 _ hS).2 rfl
      · rw [hφe, hφσe, hφx0, j_crossingOf_σ]
        intro h
        have hS : Γ.curve a ∈ Γ.curves (Γ.crossingOf s2) := by
          rw [i_mem_curves, hcs2]; exact Or.inl rfl
        rw [h, j_crossingOf_σ] at hS; exact (hw1 _ hS).2 rfl
  · have h5 := i_φ4 h4
    rw [← h0, j_φ_apply, j_α_α] at h5
    -- `σ e = α s²a`, so `σ² e = b`
    have := j_curve_σσ (Γ := Γ) e
    rw [h5, ← hbd, he.1.1] at this
    exact T.c2S this

end SConf

end Pca.Sweep
