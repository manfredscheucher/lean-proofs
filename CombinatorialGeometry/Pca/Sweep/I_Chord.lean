/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package I (SH Lemma 3.9, Case 2): the chords of `γ` inside the triangle

`X` removes `γ`, `Γ − γ` has the empty triangle `Δ(i, v, i + 1)` above `d'`, `v` is hidden and `γ`
crosses both legs twice. The boundary walk of the triangle (package E, starting with the first leg)
is `a, sa, s²a` (leg `⟨i, v⟩`, ports `u₁`, `u₂` at positions `0`, `1`), `b, sb, s²b` (leg
`⟨v, i + 1⟩`, ports `w₁`, `w₂` at positions `3`, `4`) and the base (position `6`). By the chord
lemma the edges of `γ` inside the triangle pair up the four ports; `u₁–u₂` with `w₁–w₂` would make
`v` visible, `u₁–w₁` with `u₂–w₂` cross (noncrossing lemma). So the chords are `u₁–w₂` and `u₂–w₁`
(Figure 9), and the cell `B` of `Γ` between the legs below `v` is the triangle `v, w₁, u₂`:
`i_b3`.
-/
import Pca.Sweep.L39Case1

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

namespace Removal

variable {R : Finset (Fin n)} (X : Γ.Removal R)

/-- The number of deleted crossings on a joined segment is `hits`, given by the crossings passed. -/
theorem i_hits_eq (x' : X.D') {k : ℕ}
    (hdel : ∀ i < k, Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ i) (X.ι x')))))
    (hnd : ¬ Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ k) (X.ι x'))))) : X.hits x' = k := by
  obtain ⟨hd, hn, -⟩ := gk_hits_spec X x'
  rcases lt_trichotomy (X.hits x') k with h | h | h
  · exact absurd (hdel _ h) hn
  · exact h
  · exact absurd (hd _ h) hnd

/-- `eJ` (package E) is `hits`. -/
theorem i_eJ_hits (x' : X.D') : X.eJ x' = X.hits x' := by
  obtain ⟨hd, hn, -⟩ := gk_hits_spec X x'
  have hle : X.hits x' ≤ X.eJ x' := by
    by_contra hc
    push Not at hc
    have h1 := hd _ hc
    have h2 : Γ.rK R (Γ.α (X.ePc x' (X.eJ x'))) := (e_pc_rK le_rfl).2 rfl
    exact h2 h1
  exact ((e_pc_rK hle).1 hn).symm

end Removal

open Removal

/-- **Chords** (Figure 9): the cell between the legs below `v` is the triangle `v, w₁, u₂`:
`σ (α (σ (α b))) = s² a`. -/
theorem i_b3 (hΓ : Γ.MinCE) {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'} (h : X.Γ'.EmptyTriAt d')
    (hv : ¬ ApexVisible X d') (h₁ : X.hits (X.Γ'.σ d') = 2)
    (h₂ : X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) :
    Γ.σ (Γ.α (Γ.σ (Γ.α (X.ι (X.Γ'.φ (X.Γ'.σ d')))))) = (Γ.straight ^ 2) (X.ι (X.Γ'.σ d')) := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  rw [h₁, h₂] at T
  set c := X.Γ'.σ d' with hc
  -- the triangle cell, starting with the first leg
  have hφα : X.Γ'.φ (X.Γ'.α d') = c := by rw [j_φ_apply, j_α_α]
  have h3 := f_φ_three (Γ := X.Γ') (x := X.Γ'.α d') h.2
  rw [hφα] at h3
  have hcell : X.Γ'.cellOf c = X.Γ'.cellOf (X.Γ'.α d') := j_cellOf_σ _ d'
  have hM : X.eM c = 3 := by
    unfold eM
    rw [← c_size, hcell]; exact h.2
  have hC0 : X.eC c 0 = c := rfl
  have hC1 : X.eC c 1 = X.Γ'.φ c := by unfold eC; rw [pow_one]
  have hC2 : X.eC c 2 = X.Γ'.α d' := by
    unfold eC; rw [pow_two, Perm.mul_apply]; exact h3
  -- the number of pieces
  have hJ0 : X.eJ c = 2 := by rw [i_eJ_hits]; exact h₁
  have hJ1 : X.eJ (X.eC c 1) = 2 := by rw [hC1, i_eJ_hits]; exact h₂
  have hJ2 : X.eJ (X.eC c 2) = 0 := by
    rw [hC2, e_eJ_α, i_eJ_hits]
    obtain ⟨-, -, hα⟩ := gk_hits_spec X d'
    rw [h37] at hα
    have he := (Γ.α.injective hα).symm
    have h1 := gk_hits_lt_period X d'
    exact no_pow_inj h1 (period_pos _ _) (by rw [he, pow_zero, Perm.one_apply])
  have hP1 : X.eP c 1 = 3 := by rw [e_P_one, hJ0]
  have hP2 : X.eP c 2 = 6 := by rw [e_P_succ, hP1, hJ1]
  have hN : X.eN c = 7 := by
    unfold eN; rw [hM, e_P_succ, hP2, hJ2]
  -- the walk
  set a := X.ι c with ha
  set b := X.ι (X.Γ'.φ c) with hb
  have hW : ∀ t ≤ 2, X.eW c t = (Γ.straight ^ t) a := by
    intro t ht
    have := e_W_pos (X := X) (b' := c) 0 (t := t) (by rw [hC0, hJ0]; exact ht)
    rwa [e_P_zero, zero_add, hC0] at this
  have hW' : ∀ t ≤ 2, X.eW c (3 + t) = (Γ.straight ^ t) b := by
    intro t ht
    have := e_W_pos (X := X) (b' := c) 1 (t := t) (by rw [hJ1]; exact ht)
    rwa [hP1, hC1] at this
  -- ports
  have hport : ∀ t < 2, X.EPort c t := by
    intro t ht
    have := (e_port_of (X := X) (b' := c) (i := 0) (by omega) (by rw [hC0, hJ0]; exact ht)).1
    rwa [e_P_zero, zero_add] at this
  have hport' : ∀ t < 2, X.EPort c (3 + t) := by
    intro t ht
    have := (e_port_of (X := X) (b' := c) (i := 1) (by omega) (by rw [hJ1]; exact ht)).1
    rwa [hP1] at this
  have hnp : ∀ i < 3, ¬ X.EPort c (X.eP c i + X.eJ (X.eC c i)) := by
    intro i _ hp
    apply hp
    rw [e_W_pos i le_rfl]
    exact (e_pc_rK le_rfl).2 rfl
  have hnp2 : ¬ X.EPort c 2 := by have := hnp 0 (by omega); rwa [e_P_zero, hC0, hJ0] at this
  have hnp5 : ¬ X.EPort c 5 := by have := hnp 1 (by omega); rwa [hP1, hJ1] at this
  have hnp6 : ¬ X.EPort c 6 := by have := hnp 2 (by omega); rwa [hP2, hJ2] at this
  have hports : ∀ v < X.eN c, X.EPort c v → v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4 := by
    intro v hv hp
    rw [hN] at hv
    interval_cases v <;> simp_all
  -- the chord lemma
  have hup : X.Γ'.side (X.Γ'.cellOf c) = 1 := by rw [hcell]; exact h.1.1.2
  have h34 : ∀ δ, Γ.Present δ → Γ.MeetsSweep δ := fun δ hδ => hΓ.lemma_3_4 hδ
  have hch : ∀ u < X.eN c, X.EPort c u → ∃ v, (v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4) ∧ X.ECh c u v := by
    intro u hu hp
    obtain ⟨v, hv, hpv, hch⟩ := e_chord h34 hup hu hp
    exact ⟨v, hports v hv hpv, hch⟩
  have hN7 : ∀ u, u < 7 → u < X.eN c := fun u h => by rw [hN]; exact h
  have hp0 := hport 0 (by omega)
  have hp1 := hport 1 (by omega)
  have hp3 : X.EPort c 3 := hport' 0 (by omega)
  have hp4 : X.EPort c 4 := hport' 1 (by omega)
  have huniq : ∀ {u v w : ℕ}, v < 7 → w < 7 → X.ECh c u v → X.ECh c u w → v = w :=
    fun hv hw h1 h2 => e_ch_unique (hN7 _ hv) (hN7 _ hw) h1 h2
  -- the target
  have hgoal : X.ECh c 3 1 → Γ.σ (Γ.α (Γ.σ (Γ.α b))) = (Γ.straight ^ 2) a := by
    intro h31
    unfold ECh at h31
    have e3 : X.eG c 3 = Γ.σ (Γ.α b) := by
      unfold eG; rw [show (3 : ℕ) = 3 + 0 from rfl, hW' 0 (by omega), pow_zero, Perm.one_apply]
    rw [← e3, h31, ← e_W_port_succ hp1, hW 2 le_rfl]
  obtain ⟨v, hv, h3v⟩ := hch 3 (hN7 3 (by omega)) hp3
  rcases hv with rfl | rfl | rfl | rfl
  · -- `u₁–w₁`: then `u₂–w₂`, the chords cross
    obtain ⟨w, hw, h1w⟩ := hch 1 (hN7 1 (by omega)) hp1
    have h03 : X.ECh c 0 3 := e_ch_symm h3v
    rcases hw with rfl | rfl | rfl | rfl
    · exact absurd (huniq (by omega) (by omega) h03 (e_ch_symm h1w)) (by omega)
    · exact (e_ch_ne h1w).elim
    · exact absurd (huniq (by omega) (by omega) h3v (e_ch_symm h1w)) (by omega)
    · exact (e_noncross (X := X) (b' := c) (a2 := 3) (b := 1) (b2 := 4) (by omega) (by omega)
        (by omega) (hN7 4 (by omega)) hp0 hp3 hp1 h03 h1w).elim
  · exact hgoal h3v
  · exact (e_ch_ne h3v).elim
  · -- `w₁–w₂`: then `u₁–u₂`, and `v` is visible
    obtain ⟨w, hw, h0w⟩ := hch 0 (hN7 0 (by omega)) hp0
    rcases hw with rfl | rfl | rfl | rfl
    · exact (e_ch_ne h0w).elim
    · exfalso
      apply hv
      refine ⟨b, Orbit.mem_darts.2 ?_, rfl⟩
      have hb2 : Γ.cellOf b = Γ.cellOf ((Γ.straight ^ 2) a) := T.cell_b
      have e2 : (Γ.straight ^ 2) a = Γ.φ (X.eG c 0) := by
        rw [j_φ_apply]; unfold ECh at h0w
        rw [h0w, ← e_W_port_succ hp1, hW 2 le_rfl]
      show Γ.cellOf b = _
      rw [hb2, e2, j_cellOf_φ, e_cell_G, hW 0 (by omega), pow_zero, Perm.one_apply, T.cell_a]
      rfl
    · exact absurd (huniq (by omega) (by omega) h3v (e_ch_symm h0w)) (by omega)
    · exact absurd (huniq (by omega) (by omega) (e_ch_symm h3v) (e_ch_symm h0w)) (by omega)

end SConf

end Pca.Sweep
