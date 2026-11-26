/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: extending the ∞-arc to all of `S` except the edges `[tA, tB)`

Used by the surgery of Lemma 3.11 (`doc/pca/sweep.md`, step 3.1). Same darts, `σ`, `α`,
labels and side function; the ∞-arc starts with the sweep dart from vertex `tB` and ends with the
one into vertex `tA`, so the vertices on the sweep are exactly `tA, …, tB`.
-/
import Pca.Sweep.NO_Sweep

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

theorem p_noC_add_period (z : D) (t : ℕ) :
    Γ.noC z (t + period Γ.straight z) = Γ.noC z t := by
  unfold noC
  rw [← no_period_w z, no_pow_period]

theorem p_period_noC (z : D) (t : ℕ) : period Γ.straight (Γ.noC z t) = period Γ.straight z := by
  unfold noC; rw [no_period_pow, no_period_w]

variable (Γ) in
/-- `Γ` with the ∞-arc from vertex `tB` around to vertex `tA`. -/
def pRedir {z : D} (hz : Γ.infStart = some z) (tA tB : ℕ) : SConf n D :=
  { Γ with
    infStart := some (Γ.noC z tB)
    infLen := period Γ.straight z - 1 - (tB - tA)
    infStart_isSome := fun _ => rfl
    infLen_le := by
      intro z' hz'
      obtain rfl : z' = Γ.noC z tB := (Option.mem_some_iff.1 hz').symm
      change _ ≤ period Γ.straight (Γ.noC z tB)
      rw [p_period_noC]; omega
    infArc_sweep := by
      intro e he
      simp only [arcOf, Option.elim, mem_image, mem_range] at he
      obtain ⟨i, -, rfl⟩ := he
      have h := no_sweep_pow (no_noC_sweep hz tB) i
      exact h }

section Redir

variable {z : D} (hz : Γ.infStart = some z) {tA tB : ℕ}
include hz

theorem p_redir_infStart : (Γ.pRedir hz tA tB).infStart = some (Γ.noC z tB) := rfl

theorem p_redir_noC (hAB : tA ≤ tB) (hB : tB < period Γ.straight z) (t : ℕ) :
    (Γ.pRedir hz tA tB).noC (Γ.noC z tB) t = Γ.noC z (tA + t) := by
  have hP := period_pos Γ.straight z
  change (Γ.straight ^ t) ((Γ.straight ^ (period Γ.straight z - 1 - (tB - tA) + 1))
    (Γ.noC z tB)) = _
  rw [← no_pow_add, no_noC_eq, ← no_pow_add,
    show t + (period Γ.straight z - 1 - (tB - tA) + 1) + (tB + (Γ.infLen + 1)) =
      (tA + t + period Γ.straight z) + (Γ.infLen + 1) by omega,
    ← no_noC_eq, p_noC_add_period]

theorem p_redir_period : period (Γ.pRedir hz tA tB).straight (Γ.noC z tB) =
    period Γ.straight z := by
  change period Γ.straight (Γ.noC z tB) = _; exact p_period_noC z tB

/-- The vertices on the sweep of the redirected configuration. -/
theorem p_redir_fin (hAB : tA ≤ tB) (hB : tB < period Γ.straight z) {t : ℕ}
    (ht : t < period Γ.straight z) :
    (Γ.pRedir hz tA tB).IsFinVertex (Γ.crossingOf (Γ.noC z t)) ↔ tA ≤ t ∧ t ≤ tB := by
  set Γ₁ := Γ.pRedir hz tA tB
  set P := period Γ.straight z
  have hz₁ : Γ₁.infStart = some (Γ.noC z tB) := rfl
  have hP₁ : period Γ₁.straight (Γ.noC z tB) = P := p_redir_period hz
  set s := (t + P - tA) % P with hs
  have hsP : s < P := Nat.mod_lt _ (by omega)
  have hst : Γ.noC z (tA + s) = Γ.noC z t := by
    rcases Nat.lt_or_ge t tA with h | h
    · rw [hs, Nat.mod_eq_of_lt (by omega), show tA + (t + P - tA) = t + P by omega,
        p_noC_add_period]
    · rw [hs, show t + P - tA = (t - tA) + P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), show tA + (t - tA) = t by omega]
  have h1 := no_noC_fin hz₁ (t := s) (by rw [hP₁]; exact hsP)
  rw [p_redir_noC hz hAB hB, hst, hP₁] at h1
  change Γ₁.IsFinVertex (Γ₁.crossingOf (Γ.noC z t)) ↔ _
  rw [h1]
  change s + (P - 1 - (tB - tA)) < P ↔ _
  rcases Nat.lt_or_ge t tA with h | h
  · rw [hs, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [hs, show t + P - tA = (t - tA) + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- A finite edge of the redirected configuration is an edge `[t, t + 1]`, `tA ≤ t < tB`. -/
theorem p_redir_finSeg (hAB : tA ≤ tB) (hB : tB < period Γ.straight z) {e : D}
    (he : (Γ.pRedir hz tA tB).IsFinSeg e) : ∃ t, tA ≤ t ∧ t < tB ∧ Γ.noC z t = e := by
  set Γ₁ := Γ.pRedir hz tA tB
  set P := period Γ.straight z
  have hz₁ : Γ₁.infStart = some (Γ.noC z tB) := rfl
  have hP₁ : period Γ₁.straight (Γ.noC z tB) = P := p_redir_period hz
  obtain ⟨s, hs, rfl⟩ := no_noC_surj hz₁ he.1
  rw [hP₁] at hs
  have hna := (no_noC_arc hz₁ (by rw [hP₁]; exact hs)).not.1 he.2
  rw [hP₁] at hna
  change ¬ (P ≤ s + (P - 1 - (tB - tA)) + 1) at hna
  refine ⟨tA + s, by omega, by omega, ?_⟩
  rw [p_redir_noC hz hAB hB]

/-- The vertices on the sweep of the redirected configuration are vertices on the sweep of `Γ`
(for `tB` a vertex on the sweep of `Γ`). -/
theorem p_redir_fin_sub (hAB : tA ≤ tB) (hB : tB + Γ.infLen < period Γ.straight z)
    {x : Γ.Crossing} (hx : (Γ.pRedir hz tA tB).IsFinVertex x) : Γ.IsFinVertex x := by
  obtain ⟨t, ht, rfl⟩ := no_onSweep_noC hz (hx.1 : Γ.OnSweep x)
  have := (p_redir_fin hz hAB (by omega) ht).1 hx
  exact (no_noC_fin hz ht).2 (by omega)

open Classical in
/-- Dropping a vertex on the sweep makes the configuration smaller. -/
theorem p_redir_numVertices (hAB : tA ≤ tB) (hB : tB + Γ.infLen < period Γ.straight z) {t : ℕ}
    (ht : t + Γ.infLen < period Γ.straight z) (hout : t < tA ∨ tB < t) :
    (Γ.pRedir hz tA tB).numVertices < Γ.numVertices := by
  unfold numVertices
  have key : (univ.filter (fun x : Γ.Crossing =>
      (Γ.pRedir hz tA tB).IsFinVertex x ∨ Γ.IsAboveVertex x)).card <
      (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x)).card := by
    apply card_lt_card
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hx ⊢
      refine ⟨mem_univ _, ?_⟩
      rcases hx.2 with h | h
      · exact Or.inl (p_redir_fin_sub hz hAB hB h)
      · exact Or.inr h
    · have hm : Γ.crossingOf (Γ.noC z t) ∈ univ.filter
          (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x) :=
        mem_filter.2 ⟨mem_univ _, Or.inl ((no_noC_fin hz (by omega)).2 ht)⟩
      have := (mem_filter.1 (hsub hm)).2
      rcases this with h | h
      · have := (p_redir_fin hz hAB (by omega) (t := t) (by omega)).1 h
        omega
      · exact h.1 (no_S_mem_noC hz t)
  refine lt_of_le_of_lt (card_le_card_of_injOn (fun x => x) (fun x hx => ?_)
    (fun _ _ _ _ h => h)) key
  have hx' := (mem_filter.1 hx).2
  exact mem_filter.2 ⟨mem_univ _, hx'⟩

end Redir

end SConf

end Pca.Sweep
