/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: Euler of the untangling

`uG` is constant on new cells (`UHyp.uG_ph`) and onto the old cells, so `F' ≥ F`; `V' = V`,
`E' = E`, and `V' - E' + F' ≤ 2` for the connected new map (`Pca.MapFacts.euler_le_two`).
-/
import Pca.Sweep.U_Cell

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

theorem u_card_two {X : Type u} [Fintype X] [DecidableEq X] (f : Perm X)
    (hf : ∀ y, (orbitFinset f y).card = 2) : Fintype.card X = 2 * Fintype.card (Orbit f) := by
  rw [card_eq_sum_size f]
  have : ∀ o : Orbit f, o.size = 2 := by
    intro o
    obtain ⟨y, rfl⟩ := o.exists_mk
    exact hf y
  rw [sum_congr rfl fun o _ => this o, sum_const, card_univ, smul_eq_mul, mul_comm]

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.uG_pow (x : D) (i : ℕ) : Γ.uG d a ((H.ph ^ i) x) = Γ.uG d a x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [u_pow_succ, H.uG_ph, ih]

/-- The old cell (`T` merged into `B`) of a new cell. -/
noncomputable def UHyp.Gc : Orbit H.ph → Γ.Cell :=
  Quotient.lift (Γ.uG d a) (fun x y (h : H.ph.SameCycle x y) => by
    obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
    exact (H.uG_pow x i).symm)

theorem UHyp.Gc_mk (x : D) : H.Gc (Orbit.mk H.ph x) = Γ.uG d a x := rfl

theorem UHyp.Gc_surj : Function.Surjective H.Gc := by
  intro f
  obtain ⟨y, rfl⟩ := f.exists_mk
  show ∃ o, H.Gc o = Γ.cellOf y
  have hcell := H.cell_uM
  have viaM : ∀ (i : Fin 12) (c : Fin 7), uCI i = c → c ≠ 2 →
      (∀ j : Fin 12, (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 10) → j ≠ i) →
      ∃ o, H.Gc o = Γ.uCell d a c := by
    intro i c hic hc2 hj
    refine ⟨Orbit.mk H.ph (Γ.uM d a i), ?_⟩
    rw [H.Gc_mk, H.uG_of (hcell i), hic, if_neg hc2]
    refine H.notSp (hcell i) ?_ ?_ ?_ ?_ ?_
    · intro _ h; exact hj 0 (by decide) (H.uM_inj h).symm
    · intro _ h; exact hj 1 (by decide) (H.uM_inj h).symm
    · intro _ h; exact hj 2 (by decide) (H.uM_inj h).symm
    · intro _ h; exact hj 3 (by decide) (H.uM_inj h).symm
    · intro _; exact ⟨H.uM_ne_d i, fun h => hj 10 (by decide) (H.uM_inj h).symm⟩
  by_cases h2 : Γ.cellOf y = Γ.uCell d a 2
  · exact ⟨Orbit.mk H.ph d, by rw [H.Gc_mk, H.uG_d, h2]⟩
  by_cases h0 : Γ.cellOf y = Γ.uCell d a 0
  · rw [h0]; exact viaM 7 0 rfl (by decide) (by decide)
  by_cases h1 : Γ.cellOf y = Γ.uCell d a 1
  · rw [h1]; exact viaM 4 1 rfl (by decide) (by decide)
  by_cases h3 : Γ.cellOf y = Γ.uCell d a 3
  · rw [h3]; exact viaM 6 3 rfl (by decide) (by decide)
  by_cases h4 : Γ.cellOf y = Γ.uCell d a 4
  · rw [h4]; exact viaM 9 4 rfl (by decide) (by decide)
  refine ⟨Orbit.mk H.ph y, ?_⟩
  rw [H.Gc_mk, H.uG_gen, if_neg h2]
  rintro (h | h | h | h | h | h) <;> subst h
  · exact h4 rfl
  · exact h4 (hcell 10)
  · exact h0 (hcell 0)
  · exact h1 (hcell 1)
  · exact h2 (hcell 2)
  · exact h3 (hcell 3)

theorem UHyp.card_cells : Fintype.card Γ.Cell ≤ Fintype.card (Orbit H.ph) :=
  Fintype.card_le_of_surjective _ H.Gc_surj

theorem UHyp.card_seg : Fintype.card (Orbit H.α') = Fintype.card (Orbit Γ.α) := by
  have h1 := u_card_two H.α' (fun y => by
    rw [Pca.MapFacts.orbitFinset_inv _ (fun x => H.uαf_invol x)]
    exact card_pair (H.uαf_ne y).symm)
  have h2 := u_card_two Γ.α (fun y => by
    rw [Pca.MapFacts.orbitFinset_inv _ (fun x => Γ.j_α_α x)]
    exact card_pair (Γ.isSConf.α_ne y).symm)
  omega

theorem UHyp.euler (hne : Nonempty D) :
    (Fintype.card (Orbit Γ.σ) : ℤ) - Fintype.card (Orbit H.α') +
      Fintype.card (Orbit (Γ.σ * H.α')) = 2 := by
  have heu := Γ.isSConf.euler hne
  have hle := Pca.MapFacts.euler_le_two (σ := Γ.σ) (α := H.α') (fun x => H.uαf_invol x)
    (fun x => H.uαf_ne x) (fun x y => H.connected x y)
  have hc := H.card_cells
  have hs := H.card_seg
  change (Fintype.card (Orbit Γ.σ) : ℤ) - Fintype.card (Orbit Γ.α) +
    Fintype.card Γ.Cell = 2 at heu
  change _ ≤ Fintype.card (Orbit H.ph) at hc
  change (Fintype.card (Orbit Γ.σ) : ℤ) - Fintype.card (Orbit H.α') +
    Fintype.card (Orbit H.ph) ≤ 2 at hle
  change (Fintype.card (Orbit Γ.σ) : ℤ) - Fintype.card (Orbit H.α') +
    Fintype.card (Orbit H.ph) = 2
  rw [hs] at hle ⊢
  omega

end Hyp

end SConf

end Pca.Sweep
