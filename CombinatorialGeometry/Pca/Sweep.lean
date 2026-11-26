/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweeping lemma: the two forms (milestone 7)

* `Arrangement.SweepFirstMove`: the sweeping lemma in the form of FS2021: on the side of `C` containing a given cell `f₀` there is a digon or triangle `≠ f₀` with a side
  on `C` (Felsner-Scheucher 2021, proof of `thm:2n_3_triangles`),
* `Arrangement.SweepTwoCells`: on each side of each pseudocircle `C` there are two distinct
  digons or triangles with a side on `C` (Snoeyink-Hershberger 1991, proof of Lemma 4.1; quoted in
  Felsner-Scheucher 2021, lines 177-178: "every pseudocircle is incident to two cells which are
  digons or triangles on either side"),
* `Arrangement.sweepFirstMove_iff`: the two forms are equivalent (no axiom),
Both hold for every arrangement: `Arrangement.sweepFirstMove`, `Arrangement.sweepTwoCells`
(`Pca/SweepLemma.lean`), proved via Snoeyink-Hershberger in graph language (`Pca/Sweep/`).

Both forms are decidable; they are checked on the test instances (`Pca/Instances/Sweep.lean`).
-/
import Pca.Side

open Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- The sweeping lemma (first move of a sweep), for one arrangement. -/
def SweepFirstMove : Prop :=
  ∀ (C : Fin n) (s : A.Cell → ZMod 2), A.IsSide C s → ∀ f₀ : A.Cell,
    ∃ g : A.Cell, g ≠ f₀ ∧ s g = s f₀ ∧ (∃ d ∈ g.darts, A.curve d = C) ∧
      (A.IsDigon g ∨ A.IsTriangle g)

/-- For the side function `s` of `C`: on each side there are two distinct digons or triangles with
a side on `C`. -/
def TwoCellsOn (C : Fin n) (s : A.Cell → ZMod 2) : Prop :=
  ∀ b : ZMod 2, ∃ g₁ g₂ : A.Cell, g₁ ≠ g₂ ∧ s g₁ = b ∧ s g₂ = b ∧
    ((∃ d ∈ g₁.darts, A.curve d = C) ∧ (A.IsDigon g₁ ∨ A.IsTriangle g₁)) ∧
    ((∃ d ∈ g₂.darts, A.curve d = C) ∧ (A.IsDigon g₂ ∨ A.IsTriangle g₂))

/-- On each side of each pseudocircle `C` there are two distinct digons or triangles with a side
on `C` (the form of Snoeyink-Hershberger, Lemma 4.1). -/
def SweepTwoCells : Prop :=
  ∀ (C : Fin n) (s : A.Cell → ZMod 2), A.IsSide C s → A.TwoCellsOn C s

instance (C : Fin n) (s : A.Cell → ZMod 2) : Decidable (A.TwoCellsOn C s) := by
  unfold TwoCellsOn; infer_instance

/-- `TwoCellsOn` does not depend on the choice of the side function. -/
theorem TwoCellsOn.add_one {C : Fin n} {s : A.Cell → ZMod 2} (h : A.TwoCellsOn C s) :
    A.TwoCellsOn C (fun f => s f + 1) := by
  intro b
  obtain ⟨g₁, g₂, hne, h₁, h₂, k₁, k₂⟩ := h (b + 1)
  refine ⟨g₁, g₂, hne, ?_, ?_, k₁, k₂⟩ <;>
  · simp only [h₁, h₂, add_assoc, zmod2_add_self, add_zero]

/-- To check `SweepTwoCells` it suffices to check one side function per curve (side functions
are unique up to swapping the sides). Used for the test instances. -/
theorem sweepTwoCells_of_exists (h : ∀ C, ∃ s, A.IsSide C s ∧ A.TwoCellsOn C s) :
    A.SweepTwoCells := by
  intro C s' hs'
  obtain ⟨s, hs, hT⟩ := h C
  rcases hs.eq_or_eq_add_one hs' with rfl | rfl
  · exact hT
  · exact hT.add_one

/-- The two forms of the sweeping lemma are equivalent. -/
theorem sweepFirstMove_iff : A.SweepFirstMove ↔ A.SweepTwoCells := by
  constructor
  · intro h C s hs b
    obtain ⟨y, -, hy⟩ := exists_dart_on_side hs b
    obtain ⟨g₁, hne₁, hs₁, hC₁, hk₁⟩ := h C s hs (A.cellOf y)
    obtain ⟨g₂, hne₂, hs₂, hC₂, hk₂⟩ := h C s hs g₁
    exact ⟨g₁, g₂, hne₂.symm, hs₁.trans hy, hs₂.trans (hs₁.trans hy), ⟨hC₁, hk₁⟩, ⟨hC₂, hk₂⟩⟩
  · intro h C s hs f₀
    obtain ⟨g₁, g₂, hne, hs₁, hs₂, ⟨hC₁, hk₁⟩, ⟨hC₂, hk₂⟩⟩ := h C s hs (s f₀)
    by_cases h₁ : g₁ = f₀
    · exact ⟨g₂, fun h₂ => hne (h₁.trans h₂.symm), hs₂, hC₂, hk₂⟩
    · exact ⟨g₁, h₁, hs₁, hC₁, hk₁⟩

end Pca.Arrangement
