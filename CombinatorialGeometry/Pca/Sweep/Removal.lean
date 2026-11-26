/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: removing curves (package R)

SH remove curves throughout section 3.2 ("Removing any curve `γ` from the arrangement `Γ`",
Lemma 3.3, p. 318; `Γ − {γ(k)}`, Lemma 3.8; `Γ' = {γ(i + 1), …, γ(j − 1)}`, Lemma 3.6; the
arrangement `{γ, γ', c}`, Lemma 3.10). In the dart model, removing the set `R` of curves
(`S ∉ R`) deletes

* every dart on a curve of `R`, and every dart at a crossing with a curve of `R` (these crossings
  disappear),
* every dart that is no longer connected to `S` (curves that only met curves of `R` drop out; this
  keeps the map connected, see `doc/pca/sweep.md`, section 3, why this matches SH),

and joins the pieces of a segment: `α'` goes straight through the deleted crossings until it
reaches a kept crossing. `σ`, the labels, the side function and `S` are inherited; the ∞-arc of
the result starts with the joined segment containing the old start, and its inner crossings are
the kept inner crossings of the old arc. `IsRemoval` specifies this through the dart
embedding `ι : D' → D`; it determines the result up to isomorphism. Existence: `exists_removal`.
-/
import Pca.Sweep.R_Make
import Pca.Sweep.R_Prop

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Removing curves gives again a sweep configuration (Euler: every deleted segment separated two
distinct cells, `cellOf_α_ne`; connectivity: by the choice of the kept darts). -/
theorem exists_removal (R : Finset (Fin n)) (hS : Γ.S ∉ R) : Nonempty (Γ.Removal R) :=
  r_exists_removal hS

namespace Removal

variable {R : Finset (Fin n)} (X : Γ.Removal R)

/-- Removing a curve with a part above the sweep makes the configuration smaller. -/
theorem sizeLT (h : ∃ γ ∈ R, Γ.Present γ) : SConf.SizeLT X.Γ' Γ := by
  have h1 := r_numVertices_le X
  have h2 := r_numCurves_lt X h
  rcases h1.lt_or_eq with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h2⟩

/-- The curves of `Γ'` with a part above the sweep are those of `Γ` not in `R` and still
connected to `S`; such a curve intersects the sweep in `Γ'` iff it does in `Γ`. -/
theorem meetsSweep_iff {γ : Fin n} (h : X.Γ'.Present γ) :
    Γ.Present γ ∧ γ ∉ R ∧ (X.Γ'.MeetsSweep γ ↔ Γ.MeetsSweep γ) := by
  obtain ⟨hp, hR⟩ := r_present X h
  obtain ⟨-, d', -⟩ := h
  exact ⟨hp, hR, r_meetsSweep_to X, r_meetsSweep_of X hp.1 hR (r_S_not_mem X d')⟩

open Classical in
/-- The number of pieces minus one of the joined segment starting at `d'`, i.e. the number of
deleted crossings on it (SH: the number of times `γ` crosses a leg, Lemma 3.9). -/
noncomputable def hits (d' : X.D') : ℕ :=
  Nat.find (p := fun k => ¬ Γ.Deleted R
      (Γ.crossingOf (Γ.α ((Γ.straight ^ k) (X.ι d'))))) (by
    obtain ⟨e, ⟨k, hk, rfl⟩, hnd, -⟩ := X.isRemoval.α d'
    exact ⟨k, hnd⟩)

end Removal

end SConf

end Pca.Sweep
