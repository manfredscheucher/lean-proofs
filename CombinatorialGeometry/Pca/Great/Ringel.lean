/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel's theorem for great-pseudocircle arrangements (P3, `doc/pca/great.md` section 3)

Every great arrangement flips to the canonical form (`reach_cf`), two canonical forms are
isomorphic (`cf_iso`), and flips are reversible (`AFlip.symm`) and can be transported along
isomorphisms (`AFlip.transport`).
-/
import Pca.Great.R_Trans

open Equiv Finset

namespace Pca.Great

universe u v

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

/-- A frame exists. -/
theorem exists_frame (A : Arrangement n D) : Nonempty (Frame A) := by
  have hn := A.two_le_n
  obtain ⟨y, hy⟩ := A.exists_dart_on (⟨0, by omega⟩ : Fin n)
  exact ⟨⟨_, y, hy⟩⟩

/-- Antipodal flips keep greatness along a flip sequence. -/
theorem reach_great {D' : Type v} [Fintype D'] [DecidableEq D'] {Y Y' : Arrangement n D'}
    (h : Relation.ReflTransGen Arrangement.AFlip Y Y') (hY : Y.IsGreat) : Y'.IsGreat := by
  induction h with
  | refl => exact hY
  | tail _ hZW ih => exact AFlip.isGreat ih hZW

/-- Transport of a flip sequence along an isomorphism. -/
theorem reach_transport {D' : Type v} [Fintype D'] [DecidableEq D'] {Y Y' : Arrangement n D'}
    (h : Relation.ReflTransGen Arrangement.AFlip Y Y') (hY : Y.IsGreat) :
    ∀ (X : Arrangement n D), X.IsGreat → Iso X Y →
      ∃ X', Relation.ReflTransGen Arrangement.AFlip X X' ∧ Nonempty (Iso X' Y') := by
  induction h with
  | refl => intro X _ φ; exact ⟨X, .refl, ⟨φ⟩⟩
  | tail hYZ hZW ih =>
    intro X hX φ
    obtain ⟨X', hXX', ⟨ψ⟩⟩ := ih X hX φ
    obtain ⟨X'', hX'X'', hiso⟩ := AFlip.transport (reach_great hXX' hX) (reach_great hYZ hY) ψ hZW
    exact ⟨X'', .tail hXX' hX'X'', hiso⟩

/-- **Ringel's theorem** (P3): any two great-pseudocircle arrangements on `n` curves are joined by
a finite sequence of antipodal flips, up to isomorphism. -/
theorem ringel {D' : Type v} [Fintype D'] [DecidableEq D'] (A : Arrangement n D)
    (B : Arrangement n D') (hA : A.IsGreat) (hB : B.IsGreat) :
    ∃ C : Arrangement n D, Relation.ReflTransGen Arrangement.AFlip A C ∧ Nonempty (Iso C B) := by
  obtain ⟨FA⟩ := exists_frame A
  obtain ⟨FB⟩ := exists_frame B
  obtain ⟨A', FA', hAA', hA', hpA, -, -⟩ := FA.reach_cf hA
  obtain ⟨B', FB', hBB', hB', hpB, -, -⟩ := FB.reach_cf hB
  obtain ⟨φ⟩ := FA'.cf_iso FB' hA' hB' hpA hpB
  have hsymm : ∀ {X Y : Arrangement n D'}, Relation.ReflTransGen Arrangement.AFlip X Y →
      Relation.ReflTransGen Arrangement.AFlip Y X := by
    intro X Y h
    induction h with
    | refl => exact .refl
    | tail _ h2 ih => exact .head (AFlip.symm h2) ih
  obtain ⟨C, hA'C, hiso⟩ := reach_transport (hsymm hBB') hB' A' hA' φ
  exact ⟨C, hAA'.trans hA'C, hiso⟩

end Pca.Great
