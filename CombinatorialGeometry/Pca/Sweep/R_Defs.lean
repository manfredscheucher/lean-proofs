/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: removing curves, the definitions (package R)

`Deleted`, `Piece`, `KeptStep`, `Keep`, `IsRemoval`, `Removal`; explained and used in
`Pca/Sweep/Removal.lean` (split off so that the helper files `R_*.lean` can use them).
-/
import Pca.Sweep.Jordan

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- The crossing `x` disappears when the curves `R` are removed. -/
def Deleted (R : Finset (Fin n)) (x : Γ.Crossing) : Prop := ∃ γ ∈ R, Γ.OnCurve γ x

/-- `e` is a piece of the joined segment starting with `d`: `e = straight^k d`, and the crossings
passed on the way (the ends of the earlier pieces) are deleted. -/
def Piece (R : Finset (Fin n)) (d e : D) : Prop :=
  ∃ k : ℕ, (∀ i < k, Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ i) d)))) ∧
    (Γ.straight ^ k) d = e

/-- One step in the map after the removal (before dropping components): `σ` at a kept crossing,
or the joined segment. -/
def KeptStep (R : Finset (Fin n)) (a b : D) : Prop :=
  ¬ Γ.Deleted R (Γ.crossingOf a) ∧ ¬ Γ.Deleted R (Γ.crossingOf b) ∧
    (b = Γ.σ a ∨ ∃ e, Γ.Piece R a e ∧ b = Γ.α e)

/-- The dart `d` survives the removal of `R`: its crossing is kept and it is connected to `S`. -/
def Keep (R : Finset (Fin n)) (d : D) : Prop :=
  ¬ Γ.Deleted R (Γ.crossingOf d) ∧
    ∃ e, Γ.curve e = Γ.S ∧ Relation.EqvGen (Γ.KeptStep R) d e

/-- `Γ'` (with dart embedding `ι`) is `Γ` with the curves `R` removed. -/
structure IsRemoval (R : Finset (Fin n)) {D' : Type u} [Fintype D'] [DecidableEq D']
    (Γ' : SConf n D') (ι : D' → D) : Prop where
  inj : Function.Injective ι
  range : ∀ d, (∃ d', ι d' = d) ↔ Γ.Keep R d
  curve : ∀ d', Γ'.curve d' = Γ.curve (ι d')
  S : Γ'.S = Γ.S
  σ : ∀ d', ι (Γ'.σ d') = Γ.σ (ι d')
  α : ∀ d', ∃ e, Γ.Piece R (ι d') e ∧ ¬ Γ.Deleted R (Γ.crossingOf (Γ.α e)) ∧
    ι (Γ'.α d') = Γ.α e
  side : ∀ d', Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) d') = Γ.side (Γ.cellOf (ι d'))
  /-- the ∞-arc of `Γ'` starts with the joined segment containing the start of the ∞-arc of `Γ` -/
  infStart : ∀ z' ∈ Γ'.infStart, ∃ z ∈ Γ.infStart, Γ.Piece R (ι z') z
  /-- the crossings inside the ∞-arc of `Γ'` are the kept crossings inside the ∞-arc of `Γ` -/
  infVertex : ∀ d', Γ'.IsInfVertex (Γ'.crossingOf d') ↔ Γ.IsInfVertex (Γ.crossingOf (ι d'))

/-- A removal of the curves `R` from `Γ`, bundled with its dart type. -/
structure Removal (R : Finset (Fin n)) where
  D' : Type u
  [fin : Fintype D']
  [dec : DecidableEq D']
  Γ' : SConf n D'
  ι : D' → D
  isRemoval : Γ.IsRemoval R Γ' ι

attribute [instance] Removal.fin Removal.dec

end SConf

end Pca.Sweep
