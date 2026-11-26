/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: sweep configurations (skeleton)

Source: J. Snoeyink, J. Hershberger, *Sweeping arrangements of curves*, DIMACS Series 6 (1991),
309-349 (cited as SH, journal page numbers). Plan and translation: `doc/pca/sweep.md`.

A **sweep configuration** is the existing dart model of `Pca/Model.lean` (`σ`, `α`, `curve`, same
conventions: `φ = σ * α`, the cell of `d` is the cell to the right of `d`), with

* one curve label `S`, the sweeping curve (SH's `c`),
* a side function `side` of `S` (`side = 1`: the side **above** `S`, the side being swept),
* the **∞-arc**, given by its first dart `infStart` and the number `infLen` of crossings strictly
  inside it: the darts `straight^i infStart`, `i ≤ infLen`, of `S` (all directed with the upper
  side on their left, SH's orientation of `c`, p. 313). A start dart is needed (a set of darts is
  not enough): when the arc covers all of `S`, the set cannot tell "no vertex on the sweep" from
  "exactly one" (`doc/pca/sweep.md`, section 2.1). It is the graph-language form of SH's
  puncture point `∞` on `c` (p. 325: "To sweep a sphere with a closed curve `c`, simply find a
  point that lies only on `c` and remove this point"): the edges `[m, ∞]` and `[∞, 1]` of SH are the
  first and last segment of the arc; the crossings strictly inside the arc are the places where
  rays reach `∞` (they are not vertices of SH's graph `G`). Initially the arc is one segment
  (`infLen = 0`).

Axioms: those of `IsArrangement` with axiom 6 (intersecting, exactly two crossings per pair)
relaxed to SH's **two-intersection property** (at most two crossings per pair, SH p. 313,
`k = 2`), with connectivity added (`doc/pca/model.md`, section 2: without "intersecting", Euler alone
does not give genus 0), and with Euler and "`S` has a dart" required only for a nonempty map (the
empty map is the configuration in which every curve has been removed).
-/
import Pca.Model

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- One step of the connectivity relation: `σ` or `α`. -/
def StepRel (σ α : Perm D) (a b : D) : Prop := b = σ a ∨ b = α a

/-- The axioms of a sweep configuration: axioms 1-5 of `IsArrangement` unchanged, axiom 6
relaxed to "at most two crossings per pair", connectivity added, Euler for a nonempty map. -/
structure IsSConf (n : ℕ) (σ α : Perm D) (curve : D → Fin n) (S : Fin n) : Prop where
  card_crossing : ∀ d, (orbitFinset σ d).card = 4
  α_ne : ∀ d, α d ≠ d
  α_α : ∀ d, α (α d) = d
  curve_α : ∀ d, curve (α d) = curve d
  curve_σ : ∀ d, curve (σ d) ≠ curve d
  curve_σσ : ∀ d, curve (σ (σ d)) = curve d
  straight : ∀ d e, curve d = curve e →
    (straightPerm σ α).SameCycle d e ∨ (straightPerm σ α).SameCycle d (σ (σ e))
  /-- two-intersection property (SH p. 313, `k = 2`); replaces "intersecting" -/
  two_int : ∀ c c' : Fin n, c ≠ c' →
    (univ.filter (fun x : Orbit σ => crossingCurves σ curve x = {c, c'})).card ≤ 2
  /-- the map is connected (needed for genus 0 once "intersecting" is dropped) -/
  connected : ∀ d e, Relation.EqvGen (StepRel σ α) d e
  /-- sphere (Euler), for a nonempty map -/
  euler : Nonempty D → (Fintype.card (Orbit σ) : ℤ) - Fintype.card (Orbit α) +
    Fintype.card (Orbit (σ * α)) = 2
  /-- the sweeping curve is part of the map -/
  S_mem : Nonempty D → ∃ d, curve d = S

/-- The darts `straight^i z` for `i ≤ k` (the ∞-arc starting at `z` with `k` inner crossings);
empty if there is no start dart. -/
def arcOf (σ α : Perm D) (z : Option D) (k : ℕ) : Finset D :=
  z.elim ∅ fun z => (range (k + 1)).image (fun i => (straightPerm σ α ^ i) z)

/-- A **sweep configuration**: a sphere map with a sweeping curve `S`, its upper side and the
∞-arc. -/
structure SConf (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] where
  σ : Perm D
  α : Perm D
  curve : D → Fin n
  S : Fin n
  isSConf : IsSConf n σ α curve S
  /-- side function of `S`; `side f = 1`: the cell `f` lies above `S` -/
  side : Orbit (σ * α) → ZMod 2
  isSide : ∀ y, side (Orbit.mk (σ * α) y) + side (Orbit.mk (σ * α) (α y)) =
    if curve y = S then 1 else 0
  /-- the first dart of the ∞-arc (`none` only for the empty map) -/
  infStart : Option D
  /-- the number of crossings strictly inside the ∞-arc: the arc is `straight^i infStart`,
  `i ≤ infLen`, its inner crossings are the ends of `straight^i infStart`, `i < infLen` -/
  infLen : ℕ
  infStart_isSome : Nonempty D → infStart.isSome
  /-- `infLen = period` means: every crossing on `S` is inside the arc (no vertex on the sweep);
  `infLen = period - 1`: exactly one vertex on the sweep -/
  infLen_le : ∀ z ∈ infStart, infLen ≤ period (straightPerm σ α) z
  /-- the darts of the ∞-arc are darts of `S`, directed with the upper side on the left -/
  infArc_sweep : ∀ d ∈ arcOf σ α infStart infLen,
    curve d = S ∧ side (Orbit.mk (σ * α) (α d)) = 1

/-- A configuration bundled with its dart type (the minimal counterexample of SH p. 318 ranges
over all of them). -/
structure Conf (n : ℕ) : Type (u + 1) where
  D : Type u
  [fin : Fintype D]
  [dec : DecidableEq D]
  Γ : SConf n D

attribute [instance] Conf.fin Conf.dec

end Pca.Sweep
