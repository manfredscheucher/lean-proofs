/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The model: simple intersecting arrangements of pseudocircles as combinatorial maps

See `doc/pca/model.md` for the definitions in words and the correspondence to the papers.

A *dart* is a half-edge of the arrangement graph, i.e. a segment end at a crossing,
oriented away from that crossing. On the darts we have

* `σ` : the counter-clockwise successor of a dart at its crossing (rotation),
* `α` : the reverse dart (the other half of the same segment),
* `curve` : the pseudocircle a dart runs along.

Derived permutations:

* `φ = σ * α` (i.e. `d ↦ σ (α d)`): the face permutation; the orbit of `d` is the cell to
  the right of `d`, traversed with the cell on the right (the convention of
  rusty-arrangements, `Arrangement::face_successors`),
* `straight = σ * σ * α` (i.e. `d ↦ σ (σ (α d))`): go straight through the next crossing.

Crossings are the `σ`-orbits, segments the `α`-orbits, cells the `φ`-orbits.
-/
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2

open Equiv Finset

namespace Pca

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Orbits of a permutation

The orbit of `d` under `f` is computed as `d, f d, …, f^[k-1] d` with `k` the period of `d`
(the least `k > 0` with `f^[k] d = d`). This is much faster than Mathlib's decision procedure
for `SameCycle` (which iterates `card D` times), which matters for `native_decide` on the test
instances. `mem_orbitList` shows that it is the `SameCycle` class.
-/

omit [DecidableEq D] in
theorem exists_iterate_eq (f : Perm D) (d : D) : ∃ k, 0 < k ∧ (f^[k]) d = d :=
  ⟨orderOf f, orderOf_pos f, by rw [← Perm.coe_pow, pow_orderOf_eq_one]; rfl⟩

/-- The period of `d` under `f`: the least `k > 0` with `f^[k] d = d`. -/
def period (f : Perm D) (d : D) : ℕ := Nat.find (exists_iterate_eq f d)

theorem period_pos (f : Perm D) (d : D) : 0 < period f d :=
  (Nat.find_spec (exists_iterate_eq f d)).1

theorem iterate_period (f : Perm D) (d : D) : (f^[period f d]) d = d :=
  (Nat.find_spec (exists_iterate_eq f d)).2

/-- The orbit of `d` as the list `d, f d, …, f^[period - 1] d`. -/
def orbitList (f : Perm D) (d : D) : List D :=
  (List.range (period f d)).map (fun i => (f^[i]) d)

theorem mem_orbitList {f : Perm D} {a b : D} : b ∈ orbitList f a ↔ f.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    rw [← Perm.coe_pow]
    exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl f a)
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    have hp : Function.IsPeriodicPt f (period f a) a := iterate_period f a
    refine List.mem_map.2 ⟨i % period f a, List.mem_range.2 (Nat.mod_lt _ (period_pos f a)), ?_⟩
    rw [hp.iterate_mod_apply, ← Perm.coe_pow, hi]

/-- Fast decision of `SameCycle` (used instead of Mathlib's instance). -/
instance (priority := high) decSameCycle (f : Perm D) : DecidableRel f.SameCycle :=
  fun a b => decidable_of_iff _ (mem_orbitList (f := f) (a := a) (b := b))

/-- The orbit of `d` under `f`, as a finset of darts. -/
def orbitFinset (f : Perm D) (d : D) : Finset D := (orbitList f d).toFinset

theorem mem_orbitFinset {f : Perm D} {a b : D} : b ∈ orbitFinset f a ↔ f.SameCycle a b := by
  rw [orbitFinset, List.mem_toFinset, mem_orbitList]

theorem orbitFinset_eq_of_sameCycle {f : Perm D} {a b : D} (h : f.SameCycle a b) :
    orbitFinset f a = orbitFinset f b := by
  ext e
  rw [mem_orbitFinset, mem_orbitFinset]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- The type of orbits of a permutation `f` of the darts. -/
def Orbit (f : Perm D) : Type _ := Quotient (Perm.SameCycle.setoid f)

instance (f : Perm D) : DecidableRel (Perm.SameCycle.setoid f).r :=
  fun a b => decSameCycle f a b

instance (f : Perm D) : DecidableEq (Orbit f) :=
  inferInstanceAs (DecidableEq (Quotient (Perm.SameCycle.setoid f)))

instance (f : Perm D) : Fintype (Orbit f) :=
  inferInstanceAs (Fintype (Quotient (Perm.SameCycle.setoid f)))

/-- The orbit of a dart. -/
def Orbit.mk (f : Perm D) (d : D) : Orbit f := Quotient.mk _ d

/-- The darts of an orbit. -/
def Orbit.darts {f : Perm D} : Orbit f → Finset D :=
  Quotient.lift (orbitFinset f) (fun _ _ h => orbitFinset_eq_of_sameCycle h)

/-- The number of darts of an orbit. -/
def Orbit.size {f : Perm D} (o : Orbit f) : ℕ := o.darts.card

/-! ## The structure -/

/-- The straight-ahead permutation `d ↦ σ (σ (α d))`: walk along the segment of `d` to the
next crossing and leave it on the same curve. -/
def straightPerm (σ α : Perm D) : Perm D := σ * σ * α

/-- The two curves through a crossing (as a finset of curve labels). -/
def crossingCurves {n : ℕ} (σ : Perm D) (curve : D → Fin n) (x : Orbit σ) : Finset (Fin n) :=
  x.darts.image curve

/-- The axioms of a simple intersecting arrangement of `n` pseudocircles on the sphere, given
as a combinatorial map (rotation `σ`, edge involution `α`, curve labels `curve`). -/
structure IsArrangement (n : ℕ) (σ α : Perm D) (curve : D → Fin n) : Prop where
  /-- every crossing has exactly four darts (the arrangement graph is 4-regular) -/
  card_crossing : ∀ d, (orbitFinset σ d).card = 4
  /-- `α` has no fixed points -/
  α_ne : ∀ d, α d ≠ d
  /-- `α` is an involution -/
  α_α : ∀ d, α (α d) = d
  /-- both darts of a segment lie on the same curve -/
  curve_α : ∀ d, curve (α d) = curve d
  /-- at a crossing, consecutive darts lie on different curves ... -/
  curve_σ : ∀ d, curve (σ d) ≠ curve d
  /-- ... and opposite darts on the same curve (the curves cross, they do not touch) -/
  curve_σσ : ∀ d, curve (σ (σ d)) = curve d
  /-- every curve label is a single closed curve: two darts on the same curve are on the same
  straight walk, up to reversing the direction at the crossing (`σ²`) -/
  straight : ∀ d e, curve d = curve e →
    (straightPerm σ α).SameCycle d e ∨ (straightPerm σ α).SameCycle d (σ (σ e))
  /-- intersecting: two distinct curves cross in exactly two crossings -/
  intersecting : ∀ c c' : Fin n, c ≠ c' →
    (univ.filter (fun x : Orbit σ => crossingCurves σ curve x = {c, c'})).card = 2
  /-- sphere (Euler): #crossings - #segments + #cells = 2 -/
  euler : (Fintype.card (Orbit σ) : ℤ) - Fintype.card (Orbit α) + Fintype.card (Orbit (σ * α))
    = 2

instance (n : ℕ) (σ α : Perm D) (curve : D → Fin n) :
    Decidable (IsArrangement n σ α curve) :=
  decidable_of_iff
    ((∀ d, (orbitFinset σ d).card = 4) ∧ (∀ d, α d ≠ d) ∧ (∀ d, α (α d) = d) ∧
      (∀ d, curve (α d) = curve d) ∧ (∀ d, curve (σ d) ≠ curve d) ∧
      (∀ d, curve (σ (σ d)) = curve d) ∧
      (∀ d e, curve d = curve e →
        (straightPerm σ α).SameCycle d e ∨ (straightPerm σ α).SameCycle d (σ (σ e))) ∧
      (∀ c c' : Fin n, c ≠ c' →
        (univ.filter (fun x : Orbit σ => crossingCurves σ curve x = {c, c'})).card = 2) ∧
      ((Fintype.card (Orbit σ) : ℤ) - Fintype.card (Orbit α) + Fintype.card (Orbit (σ * α))
        = 2))
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
     fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

/-- A simple intersecting arrangement of `n` pseudocircles on the sphere, as a combinatorial
map on the dart type `D`. -/
structure Arrangement (n : ℕ) (D : Type*) [Fintype D] [DecidableEq D] where
  /-- counter-clockwise rotation of the darts at a crossing -/
  σ : Perm D
  /-- the reverse dart of the same segment -/
  α : Perm D
  /-- the pseudocircle a dart runs along -/
  curve : D → Fin n
  isArrangement : IsArrangement n σ α curve

namespace Arrangement

variable {n : ℕ} (A : Arrangement n D)

/-- The face permutation `d ↦ σ (α d)`; its orbit through `d` is the cell to the right of `d`. -/
def φ : Perm D := A.σ * A.α

/-- Go straight: `d ↦ σ (σ (α d))`. -/
def straight : Perm D := straightPerm A.σ A.α

/-- Crossings: orbits of `σ`. -/
abbrev Crossing := Orbit A.σ
/-- Segments (edges of the arrangement graph): orbits of `α`. -/
abbrev Segment := Orbit A.α
/-- Cells (faces): orbits of `φ`. -/
abbrev Cell := Orbit A.φ

/-- The crossing at which the dart `d` starts. -/
def crossingOf (d : D) : A.Crossing := Orbit.mk A.σ d
/-- The segment of the dart `d`. -/
def segmentOf (d : D) : A.Segment := Orbit.mk A.α d
/-- The cell to the right of the dart `d`. -/
def cellOf (d : D) : A.Cell := Orbit.mk A.φ d

end Arrangement

end Pca
