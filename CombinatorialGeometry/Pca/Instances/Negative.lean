/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Pca.Fingerprint
import Pca.Instances.All4.A6
import Pca.Instances.All4.A8

/-!
# Negative tests

Maps that violate exactly one axiom of `IsArrangement` and are rejected:

* `fpBad` (Euler, axiom 7): the Krupp fingerprint `[[2, 3, -2, -3], [-1, 3, 1, -3], [-1, -2, 1, 2]]`
  with the cyclic order of the third list changed to `[-1, 1, -2, 2]` is well formed and
  satisfies all local axioms, but the map is not on the sphere (`V - E + F = -2`).
* `bad5` (one closed curve per label, axiom 5): label 0 consists of two disjoint closed curves
  `P`, `P'`. Curves `B` (label 1) and `C` (label 2) cross twice, `P` crosses only `B` (twice),
  `P'` crosses only `C` (twice). A planar, connected picture with 6 crossings.
* `bad6` (intersecting, axiom 6): two closed curves crossing four times (a circle and an
  ellipse), a planar, connected picture with 4 crossings.

The darts tables of `bad5`, `bad6` use the encoding of `Pca/Fingerprint.lean` (darts `2k`,
`2k+1` at the `k`-th entry of the concatenated lists of the curves, in the order
`P, P', B, C` resp. the two curves); they are hand-written, not fingerprints, because
`Fingerprint.partner` cannot handle a pair of curves crossing more than once or a label with
two curves.

Finally, `Describes` distinguishes lines 6 and 8 of `all4.txt`, which have the same
`(p_2, p_3)`.
-/

namespace Pca.Instances.Negative

open Pca Fingerprint

/-! ## Euler -/

/-- A well-formed fingerprint that is not an arrangement on the sphere. -/
def fpBad : Fingerprint := [[2, 3, -2, -3], [-1, 3, 1, -3], [-1, 1, -2, 2]]

theorem fpBad_wellFormed : fpBad.WellFormed 3 24 := by native_decide

theorem hσ : ∀ i, fpBad.sigmaFun 24 (fpBad.sigmaFun 24 (fpBad.sigmaFun 24
    (fpBad.sigmaFun 24 i))) = i := by native_decide

theorem hα : ∀ i, fpBad.alphaFun 24 (fpBad.alphaFun 24 i) = i := by native_decide

/-- The map of `fpBad`. -/
abbrev badσ : Equiv.Perm (Fin 24) := permOfPow4 _ hσ
abbrev badα : Equiv.Perm (Fin 24) := permOfInvolution _ hα
abbrev badcurve : Fin 24 → Fin 3 := fpBad.curveFun 3 24

/-- `fpBad` satisfies every axiom except axiom 7 ... -/
theorem fpBad_others :
    (∀ d, (orbitFinset badσ d).card = 4) ∧ (∀ d, badα d ≠ d) ∧ (∀ d, badα (badα d) = d) ∧
      (∀ d, badcurve (badα d) = badcurve d) ∧ (∀ d, badcurve (badσ d) ≠ badcurve d) ∧
      (∀ d, badcurve (badσ (badσ d)) = badcurve d) ∧
      (∀ d e, badcurve d = badcurve e →
        (straightPerm badσ badα).SameCycle d e ∨
          (straightPerm badσ badα).SameCycle d (badσ (badσ e))) ∧
      (∀ c c' : Fin 3, c ≠ c' →
        (Finset.univ.filter (fun x : Orbit badσ =>
          crossingCurves badσ badcurve x = {c, c'})).card = 2) := by
  native_decide

/-- ... but its Euler characteristic is `-2` ... -/
theorem fpBad_euler :
    (Fintype.card (Orbit (permOfPow4 _ hσ)) : ℤ) - Fintype.card (Orbit (permOfInvolution _ hα))
      + Fintype.card (Orbit (permOfPow4 _ hσ * permOfInvolution _ hα)) = -2 := by native_decide

/-- ... so it is not an arrangement. -/
theorem fpBad_not : ¬ IsArrangement 3 (permOfPow4 _ hσ) (permOfInvolution _ hα)
    (fpBad.curveFun 3 24) := by native_decide

/-! ## Hand-written darts tables -/

/-- A table `l` (dart number ↦ dart number) as a function on `Fin m`. -/
def tableFun (m : ℕ) (l : List ℕ) : Fin m → Fin m := finFun m (fun i => l.getD i 0)

/-- A table of curve labels as a function to `Fin n`. -/
def labelFun (n m : ℕ) [NeZero n] (l : List ℕ) : Fin m → Fin n := fun a => Fin.ofNat n (l.getD a 0)

/-! ## Axiom 5: two closed curves with one label -/

def σ5 : List ℕ :=
  [12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18, 1, 0, 2, 3, 9, 8, 10, 11, 5, 4, 6, 7]
def α5 : List ℕ :=
  [3, 2, 1, 0, 7, 6, 5, 4, 11, 14, 13, 8, 15, 10, 9, 12, 19, 22, 21, 16, 23, 18, 17, 20]
def curve5 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]

theorem hσ5 : ∀ i, tableFun 24 σ5 (tableFun 24 σ5 (tableFun 24 σ5 (tableFun 24 σ5 i))) = i := by
  native_decide
theorem hα5 : ∀ i, tableFun 24 α5 (tableFun 24 α5 i) = i := by native_decide

/-- The map of `bad5`. -/
abbrev bad5σ : Equiv.Perm (Fin 24) := permOfPow4 _ hσ5
abbrev bad5α : Equiv.Perm (Fin 24) := permOfInvolution _ hα5
abbrev bad5curve : Fin 24 → Fin 3 := labelFun 3 24 curve5

/-- `bad5` satisfies every axiom except axiom 5 ... -/
theorem bad5_others :
    (∀ d, (orbitFinset bad5σ d).card = 4) ∧ (∀ d, bad5α d ≠ d) ∧ (∀ d, bad5α (bad5α d) = d) ∧
      (∀ d, bad5curve (bad5α d) = bad5curve d) ∧ (∀ d, bad5curve (bad5σ d) ≠ bad5curve d) ∧
      (∀ d, bad5curve (bad5σ (bad5σ d)) = bad5curve d) ∧
      (∀ c c' : Fin 3, c ≠ c' →
        (Finset.univ.filter (fun x : Orbit bad5σ =>
          crossingCurves bad5σ bad5curve x = {c, c'})).card = 2) ∧
      ((Fintype.card (Orbit bad5σ) : ℤ) - Fintype.card (Orbit bad5α) +
        Fintype.card (Orbit (bad5σ * bad5α)) = 2) := by
  native_decide

/-- ... and violates axiom 5 ... -/
theorem bad5_not_straight : ¬ ∀ d e, bad5curve d = bad5curve e →
    (straightPerm bad5σ bad5α).SameCycle d e ∨
      (straightPerm bad5σ bad5α).SameCycle d (bad5σ (bad5σ e)) := by
  native_decide

/-- ... so it is not an arrangement. -/
theorem bad5_not : ¬ IsArrangement 3 bad5σ bad5α bad5curve := by native_decide

/-! ## Axiom 6: two curves crossing four times -/

def σ6 : List ℕ := [8, 9, 11, 10, 12, 13, 15, 14, 1, 0, 2, 3, 5, 4, 6, 7]
def α6 : List ℕ := [3, 6, 5, 0, 7, 2, 1, 4, 11, 14, 13, 8, 15, 10, 9, 12]
def curve6 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]

theorem hσ6 : ∀ i, tableFun 16 σ6 (tableFun 16 σ6 (tableFun 16 σ6 (tableFun 16 σ6 i))) = i := by
  native_decide
theorem hα6 : ∀ i, tableFun 16 α6 (tableFun 16 α6 i) = i := by native_decide

/-- The map of `bad6`. -/
abbrev bad6σ : Equiv.Perm (Fin 16) := permOfPow4 _ hσ6
abbrev bad6α : Equiv.Perm (Fin 16) := permOfInvolution _ hα6
abbrev bad6curve : Fin 16 → Fin 2 := labelFun 2 16 curve6

/-- `bad6` satisfies every axiom except axiom 6 ... -/
theorem bad6_others :
    (∀ d, (orbitFinset bad6σ d).card = 4) ∧ (∀ d, bad6α d ≠ d) ∧ (∀ d, bad6α (bad6α d) = d) ∧
      (∀ d, bad6curve (bad6α d) = bad6curve d) ∧ (∀ d, bad6curve (bad6σ d) ≠ bad6curve d) ∧
      (∀ d, bad6curve (bad6σ (bad6σ d)) = bad6curve d) ∧
      (∀ d e, bad6curve d = bad6curve e →
        (straightPerm bad6σ bad6α).SameCycle d e ∨
          (straightPerm bad6σ bad6α).SameCycle d (bad6σ (bad6σ e))) ∧
      ((Fintype.card (Orbit bad6σ) : ℤ) - Fintype.card (Orbit bad6α) +
        Fintype.card (Orbit (bad6σ * bad6α)) = 2) := by
  native_decide

/-- ... and violates axiom 6 (the two curves cross four times) ... -/
theorem bad6_four : (Finset.univ.filter (fun x : Orbit bad6σ =>
    crossingCurves bad6σ bad6curve x = {0, 1})).card = 4 := by
  native_decide

/-- ... so it is not an arrangement. -/
theorem bad6_not : ¬ IsArrangement 2 bad6σ bad6α bad6curve := by native_decide

/-! ## `Describes` separates lines 6 and 8 of `all4.txt` -/

theorem not_describes_6_8 : ¬ All4.fp8.Describes All4.A6 := by native_decide
theorem not_describes_8_6 : ¬ All4.fp6.Describes All4.A8 := by native_decide

end Pca.Instances.Negative
