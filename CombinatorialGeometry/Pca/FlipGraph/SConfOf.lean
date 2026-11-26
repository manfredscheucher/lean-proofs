/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): an arrangement as a sweep configuration

`sconfOf A C s b y hy`: the arrangement `A` itself as a sweep configuration (`Pca/Sweep/Conf.lean`)
with sweep curve `C`, upper side the cells with `s = b` (`s` a side function of `C`) and the
∞-arc the segment of `α y` (`y` a dart of `C` on the upper side). Same construction as in
`Pca/Sweep/Instance.lean`; it gives access to the Jordan facts of `Pca/Sweep/Jordan.lean`
(`upper_arc`: the part of a curve on one side of `C` is one arc).
-/
import Pca.FlipGraph.Basic
import Pca.Sweep.Jordan

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The arrangement as a sweep configuration (upper side: `s = b`). -/
def sconfOf (A : Arrangement n D) (C : Fin n) (s : A.Cell → ZMod 2) (hs : A.IsSide C s)
    (b : ZMod 2) (y : D) (hy : A.curve y = C) (hyb : s (A.cellOf y) = b) : Sweep.SConf n D where
  σ := A.σ
  α := A.α
  curve := A.curve
  S := C
  isSConf :=
    { card_crossing := A.isArrangement.card_crossing, α_ne := A.isArrangement.α_ne
      α_α := A.isArrangement.α_α, curve_α := A.isArrangement.curve_α
      curve_σ := A.isArrangement.curve_σ, curve_σσ := A.isArrangement.curve_σσ
      straight := A.isArrangement.straight
      two_int := fun c c' h => (A.isArrangement.intersecting c c' h).le
      connected := fun d e => A.connected d e
      euler := fun _ => A.isArrangement.euler
      S_mem := fun _ => ⟨y, hy⟩ }
  side := fun f => s f + b + 1
  isSide := by
    intro d
    show s (A.cellOf d) + b + 1 + (s (A.cellOf (A.α d)) + b + 1) = _
    rw [← hs d]
    have key : ∀ u v c : ZMod 2, u + c + 1 + (v + c + 1) = u + v := by decide
    exact key _ _ b
  infStart := some (A.α y)
  infLen := 0
  infStart_isSome := fun _ => rfl
  infLen_le := fun _ _ => Nat.zero_le _
  infArc_sweep := by
    intro d hd
    simp only [Sweep.arcOf, Option.elim, zero_add, range_one, image_singleton, pow_zero,
      Perm.one_apply, mem_singleton] at hd
    subst hd
    refine ⟨by rw [A.isArrangement.curve_α]; exact hy, ?_⟩
    show s (A.cellOf (A.α (A.α y))) + b + 1 = 1
    rw [A.isArrangement.α_α, hyb]
    have key : ∀ c : ZMod 2, c + c + 1 = 1 := by decide
    exact key b

theorem sconfOf_above {A : Arrangement n D} {C : Fin n} {s : A.Cell → ZMod 2} {hs : A.IsSide C s}
    {b : ZMod 2} {y : D} {hy : A.curve y = C} {hyb : s (A.cellOf y) = b} {d : D} :
    (sconfOf A C s hs b y hy hyb).Above d ↔ A.curve d ≠ C ∧ s (A.cellOf d) = b := by
  have key : ∀ u c : ZMod 2, u + c + 1 = 1 ↔ u = c := by decide
  exact and_congr Iff.rfl (key _ _)

theorem sconfOf_straight {A : Arrangement n D} {C : Fin n} {s : A.Cell → ZMod 2}
    {hs : A.IsSide C s} {b : ZMod 2} {y : D} {hy : A.curve y = C} {hyb : s (A.cellOf y) = b} :
    (sconfOf A C s hs b y hy hyb).straight = A.straight := rfl

end Pca.FlipGraph
