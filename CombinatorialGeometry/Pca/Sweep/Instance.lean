/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: the start configuration (package Q)

SH p. 325: "To sweep a sphere with a closed curve `c`, simply find a point that lies only on `c` and
remove this point from the plane. Sweeping this punctured sphere is equivalent to sweeping the
Euclidean plane with a bi-infinite curve."

Graph language: for an arrangement `A`, a pseudocircle `C`, a side function `s` of `C` and a dart
`y` on `C`, the sweep configuration is `A` itself (same darts, `σ`, `α`, `curve`; `S = C`), with the
side of `cellOf y` as the upper side and the ∞-arc the single segment of `y` (the puncture point
lies on that segment; `cellOf y` is SH's unbounded face above `c`). The axioms: 1-5 and Euler are
those of `A`, two-intersection follows from "intersecting", connectivity is `Arrangement.connected`.

Every curve `≠ C` crosses `C` twice, at vertices on the sweep (the arc has no inner crossing), so
no loop can be taken and the configuration is not finished (`n ≥ 2`). An empty hump or triangle is
a digon or triangle cell with a side on `C`, on the side of `cellOf y`, and `≠ cellOf y` (a digon
or triangle has only one side on `C`, and its side is a finite edge, not the segment of `y`).
-/
import Pca.Sweep.Main
import Pca.Side

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

open Pca.Arrangement in
/-- In a cell with at most three darts, two darts on the same curve are equal (consecutive darts
of a cell lie on different curves). -/
private theorem q_small_cell_curve {A : Pca.Arrangement n D} {x y : D}
    (hk : (A.cellOf x).size ≤ 3) (hxy : A.φ.SameCycle x y) (hc : A.curve y = A.curve x) :
    y = x := by
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  set p := period A.φ x with hp
  have hpk : p ≤ 3 := by rw [hp, ← A.size_cellOf]; exact hk
  have hp0 : 0 < p := period_pos _ _
  have hper : Function.IsPeriodicPt A.φ p x := iterate_period A.φ x
  have hmod : (A.φ ^ i) x = (A.φ^[i % p]) x := by
    rw [Perm.coe_pow]; exact (hper.iterate_mod_apply i).symm
  have hlt : i % p < p := Nat.mod_lt _ hp0
  rw [hmod] at hc ⊢
  generalize i % p = j at hc hlt ⊢
  have hj3 : j < 3 := by omega
  interval_cases j
  · rfl
  · exact absurd hc (A.curve_φ_ne x)
  · -- `p = 3`: `φ (φ² x) = x`
    have h3 : p = 3 := by omega
    have hx : A.φ (A.φ^[2] x) = x := by
      have := hper; rw [h3] at this; exact this
    exfalso
    apply A.curve_φ_ne (A.φ^[2] x)
    rw [hx, hc]

/-- The start configuration of the sweep of the side of `cellOf y`, and what its first move
gives. -/
theorem exists_ofSide (A : Pca.Arrangement n D) (C : Fin n) (s : A.Cell → ZMod 2)
    (hs : A.IsSide C s) (y : D) (hy : A.curve y = C) :
    ∃ Γ : SConf n D, ¬ Γ.Terminal ∧ ¬ Γ.CanTakeLoop ∧
      ∀ d, Γ.EmptyHumpAt d ∨ Γ.EmptyTriAt d →
        ∃ g : A.Cell, g ≠ A.cellOf y ∧ s g = s (A.cellOf y) ∧ (∃ e ∈ g.darts, A.curve e = C) ∧
          (A.IsDigon g ∨ A.IsTriangle g) := by
  classical
  set b := s (A.cellOf y) with hb
  -- the side function of `Γ`: `1` on the side of `cellOf y`
  let side : A.Cell → ZMod 2 := fun f => s f + b + 1
  have hside : ∀ f, side f = 1 ↔ s f = b := by
    intro f
    have key : ∀ u c : ZMod 2, u + c + 1 = 1 ↔ u = c := by decide
    exact key (s f) b
  have hyy : A.α (A.α y) = y := A.isArrangement.α_α y
  have hIA := A.isArrangement
  let Γ : SConf n D :=
    { σ := A.σ, α := A.α, curve := A.curve, S := C
      isSConf :=
        { card_crossing := hIA.card_crossing, α_ne := hIA.α_ne, α_α := hIA.α_α
          curve_α := hIA.curve_α, curve_σ := hIA.curve_σ, curve_σσ := hIA.curve_σσ
          straight := hIA.straight
          two_int := fun c c' h => (hIA.intersecting c c' h).le
          connected := fun d e => A.connected d e
          euler := fun _ => hIA.euler
          S_mem := fun _ => ⟨y, hy⟩ }
      side := side
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
        simp only [arcOf, Option.elim, zero_add, range_one, image_singleton, pow_zero,
          Perm.one_apply, mem_singleton] at hd
        subst hd
        refine ⟨by rw [hIA.curve_α]; exact hy, ?_⟩
        show side (A.cellOf (A.α (A.α y))) = 1
        rw [hyy, hside] }
  -- no crossing is inside the ∞-arc
  have hnoInf : ∀ x, ¬ Γ.IsInfVertex x := by
    rintro x ⟨z, -, i, hi, -⟩
    exact Nat.not_lt_zero _ hi
  -- every curve `≠ C` meets the sweep
  have hmeet : ∀ γ, γ ≠ C → Γ.MeetsSweep γ := by
    intro γ hγ
    have h2 := hIA.intersecting γ C hγ
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < _ by rw [h2]; norm_num)
    have hx' : crossingCurves A.σ A.curve x = {γ, C} := (mem_filter.1 hx).2
    refine ⟨x, ⟨?_, hnoInf x⟩, ?_⟩
    · show C ∈ crossingCurves A.σ A.curve x
      rw [hx']; simp
    · show γ ∈ crossingCurves A.σ A.curve x
      rw [hx']; simp
  refine ⟨Γ, ?_, ?_, ?_⟩
  · -- not finished: the curve of `φ y` is present and not a ray
    rintro ⟨-, hR⟩
    have hne : A.curve (A.φ y) ≠ C := by rw [← hy]; exact A.curve_φ_ne y
    have hpres : Γ.Present (A.curve (A.φ y)) := by
      refine ⟨hne, A.φ y, rfl, hne, ?_⟩
      show side (A.cellOf (A.φ y)) = 1
      rw [hside, A.cellOf_φ]
    obtain ⟨-, x, hx, -⟩ := hR _ hpres
    exact hnoInf x hx
  · -- no loop can be taken
    rintro ⟨d, e, -, -, he, hm⟩
    exact hm (hmeet _ he)
  · intro d hd
    have hfin : Γ.IsFinSeg d ∧ ((Γ.upperCell d).size = 2 ∨ (Γ.upperCell d).size = 3) := by
      rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr h2⟩
    obtain ⟨⟨⟨hdC, hup⟩, hdarc⟩, hsz⟩ := hfin
    have hdC' : A.curve d = C := hdC
    have hup' : s (A.cellOf (A.α d)) = b := (hside _).1 hup
    have hsz' : (A.cellOf (A.α d)).size = 2 ∨ (A.cellOf (A.α d)).size = 3 := hsz
    have hdne : d ≠ A.α y := by
      intro h
      apply hdarc
      show d ∈ arcOf A.σ A.α (some (A.α y)) 0
      simp [arcOf, h]
    refine ⟨A.cellOf (A.α d), ?_, hup', ⟨A.α d, A.mem_darts_cellOf_self _, ?_⟩, ?_⟩
    · intro hg
      have hsc : A.φ.SameCycle (A.α d) y := (A.cellOf_eq_iff).1 hg
      have := q_small_cell_curve (by omega) hsc (by rw [hy, hIA.curve_α, hdC'])
      apply hdne
      rw [this, hIA.α_α]
    · rw [hIA.curve_α]; exact hdC'
    · rcases hsz' with h | h
      · exact Or.inl h
      · exact Or.inr h

end Pca.Sweep
