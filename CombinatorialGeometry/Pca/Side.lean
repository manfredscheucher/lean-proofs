/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Sides of a pseudocircle (milestone 7)

`IsSide C s` (new core definition): `s : Cell → ZMod 2` is a side function of the pseudocircle
`C`, i.e. `s (cellOf y) + s (cellOf (α y)) = [curve y = C]` for every dart `y`. Such a function
exists (`exists_side`, the combinatorial Jordan theorem of `Pca/Jordan.lean`), and it is unique up
to the swap of the two sides (`IsSide.eq_or_eq_add_one`). So the two **sides** of `C`, the sets
`{f | s f = 0}` and `{f | s f = 1}`, do not depend on the choice of `s`.

Further facts:

* `Arrangement.two_le_n`: every model has `n ≥ 2`,
* `Arrangement.exists_dart_on_side`: on each side of `C` there is a cell with a side on `C`,
* `Arrangement.side_straight`: walking straight along a curve `C' ≠ C`, the side of `C` changes
  exactly at the crossings with `C`,
* `Arrangement.not_sameCycle_straight_σσ`: the two directions of a curve are different straight
  walks (stated in `doc/pca/model.md`, axiom 5, proved here).
-/
import Pca.Jordan

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- `s` is a **side function** of the pseudocircle `C`: it changes exactly across the segments
of `C`. The two sides of `C` are `{f | s f = 0}` and `{f | s f = 1}`. -/
def IsSide (C : Fin n) (s : A.Cell → ZMod 2) : Prop :=
  ∀ y, s (A.cellOf y) + s (A.cellOf (A.α y)) = if A.curve y = C then 1 else 0

instance (C : Fin n) (s : A.Cell → ZMod 2) : Decidable (A.IsSide C s) := by
  unfold IsSide; infer_instance

variable {A}

theorem exists_isSide (C : Fin n) : ∃ s, A.IsSide C s := A.exists_side C

/-- The complement of a side function is a side function. -/
theorem IsSide.add_one {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) :
    A.IsSide C (fun f => s f + 1) := by
  intro y
  have h : ∀ a b : ZMod 2, a + 1 + (b + 1) = a + b := by decide
  show s (A.cellOf y) + 1 + (s (A.cellOf (A.α y)) + 1) = _
  rw [h]; exact hs y

/-- A side function is unique up to swapping the two sides. -/
theorem IsSide.eq_or_eq_add_one {C : Fin n} {s s' : A.Cell → ZMod 2} (hs : A.IsSide C s)
    (hs' : A.IsSide C s') : s' = s ∨ s' = fun f => s f + 1 := by
  set g : A.Cell → ZMod 2 := fun f => s' f + s f with hg
  have hker : g ∈ LinearMap.ker A.cellBdry := by
    rw [LinearMap.mem_ker]
    funext e
    obtain ⟨y, rfl⟩ := e.exists_mk
    change A.cellBdry g (A.segmentOf y) = 0
    rw [cellBdry_segmentOf, hg]
    have h1 := hs y
    have h2 := hs' y
    calc s' (A.cellOf y) + s (A.cellOf y) + (s' (A.cellOf (A.α y)) + s (A.cellOf (A.α y)))
        = (s' (A.cellOf y) + s' (A.cellOf (A.α y))) + (s (A.cellOf y) + s (A.cellOf (A.α y))) :=
          by ring
      _ = 0 := by rw [h1, h2, zmod2_add_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (A.ker_cellBdry_le hker)
  have key : ∀ f, s' f = s f + c := fun f => by
    have := congrFun hc f
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, hg] at this
    rw [this, add_comm (s' f), ← add_assoc, zmod2_add_self, zero_add]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
  · left; funext f; rw [key, add_zero]
  · right; funext f; rw [key]

/-- Every model has at least two curves (no darts would contradict Euler). -/
theorem two_le_n (A : Arrangement n D) : 2 ≤ n := by
  rcases isEmpty_or_nonempty D with hD | ⟨⟨y⟩⟩
  · exfalso
    have he := A.isArrangement.euler
    have h1 : Fintype.card (Orbit A.σ) = 0 :=
      Fintype.card_eq_zero_iff.2 ⟨fun x => (IsEmpty.false x.exists_mk.choose).elim⟩
    have h2 : Fintype.card (Orbit A.α) = 0 :=
      Fintype.card_eq_zero_iff.2 ⟨fun x => (IsEmpty.false x.exists_mk.choose).elim⟩
    have h3 : Fintype.card (Orbit (A.σ * A.α)) = 0 :=
      Fintype.card_eq_zero_iff.2 ⟨fun x => (IsEmpty.false x.exists_mk.choose).elim⟩
    rw [h1, h2, h3] at he
    norm_num at he
  · have h := A.isArrangement.curve_σ y
    by_contra hn
    exact h (Fin.ext (by have := (A.curve y).isLt; have := (A.curve (A.σ y)).isLt; omega))

/-- Every pseudocircle carries a dart. -/
theorem exists_dart_on (C : Fin n) : ∃ y, A.curve y = C := by
  have h := A.card_darts_on C
  have hn := A.two_le_n
  obtain ⟨y, hy⟩ := card_pos.1 (show 0 < (univ.filter (fun e => A.curve e = C)).card by
    rw [h]; omega)
  exact ⟨y, (mem_filter.1 hy).2⟩

/-- On each side of `C` there is a cell with a side on `C`. -/
theorem exists_dart_on_side {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) (b : ZMod 2) :
    ∃ y, A.curve y = C ∧ s (A.cellOf y) = b := by
  obtain ⟨y, hy⟩ := A.exists_dart_on C
  by_cases hb : s (A.cellOf y) = b
  · exact ⟨y, hy, hb⟩
  · refine ⟨A.α y, by rw [curve_α, hy], ?_⟩
    have h := hs y
    rw [if_pos hy] at h
    have h' := zmod2_eq_add_of_add_eq h
    rw [h']
    have hz : ∀ a b : ZMod 2, ¬ a = b → a + 1 = b := by decide
    exact hz _ _ hb

/-- Walking straight along a curve other than `C`, the side of `C` changes exactly at the
crossings with `C`: the crossing at the end of `y` lies on `C` iff `curve (σ (α y)) = C`. -/
theorem side_straight {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {y : D}
    (hy : A.curve y ≠ C) :
    s (A.cellOf (A.straight y)) =
      s (A.cellOf y) + if A.curve (A.σ (A.α y)) = C then 1 else 0 := by
  rw [straight_apply, A.side_σσ hs, curve_α, if_neg hy, add_zero]
  have h := hs y
  rw [if_neg hy] at h
  rw [zmod2_eq_add_of_add_eq h, add_zero]

/-- The crossing at the end of a dart `y` with `curve y ≠ C` lies on `C` iff
`curve (σ (α y)) = C`. -/
theorem mem_curves_end_iff {C : Fin n} {y : D} (hy : A.curve y ≠ C) :
    C ∈ Crossing.curves A (A.crossingOf (A.α y)) ↔ A.curve (A.σ (A.α y)) = C := by
  rw [curves_crossingOf, mem_insert, mem_singleton, curve_α]
  constructor
  · rintro (h | h)
    · exact absurd h.symm hy
    · exact h.symm
  · exact fun h => Or.inr h.symm

/-- The two directions of a curve are different straight walks: `σ² d` is not on the straight
walk of `d`. If `straight^i d = σ² d`, then with `e = straight^j d` and `i = 2j` (resp.
`i = 2j + 1`) one gets `σ² e = e` (resp. `α e = e`). -/
theorem not_sameCycle_straight_σσ (d : D) : ¬ A.straight.SameCycle d (A.σ (A.σ d)) := by
  set τ : Perm D := A.σ * A.σ with hτdef
  have hτ : ∀ y, τ y = A.σ (A.σ y) := fun y => rfl
  have hττ : τ * τ = 1 := by
    ext y; simp only [Perm.mul_apply, hτ, A.σ_σ_σ_σ, Perm.one_apply]
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hconj : τ * A.straight * τ⁻¹ = A.straight⁻¹ := by
    rw [hτinv]
    ext y
    rw [Perm.mul_apply, Perm.mul_apply, hτ, hτ, straight_apply, A.σ_σ_σ_σ, eq_comm,
      Perm.inv_eq_iff_eq, straight_apply, α_α, A.σ_σ_σ_σ]
  have hcomm : ∀ j : ℤ, ∀ y, τ ((A.straight ^ j) y) = (A.straight ^ (-j)) (τ y) := by
    intro j y
    have h1 : (τ * A.straight * τ⁻¹) ^ j = τ * A.straight ^ j * τ⁻¹ := conj_zpow
    rw [hconj, inv_zpow', hτinv] at h1
    have := congrArg (fun p : Perm D => p (τ y)) h1
    simp only [Perm.mul_apply] at this
    rw [this, show τ (τ y) = y by rw [← Perm.mul_apply, hττ, Perm.one_apply]]
  rintro ⟨i, hi⟩
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · -- `i = 2j`: `e = straight^j d` is fixed by `σ²`
    apply A.σ_σ_ne ((A.straight ^ j) d)
    rw [← hτ, hcomm, show τ d = (A.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add, hj]
    congr 2; ring
  · -- `i = 2j + 1`: `τ e = straight e`, so `α e = e`
    apply A.isArrangement.α_ne ((A.straight ^ j) d)
    have h1 : τ ((A.straight ^ j) d) = A.straight ((A.straight ^ j) d) := by
      rw [hcomm, show τ d = (A.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add,
        ← Perm.mul_apply, ← zpow_one_add, hj]
      congr 2; ring
    have h2 : A.straight ((A.straight ^ j) d) = τ (A.α ((A.straight ^ j) d)) := rfl
    rw [h2] at h1
    exact (τ.injective h1).symm

end Pca.Arrangement
