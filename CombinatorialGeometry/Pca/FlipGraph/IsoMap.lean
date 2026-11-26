/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): dart bijections commuting with `σ` and `α`

A bijection `e` of the darts of `A` and `A'` with `e ∘ σ = σ' ∘ e` and `e ∘ α = α' ∘ e` commutes
with every permutation built from `σ` and `α` (`φ`, `straight`), maps cells to cells
(`cellMap`), side functions to side functions, triangles to triangles, and commutes with the
triangle flip (`flipα_map`, `flipG'_map`).
-/
import Pca.FlipGraph.Basic

open Equiv Finset

namespace Pca.FlipGraph

universe u v

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D] {D' : Type v} [Fintype D']
  [DecidableEq D']

open Arrangement

/-- Conjugate permutations have corresponding cycles. -/
theorem sameCycle_map {f : Perm D} {f' : Perm D'} (e : D ≃ D') (h : ∀ x, e (f x) = f' (e x))
    {a b : D} (hab : f.SameCycle a b) : f'.SameCycle (e a) (e b) := by
  obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ j : ℕ, e ((f ^ j) a) = (f' ^ j) (e a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]
  exact ⟨k, by rw [zpow_natCast, ← hpow, hk]⟩

theorem sameCycle_map_iff {f : Perm D} {f' : Perm D'} (e : D ≃ D') (h : ∀ x, e (f x) = f' (e x))
    {a b : D} : f'.SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  refine ⟨fun hab => ?_, sameCycle_map e h⟩
  have h' : ∀ x, e.symm (f' x) = f (e.symm x) := fun x => by
    apply e.injective; rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]
  have := sameCycle_map e.symm h' hab
  simpa using this

variable {A : Arrangement n D} {A' : Arrangement n D'} (e : D ≃ D')
  (hσ : ∀ d, e (A.σ d) = A'.σ (e d)) (hα : ∀ d, e (A.α d) = A'.α (e d))

include hσ hα

theorem map_φ (d : D) : e (A.φ d) = A'.φ (e d) := by
  rw [φ_apply, φ_apply, hσ, hα]

theorem map_straight (d : D) : e (A.straight d) = A'.straight (e d) := by
  rw [straight_apply, straight_apply, hσ, hσ, hα]

theorem map_straight_symm (d : D) : e (A.straight.symm d) = A'.straight.symm (e d) := by
  apply A'.straight.injective
  rw [Equiv.apply_symm_apply, ← map_straight e hσ hα, Equiv.apply_symm_apply]

theorem map_cellOf_eq_iff {a b : D} : A'.cellOf (e a) = A'.cellOf (e b) ↔ A.cellOf a = A.cellOf b := by
  rw [cellOf_eq_iff, cellOf_eq_iff]
  exact sameCycle_map_iff e (map_φ e hσ hα)

omit hσ hα in
/-- The cell bijection induced by `e`. -/
def cellMap (h : ∀ x, e (A.φ x) = A'.φ (e x)) : A.Cell → A'.Cell :=
  Quotient.lift (fun d => A'.cellOf (e d)) (fun a b hab => by
    change A'.cellOf (e a) = A'.cellOf (e b)
    rw [cellOf_eq_iff]; exact sameCycle_map e h hab)

theorem cellMap_cellOf (d : D) : cellMap e (map_φ e hσ hα) (A.cellOf d) = A'.cellOf (e d) := rfl

theorem cellMap_injective : Function.Injective (cellMap e (map_φ e hσ hα)) := by
  intro f g h
  obtain ⟨a, rfl⟩ := f.exists_mk
  obtain ⟨b, rfl⟩ := g.exists_mk
  exact (map_cellOf_eq_iff e hσ hα).1 h

theorem darts_cellOf_map (d : D) : (A'.cellOf (e d)).darts = (A.cellOf d).darts.map e.toEmbedding := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [mem_map, Equiv.coe_toEmbedding, Orbit.mem_darts, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right]
  exact map_cellOf_eq_iff e hσ hα

theorem size_cellOf_map (d : D) : (A'.cellOf (e d)).size = (A.cellOf d).size := by
  unfold Orbit.size
  rw [darts_cellOf_map e hσ hα, card_map]

theorem isTriangle_map {d : D} (hT : A.IsTriangle (A.cellOf d)) :
    A'.IsTriangle (A'.cellOf (e d)) := by
  unfold IsTriangle IsKCell; rw [size_cellOf_map e hσ hα]; exact hT

theorem mem_sideDarts_map {d y : D} : e y ∈ A'.sideDarts (e d) ↔ y ∈ A.sideDarts d := by
  rw [mem_sideDarts, mem_sideDarts, ← hα, map_cellOf_eq_iff e hσ hα, map_cellOf_eq_iff e hσ hα]

theorem flipρ_map {d : D} (hT : A.IsTriangle (A.cellOf d)) (y : D) :
    e (flipρ hT y) = flipρ (isTriangle_map e hσ hα hT) (e y) := by
  rw [flipρ_apply, flipρ_apply, swapAlong, swapAlong]
  by_cases h1 : y ∈ A.sideDarts d
  · rw [if_pos h1, if_pos ((mem_sideDarts_map e hσ hα).2 h1)]; exact map_straight e hσ hα y
  · rw [if_neg h1, if_neg (fun h => h1 ((mem_sideDarts_map e hσ hα).1 h))]
    have h3 : A'.straight.symm (e y) ∈ A'.sideDarts (e d) ↔ A.straight.symm y ∈ A.sideDarts d := by
      rw [← map_straight_symm e hσ hα]; exact mem_sideDarts_map e hσ hα
    by_cases h2 : A.straight.symm y ∈ A.sideDarts d
    · rw [if_pos h2, if_pos (h3.2 h2)]
      exact map_straight_symm e hσ hα y
    · rw [if_neg h2, if_neg (fun h => h2 (h3.1 h))]

theorem flipα_map {d : D} (hT : A.IsTriangle (A.cellOf d)) (y : D) :
    e (flipα hT y) = flipα (isTriangle_map e hσ hα hT) (e y) := by
  rw [flipα_apply, flipα_apply, flipρ_map e hσ hα, hα, flipρ_map e hσ hα]

theorem flipG'_map (d y : D) : e (flipG' A d y) = flipG' A' (e d) (e y) := by
  unfold flipG'
  simp only [← hσ, ← hα, ← map_φ e hσ hα, map_cellOf_eq_iff e hσ hα]
  split_ifs <;> simp only [hσ, hα, map_φ e hσ hα]

end Pca.FlipGraph
