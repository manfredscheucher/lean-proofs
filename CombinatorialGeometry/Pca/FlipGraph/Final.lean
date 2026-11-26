/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): FROS Theorems 3 and 4, and the sphere version

* `thm_main_cipa` (FROS Theorem 4): the triangle flip graph of intersecting cylindrical
  arrangements of `n` pseudocircles is connected: any two are joined by a sequence of flips through
  cylindrical arrangements, up to isomorphism.
* `thm_main_ipa` (FROS Theorem 3): the triangle flip graph of intersecting arrangements of `n`
  pseudocircles is connected.
* `sphere_connected`: the same on the sphere (no marked cell; any triangle may be flipped).

The flip graph is undirected (`flipStep_symm`), so "joined by a path up to isomorphism" is
connectivity of the flip graph on isomorphism classes.
-/
import Pca.FlipGraph.Thm3
import Pca.FlipGraph.Process

open Equiv Finset

namespace Pca.FlipGraph

universe u v

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D] {D' : Type v} [Fintype D']
  [DecidableEq D']

/-- Every cylindrical arrangement can be flipped (through cylindrical arrangements) to `𝒜_n^-`. -/
theorem exists_canon (M : Marked n D) (hc : M.Cylindrical) :
    ∃ N c, CylReach M N ∧ N.Canon c := by
  have hend : ∀ {M N : Marked n D}, M.Cylindrical → CylReach M N → N.Cylindrical := by
    intro M N hM h
    induction h with
    | refl => exact hM
    | tail _ hs _ => exact hs.2.2
  obtain ⟨y₀, hy₀⟩ := M.z.exists_mk
  obtain ⟨N₁, hr₁, hclear, hz⟩ := clear_first M hc hy₀
  have hc₁ := hend hc hr₁
  obtain ⟨c, hinv, hmark⟩ := order_of_first N₁ hc₁ _ hclear hz
  have key : ∀ k, 1 ≤ k → k ≤ n →
      ∃ N, CylReach M N ∧ N.Cylindrical ∧ N.CanonUpTo c k ∧ N.MarkOnFirst c := by
    intro k hk hkn
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · exact ⟨N₁, hr₁, hc₁, hinv, hmark⟩
      · obtain ⟨N, hN, hcN, hiN, hmN⟩ := ih hk' (by omega)
        obtain ⟨N', hN', hiN', hmN'⟩ := process_step N hcN c hk' (by omega) hiN hmN
        exact ⟨N', hN.trans hN', hend hcN hN', hiN', hmN'⟩
  have hn := M.A.two_le_n
  obtain ⟨N, hN, -, hi, hm⟩ := key n (by omega) le_rfl
  exact ⟨N, c, hN, hi, hm⟩

/-- **FROS Theorem 4** (`thm:main_cipa`): the triangle flip graph of intersecting cylindrical
arrangements of `n` pseudocircles is connected. -/
theorem thm_main_cipa (M₁ : Marked n D) (M₂ : Marked n D') (h₁ : M₁.Cylindrical)
    (h₂ : M₂.Cylindrical) : ∃ N, CylReach M₁ N ∧ IsIso N M₂ := by
  obtain ⟨N₁, c₁, hr₁, hN₁⟩ := exists_canon M₁ h₁
  obtain ⟨N₂, c₂, hr₂, hN₂⟩ := exists_canon M₂ h₂
  obtain ⟨N, hN, hi⟩ := (canon_iso hN₁ hN₂).cylReach (cylReach_symm hr₂)
  exact ⟨N, hr₁.trans hN, hi⟩

/-- **FROS Theorem 3** (`thm:main_ipa`): the triangle flip graph of intersecting arrangements of
`n` pseudocircles is connected. -/
theorem thm_main_ipa (M₁ : Marked n D) (M₂ : Marked n D') : ∃ N, Reach M₁ N ∧ IsIso N M₂ := by
  obtain ⟨N₁, hr₁, hc₁⟩ := reach_cylindrical M₁
  obtain ⟨N₂, hr₂, hc₂⟩ := reach_cylindrical M₂
  obtain ⟨N, hN, hi⟩ := thm_main_cipa N₁ N₂ hc₁ hc₂
  have hN' : Reach N₁ N := by
    clear hi
    induction hN with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact Relation.ReflTransGen.tail ih hs.1
  obtain ⟨N', hN'', hi'⟩ := hi.reach (reach_symm hr₂)
  exact ⟨N', hr₁.trans (hN'.trans hN''), hi'⟩

/-- **The sphere version**: on the sphere (no marked cell, every triangle may be flipped), any two
intersecting arrangements of `n` pseudocircles are joined by triangle flips up to isomorphism. -/
theorem sphere_connected (A₁ : Arrangement n D) (A₂ : Arrangement n D') :
    ∃ B, Relation.ReflTransGen SphereStep A₁ B ∧ SphereIso B A₂ := by
  obtain ⟨y₁, -⟩ := A₁.exists_dart_on ⟨0, by have := A₁.two_le_n; omega⟩
  obtain ⟨y₂, -⟩ := A₂.exists_dart_on ⟨0, by have := A₂.two_le_n; omega⟩
  obtain ⟨N, hN, ⟨I⟩⟩ := thm_main_ipa ⟨A₁, A₁.cellOf y₁⟩ ⟨A₂, A₂.cellOf y₂⟩
  refine ⟨N.A, ?_, I.e, I.π, I.map_σ, I.map_α, I.map_curve⟩
  have key : ∀ {M M' : Marked n D}, Reach M M' → Relation.ReflTransGen SphereStep M.A M'.A := by
    intro M M' h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨d, hT, -, rfl⟩ := hs
      exact ih.tail ⟨d, hT, rfl⟩
  exact key hN

end Pca.FlipGraph
