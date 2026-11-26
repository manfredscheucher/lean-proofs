/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Generic facts on maps: first returns, orbit counts, Euler bound

Used by the removal of curves in `Pca/Sweep/` and by the insertion count in `Pca/Great/`:

* `frPerm`: the first-return permutation of `f` on the subtype `K` (`isFR_frPerm`),
* `card_orbit_le_mul`: composing with an involution `R` merges at most `|supp R| / 2` orbits,
* `card_eq_two_mul_card_orbit`: a fixed-point-free involution has `|X| / 2` orbits,
* `euler_le_two`: `V - E + F ≤ 2` for every connected map (the argument of `Pca/Jordan.lean`).
-/
import Pca.Great.Map_Perm

open Equiv Finset Module

set_option linter.unusedSectionVars false

namespace Pca.MapFacts

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## The first-return permutation on a subtype -/

section FRSub

variable (f : Perm X) (K : X → Prop) [DecidablePred K]

theorem exists_return (x : {x // K x}) : ∃ k, 0 < k ∧ K ((f ^ k) x.1) :=
  ⟨orderOf f, orderOf_pos f, by rw [pow_orderOf_eq_one]; exact x.2⟩

noncomputable def frTime (x : {x // K x}) : ℕ := Nat.find (exists_return f K x)

noncomputable def frFun (x : {x // K x}) : {x // K x} :=
  ⟨(f ^ frTime f K x) x.1, (Nat.find_spec (exists_return f K x)).2⟩

theorem frFun_injective : Function.Injective (frFun f K) := by
  have key : ∀ x y : {x // K x}, frTime f K x < frTime f K y →
      (f ^ frTime f K x) x.1 = (f ^ frTime f K y) y.1 → False := by
    intro x y hlt he
    have h1 : x.1 = (f ^ (frTime f K y - frTime f K x)) y.1 := by
      rw [← pow_inv_pow_apply f hlt.le, ← he]; exact (Perm.inv_eq_iff_eq.mpr rfl).symm
    have := Nat.find_min (exists_return f K y) (m := frTime f K y - frTime f K x) (by
      unfold frTime at hlt ⊢; have := (Nat.find_spec (exists_return f K x)).1; omega)
    exact this ⟨by omega, h1 ▸ x.2⟩
  intro x y hxy
  have he : (f ^ frTime f K x) x.1 = (f ^ frTime f K y) y.1 := congrArg Subtype.val hxy
  rcases lt_trichotomy (frTime f K x) (frTime f K y) with hlt | heq | hgt
  · exact (key x y hlt he).elim
  · rw [heq] at he; exact Subtype.ext ((f ^ frTime f K y).injective he)
  · exact (key y x hgt he.symm).elim

noncomputable def frPerm : Perm {x // K x} :=
  Equiv.ofBijective (frFun f K) (Finite.injective_iff_bijective.1 (frFun_injective f K))

theorem isFR_frPerm : IsFR f (frPerm f K) Subtype.val K := by
  intro x
  refine ⟨frTime f K x, (Nat.find_spec (exists_return f K x)).1, rfl, fun j hj0 hj => ?_⟩
  exact fun hK => Nat.find_min (exists_return f K x) hj ⟨hj0, hK⟩

end FRSub

/-! ## Composing with an involution -/

section Swap

/-- If the `g`-orbit of `x` avoids `a` and `b`, then `g * swap a b` agrees with `g` on it. -/
theorem pow_mul_swap_apply (g : Perm X) (a b x : X) (hx : ∀ i : ℕ, (g ^ i) x ≠ a ∧ (g ^ i) x ≠ b)
    (i : ℕ) : ((g * swap a b) ^ i) x = (g ^ i) x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply, swap_apply_of_ne_of_ne (hx i).1 (hx i).2,
      ← Perm.mul_apply, ← pow_succ']

theorem card_orbit_le_mul_swap (g : Perm X) (a b : X) :
    Fintype.card (Orbit g) ≤ Fintype.card (Orbit (g * swap a b)) + 1 := by
  set h := g * swap a b
  have avoid : ∀ x, ¬ g.SameCycle x a → ¬ g.SameCycle x b →
      ∀ i : ℕ, (g ^ i) x ≠ a ∧ (g ^ i) x ≠ b := fun x ha hb i =>
    ⟨fun he => ha (he ▸ sameCycle_of_pow g x i), fun he => hb (he ▸ sameCycle_of_pow g x i)⟩
  have same : ∀ x y, ¬ g.SameCycle x a → ¬ g.SameCycle x b →
      (h.SameCycle x y ↔ g.SameCycle x y) := by
    intro x y ha hb
    rw [sameCycle_iff_nat, sameCycle_iff_nat]
    simp only [h, pow_mul_swap_apply g a b x (avoid x ha hb)]
  classical
  let Ψ0 : X → Orbit h := fun x =>
    if g.SameCycle x a ∨ g.SameCycle x b then Orbit.mk h b else Orbit.mk h x
  have hΨ0 : ∀ x y, g.SameCycle x y → Ψ0 x = Ψ0 y := by
    intro x y hxy
    simp only [Ψ0]
    by_cases hc : g.SameCycle x a ∨ g.SameCycle x b
    · have hc' : g.SameCycle y a ∨ g.SameCycle y b :=
        hc.imp (fun h1 => hxy.symm.trans h1) (fun h1 => hxy.symm.trans h1)
      rw [if_pos hc, if_pos hc']
    · have hc' : ¬ (g.SameCycle y a ∨ g.SameCycle y b) := fun h' =>
        hc (h'.imp (fun h1 => hxy.trans h1) (fun h1 => hxy.trans h1))
      rw [if_neg hc, if_neg hc']
      push Not at hc
      exact Orbit.mk_eq_mk.2 ((same x y hc.1 hc.2).2 hxy)
  let Ψ : Orbit g → Orbit h := Quotient.lift Ψ0 hΨ0
  have hΨ : ∀ x, Ψ (Orbit.mk g x) = Ψ0 x := fun _ => rfl
  have hinj : Set.InjOn Ψ ↑(univ.erase (Orbit.mk g a)) := by
    intro o1 ho1 o2 ho2 he
    obtain ⟨x, rfl⟩ := o1.exists_mk
    obtain ⟨y, rfl⟩ := o2.exists_mk
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and, Orbit.mk_eq_mk] at ho1 ho2
    rw [hΨ, hΨ] at he
    simp only [Ψ0] at he
    rw [Orbit.mk_eq_mk]
    by_cases hx : g.SameCycle x a ∨ g.SameCycle x b <;>
      by_cases hy : g.SameCycle y a ∨ g.SameCycle y b
    · have hxb := hx.resolve_left ho1
      have hyb := hy.resolve_left ho2
      exact hxb.trans hyb.symm
    · rw [if_pos hx, if_neg hy, Orbit.mk_eq_mk] at he
      push Not at hy
      exact absurd ((same y b hy.1 hy.2).1 he.symm).symm (fun h' => hy.2 h'.symm)
    · rw [if_neg hx, if_pos hy, Orbit.mk_eq_mk] at he
      push Not at hx
      exact absurd ((same x b hx.1 hx.2).1 he) (fun h' => hx.2 h')
    · rw [if_neg hx, if_neg hy, Orbit.mk_eq_mk] at he
      push Not at hx
      exact (same x y hx.1 hx.2).1 he
  have := card_le_card_of_injOn Ψ (fun _ _ => mem_coe.2 (mem_univ _)) hinj
  rw [card_erase_of_mem (mem_univ _), card_univ, card_univ] at this
  omega

/-- Composing with an involution `R` merges at most `|supp R| / 2` orbits. -/
theorem card_orbit_le_mul (f : Perm X) :
    ∀ (R : Perm X), (∀ x, R (R x) = x) →
      2 * Fintype.card (Orbit f) ≤
        2 * Fintype.card (Orbit (f * R)) + (univ.filter (fun x => R x ≠ x)).card := by
  intro R
  induction hn : (univ.filter (fun x => R x ≠ x)).card using Nat.strong_induction_on
    generalizing R with
  | _ n ih =>
  intro hR
  rcases (univ.filter (fun x => R x ≠ x)).eq_empty_or_nonempty with he | ⟨a, ha⟩
  · have : R = 1 := by
      ext x
      by_contra hx
      have : x ∈ univ.filter (fun x => R x ≠ x) := mem_filter.2 ⟨mem_univ _, hx⟩
      rw [he] at this; exact absurd this (Finset.notMem_empty _)
    subst this; simp
  · have hab : R a ≠ a := (mem_filter.1 ha).2
    set b := R a
    have hRb : R b = a := hR a
    set R' := R * swap a b
    have hR'a : R' a = a := by simp [R', swap_apply_left, hRb]
    have hR'b : R' b = b := by
      show R (swap a b b) = b
      rw [swap_apply_right]
    have hR'x : ∀ x, x ≠ a → x ≠ b → R' x = R x := fun x h1 h2 => by
      simp [R', swap_apply_of_ne_of_ne h1 h2]
    have hR' : ∀ x, R' (R' x) = x := by
      intro x
      by_cases h1 : x = a
      · subst h1; rw [hR'a, hR'a]
      by_cases h2 : x = b
      · subst h2; rw [hR'b, hR'b]
      have h3 : R x ≠ a := fun he => h2 (by rw [← hR x, he])
      have h4 : R x ≠ b := fun he => h1 (by rw [← hR x, he, hRb])
      rw [hR'x x h1 h2, hR'x _ h3 h4, hR]
    have hfilter : univ.filter (fun x => R' x ≠ x) =
        ((univ.filter (fun x => R x ≠ x)).erase a).erase b := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      constructor
      · intro hx
        have h1 : x ≠ a := fun he => hx (he ▸ hR'a)
        have h2 : x ≠ b := fun he => hx (he ▸ hR'b)
        exact ⟨h2, h1, by rwa [hR'x x h1 h2] at hx⟩
      · rintro ⟨h2, h1, hx⟩
        rwa [hR'x x h1 h2]
    have hbmem : b ∈ (univ.filter (fun x => R x ≠ x)).erase a :=
      mem_erase.2 ⟨hab, mem_filter.2 ⟨mem_univ _, by rw [hRb]; exact hab.symm⟩⟩
    have hcard : (univ.filter (fun x => R' x ≠ x)).card = n - 2 := by
      rw [hfilter, card_erase_of_mem hbmem, card_erase_of_mem ha, hn]; omega
    have hn2 : 2 ≤ n := by
      have := card_erase_of_mem hbmem
      have := card_erase_of_mem ha
      have : 0 < (((univ.filter (fun x => R x ≠ x)).erase a)).card := card_pos.2 ⟨b, hbmem⟩
      omega
    have h1 := ih (n - 2) (by omega) R' hcard hR'
    have h2 := card_orbit_le_mul_swap (f * R') a b
    have hRR : f * R' * swap a b = f * R := by
      simp only [R', mul_assoc, swap_mul_self, mul_one]
    rw [hRR] at h2
    omega

end Swap

/-! ## Fixed-point-free involutions -/

theorem orbitFinset_inv (α : Perm X) (hαα : ∀ x, α (α x) = x) (y : X) :
    orbitFinset α y = {y, α y} := by
  ext z
  rw [mem_orbitFinset, mem_insert, mem_singleton, sameCycle_iff_nat]
  constructor
  · rintro ⟨i, rfl⟩
    induction i with
    | zero => exact Or.inl rfl
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h, hαα]; exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem card_eq_two_mul_card_orbit (α : Perm X) (hαα : ∀ x, α (α x) = x)
    (hαne : ∀ x, α x ≠ x) : Fintype.card X = 2 * Fintype.card (Orbit α) := by
  rw [card_eq_sum_size α]
  have : ∀ o : Orbit α, o.size = 2 := by
    intro o
    obtain ⟨y, rfl⟩ := o.exists_mk
    rw [Orbit.size, Orbit.darts_mk, orbitFinset_inv α hαα, card_pair (hαne y).symm]
  rw [sum_congr rfl fun o _ => this o, sum_const, card_univ, smul_eq_mul, mul_comm]

/-! ## The Euler bound for connected maps -/

section Euler

variable (σ α : Perm X)

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

theorem zmod2_trans (p q r : ZMod 2) : p + r = p + q + (q + r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> decide

theorem map_orbitFinset_self (y : X) :
    (orbitFinset σ y).map σ.toEmbedding = orbitFinset σ y := by
  ext z
  simp only [mem_map, mem_orbitFinset, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw.trans (sameCycle_of_pow σ w 1)
  · intro hz
    exact ⟨σ.symm z, Perm.sameCycle_symm_apply_right.2 hz, σ.apply_symm_apply z⟩

/-- `L`: a function on faces gives on each edge the sum over its two sides. -/
def cellBdry : (Orbit (σ * α) → ZMod 2) →ₗ[ZMod 2] (Orbit α → ZMod 2) where
  toFun g s := ∑ y ∈ s.darts, g (Orbit.mk (σ * α) y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

/-- `B`: a function on edges gives on each vertex the sum over its darts. -/
def segBdry : (Orbit α → ZMod 2) →ₗ[ZMod 2] (Orbit σ → ZMod 2) where
  toFun h x := ∑ y ∈ x.darts, h (Orbit.mk α y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

def sumAll : (Orbit σ → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ x, v x
  map_add' v w := by simp [sum_add_distrib]
  map_smul' c v := by simp [mul_sum]

variable {σ α} (hαα : ∀ x, α (α x) = x) (hαne : ∀ x, α x ≠ x)
  (hconn : ∀ x y, Relation.EqvGen (fun a b => b = σ a ∨ b = α a) x y)
include hαα hαne hconn

theorem cellBdry_mk (g : Orbit (σ * α) → ZMod 2) (y : X) :
    cellBdry σ α g (Orbit.mk α y) = g (Orbit.mk (σ * α) y) + g (Orbit.mk (σ * α) (α y)) := by
  show ∑ z ∈ (Orbit.mk α y).darts, g (Orbit.mk (σ * α) z) = _
  rw [Orbit.darts_mk, orbitFinset_inv α hαα, sum_pair (hαne y).symm]

theorem mk_φ_α (y : X) : Orbit.mk (σ * α) (α y) = Orbit.mk (σ * α) (σ y) := by
  rw [Orbit.mk_eq_mk]
  have : (σ * α) (α y) = σ y := by rw [Perm.mul_apply, hαα]
  rw [← this]; exact sameCycle_of_pow _ _ 1

theorem segBdry_cellBdry (g : Orbit (σ * α) → ZMod 2) :
    segBdry σ α (cellBdry σ α g) = 0 := by
  funext x
  obtain ⟨y, rfl⟩ := x.exists_mk
  show ∑ z ∈ (Orbit.mk σ y).darts, cellBdry σ α g (Orbit.mk α z) = 0
  simp only [cellBdry_mk hαα hαne hconn, mk_φ_α hαα hαne hconn, sum_add_distrib]
  rw [Orbit.darts_mk]
  have := sum_map (orbitFinset σ y) σ.toEmbedding (fun z => g (Orbit.mk (σ * α) z))
  rw [map_orbitFinset_self] at this
  simp only [Equiv.toEmbedding_apply] at this
  rw [← this]
  exact zmod2_add_self _

theorem const_of_invariant {β : Type*} (G : X → β) (hσ : ∀ y, G (σ y) = G y)
    (hα : ∀ y, G (α y) = G y) (y z : X) : G y = G z := by
  induction hconn y z with
  | rel a b h => rcases h with rfl | rfl
                 · exact (hσ a).symm
                 · exact (hα a).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem finrank_ker_cellBdry_le : finrank (ZMod 2) (LinearMap.ker (cellBdry σ α)) ≤ 1 := by
  have hle : LinearMap.ker (cellBdry σ α) ≤ ZMod 2 ∙ (fun _ => 1) := by
    intro g hg
    rw [LinearMap.mem_ker] at hg
    have h : ∀ y, g (Orbit.mk (σ * α) (α y)) = g (Orbit.mk (σ * α) y) := fun y => by
      have := congrFun hg (Orbit.mk α y)
      rw [cellBdry_mk hαα hαne hconn, Pi.zero_apply] at this
      calc _ = g (Orbit.mk (σ * α) y) + (g (Orbit.mk (σ * α) y) +
              g (Orbit.mk (σ * α) (α y))) := by
                rw [← add_assoc, zmod2_add_self, zero_add]
        _ = _ := by rw [this, add_zero]
    rcases isEmpty_or_nonempty X with hD | ⟨⟨y0⟩⟩
    · have : g = 0 := funext fun f => by
        obtain ⟨y, -⟩ := f.exists_mk; exact (IsEmpty.false y).elim
      rw [this]; exact Submodule.zero_mem _
    · rw [Submodule.mem_span_singleton]
      refine ⟨g (Orbit.mk (σ * α) y0), funext fun f => ?_⟩
      obtain ⟨y, rfl⟩ := f.exists_mk
      have := const_of_invariant hαα hαne hconn (fun z => g (Orbit.mk (σ * α) z))
        (fun z => by rw [← mk_φ_α hαα hαne hconn, h]) h y0 y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact this
  refine (Submodule.finrank_mono hle).trans ?_
  refine (finrank_span_le_card ({fun _ => 1} : Set (Orbit (σ * α) → ZMod 2))).trans ?_
  simp

theorem segBdry_single (y : X) :
    segBdry σ α (Pi.single (Orbit.mk α y) 1) =
      Pi.single (Orbit.mk σ y) 1 + Pi.single (Orbit.mk σ (α y)) 1 := by
  funext x
  have hne : y ≠ α y := (hαne y).symm
  change ∑ z ∈ x.darts, (Pi.single (Orbit.mk α y) 1 : Orbit α → ZMod 2) (Orbit.mk α z) = _
  have hz : ∀ z, (Pi.single (Orbit.mk α y) 1 : Orbit α → ZMod 2) (Orbit.mk α z) =
      (if z = y then 1 else 0) + (if z = α y then 1 else 0) := by
    intro z
    have hs : Orbit.mk α z = Orbit.mk α y ↔ z = y ∨ z = α y := by
      rw [Orbit.mk_eq_mk, ← mem_orbitFinset, orbitFinset_inv α hαα, mem_insert, mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, hαα])
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, hαα])
    simp only [Pi.single_apply, hs]
    by_cases h1 : z = y
    · subst h1; simp [hne]
    · by_cases h2 : z = α y <;> simp [h1, h2, hαne y]
  rw [sum_congr rfl fun z _ => hz z, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    Pi.add_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  · by_cases h : x = Orbit.mk σ y
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]
  · by_cases h : x = Orbit.mk σ (α y)
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]

theorem single_add_single_mem (y z : X) :
    Pi.single (Orbit.mk σ y) (1 : ZMod 2) + Pi.single (Orbit.mk σ z) 1 ∈
      LinearMap.range (segBdry σ α) := by
  induction hconn y z with
  | rel a b h =>
    rcases h with rfl | rfl
    · rw [show Orbit.mk σ (σ a) = Orbit.mk σ a from
        (Orbit.mk_eq_mk.2 (sameCycle_of_pow σ a 1)).symm,
        ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      exact Submodule.zero_mem _
    · exact ⟨_, segBdry_single hαα hαne hconn a⟩
  | refl a =>
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact Submodule.zero_mem _
  | symm a b _ ih => rw [add_comm]; exact ih
  | trans a b c _ _ ih1 ih2 =>
    have := Submodule.add_mem _ ih1 ih2
    convert this using 1
    funext x
    simp only [Pi.add_apply]
    exact zmod2_trans _ _ _

theorem card_le_finrank_range_segBdry :
    Fintype.card (Orbit σ) ≤ finrank (ZMod 2) (LinearMap.range (segBdry σ α)) + 1 := by
  have hker : LinearMap.ker (sumAll σ) ≤ LinearMap.range (segBdry σ α) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    change ∑ x, v x = 0 at hv
    rcases isEmpty_or_nonempty X with hD | ⟨⟨y0⟩⟩
    · have : v = 0 := funext fun x => by
        obtain ⟨y, -⟩ := x.exists_mk; exact (IsEmpty.false y).elim
      rw [this]; exact Submodule.zero_mem _
    have hv' : v = ∑ x, v x • (Pi.single x (1 : ZMod 2) + Pi.single (Orbit.mk σ y0) 1) := by
      rw [sum_congr rfl fun x _ => smul_add (v x) _ _, sum_add_distrib, ← sum_smul, hv,
        zero_smul, add_zero]
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv']
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    obtain ⟨y, rfl⟩ := x.exists_mk
    exact single_add_single_mem hαα hαne hconn y y0
  have h1 := LinearMap.finrank_range_add_finrank_ker (sumAll σ)
  have h2 : finrank (ZMod 2) (LinearMap.range (sumAll σ)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (sumAll σ))
    rwa [finrank_self] at this
  have h3 := Submodule.finrank_mono hker
  rw [finrank_fintype_fun_eq_card] at h1
  omega

/-- **Euler bound**: every connected map satisfies `V - E + F ≤ 2`. -/
theorem euler_le_two :
    (Fintype.card (Orbit σ) : ℤ) - Fintype.card (Orbit α) + Fintype.card (Orbit (σ * α)) ≤ 2 := by
  have hle : LinearMap.range (cellBdry σ α) ≤ LinearMap.ker (segBdry σ α) := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]; exact segBdry_cellBdry hαα hαne hconn g
  have hL := LinearMap.finrank_range_add_finrank_ker (cellBdry σ α)
  have hB := LinearMap.finrank_range_add_finrank_ker (segBdry σ α)
  rw [finrank_fintype_fun_eq_card] at hL hB
  have hk := finrank_ker_cellBdry_le hαα hαne hconn
  have hr := card_le_finrank_range_segBdry hαα hαne hconn
  have h3 := Submodule.finrank_mono hle
  omega

end Euler

end Pca.MapFacts
