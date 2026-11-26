/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): walking along a curve

Public versions (for `Arrangement`) of the walk facts that are private in `Pca/Sweep/Jordan.lean`
(`j_flips`, `j_card_flips`): along the straight walk of a dart `d` of a curve `c`, the walk meets
another curve `C` exactly at the two crossings of `c` and `C` (`card_flipsOn`). Also:

* `Marked.inside_straight`: the interior status of `C` along a straight walk changes exactly at
  the crossings with `C`;
* `cyc_ends`: a combinatorial lemma on a cyclic sequence with two kinds of flips (used for the
  transversality of the lens of two curves, `Lens.lean`).
-/
import Pca.FlipGraph.Lemmas

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Walk

variable (A : Arrangement n D)

theorem pow_period_apply (d : D) : (A.straight ^ period A.straight d) d = d := by
  rw [Perm.coe_pow]; exact iterate_period _ _

theorem exists_idx {d e : D} (h : A.straight.SameCycle d e) :
    ∃ k < period A.straight d, (A.straight ^ k) d = e := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨k, List.mem_range.1 hk, by rw [Perm.coe_pow]⟩

theorem pow_inj {d : D} {i j : ℕ} (hi : i < period A.straight d)
    (hj : j < period A.straight d) (h : (A.straight ^ i) d = (A.straight ^ j) d) : i = j := by
  rw [period_eq_minimalPeriod] at hi hj
  rw [Perm.coe_pow, Perm.coe_pow] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

theorem pow_succ_apply (d : D) (i : ℕ) :
    (A.straight ^ (i + 1)) d = A.straight ((A.straight ^ i) d) := by
  rw [_root_.pow_succ', Perm.mul_apply]

theorem curve_pow (d : D) (i : ℕ) : A.curve ((A.straight ^ i) d) = A.curve d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ_apply, A.curve_straight, ih]

theorem curve_zpow (d : D) (i : ℤ) : A.curve ((A.straight ^ i) d) = A.curve d := by
  obtain ⟨j, -, hj⟩ := exists_idx A (show A.straight.SameCycle d ((A.straight ^ i) d) from ⟨i, rfl⟩)
  rw [← hj, curve_pow]

theorem zpow_add_period (d : D) (i : ℤ) :
    (A.straight ^ (i + (period A.straight d : ℤ))) d = (A.straight ^ i) d := by
  rw [zpow_add, Perm.mul_apply, zpow_natCast, pow_period_apply]

/-- `straight ∘ α = α ∘ straight⁻¹`. -/
theorem zpow_α (y : D) (j : ℤ) : (A.straight ^ j) (A.α y) = A.α ((A.straight ^ (-j)) y) := by
  have h1 : ∀ v, A.straight (A.α (A.straight v)) = A.α v := fun v => by
    rw [A.straight_apply, A.straight_apply, A.α_α, A.σ_σ_σ_σ]
  have hc : A.straight * A.α * A.straight = A.α := by ext v; exact h1 v
  have hc' : A.straight * A.α = A.α * A.straight⁻¹ := by
    calc A.straight * A.α = A.straight * A.α * A.straight * A.straight⁻¹ := by group
      _ = A.α * A.straight⁻¹ := by rw [hc]
  have key : ∀ j : ℤ, A.straight ^ j * A.α = A.α * A.straight ^ (-j) := by
    intro j
    induction j using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [zpow_add_one, mul_assoc, hc', ← mul_assoc, ih, mul_assoc, neg_add, zpow_add,
        zpow_neg_one]
    | pred i ih =>
      have hc'' : A.straight⁻¹ * A.α = A.α * A.straight := by
        have := congrArg (fun p => A.straight⁻¹ * p * A.straight) hc'
        simp only [mul_assoc, inv_mul_cancel, mul_one] at this
        rw [← mul_assoc] at this
        exact (by simpa [mul_assoc] using this.symm)
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, mul_assoc, hc'', ← mul_assoc, ih, mul_assoc,
        ← zpow_add_one]
      congr 2; ring
  have := congrArg (fun p : Perm D => p y) (key j)
  simpa only [Perm.mul_apply] using this

/-- The positions (within one period of the straight walk of `d`) at which the walk crosses
`C`. -/
def flipsOn (C : Fin n) (d : D) : Finset ℕ :=
  (range (period A.straight d)).filter
    (fun i => A.curve (A.σ (A.α ((A.straight ^ i) d))) = C)

theorem mem_flipsOn {C : Fin n} {d : D} {i : ℕ} : i ∈ flipsOn A C d ↔
    i < period A.straight d ∧ A.curve (A.σ (A.α ((A.straight ^ i) d))) = C := by
  rw [flipsOn, mem_filter, mem_range]

/-- The flips along the walk of `d` are the crossings of `curve d` with `C` (port of
`Sweep.SConf.j_card_flips`). -/
theorem card_flipsOn_eq {C : Fin n} {d : D} (hd : A.curve d ≠ C) :
    (flipsOn A C d).card =
      (univ.filter (fun x : A.Crossing => Arrangement.Crossing.curves A x = {A.curve d, C})).card := by
  refine Finset.card_bij (fun i _ => A.crossingOf (A.α ((A.straight ^ i) d))) ?_ ?_ ?_
  · intro i hi
    rw [mem_flipsOn] at hi
    rw [mem_filter, A.curves_crossingOf, A.curve_α, curve_pow, hi.2]
    exact ⟨mem_univ _, rfl⟩
  · intro i hi j hj h
    rw [mem_flipsOn] at hi hj
    have h' : A.α ((A.straight ^ j) d) ∈ orbitList A.σ (A.α ((A.straight ^ i) d)) :=
      mem_orbitList.2 (Orbit.mk_eq_mk.1 h)
    rw [A.orbitList_σ] at h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h1 | h1 | h1 | h1
    · have h2 := congrArg A.α h1
      rw [A.α_α, A.α_α] at h2
      exact pow_inj A hi.1 hj.1 h2.symm
    · exfalso
      have h2 := congrArg A.curve h1
      rw [A.curve_α, curve_pow, hi.2] at h2
      exact hd h2
    · exfalso
      set a := A.straight ((A.straight ^ i) d) with ha
      have hja : (A.straight ^ j) d = A.α a := by
        rw [ha, A.straight_apply, ← h1, A.α_α]
      apply Arrangement.not_sameCycle_straight_σσ (A := A) a
      have hda : A.straight.SameCycle d a := by
        rw [ha, ← pow_succ_apply]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
      have hdb : A.straight.SameCycle d (A.σ (A.σ a)) := by
        have : A.straight ((A.straight ^ j) d) = A.σ (A.σ a) := by
          rw [hja, A.straight_apply, A.α_α]
        rw [← this, ← pow_succ_apply]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
      exact hda.symm.trans hdb
    · exfalso
      have h2 := congrArg A.curve h1
      rw [A.curve_α, curve_pow, A.curve_σσ, hi.2] at h2
      exact hd h2
  · intro x hx
    rw [mem_filter] at hx
    have hγ : A.curve d ∈ Arrangement.Crossing.curves A x := by
      rw [hx.2]; exact mem_insert_self _ _
    obtain ⟨e, he, hce⟩ := mem_image.1 hγ
    have hx' : A.crossingOf e = x := Orbit.mem_darts.1 he
    obtain ⟨y, hy, hyx⟩ : ∃ y, A.straight.SameCycle d y ∧ A.crossingOf (A.α y) = x := by
      rcases A.isArrangement.straight d e hce.symm with h | h
      · refine ⟨A.α (A.σ (A.σ e)), ?_, ?_⟩
        · have h3 : A.straight (A.α (A.σ (A.σ e))) = e := by
            rw [A.straight_apply, A.α_α, A.σ_σ_σ_σ]
          rw [← h3] at h
          exact Perm.sameCycle_apply_right.1 h
        · rw [A.α_α, A.crossingOf_σ, A.crossingOf_σ, hx']
      · refine ⟨A.α e, ?_, by rw [A.α_α, hx']⟩
        have h3 : A.straight (A.α e) = A.σ (A.σ e) := by rw [A.straight_apply, A.α_α]
        have h' : A.straight.SameCycle d (A.σ (A.σ e)) := h
        rw [← h3] at h'
        exact Perm.sameCycle_apply_right.1 h'
    obtain ⟨k, hk, rfl⟩ := exists_idx A hy
    refine ⟨k, ?_, hyx⟩
    rw [mem_flipsOn]
    refine ⟨hk, ?_⟩
    have h2 := hx.2
    rw [← hyx, A.curves_crossingOf, A.curve_α, curve_pow] at h2
    have hne := A.isArrangement.curve_σ (A.α ((A.straight ^ k) d))
    rw [A.curve_α, curve_pow] at hne
    have hm : A.curve (A.σ (A.α ((A.straight ^ k) d))) ∈ ({A.curve d, C} : Finset (Fin n)) := by
      rw [← h2]; exact mem_insert_of_mem (mem_singleton_self _)
    rcases mem_insert.1 hm with h | h
    · exact absurd h hne
    · exact mem_singleton.1 h

/-- Along the walk of a dart of `c ≠ C` there are exactly two crossings with `C`. -/
theorem card_flipsOn {C : Fin n} {d : D} (hd : A.curve d ≠ C) : (flipsOn A C d).card = 2 := by
  rw [card_flipsOn_eq A hd]; exact A.isArrangement.intersecting _ _ hd

end Walk

/-- Walking straight, the interior status of `C` changes exactly at the crossings with `C` (also
for darts of `C`: then it never changes). -/
theorem Marked.inside_straight (M : Marked n D) (C : Fin n) (y : D) :
    M.Inside C (M.A.cellOf (M.A.straight y)) ↔
      (M.Inside C (M.A.cellOf y) ↔ M.A.curve (M.A.σ (M.A.α y)) ≠ C) := by
  rw [M.A.straight_apply, M.A.cellOf_σ, M.inside_α, M.A.cellOf_σ, M.A.α_α]

/-! ## A cyclic sequence with two kinds of flips -/

/-- Between two positions with different values of `l` there is a flip of `l`. -/
theorem flip_between {fl l : ℤ → Prop} (hl : ∀ i, l (i + 1) ↔ (l i ↔ ¬ fl i)) {a b : ℤ}
    (hab : a ≤ b) (h : ¬ (l a ↔ l b)) : ∃ t, a ≤ t ∧ t < b ∧ fl t := by
  induction b, hab using Int.le_induction with
  | base => exact absurd Iff.rfl h
  | succ b hab ih =>
    by_cases hb : fl b
    · exact ⟨b, hab, by omega, hb⟩
    · have : l (b + 1) ↔ l b := by rw [hl b]; tauto
      obtain ⟨t, h1, h2, h3⟩ := ih (by rw [← this]; exact h)
      exact ⟨t, h1, by omega, h3⟩

theorem periodic_mul {f : ℤ → Prop} {p : ℤ} (hf : ∀ i, f (i + p) ↔ f i) (i t : ℤ) :
    f (i + p * t) ↔ f i := by
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih => rw [mul_add, mul_one, ← add_assoc, hf, ih]
  | pred t ih =>
    rw [← ih, show i + p * -↑t = i + p * (-↑t - 1) + p by ring, hf]

/-- At most two positions with `fl` in a window of length `p`, if there are two in `[0, p)`. -/
theorem window_card {p : ℕ} (hp : 0 < p) {f : ℤ → Prop} [DecidablePred f] (hf : ∀ i, f (i + p) ↔ f i)
    (hc : ((range p).filter (fun i : ℕ => f i)).card = 2) {a : ℤ} (s : Finset ℤ)
    (hs : ∀ x ∈ s, a ≤ x ∧ x < a + p ∧ f x) : s.card ≤ 2 := by
  classical
  rw [← hc]
  refine Finset.card_le_card_of_injOn (fun x => (x % (p : ℤ)).toNat) ?_ ?_
  · intro x hx
    obtain ⟨-, -, h3⟩ := hs x hx
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have h0 := Int.emod_nonneg x hp'.ne'
    have h1 := Int.emod_lt_of_pos x hp'
    simp only [coe_filter, Set.mem_setOf_eq, mem_range]
    refine ⟨by omega, ?_⟩
    rw [Int.toNat_of_nonneg h0, Int.emod_def, sub_eq_add_neg, ← mul_neg, periodic_mul hf]
    exact h3
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2, -⟩ := hs x (by simpa using hx)
    obtain ⟨hy1, hy2, -⟩ := hs y (by simpa using hy)
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have e : x % (p : ℤ) = y % (p : ℤ) := by
      have h0 := Int.emod_nonneg x hp'.ne'
      have h0' := Int.emod_nonneg y hp'.ne'
      simp only at hxy
      omega
    have hd : (p : ℤ) ∣ x - y := Int.ModEq.dvd e.symm
    have := Int.eq_zero_of_abs_lt_dvd hd (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
    omega

/-- **Cyclic sequence lemma.** A cyclic sequence (period `p`) of positions with two properties
`l`, `r` that change exactly at the flips `fl`, `fr` (disjoint, two of each per period). If every
`fl` flip has `r` and every `fr` flip has `l`, then for a position `0` with `l ∧ r`: walking
forward, the run of `l ∧ r` ends at an `fl` flip iff walking backward it ends at an `fr` flip. -/
theorem cyc_ends {p : ℕ} (hp : 0 < p) {fl fr l r : ℤ → Prop} [DecidablePred fl] [DecidablePred fr]
    (pfl : ∀ i, fl (i + p) ↔ fl i) (pfr : ∀ i, fr (i + p) ↔ fr i)
    (pl : ∀ i, l (i + p) ↔ l i) (pr : ∀ i, r (i + p) ↔ r i)
    (hl : ∀ i, l (i + 1) ↔ (l i ↔ ¬ fl i)) (hr : ∀ i, r (i + 1) ↔ (r i ↔ ¬ fr i))
    (hdis : ∀ i, ¬ (fl i ∧ fr i))
    (cl : ((range p).filter (fun i : ℕ => fl i)).card = 2)
    (cr : ((range p).filter (fun i : ℕ => fr i)).card = 2)
    (hA : ∀ i, fl i → r i) (hA' : ∀ i, fr i → l i) (h0 : l 0 ∧ r 0) :
    (∃ k : ℕ, (∀ i ≤ k, l i ∧ r i) ∧ fl k) ↔
      (∃ j : ℕ, (∀ i ≤ j, l (-i) ∧ r (-i)) ∧ fr (-j - 1)) := by
  classical
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨i₀, hi₀⟩ : ∃ i : ℕ, i < p ∧ fl i := by
    obtain ⟨i, hi⟩ := card_pos.1 (show 0 < _ by rw [cl]; norm_num)
    exact ⟨i, by simpa using hi⟩
  -- the first flip forward and backward
  have exF : ∃ k : ℕ, fl k ∨ fr k := ⟨i₀, Or.inl hi₀.2⟩
  have exB : ∃ m : ℕ, fl (-m - 1) ∨ fr (-m - 1) := by
    refine ⟨p - 1 - i₀, Or.inl ?_⟩
    have := (pfl ((-(p - 1 - i₀ : ℕ) : ℤ) - 1)).symm
    rw [this]
    convert hi₀.2 using 2
    have : i₀ ≤ p - 1 := by omega
    push_cast [this, show 1 ≤ p from hp]
    ring
  set k₀ := Nat.find exF
  set m₀ := Nat.find exB
  have hk₀ : fl k₀ ∨ fr k₀ := Nat.find_spec exF
  have hm₀ : fl (-m₀ - 1) ∨ fr (-m₀ - 1) := Nat.find_spec exB
  have nk : ∀ i : ℕ, i < k₀ → ¬ fl i ∧ ¬ fr i := fun i hi => by
    have := Nat.find_min exF hi; tauto
  have nm : ∀ i : ℕ, i < m₀ → ¬ fl (-i - 1) ∧ ¬ fr (-i - 1) := fun i hi => by
    have := Nat.find_min exB hi; tauto
  have Qf : ∀ i : ℕ, i ≤ k₀ → l i ∧ r i := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      obtain ⟨c, d⟩ := nk i (by omega)
      push_cast
      rw [hl, hr]; exact ⟨iff_of_true a c, iff_of_true b d⟩
  have Qb : ∀ i : ℕ, i ≤ m₀ → l (-i) ∧ r (-i) := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      obtain ⟨c, d⟩ := nm i (by omega)
      have e1 := hl (-(i : ℤ) - 1)
      have e2 := hr (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 1 = -i by ring] at e1 e2
      push_cast
      rw [show -((i : ℤ) + 1) = -i - 1 by ring]
      exact ⟨(e1.1 a).2 c, (e2.1 b).2 d⟩
  -- the left side is `fl k₀`, the right side `fr (-m₀ - 1)`
  have lhs : (∃ k : ℕ, (∀ i ≤ k, l i ∧ r i) ∧ fl k) ↔ fl k₀ := by
    refine ⟨fun ⟨k, hQ, hk⟩ => ?_, fun h => ⟨k₀, Qf, h⟩⟩
    have h1 : k₀ ≤ k := Nat.find_min' exF (Or.inl hk)
    rcases h1.lt_or_eq with h1 | h1
    · exfalso
      obtain ⟨a, b⟩ := hQ (k₀ + 1) h1
      obtain ⟨a', b'⟩ := Qf k₀ le_rfl
      push_cast at a b
      rw [hl] at a; rw [hr] at b
      rcases hk₀ with h | h
      · exact a.1 a' h
      · exact b.1 b' h
    · rw [h1]; exact hk
  have rhs : (∃ j : ℕ, (∀ i ≤ j, l (-i) ∧ r (-i)) ∧ fr (-j - 1)) ↔ fr (-m₀ - 1) := by
    refine ⟨fun ⟨j, hQ, hj⟩ => ?_, fun h => ⟨m₀, Qb, h⟩⟩
    have h1 : m₀ ≤ j := Nat.find_min' exB (Or.inr hj)
    rcases h1.lt_or_eq with h1 | h1
    · exfalso
      obtain ⟨a, b⟩ := hQ (m₀ + 1) h1
      obtain ⟨a', b'⟩ := Qb m₀ le_rfl
      have e1 := hl (-(m₀ : ℤ) - 1)
      have e2 := hr (-(m₀ : ℤ) - 1)
      rw [show -(m₀ : ℤ) - 1 + 1 = -m₀ by ring] at e1 e2
      push_cast at a b
      rw [show -((m₀ : ℤ) + 1) = -m₀ - 1 by ring] at a b
      rcases hm₀ with h | h
      · exact (e1.1 a').1 a h
      · exact (e2.1 b').1 b h
    · rw [h1]; exact hj
  rw [lhs, rhs]
  -- the window `[a, a + p)` starting at the backward flip
  set a : ℤ := -m₀ - 1 with ha
  set b : ℤ := (k₀ : ℤ) with hb
  have hab : a < b := by omega
  have noF : ∀ t, a < t → t < b → ¬ fl t ∧ ¬ fr t := by
    intro t h1 h2
    rcases le_or_gt 0 t with h | h
    · obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact nk t' (by omega)
    · obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t = -t' - 1 := ⟨(-t - 1).toNat, by omega⟩
      subst ht'
      exact nm t' (by omega)
  -- an element of a periodic set can be moved into the window
  have shift : ∀ {f : ℤ → Prop}, (∀ i, f (i + p) ↔ f i) → ∀ i, f i →
      ∃ i', a ≤ i' ∧ i' < a + p ∧ f i' := by
    intro f hf i hi
    refine ⟨a + (i - a) % p, by have := Int.emod_nonneg (i - a) hp'.ne'; omega,
      by have := Int.emod_lt_of_pos (i - a) hp'; omega, ?_⟩
    rw [Int.emod_def, show a + (i - a - p * ((i - a) / p)) = i + p * (-((i - a) / p)) by ring,
      periodic_mul hf]
    exact hi
  have hla : l (a + 1) ∧ r (a + 1) := by
    have := Qb m₀ le_rfl; rw [ha, show -(m₀ : ℤ) - 1 + 1 = -m₀ by ring]; exact this
  have hlb : l b ∧ r b := Qf k₀ le_rfl
  -- both flips of the same kind is impossible
  have same : ∀ {f g : ℤ → Prop} {u : ℤ → Prop} [DecidablePred f] [DecidablePred g], (∀ i, f (i + p) ↔ f i) →
      (∀ i, g (i + p) ↔ g i) → (∀ i, u (i + p) ↔ u i) → (∀ i, u (i + 1) ↔ (u i ↔ ¬ f i)) →
      (∀ i, ¬ (f i ∧ g i)) → ((range p).filter (fun i : ℕ => f i)).card = 2 →
      ((range p).filter (fun i : ℕ => g i)).card = 2 → (∀ i, g i → u i) →
      (∀ t, a < t → t < b → ¬ f t ∧ ¬ g t) → u (a + 1) → u b → f a → f b → False := by
    intro f g u _ _ pf pg pu hu hfg cf cg hg nF ua ub fa fb
    obtain ⟨j₀, hj₀⟩ : ∃ i : ℕ, i < p ∧ g i := by
      obtain ⟨i, hi⟩ := card_pos.1 (show 0 < _ by rw [cg]; norm_num)
      exact ⟨i, by simpa using hi⟩
    obtain ⟨i', h1, h2, h3⟩ := shift pg _ hj₀.2
    have hi'b : b < i' := by
      by_contra hc
      rcases eq_or_lt_of_le h1 with h | h
      · exact hfg a ⟨fa, h ▸ h3⟩
      rcases (not_lt.1 hc).lt_or_eq with h' | h'
      · exact (nF i' h h').2 h3
      · exact hfg b ⟨fb, h' ▸ h3⟩
    have ub1 : ¬ u (b + 1) := by rw [hu]; exact fun h => (h.1 ub) fb
    have uap : ¬ u (a + p) := by
      rw [pu]; have := (hu a).1 ua; exact fun h => this.1 h fa
    obtain ⟨t₁, t1a, t1b, t1c⟩ := flip_between hu (show b + 1 ≤ i' by omega)
      (fun h => ub1 (h.2 (hg _ h3)))
    obtain ⟨t₂, t2a, t2b, t2c⟩ := flip_between hu (show i' ≤ a + p by omega)
      (fun h => uap (h.1 (hg _ h3)))
    have := window_card hp pf cf (a := a) {a, b, t₁, t₂} (by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨le_rfl, by omega, fa⟩
      · exact ⟨by omega, by omega, fb⟩
      · exact ⟨by omega, by omega, t1c⟩
      · exact ⟨by omega, by omega, t2c⟩)
    rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
      card_pair (by omega)] at this
    omega
  rcases hk₀ with hk | hk <;> rcases hm₀ with hm | hm
  · exact absurd (same pfl pfr pl hl hdis cl cr hA' (fun t h1 h2 => noF t h1 h2) hla.1 hlb.1 hm hk)
      id
  · exact ⟨fun _ => hm, fun _ => hk⟩
  · exact ⟨fun h => absurd ⟨h, hk⟩ (hdis _), fun h => absurd ⟨hm, h⟩ (hdis _)⟩
  · exact absurd (same pfr pfl pr hr (fun i h => hdis i ⟨h.2, h.1⟩) cr cl hA
      (fun t h1 h2 => (noF t h1 h2).symm) hla.2 hlb.2 hm hk) id

/-- If every `fl` flip violates `r` and every `fr` flip violates `l` (and there is a flip), no
position has `l ∧ r`: walking forward from it, the first flip is a contradiction. -/
theorem cyc_none {fl fr l r : ℤ → Prop}
    (hl : ∀ i, l (i + 1) ↔ (l i ↔ ¬ fl i)) (hr : ∀ i, r (i + 1) ↔ (r i ↔ ¬ fr i))
    (ex : ∃ k : ℕ, fl k ∨ fr k) (hB : ∀ i, fl i → ¬ r i) (hB' : ∀ i, fr i → ¬ l i) :
    ¬ (l 0 ∧ r 0) := by
  classical
  intro h0
  have Qf : ∀ i : ℕ, i ≤ Nat.find ex → l i ∧ r i := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      have := Nat.find_min ex (show i < Nat.find ex by omega)
      push_cast
      rw [hl, hr]; exact ⟨iff_of_true a (fun h => this (Or.inl h)),
        iff_of_true b (fun h => this (Or.inr h))⟩
  rcases Nat.find_spec ex with h | h
  · exact hB _ h (Qf _ le_rfl).2
  · exact hB' _ h (Qf _ le_rfl).1
