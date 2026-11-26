/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Generic permutation facts for maps

Used by the removal of curves in `Pca/Sweep/` and by the insertion count in `Pca/Great/`:

* first-return maps (`IsFR`): a permutation `f'` of `X'` that, transported along an embedding
  `ι : X' → X` with range `K`, is the first return of `f` to `K`; its orbits correspond to the
  orbits of `f` that meet `K` (`IsFR.sameCycle_iff`, `IsFR.card_orbit`), and so do the orbit
  lists (`IsFR.map_orbitList`);
* chains `x ↦ a (p x)` and their first hits of `K` (`hit`), an involution when `a` and `p` are;
* the orbit count of `f * R` for an involution `R` (`card_orbit_le_mul`);
* the Euler bound `V - E + F ≤ 2` for every connected map (`euler_le_two`).
-/
import Pca.Jordan

open Equiv Finset Module

set_option linter.unusedSectionVars false

namespace Pca.MapFacts

universe u v

/-! ## Iterates -/

section Iter

variable {X : Type u}

theorem sameCycle_of_pow (f : Perm X) (x : X) (i : ℕ) : f.SameCycle x ((f ^ i) x) :=
  ⟨i, by rw [zpow_natCast]⟩

theorem sameCycle_iff_nat [Finite X] {f : Perm X} {a b : X} :
    f.SameCycle a b ↔ ∃ i : ℕ, (f ^ i) a = b :=
  ⟨fun h => h.exists_nat_pow_eq, fun ⟨i, h⟩ => h ▸ sameCycle_of_pow f a i⟩

theorem pow_apply_eq_iterate (f : Perm X) (i : ℕ) (x : X) : (f ^ i) x = (f^[i]) x := by
  rw [Perm.coe_pow]

end Iter

/-! ## First-return maps -/

section FR

variable {X : Type u} [Fintype X] [DecidableEq X] {X' : Type v} [Fintype X'] [DecidableEq X']

/-- `f'` is the first-return map of `f` to `K`, transported along `ι`. -/
def IsFR (f : Perm X) (f' : Perm X') (ι : X' → X) (K : X → Prop) : Prop :=
  ∀ x', ∃ k, 0 < k ∧ ι (f' x') = (f ^ k) (ι x') ∧ ∀ j, 0 < j → j < k → ¬ K ((f ^ j) (ι x'))

variable {f : Perm X} {f' : Perm X'} {ι : X' → X} {K : X → Prop}

/-- The return time of `x'`. -/
noncomputable def IsFR.time (h : IsFR f f' ι K) (x' : X') : ℕ := Classical.choose (h x')

theorem IsFR.time_pos (h : IsFR f f' ι K) (x' : X') : 0 < h.time x' :=
  (Classical.choose_spec (h x')).1

theorem IsFR.apply (h : IsFR f f' ι K) (x' : X') : ι (f' x') = (f ^ h.time x') (ι x') :=
  (Classical.choose_spec (h x')).2.1

theorem IsFR.not_mem (h : IsFR f f' ι K) (x' : X') {j : ℕ} (hj0 : 0 < j) (hj : j < h.time x') :
    ¬ K ((f ^ j) (ι x')) :=
  (Classical.choose_spec (h x')).2.2 j hj0 hj

/-- Cumulated return times along the orbit of `x'`. -/
noncomputable def IsFR.tau (h : IsFR f f' ι K) (x' : X') : ℕ → ℕ
  | 0 => 0
  | j + 1 => h.tau x' j + h.time ((f' ^ j) x')

theorem IsFR.pow_apply (h : IsFR f f' ι K) (x' : X') (j : ℕ) :
    ι ((f' ^ j) x') = (f ^ h.tau x' j) (ι x') := by
  induction j with
  | zero => simp [IsFR.tau]
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, h.apply, ih, IsFR.tau, add_comm, pow_add, Perm.mul_apply]

theorem IsFR.tau_lt_succ (h : IsFR f f' ι K) (x' : X') (j : ℕ) :
    h.tau x' j < h.tau x' (j + 1) := by
  rw [IsFR.tau]; have := h.time_pos ((f' ^ j) x'); omega

theorem IsFR.tau_strictMono (h : IsFR f f' ι K) (x' : X') : StrictMono (h.tau x') :=
  strictMono_nat_of_lt_succ (h.tau_lt_succ x')

/-- Between two consecutive returns there is no dart of `K`. -/
theorem IsFR.not_mem_between (h : IsFR f f' ι K) (x' : X') (j i : ℕ) (h1 : h.tau x' j < i)
    (h2 : i < h.tau x' (j + 1)) : ¬ K ((f ^ i) (ι x')) := by
  have he : i = (i - h.tau x' j) + h.tau x' j := by omega
  rw [he, pow_add, Perm.mul_apply, ← h.pow_apply]
  apply h.not_mem
  · omega
  · rw [IsFR.tau] at h2; omega

/-- Every time `i` lies in a unique interval `[tau j, tau (j+1))`. -/
theorem IsFR.exists_tau_le (h : IsFR f f' ι K) (x' : X') (i : ℕ) :
    ∃ j, h.tau x' j ≤ i ∧ i < h.tau x' (j + 1) := by
  induction i with
  | zero => exact ⟨0, le_rfl, by have := h.tau_lt_succ x' 0; simpa [IsFR.tau] using this⟩
  | succ i ih =>
    obtain ⟨j, hj1, hj2⟩ := ih
    by_cases hc : i + 1 < h.tau x' (j + 1)
    · exact ⟨j, by omega, hc⟩
    · refine ⟨j + 1, by omega, ?_⟩
      have := h.tau_lt_succ x' (j + 1); omega

theorem IsFR.mem_of_mem (h : IsFR f f' ι K) (hK : ∀ x', K (ι x')) (x' : X') (i : ℕ)
    (hi : K ((f ^ i) (ι x'))) : ∃ j, h.tau x' j = i := by
  obtain ⟨j, hj1, hj2⟩ := h.exists_tau_le x' i
  rcases hj1.lt_or_eq with hlt | heq
  · exact absurd hi (h.not_mem_between x' j i hlt hj2)
  · exact ⟨j, heq⟩

variable (hinj : Function.Injective ι) (hK : ∀ x', K (ι x')) (hr : ∀ x, K x → ∃ x', ι x' = x)
include hinj hK hr

theorem IsFR.sameCycle_iff (h : IsFR f f' ι K) {a b : X'} :
    f'.SameCycle a b ↔ f.SameCycle (ι a) (ι b) := by
  constructor
  · intro hab
    obtain ⟨j, rfl⟩ := hab.exists_nat_pow_eq
    rw [h.pow_apply]; exact sameCycle_of_pow _ _ _
  · intro hab
    obtain ⟨i, hi⟩ := hab.exists_nat_pow_eq
    obtain ⟨j, hj⟩ := h.mem_of_mem hK a i (hi ▸ hK b)
    rw [← hj, ← h.pow_apply] at hi
    exact hinj hi ▸ sameCycle_of_pow _ _ _

/-- The orbit of `x'` is the part in `K` of the orbit of `ι x'`. -/
theorem IsFR.map_orbitFinset (h : IsFR f f' ι K) [DecidablePred K] (a : X') :
    (orbitFinset f' a).map ⟨ι, hinj⟩ = (orbitFinset f (ι a)).filter K := by
  ext y
  simp only [mem_map, mem_orbitFinset, Function.Embedding.coeFn_mk, mem_filter]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(h.sameCycle_iff hinj hK hr).1 hb, hK b⟩
  · rintro ⟨hy, hyK⟩
    obtain ⟨b, rfl⟩ := hr y hyK
    exact ⟨b, (h.sameCycle_iff hinj hK hr).2 hy, rfl⟩

/-- The orbits of `f'` correspond to the orbits of `f` that meet `K`. -/
theorem IsFR.card_orbit (h : IsFR f f' ι K) [DecidablePred K] :
    Fintype.card (Orbit f') = (univ.filter (fun o : Orbit f => ∃ d ∈ o.darts, K d)).card := by
  let Ψ : Orbit f' → Orbit f :=
    Quotient.map' ι fun a b hab => (h.sameCycle_iff hinj hK hr).1 hab
  have hΨ : ∀ a, Ψ (Orbit.mk f' a) = Orbit.mk f (ι a) := fun _ => rfl
  have hinjΨ : Function.Injective Ψ := by
    intro o1 o2 he
    obtain ⟨a, rfl⟩ := o1.exists_mk
    obtain ⟨b, rfl⟩ := o2.exists_mk
    rw [hΨ, hΨ, Orbit.mk_eq_mk] at he
    exact Orbit.mk_eq_mk.2 ((h.sameCycle_iff hinj hK hr).2 he)
  rw [← card_univ, ← card_image_of_injective univ hinjΨ]
  congr 1
  ext o
  simp only [mem_image, mem_univ, true_and, mem_filter]
  constructor
  · rintro ⟨o', rfl⟩
    obtain ⟨a, rfl⟩ := o'.exists_mk
    exact ⟨ι a, Orbit.mem_darts.2 rfl, hK a⟩
  · rintro ⟨d, hd, hdK⟩
    obtain ⟨a, rfl⟩ := hr d hdK
    exact ⟨Orbit.mk f' a, (Orbit.mem_darts.1 hd)⟩

/-- The orbit list of `x'` is the part in `K` of the orbit list of `ι x'`. -/
theorem IsFR.map_orbitList (h : IsFR f f' ι K) [DecidablePred K] (a : X') :
    (orbitList f' a).map ι = (orbitList f (ι a)).filter (fun d => decide (K d)) := by
  -- the blocks between consecutive returns
  have hblock : ∀ j, ((List.range (h.tau a j)).map (fun i => (f^[i]) (ι a))).filter
      (fun d => decide (K d)) = (List.range j).map (fun i => ι ((f'^[i]) a)) := by
    intro j
    induction j with
    | zero => simp [IsFR.tau]
    | succ j ih =>
      have hs : h.tau a (j + 1) = h.tau a j + h.time ((f' ^ j) a) := rfl
      obtain ⟨t, ht⟩ : ∃ t, h.time ((f' ^ j) a) = t + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (h.time_pos _)).symm⟩
      rw [hs, List.range_add, List.map_append, List.filter_append, ih, List.range_succ,
        List.map_append, ht, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.filter_cons, List.map_nil]
      have hK0 : K ((f^[h.tau a j + 0]) (ι a)) := by
        rw [add_zero, ← pow_apply_eq_iterate, ← h.pow_apply]; exact hK _
      rw [if_pos (by simpa using hK0)]
      have hrest : ((List.range t).map ((fun i => (f^[i]) (ι a)) ∘ (fun x => h.tau a j + x) ∘
          Nat.succ)).filter (fun d => decide (K d)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hi
        simp only [Function.comp, decide_eq_true_eq]
        rw [← pow_apply_eq_iterate]
        apply h.not_mem_between a j
        · omega
        · rw [hs, ht]; omega
      rw [hrest, add_zero, ← pow_apply_eq_iterate, ← h.pow_apply, pow_apply_eq_iterate]
  -- the full orbit consists of `period f' a` blocks
  have hp : h.tau a (period f' a) = period f (ι a) := by
    have hper := iterate_period f' a
    have hq : (f^[h.tau a (period f' a)]) (ι a) = ι a := by
      rw [← pow_apply_eq_iterate, ← h.pow_apply, pow_apply_eq_iterate, hper]
    have hdvd : period f (ι a) ∣ h.tau a (period f' a) := by
      rw [period_eq_minimalPeriod]; exact Function.IsPeriodicPt.minimalPeriod_dvd hq
    have hpos : 0 < h.tau a (period f' a) :=
      lt_of_le_of_lt (Nat.zero_le _) (h.tau_strictMono a (period_pos f' a))
    have hle : h.tau a (period f' a) ≤ period f (ι a) := by
      by_contra hlt
      push Not at hlt
      have hKp : K ((f ^ period f (ι a)) (ι a)) := by
        rw [pow_apply_eq_iterate, iterate_period]; exact hK a
      obtain ⟨j, hj⟩ := h.mem_of_mem hK a _ hKp
      have hjlt : j < period f' a := by
        by_contra hc; push Not at hc
        have := (h.tau_strictMono a).monotone hc
        omega
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp [IsFR.tau] at hj; exact absurd hj.symm (period_pos f (ι a)).ne'
        · exact hj0
      have he : (f' ^ j) a = a := by
        apply hinj
        rw [h.pow_apply, hj, pow_apply_eq_iterate, iterate_period]
      have := Nat.find_min (exists_iterate_eq f' a) hjlt
      exact this ⟨hj0, by rw [← pow_apply_eq_iterate]; exact he⟩
    exact le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have := hblock (period f' a)
  rw [hp] at this
  rw [orbitList, orbitList, this, List.map_map]
  rfl

end FR

/-! ## Chains `x ↦ a (p x)` and their first hit of `K` -/

section Hit

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Hypotheses on the chain data: `a`, `p` involutions, `p` fixes `K` pointwise and preserves
`K`, `Q` (the label class) is preserved, and `p` has no fixed points on `Q \ K`. -/
structure HitHyp (a p : Perm X) (K Q : X → Prop) : Prop where
  aa : ∀ x, a (a x) = x
  ane : ∀ x, a x ≠ x
  pp : ∀ x, p (p x) = x
  pK : ∀ x, K x → p x = x
  Kp : ∀ x, K (p x) ↔ K x
  Qa : ∀ x, Q (a x) ↔ Q x
  Qp : ∀ x, Q (p x) ↔ Q x
  KQ : ∀ x, K x → Q x
  pne : ∀ x, Q x → ¬ K x → p x ≠ x

variable {a p : Perm X} {K Q : X → Prop} [DecidablePred K]

theorem HitHyp.exists_hit (H : HitHyp a p K Q) {k : X} (hk : K k) :
    ∃ j, K (((a * p) ^ j) (a k)) := by
  set T := a * p
  have h1 : (T ^ orderOf T) (a k) = a k := by rw [pow_orderOf_eq_one]; rfl
  obtain ⟨m, hm⟩ : ∃ m, orderOf T = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (orderOf_pos T)).symm⟩
  refine ⟨m, ?_⟩
  rw [hm, pow_succ', Perm.mul_apply] at h1
  have h2 : p ((T ^ m) (a k)) = k := by
    have := congrArg a h1
    rwa [show T ((T ^ m) (a k)) = a (p ((T ^ m) (a k))) from rfl, H.aa, H.aa] at this
  rw [← H.Kp, h2]; exact hk

/-- The first hit of `K` of the chain `a k, T (a k), T² (a k), …` with `T = a * p`. -/
noncomputable def hitIdx (a p : Perm X) (K : X → Prop) [DecidablePred K] (k : X) : ℕ :=
  @dite _ (∃ j, K (((a * p) ^ j) (a k))) (Classical.dec _) (fun h => Nat.find h) (fun _ => 0)

noncomputable def hit (a p : Perm X) (K : X → Prop) [DecidablePred K] (k : X) : X :=
  ((a * p) ^ hitIdx a p K k) (a k)

theorem HitHyp.hit_eq (H : HitHyp a p K Q) {k : X} (hk : K k) :
    hit a p K k = ((a * p) ^ hitIdx a p K k) (a k) := rfl

theorem HitHyp.hit_mem (H : HitHyp a p K Q) {k : X} (hk : K k) : K (hit a p K k) := by
  have he := H.exists_hit hk
  unfold hit hitIdx
  rw [dif_pos he]
  exact Nat.find_spec he

theorem HitHyp.not_mem_lt (H : HitHyp a p K Q) {k : X} (hk : K k) {i : ℕ}
    (hi : i < hitIdx a p K k) : ¬ K (((a * p) ^ i) (a k)) := by
  have he := H.exists_hit hk
  unfold hitIdx at hi
  rw [dif_pos he] at hi
  exact Nat.find_min he hi

/-- Characterization of the first hit. -/
theorem HitHyp.hit_eq_of (H : HitHyp a p K Q) {k : X} (hk : K k) {m : ℕ}
    (hm : K (((a * p) ^ m) (a k))) (hlt : ∀ i < m, ¬ K (((a * p) ^ i) (a k))) :
    hitIdx a p K k = m ∧ hit a p K k = ((a * p) ^ m) (a k) := by
  have he := H.exists_hit hk
  have hidx : hitIdx a p K k = m := by
    unfold hitIdx
    rw [dif_pos he]
    refine le_antisymm (Nat.find_min' he hm) ?_
    by_contra hc
    push Not at hc
    exact hlt _ hc (Nat.find_spec he)
  exact ⟨hidx, by rw [H.hit_eq hk, hidx]⟩

theorem pow_inv_pow_apply (T : Perm X) {i j : ℕ} (hi : i ≤ j) (y : X) :
    (T ^ i)⁻¹ ((T ^ j) y) = (T ^ (j - i)) y := by
  rw [Perm.inv_def, Equiv.symm_apply_eq, ← Perm.mul_apply, ← pow_add,
    show i + (j - i) = j by omega]

theorem HitHyp.a_T_a (H : HitHyp a p K Q) (i : ℕ) (x : X) :
    ((a * p) ^ i) (a x) = a (((a * p) ^ i)⁻¹ x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Perm.mul_apply, show (a * p) (a x) = a (p (a x)) from rfl, ih,
      ← pow_succ, pow_succ', mul_inv_rev, Perm.mul_apply]
    congr 2
    rw [Perm.inv_def, Equiv.eq_symm_apply]
    show a (p (p (a x))) = x
    rw [H.pp, H.aa]

theorem HitHyp.Q_pow (H : HitHyp a p K Q) (i : ℕ) (x : X) :
    Q (((a * p) ^ i) x) ↔ Q x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, show (a * p) (((a * p) ^ i) x) =
      a (p (((a * p) ^ i) x)) from rfl, H.Qa, H.Qp, ih]

theorem HitHyp.hit_hit (H : HitHyp a p K Q) {k : X} (hk : K k) :
    hit a p K (hit a p K k) = k := by
  set j := hitIdx a p K k
  have hhk := H.hit_mem hk
  have hx : hit a p K k = ((a * p) ^ j) (a k) := H.hit_eq hk
  -- `T^i (a (T^j (a k))) = a (T^(j-i) (a k))`
  have key : ∀ i ≤ j, ((a * p) ^ i) (a (hit a p K k)) = a (((a * p) ^ (j - i)) (a k)) := by
    intro i hi
    rw [H.a_T_a, hx]
    congr 1
    exact pow_inv_pow_apply _ hi _
  have hlt : ∀ i < j, ¬ K (((a * p) ^ i) (a (hit a p K k))) := by
    intro i hi
    rw [key i hi.le]
    obtain ⟨r, hr⟩ : ∃ r, j - i = r + 1 := ⟨j - i - 1, by omega⟩
    rw [hr, pow_succ', Perm.mul_apply, show (a * p) (((a * p) ^ r) (a k)) = a (p (((a * p) ^ r) (a k))) from rfl,
      H.aa, H.Kp]
    exact H.not_mem_lt hk (by omega)
  have hj : K (((a * p) ^ j) (a (hit a p K k))) := by
    rw [key j le_rfl, Nat.sub_self, pow_zero, Perm.one_apply, H.aa]; exact hk
  rw [(H.hit_eq_of hhk hj hlt).2, key j le_rfl, Nat.sub_self, pow_zero, Perm.one_apply, H.aa]

theorem HitHyp.hit_ne (H : HitHyp a p K Q) {k : X} (hk : K k) : hit a p K k ≠ k := by
  intro heq
  set j := hitIdx a p K k
  have hx : hit a p K k = ((a * p) ^ j) (a k) := H.hit_eq hk
  -- the chain is its own reverse: `T^i (a k) = a (T^(j-i) (a k))`
  have key : ∀ i ≤ j, ((a * p) ^ i) (a k) = a (((a * p) ^ (j - i)) (a k)) := by
    intro i hi
    have := congrArg (fun z => ((a * p) ^ i) (a z)) heq
    rw [← this, H.a_T_a, hx]
    congr 1
    exact pow_inv_pow_apply _ hi _
  have hQ : ∀ i, Q (((a * p) ^ i) (a k)) := fun i => (H.Q_pow i _).2 ((H.Qa k).2 (H.KQ k hk))
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · have := key m (by omega)
    rw [show j - m = m by omega] at this
    exact H.ane _ this.symm
  · have h1 := key m (by omega)
    rw [show j - m = m + 1 by omega, pow_succ', Perm.mul_apply,
      show (a * p) (((a * p) ^ m) (a k)) = a (p (((a * p) ^ m) (a k))) from rfl, H.aa] at h1
    exact H.pne _ (hQ m) (H.not_mem_lt hk (by omega)) h1.symm

/-- The chain (with an arbitrary step function agreeing with `p` on `Q \ K`) from `a k` to a dart of
`K` ends at the first hit. -/
theorem HitHyp.chain_eq_hit (H : HitHyp a p K Q) {ps : X → X}
    (hps : ∀ x, Q x → ¬ K x → ps x = p x) {k z : X} (hk : K k)
    (hc : Relation.ReflTransGen (fun e e' => ¬ K e ∧ e' = a (ps e)) (a k) z) (hz : K z) :
    z = hit a p K k := by
  have hgen : ∃ m, z = ((a * p) ^ m) (a k) ∧ ∀ i < m, ¬ K (((a * p) ^ i) (a k)) := by
    clear hz
    induction hc with
    | refl => exact ⟨0, by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | tail _ hst ih =>
      obtain ⟨m, rfl, hm⟩ := ih
      refine ⟨m + 1, ?_, fun i hi => ?_⟩
      · rw [hst.2, hps _ ((H.Q_pow m _).2 ((H.Qa k).2 (H.KQ k hk))) hst.1, pow_succ',
          Perm.mul_apply]; rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hm i hi
        · exact hst.1
  obtain ⟨m, rfl, hm⟩ := hgen
  exact (H.hit_eq_of hk hz hm).2.symm

/-- Conversely the chain reaches the first hit. -/
theorem HitHyp.chain_hit (H : HitHyp a p K Q) {ps : X → X}
    (hps : ∀ x, Q x → ¬ K x → ps x = p x) {k : X} (hk : K k) :
    Relation.ReflTransGen (fun e e' => ¬ K e ∧ e' = a (ps e)) (a k) (hit a p K k) := by
  rw [H.hit_eq hk]
  have : ∀ i ≤ hitIdx a p K k, Relation.ReflTransGen (fun e e' => ¬ K e ∧ e' = a (ps e)) (a k)
      (((a * p) ^ i) (a k)) := by
    intro i hi
    induction i with
    | zero => exact .refl
    | succ i ih =>
      refine (ih (by omega)).tail ⟨H.not_mem_lt hk (by omega), ?_⟩
      rw [hps _ ((H.Q_pow i _).2 ((H.Qa k).2 (H.KQ k hk))) (H.not_mem_lt hk (by omega)),
        pow_succ', Perm.mul_apply]; rfl
  exact this _ le_rfl

end Hit

end Pca.MapFacts
