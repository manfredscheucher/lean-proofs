/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the arcs of a lens, oriented from `L` to `R`

FROS (proof of Lemma 2): "We orient all arcs of `Q` from `L` to `R`". Graph language: a chord dart
`y` is **forward** (`Fwd`) if walking straight from `y` the chord ends on `R`. Under the separation
hypothesis `Sep` (no chord runs on a curve of `L` or `R`; true for the lens of two curves and for
the first-curve lens) every chord ends on `L` or `R` (`ends`: it crosses the curve `S` of `L`), at
one end only (`not_both`), so with `Transversal` exactly one of `y`, `α y` is forward
(`fwd_α_iff`). Every forward dart is reached from its **foot dart** `z₀` (the first dart of the
chord, `σ z₀ ∈ L`) by a straight walk of chord darts (`exists_foot`); along a chord the darts, their
segments and their crossings are distinct (`chord_lt_period`, `seg_inj`, `cross_inj`).
-/
import Pca.FlipGraph.Chain

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Arrangement'

variable {A : Arrangement n D}

theorem cellOf_σα (w : D) : A.cellOf (A.σ (A.α w)) = A.cellOf w := by rw [A.cellOf_σ, A.α_α]

theorem cellOf_ασα (w : D) : A.cellOf (A.α (A.σ (A.α w))) = A.cellOf (A.straight w) := by
  rw [← A.cellOf_σ, A.straight_apply]

theorem straight_α_straight (w : D) : A.straight (A.α (A.straight w)) = A.α w := by
  rw [A.straight_apply, A.straight_apply, A.α_α, A.σ_σ_σ_σ]

theorem pow_succ_apply' (w : D) (i : ℕ) :
    (A.straight ^ (i + 1)) w = (A.straight ^ i) (A.straight w) := by
  rw [pow_succ, Perm.mul_apply]

/-- Walking back along `α` of a straight walk. -/
theorem pow_α_pow (w : D) {t j : ℕ} (h : t ≤ j) :
    (A.straight ^ t) (A.α ((A.straight ^ j) w)) = A.α ((A.straight ^ (j - t)) w) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Walk.pow_succ_apply, ih (by omega)]
    obtain ⟨s, hs⟩ : ∃ s, j - t = s + 1 := ⟨j - t - 1, by omega⟩
    rw [hs, Walk.pow_succ_apply, straight_α_straight, show j - (t + 1) = s by omega]

/-- Two darts of one straight orbit at the same crossing are equal. -/
theorem eq_of_sameCycle_crossingOf {a b : D} (hs : A.straight.SameCycle a b)
    (hx : A.crossingOf a = A.crossingOf b) : a = b := by
  have hc : A.curve b = A.curve a := by
    obtain ⟨j, -, rfl⟩ := Walk.exists_idx A hs; exact Walk.curve_pow A a j
  rcases List.mem_cons.1 ((A.crossingOf_eq_iff).1 hx) with h | h
  · exact h.symm
  rcases List.mem_cons.1 h with h | h
  · exact absurd (h ▸ hc) (A.isArrangement.curve_σ a)
  rcases List.mem_cons.1 h with h | h
  · exact absurd (h ▸ hs) (A.not_sameCycle_straight_σσ a)
  · rw [List.mem_singleton] at h
    rw [h, A.curve_σσσ] at hc
    exact absurd hc (A.isArrangement.curve_σ a)

end Arrangement'

open Arrangement'

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- **Separation**: no chord dart runs on the curve of a dart of `L` or `R`. -/
def Sep : Prop := ∀ y z, Λ.Chord y → (Λ.L z ∨ Λ.R z) → A.curve y ≠ A.curve z

/-- A boundary dart of the lens (in `L` or `R`). -/
def Bd (y : D) : Prop := Λ.L y ∨ Λ.R y

/-- `y` is a **forward** chord dart: its chord, walked from `y`, ends on `R`. -/
def Fwd (y : D) : Prop := Λ.Chord y ∧ Λ.EndsOn Λ.R y

/-- The base dart of the run `L`. -/
noncomputable def base : D := Classical.choose Λ.L_run

/-- The length of the run `L`. -/
noncomputable def kL : ℕ := Classical.choose (Classical.choose_spec Λ.L_run)

theorem L_iff' (y : D) : Λ.L y ↔ ∃ i ≤ Λ.kL, y = (A.straight ^ i) Λ.base :=
  Classical.choose_spec (Classical.choose_spec Λ.L_run) y

theorem base_L : Λ.L Λ.base := (Λ.L_iff' _).2 ⟨0, Nat.zero_le _, by simp⟩

variable {Λ}

theorem Bd.out {z : D} (h : Λ.Bd z) : Λ.Q (A.cellOf z) ∧ ¬ Λ.Q (A.cellOf (A.α z)) :=
  h.elim (Λ.L_bd z) (Λ.R_bd z)

theorem Bd.not_chord {z : D} (h : Λ.Bd z) : ¬ Λ.Chord z := fun hc => h.out.2 hc.2

theorem chord_α {y : D} (hy : Λ.Chord y) : Λ.Chord (A.α y) := ⟨hy.2, by rw [A.α_α]; exact hy.1⟩

theorem chord_α_iff {y : D} : Λ.Chord (A.α y) ↔ Λ.Chord y :=
  ⟨fun h => by have := chord_α h; rwa [A.α_α] at this, chord_α⟩

/-- No dart of `S` is a chord dart. -/
theorem S_not_chord (hs : Λ.Sep) {z : D} (hz : A.curve z = Λ.S) : ¬ Λ.Chord z := fun hc =>
  hs z Λ.base hc (Or.inl Λ.base_L) (hz.trans (Λ.L_curve _ Λ.base_L).symm)

/-- After a boundary dart at the end, the walk leaves the chord. -/
theorem bd_next_not {w : D} (hb : Λ.Bd (A.σ (A.α w))) : ¬ Λ.Chord (A.straight w) := fun h =>
  hb.out.2 (by rw [cellOf_ασα]; exact h.1)

/-- A chord continues or ends at a boundary dart. -/
theorem chord_next (hs : Λ.Sep) {w : D} (hw : Λ.Chord w) :
    Λ.Chord (A.straight w) ∨ Λ.Bd (A.σ (A.α w)) := by
  by_cases h1 : Λ.Q (A.cellOf (A.straight w))
  · by_cases h2 : Λ.Q (A.cellOf (A.α (A.straight w)))
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd (A.curve_straight w).symm (hs w _ hw (Λ.bd _ h1 h2))
  · exact Or.inr (Λ.bd _ (by rw [cellOf_σα]; exact hw.1) (by rw [cellOf_ασα]; exact h1))

/-- **Every chord ends** (on `L` or on `R`): it crosses `S`, whose darts are not chord darts. -/
theorem ends (hs : Λ.Sep) {y : D} (hy : Λ.Chord y) : Λ.EndsOn Λ.L y ∨ Λ.EndsOn Λ.R y := by
  classical
  have ex : ∃ j, ¬ Λ.Chord ((A.straight ^ j) y) := by
    by_contra hall
    push_neg at hall
    have hc : A.curve y ≠ Λ.S := fun h => S_not_chord hs h hy
    obtain ⟨i, hi⟩ := card_pos.1 (show 0 < (Walk.flipsOn A Λ.S y).card by
      rw [Walk.card_flipsOn A hc]; norm_num)
    rw [Walk.mem_flipsOn] at hi
    have hcw := hall i
    have hcw' := hall (i + 1)
    rw [Walk.pow_succ_apply] at hcw'
    exact S_not_chord hs hi.2
      ⟨by rw [cellOf_σα]; exact hcw.1, by rw [cellOf_ασα]; exact hcw'.1⟩
  have h0 : Nat.find ex ≠ 0 := fun h => by
    have := Nat.find_spec ex; rw [h, pow_zero, Perm.one_apply] at this; exact this hy
  obtain ⟨k, hk⟩ : ∃ k, Nat.find ex = k + 1 := ⟨Nat.find ex - 1, by omega⟩
  have hall : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) y) := fun i hi =>
    not_not.1 (Nat.find_min ex (by omega))
  have hnext : ¬ Λ.Chord (A.straight ((A.straight ^ k) y)) := by
    rw [← Walk.pow_succ_apply, ← hk]; exact Nat.find_spec ex
  rcases chord_next hs (hall k le_rfl) with h | h
  · exact absurd h hnext
  · rcases h with h | h
    · exact Or.inl ⟨k, hall, h⟩
    · exact Or.inr ⟨k, hall, h⟩

/-- The end index of a chord is determined. -/
theorem endsOn_idx {P P' : D → Prop} (hP : ∀ z, P z → Λ.Bd z) (hP' : ∀ z, P' z → Λ.Bd z)
    {y : D} {k k' : ℕ} (hk : ∀ i ≤ k, Λ.Chord ((A.straight ^ i) y))
    (hkP : P (A.σ (A.α ((A.straight ^ k) y)))) (hk' : ∀ i ≤ k', Λ.Chord ((A.straight ^ i) y))
    (hkP' : P' (A.σ (A.α ((A.straight ^ k') y)))) : k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · have := hk' (k + 1) h
    rw [Walk.pow_succ_apply] at this
    exact absurd this (bd_next_not (hP _ hkP))
  · exact h
  · have := hk (k' + 1) h
    rw [Walk.pow_succ_apply] at this
    exact absurd this (bd_next_not (hP' _ hkP'))

/-- A chord does not end on both arcs. -/
theorem not_both {y : D} (hL : Λ.EndsOn Λ.L y) (hR : Λ.EndsOn Λ.R y) : False := by
  obtain ⟨k, hk, hkL⟩ := hL
  obtain ⟨k', hk', hkR⟩ := hR
  have := endsOn_idx (fun _ h => Or.inl h) (fun _ h => Or.inr h) hk hkL hk' hkR
  subst this
  exact Λ.disj _ ⟨hkL, hkR⟩

theorem fwd_α_iff (hs : Λ.Sep) (ht : Λ.Transversal) {y : D} (hy : Λ.Chord y) :
    Λ.Fwd (A.α y) ↔ ¬ Λ.Fwd y := by
  have e := ht y hy
  unfold Fwd
  rw [chord_α_iff]
  constructor
  · rintro ⟨-, h⟩ ⟨-, h'⟩
    exact not_both (e.2 h) h'
  · intro h
    refine ⟨hy, e.1 ?_⟩
    rcases ends hs hy with h' | h'
    · exact h'
    · exact absurd ⟨hy, h'⟩ h

theorem fwd_or (hs : Λ.Sep) (ht : Λ.Transversal) {y : D} (hy : Λ.Chord y) :
    Λ.Fwd y ∨ Λ.Fwd (A.α y) := by
  by_cases h : Λ.Fwd y
  · exact Or.inl h
  · exact Or.inr ((fwd_α_iff hs ht hy).2 h)

theorem Fwd.straight {y : D} (h : Λ.Fwd y) (hc : Λ.Chord (A.straight y)) :
    Λ.Fwd (A.straight y) := by
  obtain ⟨k, hk, hR⟩ := h.2
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    simp only [pow_zero, Perm.one_apply] at hR
    exact absurd hc (bd_next_not (Or.inr hR))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine ⟨hc, k', fun i hi => ?_, ?_⟩
    · rw [← pow_succ_apply']; exact hk _ (by omega)
    · rw [← pow_succ_apply']; exact hR

theorem Fwd.pow {y : D} (h : Λ.Fwd y) {j : ℕ} (hc : ∀ i ≤ j, Λ.Chord ((A.straight ^ i) y)) :
    Λ.Fwd ((A.straight ^ j) y) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Walk.pow_succ_apply]
    exact (ih fun i hi => hc i (by omega)).straight (by rw [← Walk.pow_succ_apply]; exact hc _ le_rfl)

/-- **The foot of a chord**: every forward dart is reached from the first dart `z₀` of its chord
(`σ z₀ ∈ L`) by chord darts. -/
theorem exists_foot (ht : Λ.Transversal) {y : D} (hy : Λ.Fwd y) :
    ∃ z₀ k, Λ.L (A.σ z₀) ∧ (∀ i ≤ k, Λ.Chord ((A.straight ^ i) z₀)) ∧ (A.straight ^ k) z₀ = y := by
  have hL : Λ.EndsOn Λ.L (A.α y) := by
    have := ht (A.α y) (chord_α hy.1); rw [A.α_α] at this; exact this.2 hy.2
  obtain ⟨k, hk, hkL⟩ := hL
  refine ⟨A.α ((A.straight ^ k) (A.α y)), k, hkL, fun i hi => ?_, ?_⟩
  · rw [pow_α_pow _ hi]; exact chord_α (hk _ (by omega))
  · rw [pow_α_pow _ le_rfl, Nat.sub_self, pow_zero, Perm.one_apply, A.α_α]

/-- A chord from its foot to its end on `R` is shorter than the period of the walk. -/
theorem chord_lt_period {z : D} {m : ℕ} (hm : ∀ i ≤ m, Λ.Chord ((A.straight ^ i) z))
    (hb : Λ.Bd (A.σ (A.α ((A.straight ^ m) z)))) : m < period A.straight z := by
  by_contra hle
  push_neg at hle
  have hp := period_pos A.straight z
  have h := hm (m + 1 - period A.straight z) (by omega)
  have e : (A.straight ^ (m + 1)) z = (A.straight ^ (m + 1 - period A.straight z)) z := by
    conv_lhs => rw [show m + 1 = (m + 1 - period A.straight z) + period A.straight z by omega]
    rw [pow_add, Perm.mul_apply, Walk.pow_period_apply]
  rw [← e, Walk.pow_succ_apply] at h
  exact bd_next_not hb h

/-- The darts of a chord are distinct. -/
theorem dart_inj {z : D} {m i j : ℕ} (hlt : m < period A.straight z) (hi : i ≤ m) (hj : j ≤ m)
    (h : (A.straight ^ i) z = (A.straight ^ j) z) : i = j :=
  Walk.pow_inj A (by omega) (by omega) h

/-- The segments of a chord are distinct. -/
theorem seg_inj {z : D} {m i j : ℕ} (hlt : m < period A.straight z) (hi : i ≤ m) (hj : j ≤ m)
    (h : A.segmentOf ((A.straight ^ i) z) = A.segmentOf ((A.straight ^ j) z)) : i = j := by
  rcases eq_or_eq_α_of_segmentOf h with h | h
  · exact dart_inj hlt hi hj h
  · exfalso
    have e : (A.straight ^ (i + j + 1)) z = A.σ (A.σ z) := by
      rw [show i + j + 1 = (j + 1) + i by omega, pow_add, Perm.mul_apply, h, Walk.pow_succ_apply,
        pow_α_pow _ le_rfl, Nat.sub_self, pow_zero, Perm.one_apply, A.straight_apply, A.α_α]
    exact A.not_sameCycle_straight_σσ z ⟨(i + j + 1 : ℕ), by rw [zpow_natCast]; exact e⟩

/-- The crossings of a chord are distinct. -/
theorem cross_inj {z : D} {m i j : ℕ} (hlt : m < period A.straight z) (hi : i ≤ m) (hj : j ≤ m)
    (h : A.crossingOf ((A.straight ^ i) z) = A.crossingOf ((A.straight ^ j) z)) : i = j := by
  refine dart_inj hlt hi hj (eq_of_sameCycle_crossingOf ?_ h)
  exact ⟨((j : ℤ) - i), by
    rw [← Perm.mul_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_add]; congr 1; ring_nf⟩

end Lens

end Pca.FlipGraph
