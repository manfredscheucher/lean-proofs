/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): a source of `A|_Q` gives a triangle with a side on `L`

FROS (end of the proof of Lemma 2): "Every source gives rise to a triangle with an edge on `L`
which can be flipped." A **source** (`SourceV`) is a vertex `x` of `Q` that is the first crossing
on both chords through it: the forward darts `wa`, `wb` arriving at `x` are foot darts
(`σ wa, σ wb ∈ L`).

Graph language (`sourceTri_of_source`): the region bounded by `wa`, `wb` and the piece of `L`
between the feet is the normalized cut of `root (straight wa) + root (straight wb)`. The cell `g`
of `wa` in the angle between `wa` and `wb` has value `1` (the other three cells at `x` have value
`0`, by walking along the chord of `wa` to `R`). Its side after the `L`-dart `d` at the foot of `wb`
is `wa`: otherwise it is an `R`-dart (value `0`) or a chord dart whose chord passes no segment of
the region on its way to `R` (value `0`) -- FROS: a chord starting between the feet would have to
leave the region through `wa` or `wb`. So `g` is the triangle `d, wa, α wb` with apex `x`.
-/
import Pca.FlipGraph.ClaimA

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- A **source** of the digraph `A|_Q`: a vertex of `Q` whose arriving forward darts start at `L`
(it is the first crossing on both chords through it). -/
def SourceV (x : A.Crossing) : Prop :=
  Λ.IsVertex x ∧ ∀ w, Λ.Fwd w → A.crossingOf (A.α w) = x → Λ.L (A.σ w)

variable {Λ}

theorem isTriangle_of {d : D} (h3 : A.φ (A.φ (A.φ d)) = d) (h1 : A.φ d ≠ d)
    (h2 : A.φ (A.φ d) ≠ d) : A.IsTriangle (A.cellOf d) := by
  unfold Arrangement.IsTriangle Arrangement.IsKCell
  rw [A.size_cellOf]
  have hle : period A.φ d ≤ 3 := Nat.find_min' _ ⟨by norm_num, by simpa using h3⟩
  have hpos := period_pos A.φ d
  have hit := iterate_period A.φ d
  rcases (show period A.φ d = 1 ∨ period A.φ d = 2 ∨ period A.φ d = 3 by omega) with h | h | h
  · rw [h] at hit; exact absurd (by simpa using hit) h1
  · rw [h] at hit; exact absurd (by simpa using hit) h2
  · exact h

theorem Fwd.of_straight {w : D} (h : Λ.Fwd (A.straight w)) (hc : Λ.Chord w) : Λ.Fwd w := by
  obtain ⟨k, hk, hR⟩ := h.2
  refine ⟨hc, k + 1, fun i hi => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0]; simpa using hc
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ_apply']; exact hk i' (by omega)
  · rw [pow_succ_apply']; exact hR

/-- A forward dart gives a chord from its own dart to `R`. -/
theorem walk_to_R' {y : D} {m : ℕ} (hc : ∀ i ≤ m, Λ.Chord ((A.straight ^ i) y))
    (hR : Λ.R (A.σ (A.α ((A.straight ^ m) y)))) {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2}
    (hr : IsCut c r) (hn : Norm Λ r) (hR0 : c (A.segmentOf (A.σ (A.α ((A.straight ^ m) y)))) = 0) :
    r (A.cellOf y) = ∑ t ∈ range m, c (A.segmentOf (A.σ (A.α ((A.straight ^ t) y)))) := by
  have h1 := cut_pow hr y m
  rw [← cellOf_σα, norm_R Λ hr hn hR hR0] at h1
  have key : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact key _ _ h1

/-- Two chord darts of one curve at a crossing make it a vertex. -/
theorem isVertex_of {y : D} (h1 : Λ.Chord y) (h2 : Λ.Chord (A.σ (A.σ y))) :
    Λ.IsVertex (A.crossingOf y) := by
  intro v hv
  rw [Arrangement.mem_darts_crossingOf] at hv
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact h1
  · exact ⟨by rw [A.cellOf_σ]; exact h1.2, by rw [← A.cellOf_σ]; exact h2.1⟩
  · exact h2
  · refine ⟨?_, ?_⟩
    · rw [A.cellOf_σ]; exact h2.2
    · rw [← A.cellOf_σ, A.σ_σ_σ_σ]; exact h1.1

/-- The crossing passed by a chord at an inner crossing is a vertex. -/
theorem isVertex_passed {y : D} (h1 : Λ.Chord y) (h2 : Λ.Chord (A.straight y)) :
    Λ.IsVertex (A.crossingOf (A.straight y)) := by
  refine isVertex_of h2 ?_
  rw [A.straight_apply, A.σ_σ_σ_σ]; exact chord_α h1

theorem fwd_or_σσ (hs : Λ.Sep) (ht : Λ.Transversal) {y : D} (h1 : Λ.Chord y)
    (h2 : Λ.Chord (A.σ (A.σ y))) : Λ.Fwd y ∨ Λ.Fwd (A.σ (A.σ y)) := by
  rcases fwd_or hs ht h1 with h | h
  · exact Or.inl h
  · right
    have e : A.σ (A.σ y) = A.straight (A.α y) := by rw [A.straight_apply, A.α_α]
    rw [e] at h2 ⊢; exact h.straight h2

/-- A foot dart is not a vertex dart: its crossing is on `S`. -/
theorem foot_not_vertex {w : D} (hw : Λ.L (A.σ w)) : ¬ Λ.IsVertex (A.crossingOf w) := fun hv =>
  (show Λ.Bd _ from Or.inl hw).not_chord (hv _ (by
    rw [Arrangement.mem_darts_crossingOf]; simp))

/-- **The triangle at a source** (one of the two rotations at `x`). -/
theorem tri_case (hs : Λ.Sep) (ht : Λ.Transversal) {wa wb : D} (ha : Λ.Fwd wa) (hb : Λ.Fwd wb)
    (hfa : Λ.L (A.σ wa)) (hfb : Λ.L (A.σ wb)) (hab : A.curve wa ≠ A.curve wb)
    (hrot : A.σ (A.α wa) = A.α wb) (hv : Λ.IsVertex (A.crossingOf (A.α wa))) :
    Λ.SourceTri (A.σ wb) := by
  classical
  have haS : A.curve wa ≠ Λ.S := fun h => S_not_chord hs h ha.1
  have hbS : A.curve wb ≠ Λ.S := fun h => S_not_chord hs h hb.1
  obtain ⟨ma, hma, hRa⟩ := ha.2
  obtain ⟨mb, hmb, hRb⟩ := hb.2
  have Ca : Λ.IsChord wa ma := ⟨hfa, hma, hRa⟩
  have Cb : Λ.IsChord wb mb := ⟨hfb, hmb, hRb⟩
  have hma1 : 1 ≤ ma := by
    by_contra h0
    have : ma = 0 := by omega
    subst this
    have hc1 : Λ.Chord (A.straight wa) := by
      have := hv (A.σ (A.σ (A.α wa))) (by rw [Arrangement.mem_darts_crossingOf]; simp)
      rwa [← A.straight_apply] at this
    exact bd_next_not (Or.inr (by simpa using hRa)) hc1
  have hmb1 : 1 ≤ mb := by
    by_contra h0
    have : mb = 0 := by omega
    subst this
    have hx : A.crossingOf (A.α wb) = A.crossingOf (A.α wa) := by
      rw [← hrot, A.crossingOf_σ]
    have hc1 : Λ.Chord (A.straight wb) := by
      have := hv (A.σ (A.σ (A.α wb))) (by rw [← hx, Arrangement.mem_darts_crossingOf]; simp)
      rwa [← A.straight_apply] at this
    exact bd_next_not (Or.inr (by simpa using hRb)) hc1
  set ua := A.straight wa
  set ub := A.straight wb
  set x := A.crossingOf (A.α wa)
  have hxa : A.crossingOf ua = x := by simp only [ua, x, A.straight_apply, A.crossingOf_σσ]
  have hxb : A.crossingOf ub = x := by
    simp only [ub, x, A.straight_apply, A.crossingOf_σσ]; rw [← hrot, A.crossingOf_σ]
  -- the rotation at `x`: `α wa, α wb, ua, ub`
  have hσua : A.σ ua = ub := by
    simp only [ua, ub, A.straight_apply]; rw [← hrot]
  have hσub : A.σ ub = A.α wa := by
    rw [← hσua]; simp only [ua, A.straight_apply, A.σ_σ_σ_σ]
  -- the chain and its cut
  have hua : ua = (A.straight ^ 1) wa := by simp [ua]
  have hub : ub = (A.straight ^ 1) wb := by simp [ub]
  have ca1 : ∀ i ≤ 1, Λ.Chord ((A.straight ^ i) wa) := Ca.chord' hma1
  have cb1 : ∀ i ≤ 1, Λ.Chord ((A.straight ^ i) wb) := Cb.chord' hmb1
  set C : A.Segment → ZMod 2 := Λ.root ua + Λ.root ub with hC
  have hev : IsEven C := fun y => by
    rw [hC, bd_add, hua, hub, bd_root hfa ca1, bd_root hfb cb1, ← hua, ← hub, hxa, hxb]
    have key : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
    exact key _ _
  have hsupp : Supp Λ C := by
    rw [hC, hua, hub]; exact (root_supp hfa ca1).add Λ (root_supp hfb cb1)
  obtain ⟨r, hr, hn⟩ := exists_norm Λ hev hsupp
  have hCR : ∀ v, Λ.R v → C (A.segmentOf v) = 0 := fun v hv' => by
    rw [hC, Pi.add_apply, hua, hub, root_R hfa ca1 hv', root_R hfb cb1 hv', add_zero]
  -- values of the chain near `x`
  have hCother : ∀ v, Λ.Chord v → C (A.segmentOf v) ≠ 0 →
      v = wa ∨ v = A.α wa ∨ v = wb ∨ v = A.α wb := by
    intro v hvc hne
    rw [hC, Pi.add_apply, hua, hub] at hne
    by_cases h1 : Λ.root ((A.straight ^ 1) wa) (A.segmentOf v) = 0
    · rw [h1, zero_add] at hne
      rcases root_ne_zero hfb cb1 hne with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
      · have : i = 0 := by omega
        subst this; simp only [pow_zero, Perm.one_apply] at e
        rcases e with e | e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr e))
      · exfalso
        apply (show Λ.Bd _ from Or.inl (L_of_lt_lidx hfb hi)).not_chord
        rcases e with e | e
        · rw [← e]; exact hvc
        · rw [← A.α_α ((A.straight ^ i) Λ.base), ← e]; exact chord_α hvc
    · rcases root_ne_zero hfa ca1 h1 with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
      · have : i = 0 := by omega
        subst this; simp only [pow_zero, Perm.one_apply] at e
        rcases e with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exfalso
        apply (show Λ.Bd _ from Or.inl (L_of_lt_lidx hfa hi)).not_chord
        rcases e with e | e
        · rw [← e]; exact hvc
        · rw [← A.α_α ((A.straight ^ i) Λ.base), ← e]; exact chord_α hvc
  -- (passed zero) a forward chord walk avoiding `wa`, `wb` passes no segment of the chain
  have passed0 : ∀ {y : D} {m : ℕ}, Λ.Fwd y → (∀ i ≤ m, Λ.Chord ((A.straight ^ i) y)) →
      (∀ s ≤ m, (A.straight ^ s) y ≠ wa ∧ (A.straight ^ s) y ≠ wb) →
      ∀ s < m, C (A.segmentOf (A.σ (A.α ((A.straight ^ s) y)))) = 0 := by
    intro y m hy hc havoid s hsm
    by_contra hne
    have hvc : Λ.Chord (A.σ (A.α ((A.straight ^ s) y))) :=
      ⟨by rw [cellOf_σα]; exact (hc s hsm.le).1,
        by rw [cellOf_ασα, ← Walk.pow_succ_apply]; exact (hc (s + 1) hsm).1⟩
    have hX : Λ.IsVertex (A.crossingOf ((A.straight ^ (s + 1)) y)) := by
      rw [Walk.pow_succ_apply]
      exact isVertex_passed (hc s hsm.le) (by rw [← Walk.pow_succ_apply]; exact hc _ hsm)
    have hXe := crossingOf_passed (A := A) y s
    have hfw : Λ.Fwd ((A.straight ^ (s + 1)) y) := hy.pow fun i hi => hc i (by omega)
    have hcurve : A.curve ((A.straight ^ (s + 1)) y) = A.curve y := Walk.curve_pow A y _
    rcases hCother _ hvc hne with e | e | e | e
    · exact foot_not_vertex hfa (by rw [← e, hXe]; exact hX)
    · -- the walk passes `x` on the curve of `wa` or `wb`
      have hx' : A.crossingOf ((A.straight ^ (s + 1)) y) = x := by rw [← hXe, e]
      have key := A.mem_curves_crossingOf ((A.straight ^ (s + 1)) y)
      rw [hx'] at key
      have hxcur : Arrangement.Crossing.curves A x = {A.curve wa, A.curve wb} := by
        rw [show x = A.crossingOf (A.α wa) from rfl, A.curves_crossingOf, hrot, A.curve_α,
          A.curve_α]
      rw [hxcur, mem_insert, mem_singleton] at key
      rcases key with k | k
      · rcases eq_or_σσ (hx'.trans hxa.symm) (by rw [k]; exact (A.curve_straight _).symm) with e' | e'
        · apply (havoid s hsm.le).1
          apply A.straight.injective; rw [← Walk.pow_succ_apply]; exact e'
        · have : A.σ (A.σ ua) = A.α wa := by simp only [ua, A.straight_apply, A.σ_σ_σ_σ]
          rw [this] at e'
          rw [e'] at hfw
          exact (fwd_α_iff hs ht ha.1).1 hfw ha
      · rcases eq_or_σσ (hx'.trans hxb.symm) (by rw [k]; exact (A.curve_straight _).symm) with e' | e'
        · apply (havoid s hsm.le).2
          apply A.straight.injective; rw [← Walk.pow_succ_apply]; exact e'
        · have : A.σ (A.σ ub) = A.α wb := by simp only [ub, A.straight_apply, A.σ_σ_σ_σ]
          rw [this] at e'
          rw [e'] at hfw
          exact (fwd_α_iff hs ht hb.1).1 hfw hb
    · exact foot_not_vertex hfb (by rw [← e, hXe]; exact hX)
    · have hx' : A.crossingOf ((A.straight ^ (s + 1)) y) = x := by
        rw [← hXe, e, ← hxb]; simp only [ub, A.straight_apply, A.crossingOf_σσ]
      have key := A.mem_curves_crossingOf ((A.straight ^ (s + 1)) y)
      rw [hx'] at key
      have hxcur : Arrangement.Crossing.curves A x = {A.curve wa, A.curve wb} := by
        rw [show x = A.crossingOf (A.α wa) from rfl, A.curves_crossingOf, hrot, A.curve_α,
          A.curve_α]
      rw [hxcur, mem_insert, mem_singleton] at key
      rcases key with k | k
      · rcases eq_or_σσ (hx'.trans hxa.symm) (by rw [k]; exact (A.curve_straight _).symm) with e' | e'
        · apply (havoid s hsm.le).1
          apply A.straight.injective; rw [← Walk.pow_succ_apply]; exact e'
        · have : A.σ (A.σ ua) = A.α wa := by simp only [ua, A.straight_apply, A.σ_σ_σ_σ]
          rw [this] at e'
          rw [e'] at hfw
          exact (fwd_α_iff hs ht ha.1).1 hfw ha
      · rcases eq_or_σσ (hx'.trans hxb.symm) (by rw [k]; exact (A.curve_straight _).symm) with e' | e'
        · apply (havoid s hsm.le).2
          apply A.straight.injective; rw [← Walk.pow_succ_apply]; exact e'
        · have : A.σ (A.σ ub) = A.α wb := by simp only [ub, A.straight_apply, A.σ_σ_σ_σ]
          rw [this] at e'
          rw [e'] at hfw
          exact (fwd_α_iff hs ht hb.1).1 hfw hb
  -- a forward walk that contains a foot dart starts there
  have avoid : ∀ {y : D} {m : ℕ}, (∀ i ≤ m, Λ.Chord ((A.straight ^ i) y)) → y ≠ wa → y ≠ wb →
      ∀ s ≤ m, (A.straight ^ s) y ≠ wa ∧ (A.straight ^ s) y ≠ wb := by
    intro y m hc h1 h2 s hs'
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simpa using ⟨h1, h2⟩
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      rw [Walk.pow_succ_apply]
      exact ⟨fun e => not_chord_before_foot hfa e (hc s' (by omega)),
        fun e => not_chord_before_foot hfb e (hc s' (by omega))⟩
  -- (1) the cell of `ua` has value `0`
  have r_ua : r (A.cellOf ua) = 0 := by
    have hc' : ∀ i ≤ ma - 1, Λ.Chord ((A.straight ^ i) ua) := fun i hi => by
      rw [← pow_succ_apply']; exact hma _ (by omega)
    have hR' : Λ.R (A.σ (A.α ((A.straight ^ (ma - 1)) ua))) := by
      rw [← pow_succ_apply', show ma - 1 + 1 = ma by omega]; exact hRa
    rw [walk_to_R' hc' hR' hr hn (hCR _ hR')]
    refine sum_eq_zero fun t ht => passed0 (ha.straight (by simpa using ca1 1 le_rfl)) hc'
      (fun s hs' => ⟨fun e => ?_, fun e => ?_⟩) t (mem_range.1 ht)
    · rw [← pow_succ_apply'] at e
      have := dart_inj Ca.lt_period (show s + 1 ≤ ma by omega) (Nat.zero_le _)
        (by rw [e, pow_zero, Perm.one_apply])
      omega
    · have := congrArg A.curve e
      rw [Walk.curve_pow, show A.curve ua = A.curve wa from A.curve_straight wa] at this
      exact hab this
  have hCua : C (A.segmentOf ua) = 0 := by
    rw [hC, Pi.add_apply, hua, root_self hfa hma Ca.lt_period hma1 hma1, if_neg (lt_irrefl _),
      zero_add, hub, root_other_chord hs hfb cb1 (by rw [Walk.curve_pow]; exact hab)
        (hma 1 hma1)]
  have hCub : C (A.segmentOf ub) = 0 := by
    rw [hC, Pi.add_apply, hub, root_self hfb hmb Cb.lt_period hmb1 hmb1, if_neg (lt_irrefl _),
      add_zero, hua, root_other_chord hs hfa ca1 (by rw [Walk.curve_pow]; exact hab.symm)
        (hmb 1 hmb1)]
  have hCwa : C (A.segmentOf wa) = 1 := by
    rw [hC, Pi.add_apply, hua, hub, root_other_chord hs hfb cb1 hab ha.1, add_zero]
    have := root_self hfa hma Ca.lt_period hma1 (Nat.zero_le _) (Λ := Λ)
    simp only [pow_zero, Perm.one_apply] at this
    rw [this]; norm_num
  -- (2) around `x`
  have r_ub : r (A.cellOf ub) = 0 := by rw [← hσua, cut_σ hr, r_ua, hCua, add_zero]
  have r_αwa : r (A.cellOf (A.α wa)) = 0 := by rw [← hσub, cut_σ hr, r_ub, hCub, add_zero]
  have r_g : r (A.cellOf wa) = 1 := by
    have := cut_α hr wa
    rw [r_αwa, hCwa] at this
    have key : ∀ a : ZMod 2, 0 = a + 1 → a = 1 := by decide
    exact key _ this
  -- (3) the side after `d`
  set d := A.σ wb
  have hdL : Λ.L d := hfb
  have hφwa : A.φ wa = A.α wb := hrot
  have hφαwb : A.φ (A.α wb) = d := by rw [A.φ_apply, A.α_α]
  have hgd : A.cellOf (A.φ d) = A.cellOf wa := by
    rw [A.cellOf_φ, ← hφαwb, A.cellOf_φ, ← hφwa, A.cellOf_φ]
  have hX'' : ¬ Λ.IsVertex (A.crossingOf (A.φ d)) := by
    intro hv'
    rw [A.crossingOf_φ] at hv'
    exact (show Λ.Bd _ from Or.inl hdL).out.2 (hv' (A.α d) (Orbit.mem_darts.2 rfl)).1
  have hxv : Λ.IsVertex x := hv
  have hφd : A.φ d = wa := by
    by_contra hne
    set t := A.φ d
    have hrt : r (A.cellOf t) = 1 := by rw [hgd]; exact r_g
    have ht_wb : t ≠ wb := fun e => by
      have h1 : A.crossingOf t = A.crossingOf (A.α d) := A.crossingOf_φ d
      rw [e, show A.crossingOf wb = A.crossingOf d from (A.crossingOf_σ wb).symm] at h1
      exact A.crossingOf_α_ne d h1.symm
    have htx : A.crossingOf t ≠ x := fun e => hX'' (by rw [e]; exact hxv)
    have htαwa : t ≠ A.α wa := fun e => htx (by rw [e])
    have htαwb : t ≠ A.α wb := fun e => htx (by rw [e, ← hxb]; simp [ub, A.straight_apply,
      A.crossingOf_σσ])
    have hCt : C (A.segmentOf t) = 0 := by
      by_contra h0
      by_cases htc : Λ.Chord t
      · rcases hCother t htc h0 with e | e | e | e
        · exact hne e
        · exact htαwa e
        · exact ht_wb e
        · exact htαwb e
      · -- `t` is a boundary dart on `R`, its value is `0`
        have hq : Λ.Q (A.cellOf t) := by rw [hgd]; exact ha.1.1
        have hq' : ¬ Λ.Q (A.cellOf (A.α t)) := fun h => htc ⟨hq, h⟩
        rcases Λ.bd t hq hq' with h | h
        · exact absurd (Λ.L_curve t h) (by
            rw [show t = A.σ (A.α d) from rfl]
            have := A.isArrangement.curve_σ (A.α d)
            rwa [A.curve_α, Λ.L_curve d hdL] at this)
        · exact h0 (hCR t h)
    by_cases htc : Λ.Chord t
    · rcases fwd_or hs ht htc with hf | hf
      · obtain ⟨m, hm, hRm⟩ := hf.2
        rw [walk_to_R' hm hRm hr hn (hCR _ hRm),
          sum_eq_zero fun s hs' => passed0 hf hm (avoid hm hne ht_wb) s (mem_range.1 hs')] at hrt
        exact absurd hrt (by decide)
      · obtain ⟨m, hm, hRm⟩ := hf.2
        have h0 := walk_to_R' hm hRm hr hn (hCR _ hRm)
        rw [sum_eq_zero fun s hs' => passed0 hf hm (avoid hm (fun e => htαwa (by
          rw [← e, A.α_α])) (fun e => htαwb (by rw [← e, A.α_α])) ) s (mem_range.1 hs')] at h0
        have := cut_α hr (A.α t)
        rw [A.α_α, h0, zero_add, show A.segmentOf (A.α t) = A.segmentOf t from
          Orbit.mk_eq_mk.2 (Perm.SameCycle.refl _ _ |>.trans ⟨1, by simp [A.α_α]⟩), hCt] at this
        rw [this] at hrt
        exact absurd hrt (by decide)
    · have hq : Λ.Q (A.cellOf t) := by rw [hgd]; exact ha.1.1
      have hq' : ¬ Λ.Q (A.cellOf (A.α t)) := fun h => htc ⟨hq, h⟩
      have hR : Λ.R t := by
        rcases Λ.bd t hq hq' with h | h
        · exact absurd (Λ.L_curve t h) (by
            rw [show t = A.σ (A.α d) from rfl]
            have := A.isArrangement.curve_σ (A.α d)
            rwa [A.curve_α, Λ.L_curve d hdL] at this)
        · exact h
      rw [norm_R Λ hr hn hR (hCR t hR)] at hrt
      exact absurd hrt (by decide)
  -- (4) the triangle
  refine ⟨hdL, isTriangle_of ?_ ?_ ?_, ?_⟩
  · rw [hφd, hφwa, hφαwb]
  · intro e
    have := A.crossingOf_φ_ne d
    rw [e] at this; exact this rfl
  · rw [hφd, hφwa]
    intro e
    have := congrArg A.curve e
    rw [A.curve_α, show A.curve d = Λ.S from Λ.L_curve d hdL] at this
    exact hbS this
  · rw [hφd, hφwa]
    have : A.crossingOf (A.α wb) = x := by
      rw [← hxb]; simp only [ub, A.straight_apply, A.crossingOf_σσ]
    rw [this]; exact hxv

/-- **A source gives a source triangle.** -/
theorem sourceTri_of_source (hs : Λ.Sep) (ht : Λ.Transversal) {x : A.Crossing}
    (hx : Λ.SourceV x) : ∃ d, Λ.SourceTri d := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Λ.SourceV (A.crossingOf y) at hx
  obtain ⟨hv, hsrc⟩ := hx
  have hdart : ∀ v, A.crossingOf v = A.crossingOf y → Λ.Chord v := fun v e =>
    hv v (Orbit.mem_darts.2 e)
  -- the arriving forward dart of each curve at `x`
  have arrive : ∀ v, A.crossingOf v = A.crossingOf y →
      ∃ w, Λ.Fwd w ∧ A.crossingOf (A.α w) = A.crossingOf y ∧ A.curve w = A.curve v := by
    intro v e
    have e2 : A.crossingOf (A.σ (A.σ v)) = A.crossingOf y := by rw [A.crossingOf_σσ, e]
    rcases fwd_or_σσ hs ht (hdart v e) (hdart _ e2) with hf | hf
    · -- `v` leaves forward; the dart before it arrives
      refine ⟨A.α (A.σ (A.σ v)), ?_, by rw [A.α_α, e2], by rw [A.curve_α, A.curve_σσ]⟩
      have hst : A.straight (A.α (A.σ (A.σ v))) = v := by
        rw [A.straight_apply, A.α_α, A.σ_σ_σ_σ]
      exact Fwd.of_straight (by rw [hst]; exact hf) (chord_α (hdart _ e2))
    · refine ⟨A.α v, ?_, by rw [A.α_α, e], by rw [A.curve_α]⟩
      have hst : A.straight (A.α v) = A.σ (A.σ v) := by rw [A.straight_apply, A.α_α]
      exact Fwd.of_straight (by rw [hst]; exact hf) (chord_α (hdart v e))
  obtain ⟨wa, ha, hxa, hca⟩ := arrive y rfl
  obtain ⟨wb, hb, hxb, hcb⟩ := arrive (A.σ y) (A.crossingOf_σ y)
  have hab : A.curve wa ≠ A.curve wb := by
    rw [hca, hcb]; exact (A.isArrangement.curve_σ y).symm
  have hfa := hsrc wa ha hxa
  have hfb := hsrc wb hb hxb
  -- the rotation at `x`
  have hxab : A.crossingOf (A.α wb) = A.crossingOf (A.α wa) := hxb.trans hxa.symm
  have hcα : A.curve (A.α wb) ≠ A.curve (A.α wa) := by rw [A.curve_α, A.curve_α]; exact hab.symm
  rcases eq_σ_or_σσσ hxab hcα with e | e
  · exact ⟨_, tri_case hs ht ha hb hfa hfb hab e.symm (by rw [hxa]; exact hv)⟩
  · have e' : A.σ (A.α wb) = A.α wa := by rw [e, A.σ_σ_σ_σ]
    exact ⟨_, tri_case hs ht hb ha hfb hfa hab.symm e' (by rw [hxb]; exact hv)⟩

end Lens

end Pca.FlipGraph
