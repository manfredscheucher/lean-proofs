/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): FROS Claim A

FROS (proof of Lemma 2), Claim A: "If two oriented arcs `a` and `a'` intersect in two points `p`
and `q` such that `p` precedes `q` on `a`, then `p` precedes `q` on `a'`." Proof in FROS: the region
bounded by the subarcs of `a` and `a'` from `L` to their meeting point and the corresponding part
of `L`; `a'` enters it and cannot leave it to reach `R`.

Graph language (`claimA`): the region is the normalized cut of the even chain
`root yq + root uq` (`yq`, `uq` the forward darts of the two chords at `q`, the first point on
`a'`). Walking along `a` from `q` to `R` passes no segment of the chain (`a` meets `a'` only at `p`
and `q`), so the cells at `q` off the angle between the incoming arcs have value `0`; walking along
`a'` from `q` to `R` passes exactly one segment of the chain (at `p`, a segment of `a` before `q`),
so the end cell on `R` would have value `1`.

Tools: `IsChord` (a whole chord from its foot dart), `walk_to_R` (the value of a normalized cut at a
chord dart is the sum of the passed segments up to `R`), `pair_eq` (two curves cross only at two
crossings).
-/
import Pca.FlipGraph.Root

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- A whole **chord** from its foot dart `z` (`σ z ∈ L`), with darts `straight^i z`, `i ≤ m`, ending
on `R`. -/
structure IsChord (z : D) (m : ℕ) : Prop where
  foot : Λ.L (A.σ z)
  chord : ∀ i ≤ m, Λ.Chord ((A.straight ^ i) z)
  endR : Λ.R (A.σ (A.α ((A.straight ^ m) z)))

variable {Λ}

theorem IsChord.lt_period {z : D} {m : ℕ} (h : Λ.IsChord z m) : m < period A.straight z :=
  chord_lt_period h.chord (Or.inr h.endR)

theorem IsChord.chord' {z : D} {m : ℕ} (h : Λ.IsChord z m) {j : ℕ} (hj : j ≤ m) :
    ∀ i ≤ j, Λ.Chord ((A.straight ^ i) z) := fun i hi => h.chord i (by omega)

/-- The darts passed by a chord at its inner crossings are chord darts. -/
theorem IsChord.passed {z : D} {m : ℕ} (h : Λ.IsChord z m) {t : ℕ} (ht : t < m) :
    Λ.Chord (A.σ (A.α ((A.straight ^ t) z))) := by
  refine ⟨by rw [cellOf_σα]; exact (h.chord t ht.le).1, ?_⟩
  rw [cellOf_ασα, ← Walk.pow_succ_apply]; exact (h.chord (t + 1) ht).1

theorem crossingOf_passed (z : D) (t : ℕ) :
    A.crossingOf (A.σ (A.α ((A.straight ^ t) z))) = A.crossingOf ((A.straight ^ (t + 1)) z) := by
  rw [A.crossingOf_σ, crossingOf_α_pow]

/-- **Walk to `R`**: the value of a normalized cut at a dart of a chord is the sum of the segments
passed on the way to `R`. -/
theorem IsChord.walk_to_R {z : D} {m : ℕ} (h : Λ.IsChord z m) {c : A.Segment → ZMod 2}
    {r : A.Cell → ZMod 2} (hr : IsCut c r) (hn : Norm Λ r)
    (hR : c (A.segmentOf (A.σ (A.α ((A.straight ^ m) z)))) = 0) {j : ℕ} (hj : j ≤ m) :
    r (A.cellOf ((A.straight ^ j) z)) =
      ∑ t ∈ range (m - j), c (A.segmentOf (A.σ (A.α ((A.straight ^ (j + t)) z)))) := by
  have h1 := cut_pow hr ((A.straight ^ j) z) (m - j)
  rw [← Perm.mul_apply, ← pow_add, show m - j + j = m by omega, ← cellOf_σα,
    norm_R Λ hr hn h.endR hR] at h1
  have e : ∀ t, (A.straight ^ t) ((A.straight ^ j) z) = (A.straight ^ (j + t)) z := fun t => by
    rw [← Perm.mul_apply, ← pow_add, add_comm]
  simp only [e] at h1
  have key : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact key _ _ h1

/-- The crossing of two darts of distinct curves has exactly these curves. -/
theorem curves_eq_pair {x : A.Crossing} {a b : Fin n} (hab : a ≠ b)
    (ha : a ∈ Arrangement.Crossing.curves A x) (hb : b ∈ Arrangement.Crossing.curves A x) :
    Arrangement.Crossing.curves A x = {a, b} := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  change a ∈ Arrangement.Crossing.curves A (A.crossingOf y) at ha
  change b ∈ Arrangement.Crossing.curves A (A.crossingOf y) at hb
  change Arrangement.Crossing.curves A (A.crossingOf y) = _
  rw [A.curves_crossingOf] at ha hb ⊢
  have hσ := A.isArrangement.curve_σ y
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, hb]
  · rw [ha, hb, pair_comm]
  · exact absurd (ha.trans hb.symm) hab

/-- **Two curves cross at two crossings only.** -/
theorem pair_eq {a b : Fin n} (hab : a ≠ b) {p q x : A.Crossing} (hpq : p ≠ q)
    (hp : Arrangement.Crossing.curves A p = {a, b}) (hq : Arrangement.Crossing.curves A q = {a, b})
    (hx : Arrangement.Crossing.curves A x = {a, b}) : x = p ∨ x = q := by
  classical
  have h2 := A.card_curves_eq_pair a b hab
  by_contra hn
  push_neg at hn
  have hsub : ({p, q, x} : Finset A.Crossing) ⊆
      univ.filter (fun y : A.Crossing => Arrangement.Crossing.curves A y = {a, b}) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [mem_filter]
    rcases hy with rfl | rfl | rfl <;> simp_all
  have := card_le_card hsub
  rw [h2, card_insert_of_notMem (by simp [hpq, hn.1.symm]),
    card_insert_of_notMem (by simp [hn.2.symm]), card_singleton] at this
  omega

/-- The other curve at a crossing of `y`: a dart at the crossing of `y` with another curve is
`σ y` or `σ³ y`. -/
theorem eq_σ_or_σσσ {y v : D} (hx : A.crossingOf v = A.crossingOf y) (hc : A.curve v ≠ A.curve y) :
    v = A.σ y ∨ v = A.σ (A.σ (A.σ y)) := by
  rcases List.mem_cons.1 ((A.crossingOf_eq_iff).1 hx.symm) with h | h
  · exact absurd (h ▸ rfl) hc
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  rcases List.mem_cons.1 h with h | h
  · exact absurd (by rw [h, A.curve_σσ]) hc
  · exact Or.inr (List.mem_singleton.1 h)

/-- A dart of the same curve at the crossing of `y` is `y` or `σ² y`. -/
theorem eq_or_σσ {y v : D} (hx : A.crossingOf v = A.crossingOf y) (hc : A.curve v = A.curve y) :
    v = y ∨ v = A.σ (A.σ y) := by
  rcases List.mem_cons.1 ((A.crossingOf_eq_iff).1 hx.symm) with h | h
  · exact Or.inl h
  rcases List.mem_cons.1 h with h | h
  · exact absurd (h ▸ hc) (A.isArrangement.curve_σ y)
  rcases List.mem_cons.1 h with h | h
  · exact Or.inr h
  · rw [List.mem_singleton] at h
    rw [h, A.curve_σσσ] at hc
    exact absurd hc (A.isArrangement.curve_σ y)

/-- At a crossing, the cut on the cell of a dart of the other curve, when the chain vanishes on
the segments of both darts. -/
theorem cut_other {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) {y v : D}
    (hv : v = A.σ y ∨ v = A.σ (A.σ (A.σ y))) (hy : c (A.segmentOf y) = 0)
    (hv0 : c (A.segmentOf v) = 0) : r (A.cellOf v) = r (A.cellOf y) := by
  rcases hv with rfl | rfl
  · rw [cut_σ hr, hy, add_zero]
  · have := cut_σ hr (A.σ (A.σ (A.σ y)))
    rw [A.σ_σ_σ_σ, hv0, add_zero] at this
    exact this.symm

theorem foot_curves {z : D} (hz : Λ.L (A.σ z)) :
    Λ.S ∈ Arrangement.Crossing.curves A (A.crossingOf z) := by
  rw [← A.crossingOf_σ, ← Λ.L_curve _ hz]; exact A.mem_curves_crossingOf _

/-- **FROS Claim A.** Two chords `a` (foot `z`) and `b` (foot `w`) of distinct curves crossing at
`p` and `q`, with `p` before `q` on `a`, do not have `q` before `p` on `b`. -/
theorem claimA (hs : Λ.Sep) {z w : D} {m m' i j i' j' : ℕ} (ha : Λ.IsChord z m)
    (hb : Λ.IsChord w m') (hab : A.curve z ≠ A.curve w) (hij : i < j) (hj : j ≤ m)
    (hij' : i' < j') (hj' : j' ≤ m')
    (hp : A.crossingOf ((A.straight ^ i) z) = A.crossingOf ((A.straight ^ j') w))
    (hq : A.crossingOf ((A.straight ^ j) z) = A.crossingOf ((A.straight ^ i') w)) : False := by
  classical
  have haS : (A.curve z) ≠ Λ.S := fun h => S_not_chord hs h (ha.chord 0 (Nat.zero_le _))
  have hbS : (A.curve w) ≠ Λ.S := fun h => S_not_chord hs h (hb.chord 0 (Nat.zero_le _))
  set yq := (A.straight ^ j) z
  set uq := (A.straight ^ i') w
  -- the crossings of `a` and `b`
  have hpq : (A.crossingOf ((A.straight ^ i) z)) ≠ (A.crossingOf yq) := fun h => by
    have := cross_inj ha.lt_period (by omega) hj h; omega
  have cp : Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) z)) = {(A.curve z), (A.curve w)} := curves_eq_pair hab
    (by rw [← Walk.curve_pow A z i]; exact A.mem_curves_crossingOf _)
    (by rw [hp, ← Walk.curve_pow A w j']; exact A.mem_curves_crossingOf _)
  have cq : Arrangement.Crossing.curves A (A.crossingOf yq) = {(A.curve z), (A.curve w)} := curves_eq_pair hab
    (by rw [← Walk.curve_pow A z j]; exact A.mem_curves_crossingOf _)
    (by rw [hq, ← Walk.curve_pow A w i']; exact A.mem_curves_crossingOf _)
  have only : ∀ x : A.Crossing, (A.curve z) ∈ Arrangement.Crossing.curves A x →
      (A.curve w) ∈ Arrangement.Crossing.curves A x → x = (A.crossingOf ((A.straight ^ i) z)) ∨ x = (A.crossingOf yq) := fun x h1 h2 =>
    pair_eq hab hpq cp cq (curves_eq_pair hab h1 h2)
  -- the chain and its normalized cut
  set C : A.Segment → ZMod 2 := Λ.root yq + Λ.root uq with hC
  have hev : IsEven C := fun x => by
    rw [hC, bd_add, bd_root ha.foot (ha.chord' hj), bd_root hb.foot (hb.chord' (show i' ≤ m' by omega))]
    rw [show A.crossingOf ((A.straight ^ i') w) = (A.crossingOf yq) from hq.symm]
    have key : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
    exact key _ _
  have hsupp : Supp Λ C := (root_supp ha.foot (ha.chord' hj)).add Λ
    (root_supp hb.foot (hb.chord' (show i' ≤ m' by omega)))
  obtain ⟨r, hr, hn⟩ := exists_norm Λ hev hsupp
  have hCR : ∀ v, Λ.R v → C (A.segmentOf v) = 0 := fun v hv => by
    rw [hC, Pi.add_apply, root_R ha.foot (ha.chord' hj) hv,
      root_R hb.foot (hb.chord' (show i' ≤ m' by omega)) hv, add_zero]
  -- (1) walking along `a` from `(A.crossingOf yq)` to `R`
  have r_yq : r (A.cellOf yq) = 0 := by
    rw [ha.walk_to_R hr hn (hCR _ ha.endR) hj]
    refine sum_eq_zero fun t ht => ?_
    rw [mem_range] at ht
    have hpc := ha.passed (show j + t < m by omega)
    have hcv : A.curve (A.σ (A.α ((A.straight ^ (j + t)) z))) ≠ (A.curve z) := by
      rw [← Walk.curve_pow A z (j + t), ← A.curve_α ((A.straight ^ (j + t)) z)]
      exact A.isArrangement.curve_σ _
    rw [hC, Pi.add_apply, root_other_chord hs ha.foot (ha.chord' hj) hcv hpc, zero_add]
    by_contra hne
    rcases root_ne_zero hb.foot (hb.chord' (show i' ≤ m' by omega)) hne with
      ⟨s, -, e⟩ | ⟨s, hs', e⟩
    · have hcb : A.curve (A.σ (A.α ((A.straight ^ (j + t)) z))) = (A.curve w) := by
        rcases e with e | e <;> rw [e] <;> simp [A.curve_α, Walk.curve_pow]
      rcases only (A.crossingOf ((A.straight ^ (j + t + 1)) z))
          (by rw [← Walk.curve_pow A z (j + t + 1)]; exact A.mem_curves_crossingOf _)
          (by rw [← crossingOf_passed, ← hcb]; exact A.mem_curves_crossingOf _) with e' | e'
      · have := cross_inj ha.lt_period (by omega) (by omega) e'; omega
      · have := cross_inj ha.lt_period (by omega) hj e'; omega
    · apply Bd.not_chord (show Λ.Bd _ from Or.inl (L_of_lt_lidx hb.foot hs'))
      rcases e with e | e
      · rw [← e]; exact hpc
      · rw [← A.α_α ((A.straight ^ s) Λ.base), ← e]; exact chord_α hpc
  -- (2) the cell of `uq` at `(A.crossingOf yq)`
  have r_uq : r (A.cellOf uq) = 0 := by
    have hux : A.crossingOf uq = A.crossingOf yq := hq.symm
    have huc : A.curve uq ≠ A.curve yq := by
      simp only [uq, yq, Walk.curve_pow]; exact hab.symm
    rw [cut_other hr (eq_σ_or_σσσ hux huc) ?_ ?_, r_yq]
    · rw [hC, Pi.add_apply, root_self ha.foot ha.chord ha.lt_period hj hj, if_neg (lt_irrefl _),
        zero_add, root_other_chord hs hb.foot (hb.chord' (show i' ≤ m' by omega))
          (by simp only [yq, Walk.curve_pow]; exact hab) (ha.chord j hj)]
    · rw [hC, Pi.add_apply, root_self hb.foot hb.chord hb.lt_period (by omega) (by omega),
        if_neg (lt_irrefl _), add_zero, root_other_chord hs ha.foot (ha.chord' hj)
          (by simp only [uq, Walk.curve_pow]; exact hab.symm) (hb.chord i' (by omega))]
  -- (3) walking along `b` from `(A.crossingOf yq)` to `R`: one passed segment, at `(A.crossingOf ((A.straight ^ i) z))`
  have hi0 : 1 ≤ i := by
    by_contra h0
    have : i = 0 := by omega
    have hS := foot_curves ha.foot
    rw [show z = (A.straight ^ i) z by rw [this, pow_zero, Perm.one_apply]] at hS
    change Λ.S ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) z)) at hS
    rw [cp, mem_insert, mem_singleton] at hS
    rcases hS with h | h
    · exact haS h.symm
    · exact hbS h.symm
  have r_uq' : r (A.cellOf uq) = 1 := by
    rw [hb.walk_to_R hr hn (hCR _ hb.endR) (show i' ≤ m' by omega)]
    rw [sum_eq_single (j' - i' - 1)]
    · -- the segment passed at `(A.crossingOf ((A.straight ^ i) z))`
      rw [show i' + (j' - i' - 1) = j' - 1 by omega]
      set v := A.σ (A.α ((A.straight ^ (j' - 1)) w))
      have hvx : A.crossingOf v = (A.crossingOf ((A.straight ^ i) z)) := by
        rw [crossingOf_passed, show j' - 1 + 1 = j' by omega, ← hp]
      have hvc : A.curve v ≠ (A.curve w) := by
        rw [← Walk.curve_pow A w (j' - 1), ← A.curve_α ((A.straight ^ (j' - 1)) w)]
        exact A.isArrangement.curve_σ _
      have hvca : A.curve v = (A.curve z) := by
        have := A.mem_curves_crossingOf v
        rw [hvx, cp, mem_insert, mem_singleton] at this
        rcases this with h | h
        · exact h
        · exact absurd h hvc
      have hvc' : Λ.Chord v := hb.passed (show j' - 1 < m' by omega)
      rw [hC, Pi.add_apply, root_other_chord hs hb.foot (hb.chord' (show i' ≤ m' by omega))
        (by rw [hvca]; exact hab) hvc', add_zero]
      rcases eq_or_σσ hvx (by rw [hvca, Walk.curve_pow]) with e | e
      · rw [e, root_self ha.foot ha.chord ha.lt_period hj (by omega), if_pos hij]
      · have e2 : A.segmentOf v = A.segmentOf ((A.straight ^ (i - 1)) z) := by
          rw [e, show i = (i - 1) + 1 by omega, Walk.pow_succ_apply, A.straight_apply,
            A.σ_σ_σ_σ]
          exact Orbit.mk_eq_mk.2 (Perm.SameCycle.refl _ _ |>.trans ⟨1, by simp⟩).symm
        rw [e2, root_self ha.foot ha.chord ha.lt_period hj (by omega), if_pos (by omega)]
    · intro t ht htne
      rw [mem_range] at ht
      have hpc := hb.passed (show i' + t < m' by omega)
      have hcv : A.curve (A.σ (A.α ((A.straight ^ (i' + t)) w))) ≠ (A.curve w) := by
        rw [← Walk.curve_pow A w (i' + t), ← A.curve_α ((A.straight ^ (i' + t)) w)]
        exact A.isArrangement.curve_σ _
      rw [hC, Pi.add_apply, root_other_chord hs hb.foot (hb.chord' (show i' ≤ m' by omega)) hcv hpc,
        add_zero]
      by_contra hne
      rcases root_ne_zero ha.foot (ha.chord' hj) hne with ⟨s, -, e⟩ | ⟨s, hs', e⟩
      · have hca : A.curve (A.σ (A.α ((A.straight ^ (i' + t)) w))) = (A.curve z) := by
          rcases e with e | e <;> rw [e] <;> simp [A.curve_α, Walk.curve_pow]
        rcases only (A.crossingOf ((A.straight ^ (i' + t + 1)) w))
            (by rw [← crossingOf_passed, ← hca]; exact A.mem_curves_crossingOf _)
            (by rw [← Walk.curve_pow A w (i' + t + 1)]; exact A.mem_curves_crossingOf _)
            with e' | e'
        · rw [hp] at e'
          have := cross_inj hb.lt_period (by omega) hj' e'; omega
        · rw [hq] at e'
          have := cross_inj hb.lt_period (by omega) (by omega) e'; omega
      · apply Bd.not_chord (show Λ.Bd _ from Or.inl (L_of_lt_lidx ha.foot hs'))
        rcases e with e | e
        · rw [← e]; exact hpc
        · rw [← A.α_α ((A.straight ^ s) Λ.base), ← e]; exact chord_α hpc
    · intro h; exfalso; rw [mem_range] at h; omega
  rw [r_uq] at r_uq'
  exact absurd r_uq' (by decide)

end Lens

end Pca.FlipGraph
