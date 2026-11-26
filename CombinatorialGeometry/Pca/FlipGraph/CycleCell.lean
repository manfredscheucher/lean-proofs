/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): a tight directed cycle is impossible (FROS Claim B, cell part)

FROS (Claim B): "Let `Z` be a directed cycle such that the enclosed area is minimal. Then `Z` is
the boundary of a cell of the arrangement", which is then excluded. Graph language, by parity
instead of FROS' induction on `α_j, β_1`:

* **Wedges** (`wedge_vals`): for two forward darts `u`, `u'` leaving a vertex `x`, the region of
  `root u + root u'` (bounded by the two arcs from `L` to `x` and the piece of `L`) contains none of
  the cells of `u'` and `σ u'` at `x` (walk along the arc of `u'` to `R`: by Claim A it passes no
  segment of the chain).
* **Decomposition** (`cut_eq_sum`): the chain of a cycle is the sum of the wedge chains at its
  vertices (`δ (z i) = root (straight (z i)) + root (z i)`, telescoping), so its region is the sum
  of the wedge regions.
* `Good` (**tight** cycle): no forward dart off the cycle arrives at a vertex of the cycle from the
  region. Then every side of a region cell lies on the cycle (`side_inZ`: otherwise follow the
  chord of that side to `R`; it leaves the region at a vertex of the cycle), so the cell of `z 0`
  or of `α (z 0)` has all darts of the cycle as sides and lies in no wedge: contradiction with
  `cut_eq_sum` (`not_good`).
-/
import Pca.FlipGraph.Cycle

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} {Λ : Lens A}

/-- A forward dart lies on a whole chord. -/
theorem exists_chord_rep (ht : Λ.Transversal) {u : D} (hu : Λ.Fwd u) :
    ∃ z m j, Λ.IsChord z m ∧ j ≤ m ∧ (A.straight ^ j) z = u := by
  obtain ⟨z₀, k, hz, hc, rfl⟩ := exists_foot ht hu
  obtain ⟨m', hm', hR⟩ := hu.2
  refine ⟨z₀, k + m', k, ⟨hz, fun i hi => ?_, ?_⟩, by omega, rfl⟩
  · by_cases hik : i ≤ k
    · exact hc i hik
    · have := hm' (i - k) (by omega)
      rwa [← Perm.mul_apply, ← pow_add, show i - k + k = i by omega] at this
  · rw [show k + m' = m' + k by omega, pow_add, Perm.mul_apply]; exact hR

/-- **Walk to `R` from a wedge vertex**: the cell of `u = straight^j za` has value `0` in the
region of `root u + root u'`. -/
theorem wedge_zero (hs : Λ.Sep) {za zb : D} {ma mb j k : ℕ} (ha : Λ.IsChord za ma)
    (hb : Λ.IsChord zb mb) (hj : j ≤ ma) (hk : k ≤ mb) (hab : A.curve za ≠ A.curve zb)
    (hx : A.crossingOf ((A.straight ^ j) za) = A.crossingOf ((A.straight ^ k) zb))
    {r : A.Cell → ZMod 2}
    (hr : IsCut (Λ.root ((A.straight ^ j) za) + Λ.root ((A.straight ^ k) zb)) r)
    (hn : Norm Λ r) : r (A.cellOf ((A.straight ^ j) za)) = 0 := by
  set C := Λ.root ((A.straight ^ j) za) + Λ.root ((A.straight ^ k) zb) with hC
  have hCR : ∀ v, Λ.R v → C (A.segmentOf v) = 0 := fun v hv => by
    rw [hC, Pi.add_apply, root_R ha.foot (ha.chord' hj) hv, root_R hb.foot (hb.chord' hk) hv,
      add_zero]
  rw [ha.walk_to_R hr hn (hCR _ ha.endR) hj]
  refine sum_eq_zero fun t ht' => ?_
  rw [mem_range] at ht'
  have hpc := ha.passed (show j + t < ma by omega)
  have hcv : A.curve (A.σ (A.α ((A.straight ^ (j + t)) za))) ≠ A.curve za := by
    rw [← Walk.curve_pow A za (j + t), ← A.curve_α ((A.straight ^ (j + t)) za)]
    exact A.isArrangement.curve_σ _
  rw [hC, Pi.add_apply, root_other_chord hs ha.foot (ha.chord' hj) hcv hpc, zero_add]
  by_contra hne
  rcases root_ne_zero hb.foot (hb.chord' hk) hne with ⟨s, hsk, e⟩ | ⟨s, hs', e⟩
  · have hxs : ∃ s' ≤ k, A.crossingOf ((A.straight ^ (j + t + 1)) za) =
        A.crossingOf ((A.straight ^ s') zb) := by
      rcases e with e | e
      · exact ⟨s, hsk.le, by rw [← crossingOf_passed, e]⟩
      · exact ⟨s + 1, hsk, by rw [← crossingOf_passed, e, crossingOf_α_pow]⟩
    obtain ⟨s', hs'k, hxs⟩ := hxs
    rcases lt_or_eq_of_le hs'k with hlt | rfl
    · exact claimA hs hb ha (Ne.symm hab) hlt hk (show j < j + t + 1 by omega) (by omega)
        hxs.symm hx.symm
    · have := cross_inj ha.lt_period (show j + t + 1 ≤ ma by omega) hj (hxs.trans hx.symm)
      omega
  · apply Bd.not_chord (show Λ.Bd _ from Or.inl (L_of_lt_lidx hb.foot hs'))
    rcases e with e | e
    · rw [← e]; exact hpc
    · rw [← A.α_α ((A.straight ^ s) Λ.base), ← e]; exact chord_α hpc

/-- The wedge chain of two forward darts at one crossing is even and supported in `Q`. -/
theorem wedge_even (ht : Λ.Transversal) {u u' : D} (hu : Λ.Fwd u) (hu' : Λ.Fwd u')
    (hx : A.crossingOf u = A.crossingOf u') :
    IsEven (Λ.root u + Λ.root u') ∧ Supp Λ (Λ.root u + Λ.root u') := by
  obtain ⟨z₀, k, hz, hc, rfl⟩ := exists_foot ht hu
  obtain ⟨z₁, k', hz', hc', rfl⟩ := exists_foot ht hu'
  refine ⟨fun x => ?_, (root_supp hz hc).add Λ (root_supp hz' hc')⟩
  rw [bd_add, bd_root hz hc, bd_root hz' hc', hx]
  have key : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
  exact key _ _

/-- **The wedge at a vertex** misses the cells of `u'` and `σ u'`. -/
theorem wedge_vals (hs : Λ.Sep) (ht : Λ.Transversal) {u u' : D} (hu : Λ.Fwd u) (hu' : Λ.Fwd u')
    (hx : A.crossingOf u = A.crossingOf u') {r : A.Cell → ZMod 2}
    (hr : IsCut (Λ.root u + Λ.root u') r) (hn : Norm Λ r) :
    r (A.cellOf u') = 0 ∧ r (A.cellOf (A.σ u')) = 0 := by
  by_cases hc : A.curve u = A.curve u'
  · -- the same dart: the chain is `0`
    have he : u' = u := by
      rcases eq_or_σσ hx.symm (hc.symm) with h | h
      · exact h
      · exfalso
        have hst : A.straight (A.α u') = u := by rw [A.straight_apply, A.α_α, h, A.σ_σ_σ_σ]
        have hf : Λ.Fwd (A.α u') := Fwd.of_straight (by rw [hst]; exact hu) (chord_α hu'.1)
        exact (fwd_α_iff hs ht hu'.1).1 hf hu'
    rw [he] at hr ⊢
    have h0 : IsCut (Λ.root u + Λ.root u) 0 := fun y => by
      simp only [Pi.add_apply, Arrangement.zmod2_add_self, Pi.zero_apply]
    have := norm_unique Λ hr hn h0 (fun _ _ => rfl)
    subst this
    exact ⟨rfl, rfl⟩
  · obtain ⟨za, ma, j, ha, hj, rfl⟩ := exists_chord_rep ht hu
    obtain ⟨zb, mb, k, hb, hk, rfl⟩ := exists_chord_rep ht hu'
    have hab : A.curve zb ≠ A.curve za := by
      rw [Walk.curve_pow, Walk.curve_pow] at hc; exact Ne.symm hc
    have hr' : IsCut (Λ.root ((A.straight ^ k) zb) + Λ.root ((A.straight ^ j) za)) r := by
      rw [add_comm]; exact hr
    have h1 := wedge_zero hs hb ha hk hj hab hx.symm hr' hn
    refine ⟨h1, ?_⟩
    rw [cut_σ hr, h1, zero_add, Pi.add_apply,
      root_other_chord hs ha.foot (ha.chord' hj) (by rw [Walk.curve_pow]; exact hab)
        (hb.chord k hk),
      root_self hb.foot hb.chord hb.lt_period hk hk, if_neg (lt_irrefl _), add_zero]

namespace Cyc

variable (Z : Λ.Cyc) (hs : Λ.Sep) (ht : Λ.Transversal)
include hs ht

theorem chord_straight (i : ZMod Z.k) : Λ.Chord (A.straight (Z.z i)) :=
  Z.vert (i + 1) _ (Orbit.mem_darts.2 (show A.crossingOf (A.straight (Z.z i)) = _ by
    rw [A.straight_apply, A.crossingOf_σσ, Z.link]))

theorem fwd_straight (i : ZMod Z.k) : Λ.Fwd (A.straight (Z.z i)) :=
  (Z.fwd i).straight (Z.chord_straight hs ht i)

theorem crossing_straight (i : ZMod Z.k) :
    A.crossingOf (A.straight (Z.z i)) = A.crossingOf (Z.z (i + 1)) := by
  rw [A.straight_apply, A.crossingOf_σσ, Z.link]

/-- **The chain of a cycle is the sum of its wedge chains.** -/
theorem chain_eq : Z.chain = ∑ i, (Λ.root (A.straight (Z.z i)) + Λ.root (Z.z (i + 1))) := by
  have hδ : ∀ i, δ (A.segmentOf (Z.z i)) = Λ.root (A.straight (Z.z i)) + Λ.root (Z.z i) := by
    intro i
    obtain ⟨z₀, k, hz, hc, he⟩ := exists_foot ht (Z.fwd i)
    have hc' : ∀ j ≤ k + 1, Λ.Chord ((A.straight ^ j) z₀) := fun j hj => by
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact hc j (by omega)
      · rw [show j = k + 1 by omega, Walk.pow_succ_apply, he]; exact Z.chord_straight hs ht i
    have := root_succ hz hc'
    rw [Walk.pow_succ_apply, he] at this
    rw [this]
    funext s
    simp only [Pi.add_apply]
    have key : ∀ a b : ZMod 2, b = a + b + a := by decide
    exact key _ _
  unfold chain
  simp_rw [hδ, sum_add_distrib]
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)).symm

/-- **Tight** cycle: no forward dart off the cycle arrives at a vertex of the cycle from the
region. -/
def Good : Prop :=
  ∀ y, Λ.Fwd y → ¬ Z.InZ y → (∃ i, A.crossingOf (A.α y) = A.crossingOf (Z.z i)) →
    Z.cut (A.cellOf y) = 0

/-- In a tight cycle every side of a region cell lies on the cycle. -/
theorem side_inZ (hG : Z.Good) {d : D} (h1 : Z.cut (A.cellOf d) = 1) : Z.InZ d := by
  by_contra hd
  have h2 : Z.cut (A.cellOf (A.α d)) = 1 := by rw [Z.cut_not hs ht hd]; exact h1
  have hQ : ∀ g, Z.cut g = 1 → Λ.Q g := fun g hg => by
    by_contra hq; rw [Z.cut_norm g hq] at hg; exact absurd hg (by decide)
  have hcd : Λ.Chord d := ⟨hQ _ h1, hQ _ h2⟩
  obtain ⟨y, hy, hy1, hy2, hyZ⟩ : ∃ y, Λ.Fwd y ∧ Z.cut (A.cellOf y) = 1 ∧
      Z.cut (A.cellOf (A.α y)) = 1 ∧ ¬ Z.InZ y := by
    rcases fwd_or hs ht hcd with h | h
    · exact ⟨d, h, h1, h2, hd⟩
    · exact ⟨A.α d, h, h2, by rw [A.α_α]; exact h1, by rwa [Z.inZ_α]⟩
  obtain ⟨m, hm, hR⟩ := hy.2
  have hbadm : ¬ (Z.cut (A.cellOf ((A.straight ^ m) y)) = 1 ∧
      Z.cut (A.cellOf (A.α ((A.straight ^ m) y))) = 1) := fun ⟨h, _⟩ => by
    have := norm_R Λ Z.cut_isCut Z.cut_norm hR
      (Z.chain_not hs ht fun hz => (show Λ.Bd _ from Or.inr hR).not_chord (Z.inZ_chord hz))
    rw [cellOf_σα, h] at this; exact absurd this (by decide)
  have hex : ∃ j, ¬ (Z.cut (A.cellOf ((A.straight ^ j) y)) = 1 ∧
      Z.cut (A.cellOf (A.α ((A.straight ^ j) y))) = 1) := ⟨m, hbadm⟩
  have hj0 : Nat.find hex ≠ 0 := fun h0 => by
    have := Nat.find_spec hex; rw [h0] at this; exact this (by simpa using ⟨hy1, hy2⟩)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjm : j + 1 ≤ m := hj ▸ Nat.find_min' hex hbadm
  have hgood := not_not.1 (Nat.find_min hex (show j < Nat.find hex by omega))
  have hbad := Nat.find_spec hex
  rw [hj, Walk.pow_succ_apply] at hbad
  set w := (A.straight ^ j) y with hw
  have hvx : ∃ i, A.crossingOf (A.α w) = A.crossingOf (Z.z i) := by
    by_contra hno
    have h0 : ∀ e, A.crossingOf e = A.crossingOf (A.α w) →
        Z.cut (A.cellOf (A.σ e)) = Z.cut (A.cellOf e) := fun e he => by
      rw [cut_σ Z.cut_isCut, Z.chain_not hs ht (fun hz => hno (by
        obtain ⟨i, hi⟩ := Z.inZ_vertex hz; exact ⟨i, he.symm.trans hi⟩)), add_zero]
    apply hbad
    have e1 := h0 (A.α w) rfl
    have e2 := h0 (A.σ (A.α w)) (A.crossingOf_σ _)
    have e3 := h0 (A.σ (A.σ (A.α w))) (A.crossingOf_σσ _)
    refine ⟨?_, ?_⟩
    · rw [A.straight_apply, e2, e1]; exact hgood.2
    · rw [← A.cellOf_σ, A.straight_apply, e3, e2, e1]; exact hgood.2
  have hwf : Λ.Fwd w := hy.pow fun i hi => hm i (by omega)
  have hwZ : ¬ Z.InZ w := fun hz => by
    have := cut_α Z.cut_isCut w
    rw [Z.chain_apply hs ht, if_pos hz, hgood.1, hgood.2] at this
    exact absurd this (by decide)
  have := hG w hwf hwZ hvx
  rw [hgood.1] at this; exact absurd this (by decide)

/-- **No tight cycle.** -/
theorem not_good : ¬ Z.Good := by
  intro hG
  have hW : ∀ i, ∃ r, IsCut (Λ.root (A.straight (Z.z i)) + Λ.root (Z.z (i + 1))) r ∧ Norm Λ r :=
    fun i => by
      obtain ⟨h1, h2⟩ := wedge_even ht (Z.fwd_straight hs ht i) (Z.fwd (i + 1))
        (Z.crossing_straight hs ht i)
      exact exists_norm Λ h1 h2
  choose rW hrW hnW using hW
  have hsum : Z.cut = ∑ i, rW i := by
    refine norm_unique Λ Z.cut_isCut Z.cut_norm ?_ ?_
    · rw [Z.chain_eq hs ht]; exact IsCut.sum _ fun i _ => hrW i
    · intro f hf; rw [Finset.sum_apply]; exact sum_eq_zero fun i _ => hnW i f hf
  have hv : ∀ i, rW i (A.cellOf (Z.z (i + 1))) = 0 ∧ rW i (A.cellOf (A.σ (Z.z (i + 1)))) = 0 :=
    fun i => wedge_vals hs ht (Z.fwd_straight hs ht i) (Z.fwd (i + 1))
      (Z.crossing_straight hs ht i) (hrW i) (hnW i)
  have hz := Z.cut_z hs ht 0
  rcases Chain.zmod2_cases (Z.cut (A.cellOf (Z.z 0))) with h0 | h0
  · -- the region is on the side of `α (z i)`
    set g := A.cellOf (A.α (Z.z 0))
    have hg : Z.cut g = 1 := by rw [hz, h0]; rfl
    have hall : ∀ i, A.cellOf (A.α (Z.z i)) = g := by
      refine zmod_induct_down (fun i => A.cellOf (A.α (Z.z i)) = g) (fun i hi => ?_) rfl
      have hd : A.cellOf (A.σ (Z.z (i + 1))) = g := by rw [A.cellOf_σ, hi]
      have hin := Z.side_inZ hs ht hG (show Z.cut (A.cellOf (A.σ (Z.z (i + 1)))) = 1 by rw [hd]; exact hg)
      rcases Z.inZ_at (A.crossingOf_σ _) hin with e | e
      · exact absurd e (A.σ_ne _)
      · rw [add_sub_cancel_right] at e; rw [← e]; exact hd
    have := congrFun hsum g
    rw [hg, Finset.sum_apply, sum_eq_zero fun i _ => by
      rw [← hall (i + 1), ← A.cellOf_σ]; exact (hv i).2] at this
    exact absurd this (by decide)
  · set g := A.cellOf (Z.z 0)
    have hall : ∀ i, A.cellOf (Z.z i) = g := by
      refine zmod_induct (fun i => A.cellOf (Z.z i) = g) (fun i hi => ?_) rfl
      have hd : A.cellOf (A.φ (Z.z i)) = g := by rw [A.cellOf_φ, hi]
      have hin := Z.side_inZ hs ht hG (show Z.cut (A.cellOf (A.φ (Z.z i))) = 1 by rw [hd]; exact h0)
      have hx : A.crossingOf (A.φ (Z.z i)) = A.crossingOf (Z.z (i + 1)) := by
        rw [A.crossingOf_φ, Z.link]
      rcases Z.inZ_at hx hin with e | e
      · rw [← e]; exact hd
      · rw [add_sub_cancel_right, A.φ_apply] at e; exact absurd e (A.σ_ne _)
    have := congrFun hsum g
    rw [h0, Finset.sum_apply, sum_eq_zero fun i _ => by rw [← hall (i + 1)]; exact (hv i).1] at this
    exact absurd this (by decide)

end Cyc

end Lens

end Pca.FlipGraph
