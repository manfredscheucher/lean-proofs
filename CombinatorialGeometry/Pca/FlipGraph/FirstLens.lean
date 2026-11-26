/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the lens of the first curve

For the first curve `C₀` (with a side on the marked cell `z`, dart `y₀`) and a center `p` with a
side on `C₀`: the lens `int C₀`. Its boundary darts are the walk `u k = straight^k (α y₀)` along
`C₀` (inside on the right); `u 0` is the side of the cell `T₀` across the side of `z`, `u kp` the
side of `p`. The arc `L` is `u 1, …, u kp`, the arc `R` is `u 0, u (kp+1), …`. A chord of a curve
`a` joins the two crossings of `a` and `C₀`; along the walk they are at the positions `p_a < q_a`
with `p_a < kp ≤ q_a` (`p` is inside `a`, `T₀` is not), and the chord ending at the crossing at
position `i` ends at the boundary dart `u (i + 1)`: so one end is on `L`, the other on `R`
(`firstLens_transversal`). The chords are not on `C₀` (`firstLens_sep`).
-/
import Pca.FlipGraph.Zip
import Pca.FlipGraph.Order

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-! ## The zipping step with the base of the source triangle not at the end of `L` -/

namespace Lens

open Arrangement' Chain

variable {A : Arrangement n D} {Λ : Lens A}

/-- In a source triangle `σ wb` between the feet `wa`, `wb`, the next dart after the base along `S`
is the foot `σ wa` (on `L`). -/
theorem straight_next {wa wb : D} (hT : A.IsTriangle (A.cellOf (A.σ wb)))
    (hrot : A.σ (A.α wa) = A.α wb) (hfa : Λ.L (A.σ wa)) : Λ.L (A.straight (A.σ wb)) := by
  have h1 : A.φ wa = A.α wb := by rw [A.φ_apply, hrot]
  have h2 : A.φ (A.α wb) = A.σ wb := by rw [A.φ_apply, A.α_α]
  have hc : A.cellOf wa = A.cellOf (A.σ wb) := by
    rw [← h2, ← h1, A.cellOf_φ, A.cellOf_φ]
  have h3 : A.φ (A.φ (A.φ wa)) = wa := A.φ_φ_φ_of_triangle (by rw [hc]; exact hT)
  have h4 : A.φ (A.σ wb) = wa := by rw [← h2, ← h1, h3]
  rw [A.straight_apply, ← A.φ_apply, h4]
  exact hfa

theorem sourceTri_of_source' (hs : Λ.Sep) (ht : Λ.Transversal) {x : A.Crossing}
    (hx : Λ.SourceV x) : ∃ d, Λ.SourceTri d ∧ Λ.L (A.straight d) := by
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
  · have hT := tri_case hs ht ha hb hfa hfb hab e.symm (by rw [hxa]; exact hv)
    exact ⟨_, hT, straight_next hT.2.1 e.symm hfa⟩
  · have e' : A.σ (A.α wb) = A.α wa := by rw [e, A.σ_σ_σ_σ]
    have hT := tri_case hs ht hb ha hfb hfa hab.symm e' (by rw [hxb]; exact hv)
    exact ⟨_, hT, straight_next hT.2.1 e' hfb⟩

/-- **The zipping step** (`zipStep`), with the base `d` of the source triangle followed on `S` by
another dart of `L`. -/
theorem zipStep' (Λ : Lens A) (hs : Λ.Sep) (ht : Λ.Transversal) (hv : ∃ x, Λ.IsVertex x) :
    ∃ d, Λ.SourceTri d ∧ Λ.L (A.straight d) := by
  obtain ⟨x, hx⟩ := Λ.exists_source hs ht hv
  exact sourceTri_of_source' hs ht hx

end Lens

namespace First

variable (M : Marked n D) {y₀ : D} (hy₀ : M.A.cellOf y₀ = M.z)

/-- The walk along `C₀` with the interior on the right. -/
def u (y₀ : D) (k : ℕ) : D := (M.A.straight ^ k) (M.A.α y₀)

theorem curve_u (k : ℕ) : M.A.curve (u M y₀ k) = M.A.curve y₀ := by
  rw [u, Walk.curve_pow, M.A.curve_α]

include hy₀ in
theorem in_u (k : ℕ) : M.Inside (M.A.curve y₀) (M.A.cellOf (u M y₀ k)) := by
  rw [u, M.inside_pow_of_curve (by rw [M.A.curve_α]), M.inside_α, hy₀]
  simp only [ne_eq, not_true_eq_false, iff_false]
  exact M.not_inside_z _

include hy₀ in
theorem out_α_u (k : ℕ) : ¬ M.Inside (M.A.curve y₀) (M.A.cellOf (M.A.α (u M y₀ k))) := by
  rw [M.inside_α, curve_u]
  have := in_u M hy₀ k
  tauto

theorem u_inj {i j : ℕ} (hi : i < period M.A.straight (M.A.α y₀))
    (hj : j < period M.A.straight (M.A.α y₀)) (h : u M y₀ i = u M y₀ j) : i = j :=
  Walk.pow_inj M.A hi hj h

theorem u_period : u M y₀ (period M.A.straight (M.A.α y₀)) = u M y₀ 0 := by
  rw [u, Walk.pow_period_apply]; simp [u]

theorem u_succ (k : ℕ) : u M y₀ (k + 1) = M.A.straight (u M y₀ k) := by
  rw [u, u, Walk.pow_succ_apply]

include hy₀ in
/-- The darts of `C₀` with the interior on the right are the darts of the walk. -/
theorem dart_u {y : D} (hy : M.A.curve y = M.A.curve y₀)
    (hin : M.Inside (M.A.curve y₀) (M.A.cellOf y)) :
    ∃ j < period M.A.straight (M.A.α y₀), y = u M y₀ j := by
  obtain ⟨j, hj, h | h⟩ := Order.dart_C₀ M (y₀ := M.A.α y₀) (by rw [M.A.curve_α]) hy
  · exact ⟨j, hj, h⟩
  · exfalso
    have := out_α_u M hy₀ j
    rw [u, ← h] at this
    exact this hin

include hy₀ in
/-- The cell `T₀` across the side of `z` is outside every other curve. -/
theorem out_u0 {a : Fin n} (ha : a ≠ M.A.curve y₀) : ¬ M.Inside a (M.A.cellOf (u M y₀ 0)) := by
  simp only [u, pow_zero, Perm.one_apply]
  rw [M.inside_α, hy₀]
  have := M.not_inside_z a
  tauto

include hy₀ in
/-- The cells inside `a` along the walk form the interval `(p, q]` of its two crossings. -/
theorem interval {a : Fin n} (ha : a ≠ M.A.curve y₀) {p q : ℕ} (hpq : p < q)
    (hs : Walk.flipsOn M.A a (M.A.α y₀) = {p, q}) (i : ℕ)
    (hi : i ≤ period M.A.straight (M.A.α y₀)) :
    M.Inside a (M.A.cellOf (u M y₀ i)) ↔ p < i ∧ i ≤ q := by
  induction i with
  | zero => exact ⟨fun h => absurd h (out_u0 M hy₀ ha), fun h => by omega⟩
  | succ i ih =>
    simp only [u] at ih ⊢
    rw [Order.in_succ, ih (by omega), ne_eq, Order.nx_iff M hs (by omega)]
    exact (Order.arith_step hpq).symm

end First

open First

variable (M : Marked n D) {y₀ : D} (hy₀ : M.A.cellOf y₀ = M.z) {kp : ℕ} (hkp1 : 1 ≤ kp)
  (hkpP : kp < period M.A.straight (M.A.α y₀))

include hkp1 in
/-- **The lens of the first curve**: `Q = int C₀`, `L = u 1, …, u kp`, `R` the other darts of the
walk. -/
noncomputable def firstLens : Lens M.A where
  Q := M.Inside (M.A.curve y₀)
  L := fun y => ∃ k, 1 ≤ k ∧ k ≤ kp ∧ y = u M y₀ k
  R := fun y => ∃ k, k < period M.A.straight (M.A.α y₀) ∧ (k = 0 ∨ kp < k) ∧ y = u M y₀ k
  S := M.A.curve y₀
  L_curve := fun y ⟨k, _, _, e⟩ => by rw [e, curve_u]
  L_bd := fun y ⟨k, _, _, e⟩ => by rw [e]; exact ⟨in_u M hy₀ k, out_α_u M hy₀ k⟩
  R_bd := fun y ⟨k, _, _, e⟩ => by rw [e]; exact ⟨in_u M hy₀ k, out_α_u M hy₀ k⟩
  bd := fun y hq hq' => by
    have hc : M.A.curve y = M.A.curve y₀ := by
      by_contra hc
      apply hq'
      rw [M.inside_α]
      exact ⟨fun _ => hc, fun _ => hq⟩
    obtain ⟨j, hj, rfl⟩ := dart_u M hy₀ hc hq
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact Or.inr ⟨j, hj, Or.inl h0, rfl⟩
    · by_cases hjk : j ≤ kp
      · exact Or.inl ⟨j, h0, hjk, rfl⟩
      · exact Or.inr ⟨j, hj, Or.inr (by omega), rfl⟩
  disj := fun y ⟨⟨k, h1, h2, e⟩, ⟨k', h1', h2', e'⟩⟩ => by
    have := u_inj M (by omega) h1' (e.symm.trans e')
    omega
  L_run := ⟨u M y₀ 1, kp - 1, fun y => by
    constructor
    · rintro ⟨k, h1, h2, rfl⟩
      refine ⟨k - 1, by omega, ?_⟩
      show (M.A.straight ^ k) (M.A.α y₀) =
        (M.A.straight ^ (k - 1)) ((M.A.straight ^ 1) (M.A.α y₀))
      rw [← Perm.mul_apply (M.A.straight ^ (k - 1)), ← pow_add, show k - 1 + 1 = k by omega]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i + 1, by omega, by omega, ?_⟩
      show (M.A.straight ^ i) ((M.A.straight ^ 1) (M.A.α y₀)) =
        (M.A.straight ^ (i + 1)) (M.A.α y₀)
      rw [← Perm.mul_apply (M.A.straight ^ i), ← pow_add]⟩
  compl_conn := fun f g hf hg => by
    obtain ⟨s, hs⟩ := M.A.exists_isSide (M.A.curve y₀)
    have hfg : s f = s g := by
      have h1 := M.inside_iff hs f
      have h2 := M.inside_iff hs g
      have key : ∀ a b c : ZMod 2, ((a ≠ c) ↔ (b ≠ c)) → a = b := by decide
      exact key _ _ (s M.z) (by rw [← h1, ← h2]; tauto)
    have hI : ∀ a b, AdjBy M.A (fun y => M.A.curve y ≠ M.A.curve y₀) a b →
        (¬ M.Inside (M.A.curve y₀) a ↔ ¬ M.Inside (M.A.curve y₀) b) := by
      rintro a b ⟨y, hy, rfl, rfl⟩
      rw [M.inside_α _ y]
      simp only [hy, ne_eq, not_false_eq_true, iff_true]
    refine (Marked.eqvGen_restrict hI (fun a b hab ha => ?_) (side_connected hs hfg)).2 hf
    obtain ⟨y, hy, rfl, rfl⟩ := hab
    exact ⟨y, ⟨ha, (hI _ _ ⟨y, hy, rfl, rfl⟩).1 ha⟩, rfl, rfl⟩

theorem firstLens_sep : (firstLens M hy₀ hkp1 hkpP).Sep := by
  rintro y z ⟨h1, h2⟩ hz e
  have hzc : M.A.curve z = M.A.curve y₀ := by
    rcases hz with ⟨k, -, -, rfl⟩ | ⟨k, -, -, rfl⟩ <;> exact curve_u M k
  change M.Inside (M.A.curve y₀) (M.A.cellOf y) at h1
  change M.Inside (M.A.curve y₀) (M.A.cellOf (M.A.α y)) at h2
  rw [M.inside_α, e, hzc] at h2
  exact (h2.1 h1) rfl

include hy₀ in
/-- The crossing at the end of a chord, at the boundary dart `u j`, is a crossing with the curve of
the chord at the position before `j`. -/
theorem firstLens_endpos {y : D} {k j : ℕ} (hj : j < period M.A.straight (M.A.α y₀))
    (hc : M.A.curve y ≠ M.A.curve y₀)
    (he : M.A.σ (M.A.α ((M.A.straight ^ k) y)) = u M y₀ j) :
    (if j = 0 then period M.A.straight (M.A.α y₀) - 1 else j - 1) ∈
      Walk.flipsOn M.A (M.A.curve y) (M.A.α y₀) := by
  set P := period M.A.straight (M.A.α y₀) with hP
  set i := if j = 0 then P - 1 else j - 1 with hi
  have hiP : i < P := by rw [hi]; split_ifs <;> omega
  have hsu : M.A.straight (u M y₀ i) = u M y₀ j := by
    rw [← u_succ]
    rw [hi]; split_ifs with h0
    · rw [show P - 1 + 1 = P by omega, h0]; exact u_period M
    · rw [show j - 1 + 1 = j by omega]
  set w := (M.A.straight ^ k) y
  have hwc : M.A.curve (M.A.α w) = M.A.curve y := by rw [M.A.curve_α, Walk.curve_pow]
  have hx : M.A.crossingOf (M.A.α w) = M.A.crossingOf (M.A.α (u M y₀ i)) := by
    rw [← M.A.crossingOf_straight (u M y₀ i), hsu, ← he, M.A.crossingOf_σ]
  have hm := M.A.mem_curves_crossingOf (M.A.α w)
  rw [hx, M.A.curves_crossingOf, mem_insert, mem_singleton, hwc, M.A.curve_α, curve_u] at hm
  rw [Walk.mem_flipsOn]
  refine ⟨hiP, ?_⟩
  rcases hm with h | h
  · exact absurd h hc
  · exact h.symm

include hy₀ in
/-- **All chords of the first-curve lens are transversal** (`p`, the cell of `u kp`, is inside
every other curve). -/
theorem firstLens_transversal
    (hp : ∀ a, a ≠ M.A.curve y₀ → M.Inside a (M.A.cellOf (u M y₀ kp))) :
    (firstLens M hy₀ hkp1 hkpP).Transversal := by
  classical
  set Λ := firstLens M hy₀ hkp1 hkpP
  have hs : Λ.Sep := firstLens_sep M hy₀ hkp1 hkpP
  intro y hy
  have hya : M.A.curve y ≠ M.A.curve y₀ := fun h => Lens.S_not_chord hs h hy
  set a := M.A.curve y with ha
  set P := period M.A.straight (M.A.α y₀) with hP
  obtain ⟨pa, qa, hpq⟩ := Order.flips M (y₀ := M.A.α y₀) (by rw [M.A.curve_α]) a
  obtain ⟨hpq, hfl⟩ := hpq hya
  have hb := (First.interval M hy₀ hya hpq hfl kp hkpP.le).1 (hp a hya)
  have hmem : ∀ i, i ∈ Walk.flipsOn M.A a (M.A.α y₀) → i = pa ∨ i = qa := fun i hi => by
    rw [hfl, mem_insert, mem_singleton] at hi; exact hi
  have hαc : M.A.curve (M.A.α y) = a := by rw [M.A.curve_α]
  -- two ends at the same boundary dart are impossible
  have same : ∀ k k', M.A.σ (M.A.α ((M.A.straight ^ k) y)) =
      M.A.σ (M.A.α ((M.A.straight ^ k') (M.A.α y))) → False := fun k k' e => by
    have e' := M.A.α.injective (M.A.σ.injective e)
    have h1 := M.inside_pow_of_curve (C := a) rfl k
    have h2 := M.inside_pow_of_curve hαc k'
    rw [e', h2, M.inside_α, ← ha] at h1
    tauto
  constructor
  · intro hL
    rcases Lens.ends hs (Lens.chord_α hy) with hL' | hR'
    · exfalso
      obtain ⟨k, -, j, hj1, hjk, hj⟩ := hL
      obtain ⟨k', -, j', hj1', hjk', hj'⟩ := hL'
      have e1 := hmem _ (firstLens_endpos M hy₀ (by omega) hya hj)
      have e2 := hmem _ (hαc ▸ firstLens_endpos M hy₀ (y := M.A.α y) (by omega) (by rw [hαc]; exact hya) hj')
      have hjj : j = j' := by split_ifs at e1 e2 <;> omega
      subst hjj
      exact same k k' (hj.trans hj'.symm)
    · exact hR'
  · intro hR
    rcases Lens.ends hs hy with hL | hR'
    · exact hL
    · exfalso
      obtain ⟨k, -, j, hjP, hj0, hj⟩ := hR'
      obtain ⟨k', -, j', hjP', hj0', hj'⟩ := hR
      have e1 := hmem _ (firstLens_endpos M hy₀ hjP hya hj)
      have e2 := hmem _ (hαc ▸ firstLens_endpos M hy₀ (y := M.A.α y) hjP' (by rw [hαc]; exact hya) hj')
      have hjj : j = j' := by split_ifs at e1 e2 <;> omega
      subst hjj
      exact same k k' (hj.trans hj'.symm)

end Pca.FlipGraph
