/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package A (gap lemma G1), the core

Setting (after removing `γ` from a minimal counterexample leaves a finished configuration):
there is no hump and no triangle, every curve meets the sweep, every vertex above the sweep lies
on `γ`, there is such a vertex, and every other curve reaches the ∞-arc. Then (`ab_g1_core`):

* the first segment `b` of `γ` from a vertex `l` on the sweep ends at a vertex `v` above the
  sweep, on a second curve `δ` (else `b` is a hump, or `γ` has no vertex above the sweep);
* `δ` runs from its vertex `k` on the sweep over `w`, `v` to the ∞-arc, with single segments in
  between, `w` a crossing with `γ` (otherwise a hump, a triangle with `b`, or a third crossing of
  `γ` and `δ`);
* the closed walk `C` = (`S` from `l` to `k`) + `b` + (`δ` from `k` over `w` to `v`) is a cut `r`
  (Jordan, `j_mem_range_of_mem_ker`). Above the sweep, `r` is `ρ` at the ∞-arc and at the
  segment of `γ` after `v` (`ab_g1_cut`), and `γ` crosses `C` exactly at `w` (it walks above the
  sweep from `v` to `w`), so the segment of `γ` after `w` has `r = ρ + 1`. Its other end is a
  vertex on the sweep (a triangle with `δ`'s segment from `k`), inside the ∞-arc (`r = ρ`
  there), or a crossing with a third curve `δ'`, which never crosses `C` and reaches the ∞-arc:
  a contradiction in every case.

This is a cut argument with the ray `δ`.
-/
import Pca.Sweep.AB_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-! ## Helpers -/

/-- Three crossings of the same two curves contradict the two-intersection property. -/
theorem ab_three {c c' : Fin n} (hne : c ≠ c') {x₁ x₂ x₃ : Γ.Crossing} (h12 : x₁ ≠ x₂)
    (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) (h1 : Γ.curves x₁ = {c, c'}) (h2 : Γ.curves x₂ = {c, c'})
    (h3 : Γ.curves x₃ = {c, c'}) : False := by
  classical
  have hle := Γ.isSConf.two_int c c' hne
  have hsub : ({x₁, x₂, x₃} : Finset Γ.Crossing) ⊆
      univ.filter (fun x : Orbit Γ.σ => crossingCurves Γ.σ Γ.curve x = {c, c'}) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_filter]
    rcases hx with rfl | rfl | rfl
    · exact ⟨mem_univ _, h1⟩
    · exact ⟨mem_univ _, h2⟩
    · exact ⟨mem_univ _, h3⟩
  have := card_le_card hsub
  rw [card_eq_three.2 ⟨x₁, x₂, x₃, h12, h13, h23, rfl⟩] at this
  convert hle using 0
  omega

/-- The upper arc of a curve whose walk from a vertex on `S` returns to `S` after `N + 1`
segments: every dart of the curve above `S` is on this walk. -/
theorem ab_short {a : D} (ha : Γ.Above a) (haS : Γ.S ∈ Γ.curves (Γ.crossingOf a)) {N : ℕ}
    (hall : ∀ i ≤ N, Γ.Above ((Γ.straight ^ i) a))
    (hend : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ N) a)))) {y : D} (hy : Γ.Above y)
    (hcy : Γ.curve y = Γ.curve a) :
    ∃ j ≤ N, (Γ.straight ^ j) a = y ∨ (Γ.straight ^ j) a = Γ.α y := by
  have hbA := ab_above_α (hall N le_rfl)
  have hbc : Γ.curve a = Γ.curve (Γ.α ((Γ.straight ^ N) a)) := by
    rw [j_curve_α, no_curve_pow]
  have hne : Γ.crossingOf a ≠ Γ.crossingOf (Γ.α ((Γ.straight ^ N) a)) := by
    intro h
    have h1 := ab_above_unique ha hbA haS hbc h.symm
    apply no_not_sameCycle_straight_σσ a
    refine ⟨(N + 1 : ℕ), ?_⟩
    rw [zpow_natCast, no_pow_succ, ← j_α_α Γ ((Γ.straight ^ N) a), h1, j_straight_apply, j_α_α]
  obtain ⟨L, hallL, hL, -, -, hcov⟩ := no_upper_arc ha hbA hbc haS hend hne
  rw [j_α_α] at hL
  have hLN : L ≤ N := by
    by_contra h
    push Not at h
    exact ab_no_return ha haS (j := L - N) (by omega) (fun i hi => hallL i (by omega))
      (ab_pow_cancel h.le hL.symm)
  obtain ⟨q, hq, h⟩ := hcov y hy hcy
  exact ⟨q, by omega, h⟩

theorem ab_seg_ne_of_curve {y e : D} (h : Γ.curve e ≠ Γ.curve y) :
    Γ.segmentOf y ≠ Γ.segmentOf e := by
  intro hs
  have := (j_segmentOf_eq_iff (Γ := Γ)).1 hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact h rfl
  · exact h (j_curve_α _ _)

theorem ab_seg_ne {y e : D} (h1 : e ≠ y) (h2 : e ≠ Γ.α y) : Γ.segmentOf y ≠ Γ.segmentOf e := by
  intro hs
  have := (j_segmentOf_eq_iff (Γ := Γ)).1 hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h
  · exact h1 h
  · exact h2 h

theorem ab_telescope {M : Type*} [AddCommMonoid M] (h2 : ∀ m : M, m + m = 0) (F : ℕ → M)
    {p q : ℕ} (hpq : p ≤ q) : ∑ t ∈ Ico p q, (F t + F (t + 1)) = F p + F q := by
  induction q, hpq using Nat.le_induction with
  | base => rw [Ico_self, sum_empty, h2]
  | succ q hpq ih =>
    rw [sum_Ico_succ_top hpq, ih, add_assoc, ← add_assoc (F q), h2, zero_add]

/-! ## The cut argument -/

/-- The cut of the closed walk `C` = (`S` from `l` to `k`) + `b` + `ak` + `straight ak`: `b` is
the first segment of `γ` from `l`, ending at `v`; `ak` the first segment of `δ` from `k`, ending at
`w`; `straight ak` runs from `w` to `v`. The cut changes exactly across the segments of `C`; on
darts of curves other than `S` this is described by `F`. -/
theorem ab_g1_mkcut {b ak z : D} (hz' : Γ.infStart = some z)
    (hlS : Γ.S ∈ Γ.curves (Γ.crossingOf b)) (hvS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α b)))
    (hakδ : Γ.curve ak ≠ Γ.curve b) (hδS : Γ.curve ak ≠ Γ.S)
    (hkS : Γ.S ∈ Γ.curves (Γ.crossingOf ak)) (hwS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ak)))
    (hq2 : Γ.crossingOf (Γ.α (Γ.straight ak)) = Γ.crossingOf (Γ.α b)) :
    ∃ (g : Γ.Cell → ZMod 2) (F : D → ZMod 2),
      (∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y) ∧
      (∀ y, Γ.curve y ≠ Γ.S → y ≠ b → y ≠ Γ.α b → y ≠ ak → y ≠ Γ.α ak →
        y ≠ Γ.straight ak → y ≠ Γ.α (Γ.straight ak) → F y = 0) ∧
      (∀ y, Γ.curve y ≠ Γ.S → Γ.crossingOf y ≠ Γ.crossingOf b →
        Γ.crossingOf y ≠ Γ.crossingOf (Γ.α b) → Γ.crossingOf y ≠ Γ.crossingOf ak →
        Γ.crossingOf y ≠ Γ.crossingOf (Γ.α ak) → F y = 0) ∧
      F (Γ.α ak) = 1 ∧ F (Γ.straight ak) = 1 := by
  classical
  have hsk_w : Γ.crossingOf (Γ.straight ak) = Γ.crossingOf (Γ.α ak) := no_crossingOf_α_straight ak
  -- the closed walk `C` and its cut `g`
  obtain ⟨tl, -, htl'⟩ := no_onSweep_noC hz' hlS
  obtain ⟨tk, -, htk'⟩ := no_onSweep_noC hz' hkS
  obtain ⟨p, q, hpq, hpts⟩ : ∃ p q, p ≤ q ∧
      (Pi.single (Γ.crossingOf (Γ.noC z p)) 1 + Pi.single (Γ.crossingOf (Γ.noC z q)) 1 :
        Γ.Crossing → ZMod 2) =
      Pi.single (Γ.crossingOf b) 1 + Pi.single (Γ.crossingOf ak) 1 := by
    rcases le_total tl tk with h | h
    · exact ⟨tl, tk, h, by rw [htl', htk']⟩
    · exact ⟨tk, tl, h, by rw [htl', htk', add_comm]⟩
  let sg : D → (Γ.Segment → ZMod 2) := fun y => Pi.single (Γ.segmentOf y) 1
  let h : Γ.Segment → ZMod 2 :=
    (∑ t ∈ Ico p q, sg (Γ.noC z t)) + sg b + sg ak + sg (Γ.straight ak)
  have hB : Γ.jSegBdry h = 0 := by
    have hc : ∀ t, Γ.crossingOf (Γ.α (Γ.noC z t)) = Γ.crossingOf (Γ.noC z (t + 1)) := fun t => by
      rw [← no_crossingOf_α_straight, no_noC_straight]
    simp only [h, sg, map_add, map_sum, j_segBdry_single, hc]
    rw [ab_telescope (fun m => by funext x; exact j_zmod2_add_self _)
      (fun t => (Pi.single (Γ.crossingOf (Γ.noC z t)) 1 : Γ.Crossing → ZMod 2)) hpq, hpts,
      hsk_w, hq2]
    funext x
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize (Pi.single (Γ.crossingOf b) 1 : Γ.Crossing → ZMod 2) x = A
    generalize (Pi.single (Γ.crossingOf ak) 1 : Γ.Crossing → ZMod 2) x = B
    generalize (Pi.single (Γ.crossingOf (Γ.α b)) 1 : Γ.Crossing → ZMod 2) x = V
    generalize (Pi.single (Γ.crossingOf (Γ.α ak)) 1 : Γ.Crossing → ZMod 2) x = W
    revert A B V W
    decide
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker h hB
  have hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = h (Γ.segmentOf y) := fun y => by
    rw [← j_cellBdry_segmentOf, hg]
  -- the values of `h` on darts of curves other than `S`
  have hval : ∀ y, Γ.curve y ≠ Γ.S →
      h (Γ.segmentOf y) = sg b (Γ.segmentOf y) + sg ak (Γ.segmentOf y) +
        sg (Γ.straight ak) (Γ.segmentOf y) := by
    intro y hy
    simp only [h, Pi.add_apply, Finset.sum_apply]
    rw [sum_eq_zero (fun t _ => ?_), zero_add]
    simp only [sg, Pi.single_apply]
    rw [if_neg (ab_seg_ne_of_curve (by rw [(no_noC_sweep hz' t).1]; exact fun h => hy h.symm))]
  have hsg0 : ∀ y e, e ≠ y → e ≠ Γ.α y → sg e (Γ.segmentOf y) = 0 := fun y e h1 h2 => by
    simp only [sg, Pi.single_apply]; rw [if_neg (ab_seg_ne h1 h2)]
  have hsg0' : ∀ y e, Γ.curve e ≠ Γ.curve y → sg e (Γ.segmentOf y) = 0 := fun y e h1 => by
    simp only [sg, Pi.single_apply]; rw [if_neg (ab_seg_ne_of_curve h1)]
  have hsg1 : ∀ y, sg y (Γ.segmentOf y) = 1 := fun y => by simp [sg]
  have hsk_c : Γ.curve (Γ.straight ak) = Γ.curve ak := j_curve_straight _ _
  have hf0 : ∀ y, Γ.curve y ≠ Γ.S → y ≠ b → y ≠ Γ.α b → y ≠ ak → y ≠ Γ.α ak →
      y ≠ Γ.straight ak → y ≠ Γ.α (Γ.straight ak) → h (Γ.segmentOf y) = 0 := by
    intro y hy h1 h2 h3 h4 h5 h6
    have hα : ∀ e, y ≠ Γ.α e → e ≠ Γ.α y := fun e he he' => he (by rw [he', j_α_α])
    rw [hval y hy, hsg0 y b (Ne.symm h1) (hα b h2), hsg0 y ak (Ne.symm h3) (hα ak h4),
      hsg0 y _ (Ne.symm h5) (hα _ h6), add_zero, add_zero]
  have hf0' : ∀ y, Γ.curve y ≠ Γ.S → Γ.crossingOf y ≠ Γ.crossingOf b →
      Γ.crossingOf y ≠ Γ.crossingOf (Γ.α b) → Γ.crossingOf y ≠ Γ.crossingOf ak →
      Γ.crossingOf y ≠ Γ.crossingOf (Γ.α ak) → h (Γ.segmentOf y) = 0 := by
    intro y hy h1 h2 h3 h4
    refine hf0 y hy (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))
      (fun e => h3 (by rw [e])) (fun e => h4 (by rw [e])) (fun e => h4 (by rw [e, hsk_w]))
      (fun e => h2 (by rw [e, hq2]))
  have hsk_ne_αak : Γ.straight ak ≠ Γ.α ak := by
    rw [j_straight_apply]; exact Γ.j_σσ_ne _
  have hsk_ne_ak : Γ.straight ak ≠ ak := fun e => hwS (by rw [← hsk_w, e]; exact hkS)
  have hf1 : ∀ y, (y = Γ.α ak ∨ y = Γ.straight ak) → h (Γ.segmentOf y) = 1 := by
    have hbc : ∀ y, Γ.curve y = Γ.curve ak → Γ.curve b ≠ Γ.curve y := fun y hy => by
      rw [hy]; exact Ne.symm hakδ
    rintro y (rfl | rfl)
    · have hc : Γ.curve (Γ.α ak) = Γ.curve ak := j_curve_α _ _
      rw [hval _ (by rw [hc]; exact hδS), hsg0' _ _ (hbc _ hc), j_segmentOf_α, hsg1,
        ← j_segmentOf_α, hsg0 _ _ hsk_ne_αak (by rw [j_α_α]; exact hsk_ne_ak)]
      decide
    · rw [hval _ (by rw [hsk_c]; exact hδS), hsg0' _ _ (hbc _ hsk_c), hsg1,
        hsg0 _ _ (Ne.symm hsk_ne_ak) (fun e => hvS (by rw [← hq2, ← e]; exact hkS))]
      decide
  exact ⟨g, fun y => h (Γ.segmentOf y), hr, hf0, hf0', hf1 _ (Or.inl rfl), hf1 _ (Or.inr rfl)⟩

theorem ab_ne_add_one (a : ZMod 2) : a + 1 ≠ a := by revert a; decide

/-- Above the sweep, the cut is constant on the cells at the ∞-arc (it changes only across the
curves through crossings inside the arc, and these are not on the closed walk). -/
theorem ab_cut_arc {g : Γ.Cell → ZMod 2} {F : D → ZMod 2}
    (hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y)
    (hF : ∀ y, Γ.curve y ≠ Γ.S → Γ.IsInfVertex (Γ.crossingOf y) → F y = 0) {z : D}
    (hz : Γ.infStart = some z) :
    ∀ i ≤ Γ.infLen, g (Γ.upperCell ((Γ.straight ^ i) z)) = g (Γ.upperCell z) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hsw := no_sweep_pow (no_z_sweep hz) (i + 1)
    have h1 : Γ.curve (Γ.σ (Γ.straight ((Γ.straight ^ i) z))) ≠ Γ.S := by
      rw [← no_pow_succ]; exact (no_above_σ hsw).1
    have h2 : Γ.IsInfVertex (Γ.crossingOf (Γ.σ (Γ.straight ((Γ.straight ^ i) z)))) := by
      rw [j_crossingOf_σ, no_crossingOf_α_straight]
      exact ⟨z, by rw [hz]; rfl, i, by omega, rfl⟩
    have ih' := ih (by omega)
    unfold upperCell at ih' ⊢
    rw [no_pow_succ, no_walk_sweep hr, ih', hF _ h1 h2, add_zero]

theorem ab_cut_inf {g : Γ.Cell → ZMod 2} {F : D → ZMod 2}
    (hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y)
    (hF : ∀ y, Γ.curve y ≠ Γ.S → Γ.IsInfVertex (Γ.crossingOf y) → F y = 0) {z : D}
    (hz : Γ.infStart = some z) {y : D} (hy : Γ.Above y) (hinf : Γ.IsInfVertex (Γ.crossingOf y)) :
    g (Γ.cellOf y) = g (Γ.upperCell z) := by
  have hR1 := ab_cut_arc hr hF hz
  obtain ⟨hsw, h4⟩ := no_sweep_of_above hy (ab_infVertex_onSweep hinf)
  have harc := ab_arc_of_inf hsw (by rw [j_crossingOf_σ, j_crossingOf_σ, j_crossingOf_σ]; exact hinf)
  obtain ⟨i, hi, hi'⟩ := (no_mem_infArc hz).1 harc
  rw [← hR1 i hi, hi']
  unfold upperCell
  rw [← j_cellOf_σ, h4]

/-- The cut argument (see the module docstring). `b` is the first segment of `γ` from `l`, ending
at `v`; `ak` is the first segment of `δ` from `k`, ending at `w`; `straight ak` runs from `w` to
`v`, and `straight² ak` from `v` into the ∞-arc. -/
theorem ab_g1_cut {γ : Fin n} (hab : ∀ x, Γ.IsAboveVertex x → Γ.OnCurve γ x)
    (hTri : ∀ a b, Γ.IsTri a b → Γ.curve a ≠ γ → False)
    (hray : ∀ c, c ≠ γ → Γ.Present c → ∃ x, Γ.IsInfVertex x ∧ c ∈ Γ.curves x)
    {b ak : D} (hb : Γ.Above b) (hbγ : Γ.curve b = γ) (hl : Γ.IsFinVertex (Γ.crossingOf b))
    (hv : Γ.IsAboveVertex (Γ.crossingOf (Γ.α b)))
    (hak : Γ.Above ak) (hakδ : Γ.curve ak = Γ.curve (Γ.σ (Γ.α b)))
    (hk : Γ.IsFinVertex (Γ.crossingOf ak))
    (hw : Γ.IsAboveVertex (Γ.crossingOf (Γ.α ak)))
    (hwv : Γ.crossingOf (Γ.α ak) ≠ Γ.crossingOf (Γ.α b))
    (hq2 : Γ.crossingOf (Γ.α (Γ.straight ak)) = Γ.crossingOf (Γ.α b))
    (hq3 : Γ.IsInfVertex (Γ.crossingOf (Γ.α ((Γ.straight ^ 2) ak)))) : False := by
  classical
  set δ := Γ.curve (Γ.σ (Γ.α b)) with hδ
  have hγS : γ ≠ Γ.S := by rw [← hbγ]; exact hb.1
  have hδγ : δ ≠ γ := by rw [hδ, ← hbγ, ← j_curve_α Γ b]; exact no_curve_σ_ne _
  have hδS : δ ≠ Γ.S := by rw [← hakδ]; exact hak.1
  have hlS : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hl.1
  have hkS : Γ.S ∈ Γ.curves (Γ.crossingOf ak) := hk.1
  have hcv : Γ.curves (Γ.crossingOf (Γ.α b)) = {γ, δ} := by
    rw [j_curves_crossingOf, j_curve_α, hbγ]
  have hγw : γ ∈ Γ.curves (Γ.crossingOf (Γ.α ak)) := hab _ hw
  have hcw : Γ.curves (Γ.crossingOf (Γ.α ak)) = {γ, δ} := by
    refine no_mem_curves (S := δ) ?_ hγw (Ne.symm hδγ)
    rw [← hakδ, ← j_curve_α Γ ak]; exact ab_mem_curves_self _
  have hsk_w : Γ.crossingOf (Γ.straight ak) = Γ.crossingOf (Γ.α ak) := no_crossingOf_α_straight ak
  have hs2_v : Γ.crossingOf ((Γ.straight ^ 2) ak) = Γ.crossingOf (Γ.α b) := by
    rw [no_pow_succ, pow_one, no_crossingOf_α_straight, hq2]
  have hvS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α b)) := hv.1
  have hwS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ak)) := hw.1
  -- the walk of `γ` from `b` above the sweep to `w`
  have hgw_c : Γ.curve (Γ.σ (Γ.α ak)) = γ :=
    ab_other_curve hγw (by rw [j_curve_α, hakδ]; exact Ne.symm hδγ)
  have hgw_A : Γ.Above (Γ.σ (Γ.α ak)) := ab_above_of_aboveVertex hw (j_crossingOf_σ _ _)
  have hgw_x : Γ.crossingOf (Γ.σ (Γ.α ak)) = Γ.crossingOf (Γ.α ak) := j_crossingOf_σ _ _
  obtain ⟨m, hm1, hallm, hmw⟩ : ∃ m, 1 ≤ m ∧ (∀ i ≤ m, Γ.Above ((Γ.straight ^ i) b)) ∧
      Γ.crossingOf (Γ.α ((Γ.straight ^ m) b)) = Γ.crossingOf (Γ.α ak) := by
    have hnot0 : Γ.crossingOf (Γ.α b) ≠ Γ.crossingOf (Γ.α ak) := Ne.symm hwv
    rcases upper_arc hb hgw_A (hbγ.trans hgw_c.symm) with ⟨j, hj, hje⟩ | h | ⟨j, hj, hje⟩ | h
    · rcases j with _ | j
      · exfalso
        rw [pow_zero, Perm.one_apply] at hje
        exact hwS (by rw [← hgw_x, ← hje]; exact hlS)
      · have hx : Γ.crossingOf (Γ.α ((Γ.straight ^ j) b)) = Γ.crossingOf (Γ.α ak) := by
          rw [← no_crossingOf_α_straight, ← no_pow_succ, hje, hgw_x]
        refine ⟨j, ?_, fun i hi => hj i (by omega), hx⟩
        rcases j with _ | j
        · exact absurd (by rw [← hx, pow_zero, Perm.one_apply]) hnot0
        · omega
    · exfalso
      have := no_upperWalk_to hb hlS h
      exact hwS (by rw [← hgw_x, this]; exact hlS)
    · have hx : Γ.crossingOf (Γ.α ((Γ.straight ^ j) b)) = Γ.crossingOf (Γ.α ak) := by
        rw [hje, j_α_α, hgw_x]
      refine ⟨j, ?_, hj, hx⟩
      rcases j with _ | j
      · exact absurd (by rw [← hx, pow_zero, Perm.one_apply]) hnot0
      · omega
    · exfalso
      have := no_upperWalk_to hb hlS h
      apply hnot0
      rw [← this, j_α_α, hgw_x]
  have hAm1 : Γ.Above ((Γ.straight ^ (m + 1)) b) :=
    ab_above_of_aboveVertex hw (by rw [no_pow_succ, no_crossingOf_α_straight, hmw])
  have hall1 : ∀ i ≤ m + 1, Γ.Above ((Γ.straight ^ i) b) := by
    intro i hi
    by_cases h : i ≤ m
    · exact hallm i h
    · rw [show i = m + 1 by omega]; exact hAm1
  -- the cut
  obtain ⟨z, hz, -⟩ := id hq3
  have hz' : Γ.infStart = some z := hz
  obtain ⟨g, F, hr, hf0, hf0', hFak, hFsk⟩ := ab_g1_mkcut hz' hlS hvS
    (by rw [hakδ, hbγ]; exact hδγ) (by rw [hakδ]; exact hδS) hkS hwS hq2
  have hF_inf : ∀ y, Γ.curve y ≠ Γ.S → Γ.IsInfVertex (Γ.crossingOf y) → F y = 0 :=
    fun y hy hi => hf0' y hy (fun e => hl.2 (by rw [← e]; exact hi))
      (fun e => hvS (by rw [← e]; exact ab_infVertex_onSweep hi))
      (fun e => hk.2 (by rw [← e]; exact hi))
      (fun e => hwS (by rw [← e]; exact ab_infVertex_onSweep hi))
  set ρ := g (Γ.upperCell z) with hρ
  have hR2 : ∀ y, Γ.Above y → Γ.IsInfVertex (Γ.crossingOf y) → g (Γ.cellOf y) = ρ :=
    fun y hy hi => ab_cut_inf hr hF_inf hz' hy hi
  have hsame : ∀ y, F y = 0 → g (Γ.cellOf (Γ.α y)) = g (Γ.cellOf y) := fun y hy => by
    have := hr y; rw [hy] at this; rw [j_zmod2_eq_add_of_add_eq this, add_zero]
  have hsbv : Γ.crossingOf (Γ.straight b) = Γ.crossingOf (Γ.α b) := no_crossingOf_α_straight b
  have hsb_c : Γ.curve (Γ.straight b) = γ := by rw [j_curve_straight, hbγ]
  have hcross_pow : ∀ i, Γ.crossingOf (Γ.α ((Γ.straight ^ i) b)) =
      Γ.crossingOf ((Γ.straight ^ (i + 1)) b) := fun i => by
    rw [no_pow_succ, no_crossingOf_α_straight]
  -- (1) the segment of `γ` after `v` has `r = ρ`
  have hV1 : g (Γ.cellOf (Γ.straight b)) = ρ := by
    have hs2A : Γ.Above ((Γ.straight ^ 2) ak) := ab_above_of_aboveVertex hv hs2_v
    have hs2c : Γ.curve ((Γ.straight ^ 2) ak) = δ := by rw [no_curve_pow, hakδ]
    have hs2s : (Γ.straight ^ 2) ak = Γ.straight (Γ.straight ak) := by
      rw [no_pow_succ, pow_one]
    have hF2 : F ((Γ.straight ^ 2) ak) = 0 := by
      refine hf0 _ (by rw [hs2c]; exact hδS) (fun e => hδγ ?_) (fun e => hδγ ?_)
        (fun e => hvS ?_) (fun e => hwv ?_) (fun e => hwv ?_) ?_
      · rw [← hs2c, e, hbγ]
      · rw [← hs2c, e, j_curve_α, hbγ]
      · rw [← hs2_v, e]; exact hkS
      · rw [← hs2_v, e]
      · rw [← hs2_v, e, hsk_w]
      · rw [hs2s, j_straight_apply]; exact Γ.j_σσ_ne _
    have hg2 : g (Γ.cellOf ((Γ.straight ^ 2) ak)) = ρ := by
      rw [← hsame _ hF2]; exact hR2 _ (ab_above_α hs2A) hq3
    have hFsb : F (Γ.straight b) = 0 := by
      refine hf0 _ (by rw [hsb_c]; exact hγS) (fun e => hvS ?_) ?_ (fun e => hδγ ?_)
        (fun e => hδγ ?_) (fun e => hδγ ?_) (fun e => hδγ ?_)
      · rw [← hsbv, e]; exact hlS
      · rw [j_straight_apply]; exact Γ.j_σσ_ne _
      · rw [← hakδ, ← e, hsb_c]
      · rw [← hakδ, ← j_curve_α Γ ak, ← e, hsb_c]
      · rw [← hakδ, ← j_curve_straight Γ ak, ← e, hsb_c]
      · rw [← hakδ, ← j_curve_straight Γ ak, ← j_curve_α Γ (Γ.straight ak), ← e, hsb_c]
    rcases no_mem_crossing hs2_v with h | h | h | h
    · exact absurd (by rw [← hs2c, h, j_curve_α, hbγ]) hδγ
    · have := no_corner hr (Γ.σ (Γ.α b))
      rw [show Γ.σ (Γ.σ (Γ.α b)) = Γ.straight b from (j_straight_apply Γ b).symm, ← h,
        hF2] at this
      rw [j_zmod2_eq_add_of_add_eq this, add_zero, hg2]
    · exact absurd (by rw [← hs2c, h, ← j_straight_apply, hsb_c]) hδγ
    · have := no_corner hr (Γ.σ (Γ.σ (Γ.α b)))
      rw [← h, show Γ.σ (Γ.σ (Γ.α b)) = Γ.straight b from (j_straight_apply Γ b).symm,
        hFsb] at this
      have e := j_zmod2_eq_add_of_add_eq this
      rw [add_zero] at e
      rw [← e]; exact hg2
  -- (2) along `γ` from `v` to `w` the cut does not change
  have hbS' : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hlS
  have hV2 : ∀ i, 1 ≤ i → i ≤ m → g (Γ.cellOf ((Γ.straight ^ i) b)) = ρ := by
    intro i hi1
    induction i, hi1 using Nat.le_induction with
    | base => intro _; rw [pow_one]; exact hV1
    | succ i hi1 ih =>
      intro him
      have hx : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) b))) := fun hS =>
        no_exit (hallm i (by omega)) hS (by rw [← no_pow_succ]; exact hallm (i + 1) him)
      have hF : F (Γ.σ (Γ.α ((Γ.straight ^ i) b))) = 0 := by
        refine hf0' _ (ab_curves_ne_S hx (j_crossingOf_σ _ _)) ?_ ?_ ?_ ?_ <;>
          rw [j_crossingOf_σ]
        · exact fun e => hx (by rw [e]; exact hlS)
        · intro e
          rw [hcross_pow, ← hsbv, ← pow_one Γ.straight] at e
          have := ab_walk_inj hb hlS hall1 (by omega) (by omega) e
          omega
        · exact fun e => hx (by rw [e]; exact hkS)
        · intro e
          rw [← hmw, hcross_pow, hcross_pow] at e
          have := ab_walk_inj hb hlS hall1 (by omega) (by omega) e
          omega
      rw [no_pow_succ, no_walk_straight hr, ih (by omega), hF, add_zero]
  -- (3) the segment of `γ` after `w` has `r = ρ + 1`
  have hV3 : g (Γ.cellOf ((Γ.straight ^ (m + 1)) b)) = ρ + 1 := by
    rw [no_pow_succ, no_walk_straight hr, hV2 m hm1 le_rfl]
    congr 1
    have hyc : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ m) b))) ≠ γ := by
      have := no_curve_σ_ne (Γ := Γ) (Γ.α ((Γ.straight ^ m) b))
      rwa [j_curve_α, no_curve_pow, hbγ] at this
    have hyx : Γ.crossingOf (Γ.σ (Γ.α ((Γ.straight ^ m) b))) = Γ.crossingOf (Γ.α ak) := by
      rw [j_crossingOf_σ, hmw]
    rcases no_mem_crossing hyx with h | h | h | h
    · rw [h]; exact hFak
    · exact absurd (by rw [h, hgw_c]) hyc
    · rw [h, ← j_straight_apply]; exact hFsk
    · exact absurd (by rw [h, j_curve_σσ, hgw_c]) hyc
  -- (4) the other end `u` of the segment `g₀` of `γ` after `w`
  set g₀ := (Γ.straight ^ (m + 1)) b with hg₀
  have hg₀c : Γ.curve g₀ = γ := by rw [hg₀, no_curve_pow, hbγ]
  have hg₀x : Γ.crossingOf g₀ = Γ.crossingOf (Γ.α ak) := by rw [hg₀, ← hcross_pow, hmw]
  have hFg₀ : F g₀ = 0 := by
    refine hf0 _ (by rw [hg₀c]; exact hγS) (fun e => hwS ?_) (fun e => hwv ?_)
      (fun e => hδγ ?_) (fun e => hδγ ?_) (fun e => hδγ ?_) (fun e => hδγ ?_)
    · rw [← hg₀x, e]; exact hlS
    · rw [← hg₀x, e]
    · rw [← hakδ, ← e, hg₀c]
    · rw [← hakδ, ← j_curve_α Γ ak, ← e, hg₀c]
    · rw [← hakδ, ← j_curve_straight Γ ak, ← e, hg₀c]
    · rw [← hakδ, ← j_curve_straight Γ ak, ← j_curve_α Γ (Γ.straight ak), ← e, hg₀c]
  have hαg₀ : g (Γ.cellOf (Γ.α g₀)) = ρ + 1 := by rw [hsame _ hFg₀, hV3]
  have hαg₀A : Γ.Above (Γ.α g₀) := ab_above_α hAm1
  have hγu : γ ∈ Γ.curves (Γ.crossingOf (Γ.α g₀)) := by
    rw [← hg₀c, ← j_curve_α Γ g₀]; exact ab_mem_curves_self _
  by_cases huS : Γ.OnSweep (Γ.crossingOf (Γ.α g₀))
  · by_cases hufin : Γ.IsFinVertex (Γ.crossingOf (Γ.α g₀))
    · -- a triangle with `δ`'s segment from `k`
      refine hTri ak (Γ.α g₀) ⟨hak, hαg₀A, hk, hufin, fun e => ?_, by rw [j_α_α, hg₀x], hw,
        by rw [j_curve_α, hg₀c, hakδ]; exact hδγ⟩ (by rw [hakδ]; exact hδγ)
      rw [← e, j_curves_crossingOf, hakδ, ab_other_curve hkS (by rw [hakδ]; exact Ne.symm hδS),
        mem_insert, mem_singleton] at hγu
      rcases hγu with h | h
      · exact hδγ h.symm
      · exact hγS h
    · -- `u` inside the ∞-arc
      have hinf : Γ.IsInfVertex (Γ.crossingOf (Γ.α g₀)) := by
        by_contra h; exact hufin ⟨huS, h⟩
      exact ab_ne_add_one ρ (hαg₀.symm.trans (hR2 _ hαg₀A hinf))
  · -- `u` is a crossing with a third curve `δ'`
    have hu : Γ.IsAboveVertex (Γ.crossingOf (Γ.α g₀)) := ab_aboveVertex_of hαg₀A huS
    have hAm2 : Γ.Above ((Γ.straight ^ (m + 2)) b) := ab_above_of_aboveVertex hu (by
      rw [show m + 2 = (m + 1) + 1 by omega, ← hcross_pow])
    have hall2 : ∀ i ≤ m + 2, Γ.Above ((Γ.straight ^ i) b) := by
      intro i hi
      by_cases h : i ≤ m + 1
      · exact hall1 i h
      · rw [show i = m + 2 by omega]; exact hAm2
    have hux : Γ.crossingOf (Γ.α g₀) = Γ.crossingOf ((Γ.straight ^ (m + 2)) b) := by
      rw [hg₀, hcross_pow]
    have hvx : Γ.crossingOf (Γ.α b) = Γ.crossingOf ((Γ.straight ^ 1) b) := by
      rw [pow_one, hsbv]
    have hwx : Γ.crossingOf (Γ.α ak) = Γ.crossingOf ((Γ.straight ^ (m + 1)) b) := hg₀x.symm
    have huv : Γ.crossingOf (Γ.α g₀) ≠ Γ.crossingOf (Γ.α b) := fun e => by
      rw [hux, hvx] at e
      have := ab_walk_inj hb hlS hall2 le_rfl (by omega) e
      omega
    have huw : Γ.crossingOf (Γ.α g₀) ≠ Γ.crossingOf (Γ.α ak) := fun e => by
      rw [hux, hwx] at e
      have := ab_walk_inj hb hlS hall2 le_rfl (by omega) e
      omega
    set y₀ := Γ.σ (Γ.α g₀) with hy₀
    have hy₀x : Γ.crossingOf y₀ = Γ.crossingOf (Γ.α g₀) := j_crossingOf_σ _ _
    have hy₀A : Γ.Above y₀ := ab_above_of_aboveVertex hu hy₀x
    have hδ'γ : Γ.curve y₀ ≠ γ := by
      have := no_curve_σ_ne (Γ := Γ) (Γ.α g₀)
      rwa [j_curve_α, hg₀c] at this
    have hδ'S : Γ.curve y₀ ≠ Γ.S := hy₀A.1
    have hcu : Γ.curves (Γ.crossingOf (Γ.α g₀)) = {γ, Γ.curve y₀} := by
      rw [j_curves_crossingOf, j_curve_α, hg₀c]
    have hδ'δ : Γ.curve y₀ ≠ δ := by
      intro e
      rw [e] at hcu
      exact ab_three (Ne.symm hδγ) (Ne.symm hwv) huv.symm huw.symm hcv hcw hcu
    obtain ⟨p', hp'inf, hp'c⟩ := hray _ hδ'γ ⟨hδ'S, y₀, rfl, hy₀A⟩
    obtain ⟨a', ha'x, ha'c, ha'A, -, -⟩ :=
      ab_up_dart (ab_infVertex_onSweep hp'inf) hp'c hδ'S
    have ha'S : Γ.S ∈ Γ.curves (Γ.crossingOf a') := by
      rw [ha'x]; exact ab_infVertex_onSweep hp'inf
    have hga' : g (Γ.cellOf a') = ρ := hR2 a' ha'A (by rw [ha'x]; exact hp'inf)
    have hgy₀ : g (Γ.cellOf y₀) = ρ + 1 := by rw [hy₀, j_cellOf_σ, j_α_α, hV3]
    have hFy₀ : F y₀ = 0 := by
      refine hf0' _ hδ'S ?_ ?_ ?_ ?_ <;> rw [hy₀x]
      · exact fun e => huS (by rw [e]; exact hlS)
      · exact huv
      · exact fun e => huS (by rw [e]; exact hkS)
      · exact huw
    have hgαy₀ : g (Γ.cellOf (Γ.α y₀)) = ρ + 1 := by rw [hsame _ hFy₀, hgy₀]
    -- walking along `δ'` above the sweep does not change the cut
    have hwalk : ∀ j, (∀ i ≤ j, Γ.Above ((Γ.straight ^ i) a')) →
        g (Γ.cellOf ((Γ.straight ^ j) a')) = ρ := by
      intro j
      induction j with
      | zero => intro _; exact hga'
      | succ j ih =>
        intro hall
        have hx : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ j) a'))) := fun hS =>
          no_exit (hall j (by omega)) hS (by rw [← no_pow_succ]; exact hall (j + 1) le_rfl)
        have hcj : Γ.curve (Γ.α ((Γ.straight ^ j) a')) = Γ.curve y₀ := by
          rw [j_curve_α, no_curve_pow, ha'c]
        have hmem : Γ.curve y₀ ∈ Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ j) a'))) := by
          rw [← hcj]; exact ab_mem_curves_self _
        have hF : F (Γ.σ (Γ.α ((Γ.straight ^ j) a'))) = 0 := by
          refine hf0' _ (ab_curves_ne_S hx (j_crossingOf_σ _ _)) ?_ ?_ ?_ ?_ <;>
            rw [j_crossingOf_σ]
          · exact fun e => hx (by rw [e]; exact hlS)
          · intro e
            rw [e, hcv, mem_insert, mem_singleton] at hmem
            rcases hmem with h | h
            · exact hδ'γ h
            · exact hδ'δ h
          · exact fun e => hx (by rw [e]; exact hkS)
          · intro e
            rw [e, hcw, mem_insert, mem_singleton] at hmem
            rcases hmem with h | h
            · exact hδ'γ h
            · exact hδ'δ h
        rw [no_pow_succ, no_walk_straight hr, ih (fun i hi => hall i (by omega)), hF, add_zero]
    rcases upper_arc ha'A hy₀A (ha'c.trans rfl) with ⟨j, hj, hje⟩ | h | ⟨j, hj, hje⟩ | h
    · exact ab_ne_add_one ρ (hgy₀.symm.trans (by rw [← hje]; exact hwalk j hj))
    · have := no_upperWalk_to ha'A ha'S h
      exact huS (by rw [← hy₀x, this]; exact ha'S)
    · exact ab_ne_add_one ρ (hgαy₀.symm.trans (by rw [← hje]; exact hwalk j hj))
    · have := no_upperWalk_to ha'A ha'S h
      exact ab_ne_add_one ρ (hgαy₀.symm.trans (by rw [this]; exact hga'))

/-- **Core of G1** (see the module docstring). -/
theorem ab_g1_core {γ : Fin n} (hTri : ∀ a b, Γ.IsTri a b → Γ.curve a ≠ γ → False)
    (hMeet : ∀ c, Γ.Present c → Γ.MeetsSweep c) (hγ : Γ.Present γ)
    (hab : ∀ x, Γ.IsAboveVertex x → Γ.OnCurve γ x) (hex : ∃ x, Γ.IsAboveVertex x)
    (hray : ∀ c, c ≠ γ → Γ.Present c → ∃ x, Γ.IsInfVertex x ∧ c ∈ Γ.curves x) : False := by
  classical
  have h0 : ∀ {a : D}, Γ.Above a → ∀ i ≤ 0, Γ.Above ((Γ.straight ^ i) a) := fun ha i hi => by
    rw [Nat.le_zero.1 hi, pow_zero, Perm.one_apply]; exact ha
  -- the first segment `b` of `γ` from a vertex `l` on the sweep
  obtain ⟨l, hlfin, hlγ⟩ := hMeet γ hγ
  obtain ⟨b, hbx, hbc, hbA, -, -⟩ := ab_up_dart hlfin.1 hlγ hγ.1
  have hl : Γ.IsFinVertex (Γ.crossingOf b) := by rw [hbx]; exact hlfin
  have hlS : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hl.1
  -- it ends at a vertex `v` above the sweep
  have hvS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α b)) := by
    intro hS
    obtain ⟨x, hx⟩ := hex
    obtain ⟨y, hy, hyc⟩ := mem_image.1 (hab x hx)
    have hyA := ab_above_of_aboveVertex hx (ab_mem_darts hy)
    obtain ⟨j, hj, h⟩ := ab_short hbA hlS (h0 hbA)
      (by rw [pow_zero, Perm.one_apply]; exact hS) hyA (hyc.trans hbc.symm)
    rw [Nat.le_zero.1 hj, pow_zero, Perm.one_apply] at h
    rcases h with h | h
    · exact hx.1 (by rw [← ab_mem_darts hy, ← h]; exact hlS)
    · exact hx.1 (by rw [← ab_mem_darts hy, ← j_α_α Γ y, ← h]; exact hS)
  have hv : Γ.IsAboveVertex (Γ.crossingOf (Γ.α b)) := ab_aboveVertex_of (ab_above_α hbA) hvS
  -- the second curve `δ` at `v`
  set δ := Γ.curve (Γ.σ (Γ.α b)) with hδ
  have hδA : Γ.Above (Γ.σ (Γ.α b)) := ab_above_of_aboveVertex hv (j_crossingOf_σ _ _)
  have hδγ : δ ≠ γ := by rw [hδ, ← hbc, ← j_curve_α Γ b]; exact no_curve_σ_ne _
  have hγS : γ ≠ Γ.S := hγ.1
  have hcv : Γ.curves (Γ.crossingOf (Γ.α b)) = {γ, δ} := by
    rw [j_curves_crossingOf, j_curve_α, hbc]
  have hyv : Γ.crossingOf (Γ.σ (Γ.α b)) = Γ.crossingOf (Γ.α b) := j_crossingOf_σ _ _
  -- the first segment `ak` of `δ` from a vertex `k` on the sweep, ending at `w`
  obtain ⟨k, hkfin, hkδ⟩ := hMeet δ ⟨hδA.1, _, rfl, hδA⟩
  obtain ⟨ak, hakx, hakc, hakA, -, -⟩ := ab_up_dart hkfin.1 hkδ hδA.1
  have hk : Γ.IsFinVertex (Γ.crossingOf ak) := by rw [hakx]; exact hkfin
  have hkS : Γ.S ∈ Γ.curves (Γ.crossingOf ak) := hk.1
  have hwS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ak)) := by
    intro hS
    obtain ⟨j, hj, h⟩ := ab_short hakA hkS (h0 hakA)
      (by rw [pow_zero, Perm.one_apply]; exact hS) hδA hakc.symm
    rw [Nat.le_zero.1 hj, pow_zero, Perm.one_apply] at h
    rcases h with h | h
    · exact hvS (by rw [← hyv, ← h]; exact hkS)
    · exact hvS (by rw [← hyv, ← j_α_α Γ (Γ.σ (Γ.α b)), ← h]; exact hS)
  have hw : Γ.IsAboveVertex (Γ.crossingOf (Γ.α ak)) := ab_aboveVertex_of (ab_above_α hakA) hwS
  have hγw : γ ∈ Γ.curves (Γ.crossingOf (Γ.α ak)) := hab _ hw
  have hcw : Γ.curves (Γ.crossingOf (Γ.α ak)) = {γ, δ} := by
    refine no_mem_curves (S := δ) ?_ hγw (Ne.symm hδγ)
    rw [← hakc, ← j_curve_α Γ ak]; exact ab_mem_curves_self _
  have hne_l : ∀ x, δ ∈ Γ.curves x → x ≠ Γ.crossingOf b := by
    intro x hx e
    rw [e, j_curves_crossingOf, hbc, ab_other_curve hlS (by rw [hbc]; exact Ne.symm hγS),
      mem_insert, mem_singleton] at hx
    rcases hx with h | h
    · exact hδγ h
    · exact hδA.1 h
  have hwv : Γ.crossingOf (Γ.α ak) ≠ Γ.crossingOf (Γ.α b) := by
    intro e
    refine hTri ak b ⟨hakA, hbA, hk, hl, hne_l _ (by rw [← hakc]; exact ab_mem_curves_self _),
      e, by rw [e]; exact hv, by rw [hakc, hbc]; exact hδγ⟩ (by rw [hakc]; exact hδγ)
  -- `straight ak` runs from `w` to `v`
  have hsA : Γ.Above (Γ.straight ak) :=
    ab_above_of_aboveVertex hw (no_crossingOf_α_straight ak)
  have h1 : ∀ i ≤ 1, Γ.Above ((Γ.straight ^ i) ak) := by
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · rw [pow_zero, Perm.one_apply]; exact hakA
    · rw [pow_one]; exact hsA
  have hq2S : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α (Γ.straight ak))) := by
    intro hS
    obtain ⟨j, hj, h⟩ := ab_short hakA hkS h1 (by rw [pow_one]; exact hS) hδA hakc.symm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
    · rw [pow_zero, Perm.one_apply] at h
      rcases h with h | h
      · exact hvS (by rw [← hyv, ← h]; exact hkS)
      · exact hwv (by rw [h, j_α_α, hyv])
    · rw [pow_one] at h
      rcases h with h | h
      · exact hwv (by rw [← hyv, ← h, no_crossingOf_α_straight])
      · exact hvS (by rw [← hyv, ← j_α_α Γ (Γ.σ (Γ.α b)), ← h]; exact hS)
  have hcross : ∀ i, Γ.crossingOf (Γ.α ((Γ.straight ^ i) ak)) =
      Γ.crossingOf ((Γ.straight ^ (i + 1)) ak) := fun i => by
    rw [no_pow_succ, no_crossingOf_α_straight]
  have hcδ : ∀ i, δ ∈ Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ i) ak))) := fun i => by
    rw [← hakc, ← no_curve_pow (Γ := Γ) ak i, ← j_curve_α Γ]; exact ab_mem_curves_self _
  have hcurves : ∀ i, ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) ak))) →
      Γ.Above (Γ.α ((Γ.straight ^ i) ak)) →
      Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ i) ak))) = {γ, δ} := fun i hS hA =>
    no_mem_curves (S := δ) (hcδ i) (hab _ (ab_aboveVertex_of hA hS)) (Ne.symm hδγ)
  have hwx : Γ.crossingOf (Γ.α ak) = Γ.crossingOf ((Γ.straight ^ 1) ak) := by
    rw [← hcross 0, pow_zero, Perm.one_apply]
  have hq2 : Γ.crossingOf (Γ.α (Γ.straight ak)) = Γ.crossingOf (Γ.α b) := by
    by_contra hne
    have hA2 : Γ.Above (Γ.α (Γ.straight ak)) := ab_above_α hsA
    have hall : ∀ i ≤ 2, Γ.Above ((Γ.straight ^ i) ak) := by
      intro i hi
      by_cases h : i ≤ 1
      · exact h1 i h
      · rw [show i = 2 by omega]
        exact ab_above_of_aboveVertex (ab_aboveVertex_of hA2 hq2S)
          (by rw [← hcross 1, pow_one])
    have hc2 := hcurves 1 (by rw [pow_one]; exact hq2S) (by rw [pow_one]; exact hA2)
    rw [pow_one] at hc2
    refine ab_three (Ne.symm hδγ) (Ne.symm hwv) (Ne.symm hne) (fun e => ?_) hcv hcw hc2
    rw [hwx, show Γ.straight ak = (Γ.straight ^ 1) ak by rw [pow_one],
      hcross 1] at e
    have := ab_walk_inj hakA hkS hall (by omega) le_rfl e
    omega
  -- `straight² ak` runs from `v` into the ∞-arc
  have hs2A : Γ.Above ((Γ.straight ^ 2) ak) :=
    ab_above_of_aboveVertex hv (by rw [← hcross 1, pow_one, hq2])
  have hq3S : Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ 2) ak))) := by
    by_contra hS
    have hA3 : Γ.Above (Γ.α ((Γ.straight ^ 2) ak)) := ab_above_α hs2A
    have hall : ∀ i ≤ 3, Γ.Above ((Γ.straight ^ i) ak) := by
      intro i hi
      by_cases h : i ≤ 1
      · exact h1 i h
      by_cases h' : i = 2
      · rw [h']; exact hs2A
      · rw [show i = 3 by omega]
        exact ab_above_of_aboveVertex (ab_aboveVertex_of hA3 hS) (by rw [← hcross 2])
    have hc3 := hcurves 2 hS hA3
    have hvx : Γ.crossingOf (Γ.α b) = Γ.crossingOf ((Γ.straight ^ 2) ak) := by
      rw [← hcross 1, pow_one, hq2]
    refine ab_three (Ne.symm hδγ) (Ne.symm hwv) (fun e => ?_) (fun e => ?_) hcv hcw hc3
    · rw [hvx, hcross 2] at e
      have := ab_walk_inj hakA hkS hall (by omega) le_rfl e
      omega
    · rw [hwx, hcross 2] at e
      have := ab_walk_inj hakA hkS hall (by omega) le_rfl e
      omega
  have hq3 : Γ.IsInfVertex (Γ.crossingOf (Γ.α ((Γ.straight ^ 2) ak))) := by
    by_contra hinf
    refine hTri (Γ.α ((Γ.straight ^ 2) ak)) b ⟨ab_above_α hs2A, hbA, ⟨hq3S, hinf⟩, hl,
      hne_l _ (hcδ 2), ?_, ?_, ?_⟩ (by rw [j_curve_α, no_curve_pow, hakc]; exact hδγ)
    · rw [j_α_α, ← hcross 1, pow_one, hq2]
    · rw [j_α_α, ← hcross 1, pow_one, hq2]; exact hv
    · rw [j_curve_α, no_curve_pow, hakc, hbc]; exact hδγ
  exact ab_g1_cut hab hTri hray hbA hbc hl hv hakA hakc hk hw hwv hq2 hq3

end SConf

end Pca.Sweep
