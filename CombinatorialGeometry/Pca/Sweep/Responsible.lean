/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH p. 322: one leg, responsible edges, a loop exists (package K)

"Because the removal of a curve `γ` does not allow us to move past a hump (Lemma 3.8) or take an
edge (Lemma 3.4), it must leave an empty triangle in the arrangement `Γ − {γ}`, which we denote
`Δ(i, v, j)`. Since `γ` cannot intersect the sweep between `i` and `j` (Lemma 3.7), we can assume
that `j = i + 1`." (pp. 319-320)

"We have shown that removing any curve `γ` from the minimum counterexample `Γ` must leave an empty
triangle and that `γ` must intersect only one leg of that triangle. If removing `γ` leaves
`Δ(i, v, i + 1)`, then we say that the edge `[i, i + 1]` is *responsible* for `γ`. Notice that each
edge of the sweep is responsible for at most one curve. (See Figure 11.)
In order to have an edge of the sweep responsible for every one of the `n` curves in the set `Γ`,
we need at least `n + 1` vertices on the sweep. Thus, there is a curve that intersects the sweep
twice." (p. 322)

`responsible_unique` is a **claim without proof in the source; proof to be reconstructed**.
-/
import Pca.Sweep.L39
import Pca.Derived
import Pca.Sweep.GK_Tri

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- After 3.8 (pp. 319-320): removing a curve from a minimal counterexample leaves an empty
triangle. Proved from Lemmas 3.3, 3.4, 3.8 and G1. -/
theorem MinCE.removal_leaves_triangle (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ)
    (X : Γ.Removal {γ}) : ∃ d', X.Γ'.EmptyTriAt d' := by
  have h1 := hΓ.lemma_3_3 ⟨γ, mem_singleton_self γ, hγ⟩ X
  have h2 := hΓ.removal_not_terminal hγ X
  have hP : X.Γ'.Progress := by
    by_contra h
    exact h1 ⟨h2, h⟩
  rcases hP with ⟨d', hd'⟩ | h | ⟨d, e, hd, he, hS, hm⟩
  · exact absurd hd' (hΓ.lemma_3_8 X d')
  · exact h
  · exfalso
    have hc : X.Γ'.cellOf e = X.Γ'.upperCell d := Orbit.mem_darts.1 he
    have hp : X.Γ'.Present (X.Γ'.curve e) := ⟨hS, e, rfl, hS, by rw [hc]; exact hd.2⟩
    obtain ⟨hpΓ, -, hiff⟩ := X.meetsSweep_iff hp
    exact hm (hiff.2 (hΓ.lemma_3_4 hpΓ))

/-- The finite edge of `Γ − γ` below its empty triangle is a finite edge of `Γ`. -/
private theorem gk_finSeg {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'} (h : X.Γ'.IsFinSeg d')
    (h37 : X.ι (X.Γ'.α d') = Γ.α (X.ι d')) : Γ.IsFinSeg (X.ι d') := by
  have hfin := f_finSeg_fin h
  have hf1 : Γ.IsFinVertex (Γ.crossingOf (X.ι d')) := (X.r_finVertex (X.Γ'.crossingOf d')).1 hfin.1
  have hf2 : Γ.IsFinVertex (Γ.crossingOf (Γ.α (X.ι d'))) := by
    rw [← h37]; exact (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d'))).1 hfin.2
  refine ⟨⟨by rw [← X.isRemoval.curve, h.1.1, X.isRemoval.S], ?_⟩, ?_⟩
  · show Γ.side _ = 1
    rw [← h37, ← X.isRemoval.side]; exact h.1.2
  intro hmem
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z := by
    cases hs : Γ.infStart with
    | none =>
      exfalso
      unfold infArc arcOf at hmem
      rw [hs] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    | some z => exact ⟨z, rfl⟩
  obtain ⟨j, hj, hjd⟩ := (no_mem_infArc hz).1 hmem
  rcases Nat.lt_or_ge j Γ.infLen with hlt | hge
  · exact hf2.2 ⟨z, hz, j, hlt, by rw [hjd]⟩
  have hjL : j = Γ.infLen := by omega
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · -- the ∞-arc is the one segment `z = ι d'`
    rw [h0, pow_zero, Perm.one_apply] at hjd
    obtain ⟨z', hz'⟩ : ∃ z', X.Γ'.infStart = some z' :=
      Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
    obtain ⟨z0, hz0, k, hdel, hk⟩ := X.isRemoval.infStart z' hz'
    have hz0z : z0 = z := Option.some_injective _ (hz0.symm.trans hz)
    subst hz0z
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero, Perm.one_apply, hjd] at hk
      have := X.isRemoval.inj hk
      subst this
      exact h.2 ((no_mem_infArc hz').2 ⟨0, Nat.zero_le _, rfl⟩)
    · apply (X.r_keep d').1
      rw [← hjd, ← hk, show k = (k - 1) + 1 by omega, no_pow_succ, no_crossingOf_α_straight]
      exact hdel (k - 1) (by omega)
  · apply hf1.2
    refine ⟨z, hz, j - 1, by omega, ?_⟩
    rw [← no_crossingOf_α_straight, ← no_pow_succ, Nat.sub_add_cancel hpos, hjd]

/-- Both legs not hit: the triangle of `Γ − γ` is a triangle of `Γ` (Lemma 3.6). -/
private theorem gk_no_tri (hΓ : Γ.MinCE) {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'}
    (h : X.Γ'.EmptyTriAt d') (h37 : X.ι (X.Γ'.α d') = Γ.α (X.ι d')) {a b : D} {k₁ k₂ : ℕ}
    (T : GKTri Γ γ (X.ι d') a b k₁ k₂) (h1 : k₁ = 0) (h2 : k₂ = 0) : False := by
  subst h1 h2
  have hb : b = Γ.σ (Γ.α a) := by rw [T.hb, pow_zero, Perm.one_apply]
  have hc : Γ.σ (Γ.α b) = Γ.α (X.ι d') := by rw [← T.hc, pow_zero, Perm.one_apply]
  have hbF := T.cell_b_of_zero (Or.inl rfl)
  have hfin := f_finSeg_fin h.1
  have ha : Γ.Above a := by
    rw [T.ha, ← X.isRemoval.σ]; exact X.r_above (no_above_σ h.1.1)
  have hupd : Γ.side (Γ.cellOf (Γ.α (X.ι d'))) = 1 := by
    rw [← h37, ← X.isRemoval.side]; exact h.1.1.2
  have hAb : Γ.Above (Γ.α b) := by
    refine ⟨by rw [j_curve_α]; exact T.c2S, ?_⟩
    show Γ.side _ = 1
    rw [no_side_α T.c2S, hbF, hupd]
  have hfa : Γ.IsFinVertex (Γ.crossingOf a) := by
    rw [T.ha, j_crossingOf_σ]
    exact (X.r_finVertex (X.Γ'.crossingOf d')).1 hfin.1
  have hfb : Γ.IsFinVertex (Γ.crossingOf (Γ.α b)) := by
    rw [← j_crossingOf_σ, hc, ← h37]
    exact (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d'))).1 hfin.2
  -- positions: `a` starts at `i`, `α b` at `i + 1`
  have hfs := gk_finSeg X h.1 h37
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨a⟩)
  obtain ⟨t, ht, hte⟩ := no_noC_surj hz hfs.1
  have ht1 := (no_noC_arc hz ht).not.1 (by rw [hte]; exact hfs.2)
  have hpos : Γ.pos (Γ.crossingOf a) < Γ.pos (Γ.crossingOf (Γ.α b)) := by
    rw [T.ha, j_crossingOf_σ, ← hte, no_noC_pos hz ht, ← j_crossingOf_σ, hc, ← hte,
      ← no_crossingOf_α_straight, no_noC_straight, no_noC_pos hz (by omega)]
    omega
  apply hΓ.lemma_3_6.2 a (Γ.α b)
  refine ⟨⟨ha, hAb, hfa, hfb, ?_, by rw [j_α_α, hb, j_crossingOf_σ], ?_, ?_⟩, hpos,
    by rw [j_φ_apply, j_α_α, hb]⟩
  · intro hx
    have hm : Γ.curve (Γ.α b) ∈ Γ.curves (Γ.crossingOf a) := by
      rw [hx, j_curves_crossingOf]; exact mem_insert_self _ _
    rw [T.ha, j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α, j_curve_σσ, T.dS,
      ← T.ha] at hm
    rcases hm with hm | hm
    · exact T.c12 hm.symm
    · exact T.c2S hm
  · exact f_aboveVertex ha (by rw [← hb]; exact T.c2S)
  · rw [j_curve_α]; exact T.c12

/-- p. 322 (and p. 324, "Lemma 3.7 implies that it does so twice"): `γ` crosses only one leg of
the triangle it leaves, twice. -/
theorem MinCE.removal_one_leg (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') :
    (X.hits (X.Γ'.σ d') = 2 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 0) ∨
    (X.hits (X.Γ'.σ d') = 0 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  obtain ⟨e, he, hx⟩ := hΓ.lemma_3_9 hγ X h
  have hbF := T.cell_b_of_vis (Orbit.mem_darts.1 he) hx
  have hev := T.even_of_vis hbF
  have hp := T.parity
  have h1 := T.k1le
  have h2 := T.k2le
  rcases (show (X.hits (X.Γ'.σ d') = 2 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 0) ∨
      (X.hits (X.Γ'.σ d') = 0 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) ∨
      (X.hits (X.Γ'.σ d') = 0 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 0) ∨
      (X.hits (X.Γ'.σ d') = 2 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) by omega)
    with hk | hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr hk
  · exact (gk_no_tri hΓ X h h37 T hk.1 hk.2).elim
  · exact (T.not_two_two hk.1 hk.2 hbF).elim

variable (Γ) in
/-- p. 322: the edge of the sweep dart `d` is **responsible** for `γ`: removing `γ` leaves the
empty triangle above it (by Lemma 3.7 that edge is an edge of `Γ`). -/
def Responsible (d : D) (γ : Fin n) : Prop :=
  ∃ X : Γ.Removal {γ}, ∃ d', X.Γ'.EmptyTriAt d' ∧ X.ι d' = d

/-- p. 322: "each edge of the sweep is responsible for at most one curve" (claim without proof in
the source). -/
theorem MinCE.responsible_unique (hΓ : Γ.MinCE) {d : D} {γ₁ γ₂ : Fin n}
    (hγ₁ : Γ.Present γ₁) (hγ₂ : Γ.Present γ₂)
    (h₁ : Γ.Responsible d γ₁) (h₂ : Γ.Responsible d γ₂) : γ₁ = γ₂ := by
  obtain ⟨X1, d1, h1, rfl⟩ := h₁
  obtain ⟨X2, d2, h2, hd⟩ := h₂
  have T1 := gk_tri X1 h1 (hΓ.lemma_3_7 X1 (Or.inr h1))
  have T2 := gk_tri X2 h2 (hΓ.lemma_3_7 X2 (Or.inr h2))
  rw [hd] at T2
  exact gk_unique T1 T2 (hΓ.removal_one_leg hγ₁ X1 h1) (hΓ.removal_one_leg hγ₂ X2 h2)

/-- Two vertices on the sweep on one curve make it a loop. -/
private theorem gk_loop_of_two {δ : Fin n} (hδ : δ ≠ Γ.S) {x₁ x₂ : Γ.Crossing}
    (h1 : Γ.IsFinVertex x₁ ∧ Γ.OnCurve δ x₁) (h2 : Γ.IsFinVertex x₂ ∧ Γ.OnCurve δ x₂)
    (hne : x₁ ≠ x₂) : Γ.IsLoop δ := by
  classical
  unfold IsLoop numSweepHits
  have hsub : univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x) ⊆
      univ.filter (fun x : Γ.Crossing => Γ.curves x = {δ, Γ.S}) := by
    intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨mem_univ _, no_mem_curves hx.2.1.1 hx.2.2 hδ⟩
  have hle := card_le_card hsub
  have h02 := card_sweep_crossings (Γ := Γ) δ hδ
  have hpair : ({x₁, x₂} : Finset Γ.Crossing) ⊆
      univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rw [mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨mem_univ _, h1⟩
    · exact ⟨mem_univ _, h2⟩
  have hge := card_le_card hpair
  rw [card_pair hne] at hge
  have hcard : (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve δ x)).card = 2 := by
    omega
  convert hcard using 2

/-- p. 322: there is a loop (counting: `n` responsible edges need `n + 1` vertices on the sweep,
every curve meets the sweep (Lemma 3.4) at most twice). -/
theorem MinCE.exists_loop (hΓ : Γ.MinCE) : ∃ γ, Γ.Present γ ∧ Γ.IsLoop γ := by
  classical
  by_contra hno
  push Not at hno
  set A := univ.filter Γ.Present with hAdef
  have hA : A.Nonempty := by
    by_contra hA
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hA
    apply hΓ.1.1
    refine ⟨fun x hx => ?_, fun γ hγ => absurd hγ (hA (mem_univ _))⟩
    obtain ⟨-, d, -, hd⟩ := hx
    exact hA (mem_univ _) ⟨hd.1, d, rfl, hd⟩
  obtain ⟨γ₀, hγ₀⟩ := hA
  obtain ⟨-, d₀, -, -⟩ := (mem_filter.1 hγ₀).2
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨d₀⟩)
  set P := period Γ.straight z with hP
  -- every curve has a responsible finite edge
  have hresp : ∀ γ ∈ A, ∃ t, t + Γ.infLen + 1 < P ∧ Γ.Responsible (Γ.noC z t) γ := by
    intro γ hγA
    have hγ : Γ.Present γ := (mem_filter.1 hγA).2
    obtain ⟨X⟩ := exists_removal {γ} (by rw [mem_singleton]; exact fun h => hγ.1 h.symm)
    obtain ⟨d', hd'⟩ := hΓ.removal_leaves_triangle hγ X
    have hfs := gk_finSeg X hd'.1 (hΓ.lemma_3_7 X (Or.inr hd'))
    obtain ⟨t, ht, hte⟩ := no_noC_surj hz hfs.1
    refine ⟨t, ?_, X, d', hd', hte.symm⟩
    have := (no_noC_arc hz ht).not.1 (by rw [hte]; exact hfs.2)
    omega
  choose! g hg using hresp
  have hc1 : A.card ≤ (range (P - Γ.infLen - 1)).card := by
    refine card_le_card_of_injOn g (fun γ hγ => ?_) (fun γ₁ h₁ γ₂ h₂ he => ?_)
    · rw [coe_range, Set.mem_Iio]; have := (hg γ hγ).1; omega
    · have hr₂ := (hg γ₂ h₂).2
      rw [← he] at hr₂
      exact hΓ.responsible_unique (mem_filter.1 h₁).2 (mem_filter.1 h₂).2 (hg γ₁ h₁).2 hr₂
  -- every vertex on the sweep is on a different curve
  have hc2 : (range (P - Γ.infLen)).card ≤ A.card := by
    refine card_le_card_of_injOn (fun t => Γ.curve (Γ.σ (Γ.noC z t))) (fun t ht => ?_)
      (fun t₁ h₁ t₂ h₂ he => ?_)
    · have hab := no_above_σ (no_noC_sweep hz t)
      exact mem_filter.2 ⟨mem_univ _, hab.1, _, rfl, hab⟩
    · rw [coe_range, Set.mem_Iio] at h₁ h₂
      simp only at he
      by_contra hne
      set δ := Γ.curve (Γ.σ (Γ.noC z t₁)) with hδ
      have hab := no_above_σ (no_noC_sweep hz t₁)
      have hon : ∀ t, Γ.curve (Γ.σ (Γ.noC z t)) = δ →
          Γ.OnCurve δ (Γ.crossingOf (Γ.noC z t)) := by
        intro t ht
        show δ ∈ Γ.curves _
        rw [j_curves_crossingOf, ht]; exact mem_insert_of_mem (mem_singleton_self _)
      apply hno δ ⟨hab.1, _, rfl, hab⟩
      refine gk_loop_of_two hab.1 ⟨(no_noC_fin hz (by omega)).2 (by omega), hon t₁ rfl⟩
        ⟨(no_noC_fin hz (by omega)).2 (by omega), hon t₂ he.symm⟩ ?_
      exact fun hx => hne (no_noC_inj hz (by omega) (by omega) hx)
  have hAc : 1 ≤ A.card := card_pos.2 ⟨γ₀, hγ₀⟩
  rw [card_range] at hc1 hc2
  omega

end SConf

end Pca.Sweep
