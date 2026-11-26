/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.9, Case 1 (pp. 320-321), graph language (package H)

"CASE 1. The curve `γ` intersects the legs `⟨i, v⟩` and `⟨i + 1, v⟩` once each, as shown in
Figure 7. We can form a new arrangement `Γ'` without the vertex `v` by untangling the crossing of
curves `γ(i)` and `γ(i+1)` as pictured, essentially, we switch triangle legs `⟨i, v⟩` and
`⟨i + 1, v⟩`. Since removal of `γ` leaves an empty triangle `Δ(i, v, i + 1)` and since `γ`
intersects each leg once, the arrangement `Γ'` still has the two-intersection property. It also
has one fewer vertex above the sweep, so the sweep can make progress.
How can the sweep advance? The curve that we originally removed, `γ`, still intersects both
`γ(i)` and `γ(i+1)`, so none of these three curves is a hump. Thus, some face adjacent to the
sweep must have become an empty triangle in `Γ'`. Only the faces that were touching `v` are
affected by the untangling, two faces, marked by minus signs in Figure 7, lose a vertex, one gains
a vertex, and the face bounded by `[i, i + 1]` is unchanged. Since the configuration is
symmetric, we can assume that the face `F`, bounded by the curves `γ(i)` and `γ`, is an empty
triangle `Δ(j − 1, u, j)` in `Γ'`.
Figure 8 shows the two ways in which the face `F` can become a triangle when the vertex `v` is
untangled. Notice that the curve `γ(j) = γ` and that `u` is the intersection of `γ` and leg
`⟨i, v⟩`. If `j < i`, then both `⟨j, u⟩` and `⟨i, u⟩` are edges in the original arrangement `Γ`
and `Δ(j, u, i)` is a triangle, contradicting Lemma 3.6.
So suppose that `j > i`. No curve intersects the edges `⟨i, u⟩` or `⟨j, u⟩` in the original
arrangement `Γ`, so if the sweep could jump past these edges in a single operation, then the
remaining arrangement, `Γ − {γ(i), γ(i+1), …, γ(j)}`, would be smaller than the smallest
counterexample and thus be sweepable. Moreover, these remaining curves do not affect the ability
to sweep past edges `⟨i, u⟩` and `⟨j, u⟩`. By minimality, there are no curves `γ(m)` with `m < i`
or `j < m`. Now we can direct `γ(j)` to infinity without causing any more intersections or
allowing `c` to make progress, as indicated by the dotted line in Figure 8. Thus, we delete the
vertex `j`. Since the other end of the curve `γ(j)` does not leave the region bounded by `⟨i, u⟩`
and `⟨j, u⟩`, it still intersects the sweep. But this gives a smaller unsweepable arrangement,
violating the minimality of `Γ`. This contradiction proves that Case 1 cannot occur."

Graph language (`doc/pca/sweep.md`, section 4, Lemma 3.9, open point O4). With Lemma 3.6 for
**all** triangles (`MinCE.x_no_tri`, `Reflex.lean`) SH's case split `j < i` / `j > i` and the
redirect step disappear: in both pictures of Figure 8, `⟨i, u⟩` and `⟨j, u⟩` are single edges of `Γ`
from two distinct sweep vertices to the crossing `u`, i.e. `Δ(j, u, i)` is a triangle of `Γ`.
1. `case1_untangle`: the untangling of `v` exists (`Untangle`, with lower-side completion, open
   point O1, package U), at the dart `b` from `v` along the second leg (so the cells merged are the
   one between the legs below `v` and the one above `v`), and SH's claims about `Γ'`: it is not
   finished (`γ` still crosses both new curves above `S`) and no loop can be taken (every curve
   still meets the sweep).
2. `Γ'` is smaller (`numVertices` drops by one), so by minimality it makes progress: an empty hump
   or triangle above a finite edge. That edge comes from a finite edge `e` of `Γ` (`finSeg'`), and
   by the size fields of `Untangle` and stuckness of `Γ` (no empty hump / triangle, every cell has
   at least two corners) the cell above `e` is one of the two "minus" faces at `v` and has four
   corners `v`, `u`, and the two ends of `e` (`h_tri_L`, `h_tri_R`). The corner after `u` (away
   from `v`) is a sweep vertex `j` joined to `u` by one edge of `γ`, so `Δ(j, u, i)` (resp.
   `Δ(j, u, i + 1)`) is a triangle of `Γ`, contradicting `x_no_tri`.
-/
import Pca.Sweep.L39Hide
import Pca.Sweep.Untangle

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Case 1, step 1 (package U): the untangling of the apex `v` at the dart `b` from `v` along the
second leg (`cellOf b` is the cell between the legs below `v`), with SH's claims "`γ` still
intersects both `γ(i)` and `γ(i+1)`" (not finished) and that no loop can be taken. -/
theorem MinCE.case1_untangle (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') (hv : ¬ ApexVisible X d')
    (h₁ : X.hits (X.Γ'.σ d') = 1) (h₂ : X.hits (X.Γ'.φ (X.Γ'.σ d')) = 1) :
    ∃ U : Γ.Untangle (X.ι (X.Γ'.φ (X.Γ'.σ d'))), ¬ U.Γ'.Terminal ∧ ¬ U.Γ'.CanTakeLoop := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  rw [h₁, h₂] at T
  have hd : Γ.IsSweepDart (X.ι d') := f_ι_sweep X h.1.1
  have hfd : Γ.IsFinVertex (Γ.crossingOf (X.ι d')) :=
    (X.r_finVertex (X.Γ'.crossingOf d')).1 (f_finSeg_fin h.1).1
  have hfd' : Γ.IsFinVertex (Γ.crossingOf (Γ.α (X.ι d'))) := by
    rw [← h37]; exact (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d'))).1 (f_finSeg_fin h.1).2
  exact (UHyp.of_gkTri T hd (by norm_num)).exists_untangle (by norm_num) hfd hfd'
    (fun c hc => hΓ.lemma_3_4 hc)

/-- A cell has at least two corners. -/
private theorem h_two_le_size (x : D) : 2 ≤ (Γ.cellOf x).size := by
  rw [c_size]
  have hp := period_pos Γ.φ x
  by_contra hc
  have h1 : period Γ.φ x = 1 := by omega
  have h2 := iterate_period Γ.φ x
  rw [h1] at h2
  have h3 : Γ.σ (Γ.α x) = x := h2
  apply no_curve_σ_ne (Γ := Γ) (Γ.α x)
  rw [h3, j_curve_α]

/-- The darts of a cell with four corners. -/
private theorem h_mem_cell4 {x y : D} (hp : (Γ.cellOf x).size = 4)
    (h : Γ.cellOf y = Γ.cellOf x) :
    y = x ∨ y = Γ.φ x ∨ y = Γ.φ (Γ.φ x) ∨ y = Γ.φ (Γ.φ (Γ.φ x)) := by
  rw [c_size] at hp
  have h' : Γ.φ.SameCycle x y := Orbit.mk_eq_mk.1 h.symm
  have := mem_orbitList.2 h'
  simpa [orbitList, hp, List.range_succ] using this

private theorem h_φ4 {x : D} (hp : (Γ.cellOf x).size = 4) :
    Γ.φ (Γ.φ (Γ.φ (Γ.φ x))) = x := by
  rw [c_size] at hp
  have := iterate_period Γ.φ x
  rw [hp] at this
  exact this

/-- The "minus" face at `v` beyond the second leg (`cellOf (σ b)`), above the finite edge `e`
with four corners: `Δ(j, u₂, i + 1)` is a triangle (`j` the start of `e`, `u₂` the crossing of `γ`
with the second leg). -/
private theorem h_tri_L {γ : Fin n} {d a b : D} (T : GKTri Γ γ d a b 1 1)
    (hd : Γ.IsSweepDart d) (hfd : Γ.IsFinVertex (Γ.crossingOf (Γ.α d))) {e : D}
    (he : Γ.IsFinSeg e) (hf : Γ.cellOf (Γ.α e) = Γ.cellOf (Γ.σ b))
    (h4 : (Γ.cellOf (Γ.σ b)).size = 4) : ∃ p q, Γ.IsTri p q := by
  have hx0 : Γ.cellOf (Γ.σ b) = Γ.cellOf (Γ.α b) := j_cellOf_σ Γ b
  rw [hx0] at hf h4
  have hφx0 : Γ.φ (Γ.α b) = Γ.σ b := by rw [j_φ_apply, j_α_α]
  have hcγ : Γ.curve (Γ.σ (Γ.α b)) = γ := by
    have := T.del2 0 (by norm_num); rwa [pow_zero, Perm.one_apply] at this
  have hb' : b = Γ.σ (Γ.α (Γ.straight a)) := by rw [T.hb, pow_one]
  have hcσb : Γ.curve (Γ.σ b) = Γ.curve a := by
    rw [hb', j_curve_σσ, j_curve_α, j_curve_straight]
  have heS : Γ.curve (Γ.α e) = Γ.S := by rw [j_curve_α]; exact he.1.1
  rcases h_mem_cell4 h4 hf with h0 | h0 | h0 | h0
  · exact absurd (h0 ▸ heS : Γ.curve (Γ.α b) = Γ.S) (by rw [j_curve_α]; exact T.c2S)
  · rw [hφx0] at h0
    exact absurd (h0 ▸ heS : Γ.curve (Γ.σ b) = Γ.S) (by rw [hcσb]; exact T.c1S)
  · have h5 := h_φ4 h4
    rw [← h0] at h5
    -- `φ (α e) = σ e`, so `φ (σ e) = α b`
    have hpe : Γ.σ (Γ.α (Γ.σ e)) = Γ.α b := by
      have : Γ.φ (Γ.α e) = Γ.σ e := by rw [j_φ_apply, j_α_α]
      rw [this, j_φ_apply] at h5; exact h5
    set p := Γ.σ e with hp
    set q := Γ.α (Γ.straight b) with hq
    have hAp : Γ.Above p := no_above_σ he.1
    have hAsb : Γ.Above (Γ.straight b) := by
      refine ⟨by rw [j_curve_straight]; exact T.c2S, ?_⟩
      unfold Up
      have := T.cell_αd
      rw [pow_one] at this
      rw [← this]; exact hd.2
    have hAq : Γ.Above q := f_above_α hAsb
    have hσq : Γ.σ q = Γ.α d := by have := T.hc; rwa [pow_one] at this
    have hcq : Γ.curve q = Γ.curve b := by rw [hq, j_curve_α, j_curve_straight]
    have hcpb : Γ.curve p ≠ Γ.curve b := by
      have := no_curve_σ_ne (Γ := Γ) (Γ.α p)
      rw [hpe, j_curve_α, j_curve_α] at this
      exact fun h' => this h'.symm
    have hapex : Γ.crossingOf (Γ.α p) = Γ.crossingOf (Γ.α q) := by
      rw [← j_crossingOf_σ Γ (Γ.α p), hpe, hq, j_α_α, no_crossingOf_α_straight]
    refine ⟨p, q, hAp, hAq, ?_, ?_, ?_, hapex, ?_, ?_⟩
    · rw [hp, j_crossingOf_σ]; exact (f_finSeg_fin he).1
    · rw [← j_crossingOf_σ Γ q, hσq]; exact hfd
    · intro hx
      have hm : Γ.curve p ∈ Γ.curves (Γ.crossingOf p) := by
        rw [j_curves_crossingOf]; exact mem_insert_self _ _
      rw [hx, j_curves_crossingOf, hσq, hcq, j_curve_α, hd.1, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm
      · exact hcpb hm
      · exact hAp.1 hm
    · rw [hapex, hq, j_α_α]
      have := f_aboveVertex (Γ := Γ) (a := q) hAq (by
        rw [hq, j_α_α, j_straight_apply, j_curve_σσ, hcγ]; exact T.γS)
      rwa [hq, j_α_α] at this
    · rw [hcq]; exact hcpb
  · have h5 := h_φ4 h4
    rw [← h0, j_φ_apply, j_α_α] at h5
    -- `σ e = α b`
    have := j_curve_σσ (Γ := Γ) e
    rw [h5, hcγ, he.1.1] at this
    exact (T.γS this).elim

/-- The "minus" face at `v` beyond the first leg (`cellOf (σ³ b)`), above the finite edge `e`
with four corners: `Δ(j, u₁, i)` is a triangle (`j` the end of `e`, `u₁` the crossing of `γ` with
the first leg). -/
private theorem h_tri_R {γ : Fin n} {d a b : D} (T : GKTri Γ γ d a b 1 1)
    (hd : Γ.IsSweepDart d) (hfd : Γ.IsFinVertex (Γ.crossingOf d)) {e : D}
    (he : Γ.IsFinSeg e) (hf : Γ.cellOf (Γ.α e) = Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b))))
    (h4 : (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b)))).size = 4) : ∃ p q, Γ.IsTri p q := by
  set y := Γ.straight a with hy
  have hb' : b = Γ.σ (Γ.α y) := by rw [T.hb, pow_one]
  have hx0 : Γ.σ (Γ.σ (Γ.σ b)) = Γ.α y := by rw [hb', j_σ4]
  rw [hx0] at hf h4
  have hφx0 : Γ.φ (Γ.α y) = Γ.σ y := by rw [j_φ_apply, j_α_α]
  have hcγ : Γ.curve (Γ.σ (Γ.α a)) = γ := by
    have := T.del1 0 (by norm_num); rwa [pow_zero, Perm.one_apply] at this
  have hcσy : Γ.curve (Γ.σ y) = γ := by
    rw [hy, j_straight_apply, ← hcγ]
    exact j_curve_σσ (Γ := Γ) (Γ.σ (Γ.α a))
  have hcy : Γ.curve y = Γ.curve a := j_curve_straight Γ a
  have heS : Γ.curve (Γ.α e) = Γ.S := by rw [j_curve_α]; exact he.1.1
  have hAa : Γ.Above a := T.ha ▸ no_above_σ hd
  rcases h_mem_cell4 h4 hf with h0 | h0 | h0 | h0
  · exact absurd (h0 ▸ heS : Γ.curve (Γ.α y) = Γ.S) (by rw [j_curve_α, hcy]; exact T.c1S)
  · rw [hφx0] at h0
    exact absurd (h0 ▸ heS : Γ.curve (Γ.σ y) = Γ.S) (by rw [hcσy]; exact T.γS.symm ∘ Eq.symm)
  · -- `φ (σ y) = α e`
    have hwe : Γ.σ (Γ.α (Γ.σ y)) = Γ.α e := by rw [h0, hφx0]; rfl
    set w := Γ.σ y with hw
    set p := Γ.α w with hp
    have hAw : Γ.Above w := by
      refine ⟨by rw [hcσy]; exact T.γS, ?_⟩
      unfold Up
      have : Γ.cellOf w = Γ.cellOf (Γ.α e) := by
        rw [h0, j_cellOf_φ, j_cellOf_φ, ← hφx0, j_cellOf_φ]
      rw [this]; exact he.1.2
    have hAp : Γ.Above p := f_above_α hAw
    have hcp : Γ.curve p = γ := by rw [hp, j_curve_α, hcσy]
    have hapex : Γ.crossingOf (Γ.α p) = Γ.crossingOf (Γ.α a) := by
      rw [hp, j_α_α, hw, j_crossingOf_σ, hy, no_crossingOf_α_straight]
    refine ⟨p, a, hAp, hAa, ?_, ?_, ?_, hapex, ?_, ?_⟩
    · rw [← j_crossingOf_σ Γ p, hp, hwe]; exact (f_finSeg_fin he).2
    · rw [T.ha, j_crossingOf_σ]; exact hfd
    · intro hx
      have hm : Γ.curve p ∈ Γ.curves (Γ.crossingOf p) := by
        rw [j_curves_crossingOf]; exact mem_insert_self _ _
      rw [hx, j_curves_crossingOf, hcp, T.ha, ← T.ha, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm
      · exact T.c1γ hm.symm
      · rw [T.ha, j_curve_σσ, T.dS] at hm; exact T.γS hm
    · rw [hapex]
      exact f_aboveVertex hAa (by rw [hcγ]; exact T.γS)
    · rw [hcp]; exact T.c1γ.symm
  · have h5 := h_φ4 h4
    rw [← h0, j_φ_apply, j_α_α] at h5
    -- `σ e = α y`, so `σ² e = b`
    have := j_curve_σσ (Γ := Γ) e
    rw [h5, ← hb', he.1.1] at this
    exact (T.c2S this).elim

/-- **SH Lemma 3.9, Case 1** (pp. 320-321): impossible. -/
theorem MinCE.lemma_3_9_case1 (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') (hv : ¬ ApexVisible X d')
    (h₁ : X.hits (X.Γ'.σ d') = 1) (h₂ : X.hits (X.Γ'.φ (X.Γ'.σ d')) = 1) : False := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  rw [h₁, h₂] at T
  set b := X.ι (X.Γ'.φ (X.Γ'.σ d')) with hb
  obtain ⟨U, hnt, hnl⟩ : ∃ U : Γ.Untangle b, ¬ U.Γ'.Terminal ∧ ¬ U.Γ'.CanTakeLoop :=
    hΓ.case1_untangle hγ X h hv h₁ h₂
  have hd : Γ.IsSweepDart (X.ι d') := f_ι_sweep X h.1.1
  have hfd : Γ.IsFinVertex (Γ.crossingOf (X.ι d')) :=
    (X.r_finVertex (X.Γ'.crossingOf d')).1 (f_finSeg_fin h.1).1
  have hfd' : Γ.IsFinVertex (Γ.crossingOf (Γ.α (X.ι d'))) := by
    rw [← h37]; exact (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d'))).1 (f_finSeg_fin h.1).2
  -- `Γ` is stuck: no cell above a finite edge has two or three corners
  have hsz : ∀ e, Γ.IsFinSeg e → (Γ.upperCell e).size ≠ 2 ∧ (Γ.upperCell e).size ≠ 3 :=
    fun e he => ⟨fun h2 => hΓ.1.2 (Or.inl ⟨e, he, h2⟩),
      fun h3 => hΓ.1.2 (Or.inr (Or.inl ⟨e, he, h3⟩))⟩
  -- `Γ'` is smaller, hence not stuck, hence it makes progress by an empty hump or triangle
  have hlt : SizeLT U.Γ' Γ := Or.inl (by have := U.numVertices; omega)
  have hprog : U.Γ'.Progress := by
    by_contra hp
    exact hΓ.2 U.n' ⟨U.D', U.Γ'⟩ hlt ⟨hnt, hp⟩
  obtain ⟨d'', hd'', hs⟩ : ∃ d'', U.Γ'.IsFinSeg d'' ∧
      ((U.Γ'.upperCell d'').size = 2 ∨ (U.Γ'.upperCell d'').size = 3) := by
    rcases hprog with ⟨d'', hd''⟩ | ⟨d'', hd''⟩ | hl
    · exact ⟨d'', hd''.1, Or.inl hd''.2⟩
    · exact ⟨d'', hd''.1, Or.inr hd''.2⟩
    · exact absurd hl hnl
  obtain ⟨e, he, hψ⟩ := U.finSeg' d'' hd''
  rw [hψ] at hs
  have hUp : Γ.Up (Γ.upperCell e) := he.1.2
  have hse := hsz e he
  have h2f := h_two_le_size (Γ := Γ) (Γ.α e)
  change 2 ≤ (Γ.upperCell e).size at h2f
  by_cases hcL : Γ.upperCell e = Γ.cellOf (Γ.σ b)
  · have := U.size_L
    rw [← hcL] at this
    obtain ⟨p, q, hpq⟩ := h_tri_L T hd hfd' he hcL (by rw [← hcL]; omega)
    exact hΓ.x_no_tri p q hpq
  by_cases hcR : Γ.upperCell e = Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b)))
  · have := U.size_R
    rw [← hcR] at this
    obtain ⟨p, q, hpq⟩ := h_tri_R T hd hfd he hcR (by rw [← hcR]; omega)
    exact hΓ.x_no_tri p q hpq
  by_cases hcM : Γ.upperCell e = Γ.cellOf b ∨ Γ.upperCell e = Γ.cellOf (Γ.σ (Γ.σ b))
  · have hm := U.size_merge
    have h2b := h_two_le_size (Γ := Γ) b
    have h2b' := h_two_le_size (Γ := Γ) (Γ.σ (Γ.σ b))
    rcases hcM with hc | hc
    · rw [← hc] at hm; omega
    · rw [U.merge, ← hc] at hm; omega
  have hso := U.size_other (Γ.upperCell e) hUp (by
    intro x hx hxb
    have hfx : Γ.cellOf x = Γ.upperCell e := Orbit.mem_darts.1 hx
    rcases no_mem_crossing hxb with rfl | rfl | rfl | rfl
    · exact hcM (Or.inl hfx.symm)
    · exact hcL hfx.symm
    · exact hcM (Or.inr hfx.symm)
    · exact hcR hfx.symm)
  omega

end SConf

end Pca.Sweep
