/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Fact 1 (`doc/pca/circ.md`)

Source: Felsner-Scheucher, arXiv:1712.02149 (v6), section 2, Fact 1: "Let `𝒞` be an arrangement
of circles represented on the sphere. Three circles `C₁, C₂, C₃` of `𝒞` form a Krupp if and only if
the three corresponding planes `E₁, E₂, E₃` intersect in a single point in the interior of `S`."

`IsCircleRep.fact1`: for a circle representation and distinct curves `a, b, c`,
`IsKrupp A a b c ↔ MeetInside u h a b c`.

Also basic facts of representations used later: no tangencies (`det3_ne_zero`), the two
crossings of a pair (`exists_pair`).
-/
import Pca.Circ.Side

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}
  {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}

/-- Every pair of distinct curves has two distinct crossings. -/
theorem exists_pair (A : Arrangement n D) {i j : Fin n} (hij : i ≠ j) :
    ∃ x y : A.Crossing, x ≠ y ∧ Arrangement.Crossing.curves A x = {i, j} ∧
      Arrangement.Crossing.curves A y = {i, j} := by
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.1 (A.card_curves_eq_pair i j hij)
  have hx : x ∈ univ.filter (fun z : A.Crossing => Arrangement.Crossing.curves A z = {i, j}) := by
    rw [he]; simp
  have hy : y ∈ univ.filter (fun z : A.Crossing => Arrangement.Crossing.curves A z = {i, j}) := by
    rw [he]; simp
  exact ⟨x, y, hxy, (mem_filter.1 hx).2, (mem_filter.1 hy).2⟩

/-- A crossing with curves `{i, j}` is one of two given distinct ones. -/
theorem eq_or_eq_of_pair {i j : Fin n} {x y z : A.Crossing} (hxy : x ≠ y)
    (hx : Arrangement.Crossing.curves A x = {i, j}) (hy : Arrangement.Crossing.curves A y = {i, j})
    (hz : Arrangement.Crossing.curves A z = {i, j}) : z = x ∨ z = y := by
  by_contra hc
  push_neg at hc
  exact hxy (Great.eq_of_curves_eq (x := z) (hx.trans hz.symm) (hy.trans hz.symm) hc.1.symm
    hc.2.symm)

theorem nonempty_darts (x : A.Crossing) : ∃ d, d ∈ x.darts := by
  obtain ⟨d, rfl⟩ := Orbit.exists_mk x
  exact ⟨d, Orbit.mem_darts.2 rfl⟩

namespace IsCircleRep

variable (R : IsCircleRep A u h pt sgn)
include R

/-- No tangencies: at a crossing of `a = curve d` and `b = curve (σ d)`, `det3 u_a u_b p ≠ 0`. -/
theorem det3_ne_zero (d : D) :
    det3 (u (A.curve d)) (u (A.curve (A.σ d))) (pt (A.crossingOf d)) ≠ 0 := by
  intro h0
  have := R.rot d
  unfold tangent at this
  rw [det3_smul_smul, det3_cross_cross, h0] at this
  simp at this

/-- The normals of two crossing circles are independent. -/
theorem cross_ne_zero {i j : Fin n} (hij : i ≠ j) : u i ⨯₃ u j ≠ 0 := by
  obtain ⟨x, -, -, hx, -⟩ := exists_pair A hij
  obtain ⟨d, hdx, hdi⟩ := exists_dart_of_mem (show i ∈ Arrangement.Crossing.curves A x by
    rw [hx]; simp)
  have hj : A.curve (A.σ d) = j := by
    have h1 := A.mem_curves_crossingOf_σ d
    rw [hdx, hx, mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact absurd (h1.trans hdi.symm) (A.isArrangement.curve_σ d)
    · exact h1
  intro h0
  have := R.det3_ne_zero d
  rw [hdi, hj, det3_cross, h0, zero_dotProduct] at this
  exact this rfl

/-- The point of a crossing with curves `{i, j}` is on the circles `i`, `j`. -/
theorem onCirc_pair' {x : A.Crossing} {i j : Fin n} (hx : Arrangement.Crossing.curves A x = {i, j}) :
    OnCirc (u i) (h i) (pt x) ∧ OnCirc (u j) (h j) (pt x) :=
  ⟨R.onCirc (by rw [hx]; simp), R.onCirc (by rw [hx]; simp)⟩

/-- No extra incidences: if the point of `x` lies on the circles `i ≠ j`, then the curves of `x` are
`i, j`. -/
theorem curves_eq_of_on {x : A.Crossing} {i j : Fin n} (hij : i ≠ j) (hi : u i ⬝ᵥ pt x = h i)
    (hj : u j ⬝ᵥ pt x = h j) : Arrangement.Crossing.curves A x = {i, j} := by
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := exists_pair A hij
  obtain ⟨h1i, h1j⟩ := R.onCirc_pair' hz₁
  obtain ⟨h2i, h2j⟩ := R.onCirc_pair' hz₂
  by_contra hne
  have hx1 : x ≠ z₁ := fun e => hne (e ▸ hz₁)
  have hx2 : x ≠ z₂ := fun e => hne (e ▸ hz₂)
  exact not_three_on_two_planes (R.cross_ne_zero hij) (R.on_sphere x) hi hj h1i.1 h1i.2 h1j.2
    h2i.1 h2i.2 h2j.2 (fun e => hx1 (R.inj e)) (fun e => hx2 (R.inj e)) (fun e => hz (R.inj e))

theorem onCirc_pair {x : A.Crossing} {i j : Fin n} (hx : Arrangement.Crossing.curves A x = {i, j}) :
    OnCirc (u i) (h i) (pt x) ∧ OnCirc (u j) (h j) (pt x) :=
  ⟨R.onCirc (by rw [hx]; simp), R.onCirc (by rw [hx]; simp)⟩

/-- If the planes `a, b, c` meet inside the ball, `c` separates the two crossings of `a` and `b`. -/
theorem kruppPair_of_meetInside {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : MeetInside u h a b c) : KruppPair A a b c := by
  obtain ⟨hdet, P, hPa, hPb, hPc, hPin⟩ := hm
  intro s hs x y hxy hx hy d hd e he
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := exists_pair A hac
  rw [R.side_ne_iff hac hbc hs hx hy hz hz₁ hz₂ hd he]
  have hua := R.u_ne_zero a
  obtain ⟨hxa, hxb⟩ := R.onCirc_pair hx
  obtain ⟨hya, hyb⟩ := R.onCirc_pair hy
  obtain ⟨hz₁a, hz₁c⟩ := R.onCirc_pair hz₁
  obtain ⟨hz₂a, hz₂c⟩ := R.onCirc_pair hz₂
  have hpxy : pt x ≠ pt y := fun he' => hxy (R.inj he')
  have hpz : pt z₁ ≠ pt z₂ := fun he' => hz (R.inj he')
  -- `P` on the chord `x y`
  obtain ⟨t, ht⟩ := exists_smul_of_perp (R.cross_ne_zero hab) (v := P - pt x) (v' := pt y - pt x)
    (by rw [dotProduct_sub, hPa, hxa.2, sub_self]) (by rw [dotProduct_sub, hPb, hxb.2, sub_self])
    (by rw [dotProduct_sub, hya.2, hxa.2, sub_self]) (by rw [dotProduct_sub, hyb.2, hxb.2, sub_self])
    (sub_ne_zero.2 hpxy.symm)
  have hPt : P = pt x + t • (pt y - pt x) := by rw [← ht]; abel
  have ht01 := mem_Ioo_of_inside hxa.1 hya.1 hpxy (t := t) (by rw [← hPt]; exact hPin)
  -- `P` on the chord `z₁ z₂`
  obtain ⟨μ, hμ⟩ := exists_smul_of_perp (R.cross_ne_zero hac) (v := P - pt z₁)
    (v' := pt z₂ - pt z₁)
    (by rw [dotProduct_sub, hPa, hz₁a.2, sub_self]) (by rw [dotProduct_sub, hPc, hz₁c.2, sub_self])
    (by rw [dotProduct_sub, hz₂a.2, hz₁a.2, sub_self])
    (by rw [dotProduct_sub, hz₂c.2, hz₁c.2, sub_self]) (sub_ne_zero.2 hpz.symm)
  have hPμ : P = pt z₁ + μ • (pt z₂ - pt z₁) := by rw [← hμ]; abel
  have h0 : orient (u a) (pt z₁) (pt z₂) P = 0 := by rw [hPμ]; exact orient_self_left _ _ _ _
  rw [hPt, orient_affine] at h0
  have hcx : c ∉ Arrangement.Crossing.curves A x := by
    rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨hac.symm, hbc.symm⟩
  have hcy : c ∉ Arrangement.Crossing.curves A y := by
    rw [hy]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨hac.symm, hbc.symm⟩
  have hcz₁ : c ∈ Arrangement.Crossing.curves A z₁ := by rw [hz₁]; simp
  have hcz₂ : c ∈ Arrangement.Crossing.curves A z₂ := by rw [hz₂]; simp
  have hne_of : ∀ {p q : A.Crossing}, c ∈ Arrangement.Crossing.curves A p →
      c ∉ Arrangement.Crossing.curves A q → pt p ≠ pt q := fun hp hq he' => by
    rw [R.inj he'] at hp; exact hq hp
  have ox := hz₁a.orient_ne_zero hua hz₂a hxa hpz (hne_of hcz₁ hcx) (hne_of hcz₂ hcx)
  have oy := hz₁a.orient_ne_zero hua hz₂a hya hpz (hne_of hcz₁ hcy) (hne_of hcz₂ hcy)
  set X := orient (u a) (pt z₁) (pt z₂) (pt x)
  set Y := orient (u a) (pt z₁) (pt z₂) (pt y)
  obtain ⟨ht0, ht1⟩ := ht01
  rcases lt_or_gt_of_ne ox with h1 | h1
  · have : 0 < Y := by nlinarith
    nlinarith
  · have : Y < 0 := by nlinarith
    nlinarith

/-- If `c` separates the two crossings of `a` and `b`, the planes `a, b, c` meet inside. -/
theorem meetInside_of_kruppPair {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hk : KruppPair A a b c) : MeetInside u h a b c := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair A hab
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := exists_pair A hac
  obtain ⟨s, hs⟩ := A.exists_isSide c
  obtain ⟨d, hd⟩ := nonempty_darts x
  obtain ⟨e, he⟩ := nonempty_darts y
  have hsep := (R.side_ne_iff hac hbc hs hx hy hz hz₁ hz₂ hd he).1 (hk s hs x y hxy hx hy d hd e he)
  have hua := R.u_ne_zero a
  obtain ⟨hxa, hxb⟩ := R.onCirc_pair hx
  obtain ⟨hya, hyb⟩ := R.onCirc_pair hy
  obtain ⟨hz₁a, hz₁c⟩ := R.onCirc_pair hz₁
  obtain ⟨hz₂a, hz₂c⟩ := R.onCirc_pair hz₂
  have hpxy : pt x ≠ pt y := fun he' => hxy (R.inj he')
  have hpz : pt z₁ ≠ pt z₂ := fun he' => hz (R.inj he')
  obtain ⟨t, μ, ht0, ht1, -, -, hq⟩ := chord_meet hua hxa hya hz₁a hz₂a hpxy hpz hsep
  set q := pt x + t • (pt y - pt x)
  have hqa : u a ⬝ᵥ q = h a := by
    simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, hxa.2, hya.2, sub_self,
      smul_zero, add_zero]
  have hqb : u b ⬝ᵥ q = h b := by
    simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, hxb.2, hyb.2, sub_self,
      smul_zero, add_zero]
  have hqc : u c ⬝ᵥ q = h c := by
    rw [hq]
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, hz₁c.2, hz₂c.2, sub_self,
      smul_zero, add_zero]
  refine ⟨?_, q, hqa, hqb, hqc, chord_inside hxa.1 hya.1 hpxy ht0 ht1⟩
  -- independence: otherwise `g_c` is constant on the line `x y`, so `x` is on `c`
  intro hdet
  have hw := R.cross_ne_zero hab
  have hv := eq_smul_cross_of_perp hw (v := pt y - pt x)
    (by rw [dotProduct_sub, hya.2, hxa.2, sub_self]) (by rw [dotProduct_sub, hyb.2, hxb.2, sub_self])
  have hcxy : u c ⬝ᵥ (pt y - pt x) = 0 := by
    rw [hv, dotProduct_smul, smul_eq_mul]
    have : u c ⬝ᵥ (u a ⨯₃ u b) = 0 := by
      rw [← det3, det3_cyc, det3_cyc]; exact hdet
    rw [this, mul_zero]
  have hxc : u c ⬝ᵥ pt x = h c := by
    have : u c ⬝ᵥ q = u c ⬝ᵥ pt x + t * (u c ⬝ᵥ (pt y - pt x)) := by
      simp only [q, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [hcxy, mul_zero, add_zero, hqc] at this
    exact this.symm
  have hcz := R.curves_eq_of_on hac hxa.2 hxc
  rw [hx] at hcz
  have : c ∈ ({a, b} : Finset (Fin n)) := by rw [hcz]; simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h1 | h1
  · exact hac h1.symm
  · exact hbc h1.symm

omit R in
theorem meetInside_cyc {a b c : Fin n} (hm : MeetInside u h a b c) : MeetInside u h b c a := by
  obtain ⟨hd, P, h1, h2, h3, h4⟩ := hm
  exact ⟨by rw [det3_cyc]; exact hd, P, h2, h3, h1, h4⟩

/-- **Fact 1** (arXiv:1712.02149, section 2): three circles form a Krupp iff their planes meet
in a single point in the interior of the sphere. -/
theorem fact1 {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsKrupp A a b c ↔ MeetInside u h a b c := by
  constructor
  · intro hk; exact R.meetInside_of_kruppPair hab hac hbc hk.1
  · intro hm
    have hm' := meetInside_cyc (u := u) (h := h) hm
    have hm'' := meetInside_cyc (u := u) (h := h) hm'
    exact ⟨R.kruppPair_of_meetInside hab hac hbc hm,
      R.kruppPair_of_meetInside hbc hab.symm hac.symm hm',
      R.kruppPair_of_meetInside hac.symm hbc.symm hab hm''⟩

end IsCircleRep

end Pca.Circ
