/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 19 (`doc/pca/circ.md`, decision C-D5)

Source: arXiv:1712.02149 (v6), Theorem 19: "Let `𝒜` be an intersecting arrangement of
pseudocircles which is not an arrangement of great-pseudocircles. If every triple of pseudocircles
which forms a triangle is Krupp, then `𝒜` is not circularizable."

`Pca.Circ.thm19`. The model `Pca.Arrangement` is intersecting by definition. "A triple forms a
triangle" = some triangle cell has exactly these three curves. Proof outline in
`Pca/Circ/Thm19.lean`.
-/
import Pca.Circ.Thm19Main

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- **Theorem 19.** An (intersecting) arrangement of pseudocircles that is not an arrangement of
great-pseudocircles and in which every triple forming a triangle is a Krupp is not
circularizable. -/
theorem thm19 (A : Arrangement n D) (hng : ¬ A.IsGreat)
    (htri : ∀ f : A.Cell, A.IsTriangle f → ∀ a b c : Fin n,
      Arrangement.Cell.curves A f = {a, b, c} → IsKrupp A a b c) :
    ¬ Circularizable A := by
  classical
  rintro ⟨R0⟩
  obtain ⟨Rg, hG1, hG2⟩ := R0.exists_generic
  have R := Rg.isRep
  set u := Rg.u
  set h := Rg.h
  set pt := Rg.pt
  set sgn := Rg.sgn
  -- a NonKrupp triple with triple point of minimal norm
  rw [isGreat_iff] at hng
  push_neg at hng
  obtain ⟨a0, b0, c0, h1, h2, h3, hk0⟩ := hng
  set S := univ.filter (fun t : Fin n × Fin n × Fin n =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ¬ IsKrupp A t.1 t.2.1 t.2.2)
  have hS : S.Nonempty := ⟨(a0, b0, c0), by simp [S, h1, h2, h3, hk0]⟩
  let F : Fin n × Fin n × Fin n → ℝ := fun t =>
    triplePt (u t.1) (u t.2.1) (u t.2.2) (h t.1) (h t.2.1) (h t.2.2) ⬝ᵥ
      triplePt (u t.1) (u t.2.1) (u t.2.2) (h t.1) (h t.2.1) (h t.2.2)
  obtain ⟨⟨i, j, k⟩, hmem, hFmin⟩ := S.exists_min_image F hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨hij, hik, hjk, hnk⟩ := hmem
  set P := triplePt (u i) (u j) (u k) (h i) (h j) (h k)
  have hΔ := hG1 i j k hij hik hjk
  obtain ⟨hPi, hPj, hPk⟩ := triplePt_spec (h i) (h j) (h k) hΔ
  have hmin : IsCircleRep.IsMinPt u h A P := by
    intro a b c hab hac hbc hk Q hQa hQb hQc
    obtain ⟨e1, e2, e3⟩ := triplePt_spec (h a) (h b) (h c) (hG1 a b c hab hac hbc)
    have hQ : Q = triplePt (u a) (u b) (u c) (h a) (h b) (h c) :=
      eq_of_three_planes (hG1 a b c hab hac hbc) (by rw [hQa, e1]) (by rw [hQb, e2])
        (by rw [hQc, e3])
    rw [hQ]
    exact hFmin (a, b, c) (by simp [S, hab, hac, hbc, hk])
  have hP1 := R.one_lt_of_nonKrupp hij hik hjk hnk hΔ hPi hPj hPk
  have hG2' : ∀ l, l ≠ i → l ≠ j → l ≠ k → u l ⬝ᵥ P ≠ h l := fun l hli hlj hlk e =>
    hG2 i j k l hij hik (Ne.symm hli) hjk (Ne.symm hlj) (Ne.symm hlk) P hPi hPj hPk e
  -- the contradiction from a Krupp triangle on `i, j, k` (in any order)
  have final : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → u x ⬝ᵥ P = h x → u y ⬝ᵥ P = h y →
      u z ⬝ᵥ P = h z → IsKrupp A x y z → False := by
    intro x y z hxy hxz hyz hx hy hz hk
    obtain ⟨hd, Q, hQx, hQy, hQz, hQ⟩ := (R.fact1 hxy hxz hyz).1 hk
    have : Q = P := eq_of_three_planes hd (by rw [hQx, hx]) (by rw [hQy, hy]) (by rw [hQz, hz])
    rw [this] at hQ
    linarith
  -- the corners of the triangle facing `P`
  obtain ⟨XA, XA', τA, hAA', hA, hA', hτA, hPA⟩ := R.exists_near hij hPi hPj hP1
  obtain ⟨XB, XB', τB, hBB', hB, hB', hτB, hPB⟩ := R.exists_near hik hPi hPk hP1
  obtain ⟨XC, XC', τC, hCC', hC, hC', hτC, hPC⟩ := R.exists_near hjk hPj hPk hP1
  have Ci := R.near_side hG1 hij hik hjk hPi hPj hPk hmin hG2' hAA' hA hA' hτA hPA hBB' hB hB'
    hτB hPB
  have Cj := R.near_side hG1 hij.symm hjk hik hPj hPi hPk hmin
    (fun l h1 h2 h3 => hG2' l h2 h1 h3) hAA' (by rw [hA, Finset.pair_comm])
    (by rw [hA', Finset.pair_comm]) hτA hPA hCC' hC hC' hτC hPC
  have Ck := R.near_side hG1 hik.symm hjk.symm hij hPk hPi hPj hmin
    (fun l h1 h2 h3 => hG2' l h2 h3 h1) hBB' (by rw [hB, Finset.pair_comm])
    (by rw [hB', Finset.pair_comm]) hτB hPB hCC' (by rw [hC, Finset.pair_comm])
    (by rw [hC', Finset.pair_comm]) hτC hPC
  obtain ⟨a, hpA, ha⟩ := R.near_param hij hAA' hA hA' hτA hPA
  obtain ⟨b, hpB, hb⟩ := R.near_param hik hBB' hB hB' hτB hPB
  obtain ⟨c, hpC, hc⟩ := R.near_param hjk hCC' hC hC' hτC hPC
  set Δ := det3 (u i) (u j) (u k)
  have Ni := dot_self_pos (R.u_ne_zero i)
  have Nj := dot_self_pos (R.u_ne_zero j)
  have Nk := dot_self_pos (R.u_ne_zero k)
  have ha0 : a ≠ 0 := by intro e; rw [e, zero_mul] at ha; exact lt_irrefl _ ha
  have hb0 : b ≠ 0 := by intro e; rw [e, zero_mul] at hb; exact lt_irrefl _ hb
  have hc0 : c ≠ 0 := by intro e; rw [e, zero_mul] at hc; exact lt_irrefl _ hc
  have eAB : orient (u i) (pt XA) (pt XB) P = a * b * Δ * (u i ⬝ᵥ u i) := by
    rw [hpA, hpB]; exact orient_corner _ _ _ _ _ _
  have eBC : orient (u k) (pt XB) (pt XC) P = b * c * Δ * (u k ⬝ᵥ u k) := by
    rw [hpB, hpC]; exact orient_corner2 _ _ _ _ _ _
  have eAC : orient (u j) (pt XA) (pt XC) P = a * c * Δ * (u j ⬝ᵥ u j) := by
    rw [orient_swap, hpC, hpA, orient_corner3]; ring
  have nAB : orient (u i) (pt XA) (pt XB) P ≠ 0 := by
    rw [eAB]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hΔ) Ni.ne'
  have nBC : orient (u k) (pt XB) (pt XC) P ≠ 0 := by
    rw [eBC]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hb0 hc0) hΔ) Nk.ne'
  have nAC : orient (u j) (pt XA) (pt XC) P ≠ 0 := by
    rw [eAC]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hc0) hΔ) Nj.ne'
  have hdiff : ∀ {x y : A.Crossing} {p q r s : Fin n}, Arrangement.Crossing.curves A x = {p, q} →
      Arrangement.Crossing.curves A y = {r, s} → ({p, q} : Finset (Fin n)) ≠ {r, s} → x ≠ y :=
    fun hx hy hne e => hne (by rw [← hx, ← hy, e])
  have dAB : XA ≠ XB := hdiff hA hB (by
    intro e; have : j ∈ ({i, k} : Finset (Fin n)) := by rw [← e]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hij e'.symm; exact hjk e'])
  have dAC : XA ≠ XC := hdiff hA hC (by
    intro e; have : i ∈ ({j, k} : Finset (Fin n)) := by rw [← e]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hij e'; exact hik e'])
  have dBC : XB ≠ XC := hdiff hB hC (by
    intro e; have : i ∈ ({j, k} : Finset (Fin n)) := by rw [← e]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hij e'; exact hik e'])
  have mem : ∀ {x : A.Crossing} {p q : Fin n}, Arrangement.Crossing.curves A x = {p, q} →
      p ∈ Arrangement.Crossing.curves A x ∧ q ∈ Arrangement.Crossing.curves A x :=
    fun hx => ⟨by rw [hx]; simp, by rw [hx]; simp⟩
  -- the six darts along the three sides
  obtain ⟨eAB', eBA', hAB1, hAB2, hAB3, hBA1, hBA2, hBA3, αAB, αBA⟩ :=
    R.heading_pair (mem hA).1 (mem hB).1 dAB nAB Ci
  obtain ⟨eBC', eCB', hBC1, hBC2, hBC3, hCB1, hCB2, hCB3, αBC, αCB⟩ :=
    R.heading_pair (mem hB).2 (mem hC).2 dBC nBC Ck
  obtain ⟨eAC', eCA', hAC1, hAC2, hAC3, hCA1, hCA2, hCA3, αAC, αCA⟩ :=
    R.heading_pair (mem hA).2 (mem hC).1 dAC nAC Cj
  obtain ⟨sAB1, -⟩ := sign_choice nAB
  obtain ⟨sBC1, -⟩ := sign_choice nBC
  obtain ⟨sAC1, -⟩ := sign_choice nAC
  -- `X = det3` values at the corners with their near signs
  have XB0 : 0 < b * det3 (u i) (u k) (pt XB) := by rw [det3_cross]; exact hb
  have XC0 : 0 < c * det3 (u j) (u k) (pt XC) := by rw [det3_cross]; exact hc
  have XA0 : 0 < a * det3 (u i) (u j) (pt XA) := by rw [det3_cross]; exact ha
  have KB : 0 < sgn eBA' * sgn eBC' * det3 (u i) (u k) (pt XB) * (-(a * b * c)) :=
    corner_sign (o₁ := -orient (u i) (pt XA) (pt XB) P) (o₂ := orient (u k) (pt XB) (pt XC) P)
      (by rw [hBA3]; linarith) (by rw [hBC3]; exact sBC1) XB0
      (show 0 < b ^ 2 * Δ ^ 2 * (u i ⬝ᵥ u i) * (u k ⬝ᵥ u k) by positivity)
      (by rw [eAB, eBC]; ring)
  have KC : 0 < sgn eCB' * sgn eCA' * det3 (u j) (u k) (pt XC) * (a * b * c) :=
    corner_sign (o₁ := -orient (u k) (pt XB) (pt XC) P) (o₂ := -orient (u j) (pt XA) (pt XC) P)
      (by rw [hCB3]; linarith) (by rw [hCA3]; linarith) XC0
      (show 0 < c ^ 2 * Δ ^ 2 * (u j ⬝ᵥ u j) * (u k ⬝ᵥ u k) by positivity)
      (by rw [eBC, eAC]; ring)
  have KA : 0 < sgn eAC' * sgn eAB' * det3 (u i) (u j) (pt XA) * (a * b * c) :=
    corner_sign (o₁ := orient (u j) (pt XA) (pt XC) P) (o₂ := orient (u i) (pt XA) (pt XB) P)
      (by rw [hAC3]; exact sAC1) (by rw [hAB3]; exact sAB1) XA0
      (show 0 < a ^ 2 * Δ ^ 2 * (u i ⬝ᵥ u i) * (u j ⬝ᵥ u j) by positivity)
      (by rw [eAC, eAB]; ring)
  have habc : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha0 hb0) hc0
  have sN : ∀ {Y q : ℝ}, 0 < Y * q → q < 0 → Y < 0 := fun hYq hq => by
    by_contra hc'; push_neg at hc'; nlinarith
  have sP : ∀ {Y q : ℝ}, 0 < Y * q → 0 < q → 0 < Y := fun hYq hq => pos_of_mul_pos_left hYq hq.le
  rcases lt_or_gt_of_ne habc with hneg | hpos
  · -- the triangle `A → B → C → A`
    have σB : A.σ eBA' = eBC' := R.σ_eq_of_det (by rw [hBC1, hBA1]) (by rw [hBC2, hBA2]; exact hik.symm)
      (by rw [hBA2, hBC2, hBA1]; exact sP KB (by linarith))
    have σC : A.σ eCB' = eCA' := R.σ_eq_of_det (by rw [hCA1, hCB1]) (by rw [hCA2, hCB2]; exact hjk)
      (by rw [hCB2, hCA2, hCB1, det3_swap]; have := sN KC hneg; linarith)
    have σA : A.σ eAC' = eAB' := R.σ_eq_of_det (by rw [hAB1, hAC1]) (by rw [hAB2, hAC2]; exact hij)
      (by rw [hAC2, hAB2, hAC1, det3_swap]; have := sN KA hneg; linarith)
    have φ1 : A.φ eAB' = eBC' := by rw [Arrangement.φ_apply, αAB, σB]
    have φ2 : A.φ eBC' = eCA' := by rw [Arrangement.φ_apply, αBC, σC]
    have φ3 : A.φ eCA' = eAB' := by rw [Arrangement.φ_apply, αCA, σA]
    have hT : A.IsTriangle (A.cellOf eAB') := isTriangle_of_φ3 (by rw [φ1, φ2, φ3])
      (by rw [φ1]; intro e; apply dAB; rw [← hAB1, ← hBC1, e])
      (by rw [φ1, φ2]; intro e; apply dAC; rw [← hAB1, ← hCA1, e])
    have hcur := curves_triangle hT hAB2 (by rw [φ1, hBC2]) (by rw [φ1, φ2, hCA2]) hik hij
      (Ne.symm hjk)
    exact final i k j hik hij hjk.symm hPi hPk hPj (htri _ hT i k j hcur)
  · -- the triangle `C → B → A → C`
    have σB : A.σ eBC' = eBA' := R.σ_eq_of_det (by rw [hBC1, hBA1]) (by rw [hBC2, hBA2]; exact hik)
      (by
        rw [hBA2, hBC2, hBC1, det3_swap]
        have := sN KB (by linarith)
        have e : sgn eBC' * sgn eBA' * -det3 (u i) (u k) (pt XB) =
          -(sgn eBA' * sgn eBC' * det3 (u i) (u k) (pt XB)) := by ring
        rw [e]; linarith)
    have σA : A.σ eAB' = eAC' := R.σ_eq_of_det (by rw [hAB1, hAC1]) (by rw [hAB2, hAC2]; exact hij.symm)
      (by
        rw [hAC2, hAB2, hAB1]
        have := sP KA hpos
        have e : sgn eAB' * sgn eAC' * det3 (u i) (u j) (pt XA) =
          sgn eAC' * sgn eAB' * det3 (u i) (u j) (pt XA) := by ring
        rw [e]; exact this)
    have σC : A.σ eCA' = eCB' := R.σ_eq_of_det (by rw [hCA1, hCB1]) (by rw [hCA2, hCB2]; exact hjk.symm)
      (by
        rw [hCB2, hCA2, hCA1]
        have := sP KC hpos
        have e : sgn eCA' * sgn eCB' * det3 (u j) (u k) (pt XC) =
          sgn eCB' * sgn eCA' * det3 (u j) (u k) (pt XC) := by ring
        rw [e]; exact this)
    have φ1 : A.φ eCB' = eBA' := by rw [Arrangement.φ_apply, αCB, σB]
    have φ2 : A.φ eBA' = eAC' := by rw [Arrangement.φ_apply, αBA, σA]
    have φ3 : A.φ eAC' = eCB' := by rw [Arrangement.φ_apply, αAC, σC]
    have hT : A.IsTriangle (A.cellOf eCB') := isTriangle_of_φ3 (by rw [φ1, φ2, φ3])
      (by rw [φ1]; intro e; apply dBC; rw [← hBA1, ← hCB1, e])
      (by rw [φ1, φ2]; intro e; apply dAC; rw [← hAC1, ← hCB1, e])
    have hcur := curves_triangle hT hCB2 (by rw [φ1, hBA2]) (by rw [φ1, φ2, hAC2]) hik.symm
      hjk.symm hij
    exact final k i j hik.symm hjk.symm hij hPk hPi hPj (htri _ hT k i j hcur)

end Pca.Circ
