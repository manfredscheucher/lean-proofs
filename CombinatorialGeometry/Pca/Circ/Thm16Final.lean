/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 16 (`doc/pca/circ.md`, decision C-D6)

Source: arXiv:1712.02149 (v6), Theorem 16: "Let `𝒜` be a connected digon-free arrangement of
pseudocircles. If every triple of pseudocircles which forms a triangle is NonKrupp, then `𝒜` is not
circularizable."

`Pca.Circ.thm16`. The model is intersecting (hence connected). Proof outline in
`Pca/Circ/Thm16.lean`: the first event of the outward sweep is either a Krupp triangle (Case T) or
a digon (Case D), both excluded.
-/
import Pca.Circ.Thm16Cells

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- **Theorem 16.** A digon-free (intersecting) arrangement of pseudocircles in which every triple
forming a triangle is a NonKrupp is not circularizable. -/
theorem thm16 (A : Arrangement n D) (hdig : ∀ f : A.Cell, ¬ A.IsDigon f)
    (htri : ∀ f : A.Cell, A.IsTriangle f → ∀ a b c : Fin n,
      Arrangement.Cell.curves A f = {a, b, c} → IsNonKrupp A a b c) :
    ¬ Circularizable A := by
  classical
  rintro ⟨R0⟩
  obtain ⟨Rg, hG1, hG2, hG3, hG4⟩ := R0.exists_generic2
  have R := Rg.isRep
  set u := Rg.u
  set h := Rg.h
  set pt := Rg.pt
  set sgn := Rg.sgn
  have hn := A.two_le_n
  set FD : Fin n × Fin n → ℝ := fun t =>
    foot (u t.1) (u t.2) (h t.1) (h t.2) ⬝ᵥ foot (u t.1) (u t.2) (h t.1) (h t.2)
  set SD := univ.filter (fun t : Fin n × Fin n => t.1 ≠ t.2)
  have hSD : SD.Nonempty := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [SD, Fin.ext_iff]⟩
  obtain ⟨⟨a, b⟩, hab', hFD⟩ := SD.exists_max_image FD hSD
  simp only [SD, Finset.mem_filter, Finset.mem_univ, true_and] at hab'
  have hab : a ≠ b := hab'
  have hmaxD : ∀ c d : Fin n, c ≠ d → FD (c, d) ≤ FD (a, b) := fun c d hcd =>
    hFD (c, d) (by simp [SD, hcd])
  set FT : Fin n × Fin n × Fin n → ℝ := fun t =>
    triplePt (u t.1) (u t.2.1) (u t.2.2) (h t.1) (h t.2.1) (h t.2.2) ⬝ᵥ
      triplePt (u t.1) (u t.2.1) (u t.2.2) (h t.1) (h t.2.1) (h t.2.2)
  set ST := univ.filter (fun t : Fin n × Fin n × Fin n =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ IsKrupp A t.1 t.2.1 t.2.2)
  have hQ : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → ∀ Q : V, u x ⬝ᵥ Q = h x →
      u y ⬝ᵥ Q = h y → u z ⬝ᵥ Q = h z → Q = triplePt (u x) (u y) (u z) (h x) (h y) (h z) := by
    intro x y z hxy hxz hyz Q h1 h2 h3
    obtain ⟨e1, e2, e3⟩ := triplePt_spec (h x) (h y) (h z) (hG1 x y z hxy hxz hyz)
    exact eq_of_three_planes (hG1 x y z hxy hxz hyz) (by rw [h1, e1]) (by rw [h2, e2])
      (by rw [h3, e3])
  by_cases hcase : ∃ t ∈ ST, FD (a, b) ≤ FT t
  · ------------------------------------------------------------ Case T
    obtain ⟨t0, ht0, hFt0⟩ := hcase
    obtain ⟨⟨i, j, k⟩, hmem, hFT⟩ := ST.exists_max_image FT ⟨t0, ht0⟩
    simp only [ST, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hij, hik, hjk, hK⟩ := hmem
    set P := triplePt (u i) (u j) (u k) (h i) (h j) (h k)
    have hΔ := hG1 i j k hij hik hjk
    obtain ⟨hPi, hPj, hPk⟩ := triplePt_spec (h i) (h j) (h k) hΔ
    have hPin : P ⬝ᵥ P < 1 := by
      obtain ⟨hd, Q, h1, h2, h3, h4⟩ := (R.fact1 hij hik hjk).1 hK
      rw [hQ i j k hij hik hjk Q h1 h2 h3] at h4; exact h4
    have hmaxT : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → IsKrupp A x y z → ∀ Q : V,
        u x ⬝ᵥ Q = h x → u y ⬝ᵥ Q = h y → u z ⬝ᵥ Q = h z → Q ⬝ᵥ Q ≤ P ⬝ᵥ P := by
      intro x y z hxy hxz hyz hk Q h1 h2 h3
      rw [hQ x y z hxy hxz hyz Q h1 h2 h3]
      exact hFT (x, y, z) (by simp [ST, hxy, hxz, hyz, hk])
    have hmaxD' : ∀ x y : Fin n, x ≠ y →
        foot (u x) (u y) (h x) (h y) ⬝ᵥ foot (u x) (u y) (h x) (h y) ≤ P ⬝ᵥ P := fun x y hxy =>
      le_trans (hmaxD x y hxy) (le_trans hFt0 (hFT t0 ht0))
    have hG2' : ∀ l, l ≠ i → l ≠ j → l ≠ k → u l ⬝ᵥ P ≠ h l := fun l hli hlj hlk e =>
      hG2 i j k l hij hik (Ne.symm hli) hjk (Ne.symm hlj) (Ne.symm hlk) P hPi hPj hPk e
    have hPm : ∀ {x y z : Fin n}, x ≠ y → x ≠ z → y ≠ z → u z ⬝ᵥ P = h z →
        P ≠ foot (u x) (u y) (h x) (h y) := fun hxy hxz hyz hz e =>
      hG4 _ _ _ hxy hxz hyz (by rw [← e]; exact hz)
    obtain ⟨XA, XA', τA, a', hAA', hA, hA', hτA, hPA, hoA, hpA, ha⟩ :=
      R.exists_outer hij hPi hPj hPin (hPm hij hik hjk hPk)
    obtain ⟨XB, XB', τB, b', hBB', hB, hB', hτB, hPB, hoB, hpB, hb⟩ :=
      R.exists_outer hik hPi hPk hPin (hPm hik hij hjk.symm hPj)
    obtain ⟨XC, XC', τC, c', hCC', hC, hC', hτC, hPC, hoC, hpC, hc⟩ :=
      R.exists_outer hjk hPj hPk hPin (hPm hjk hij.symm hik.symm hPi)
    have fc : ∀ {x y : Fin n}, x ≠ y → foot (u y) (u x) (h y) (h x) = foot (u x) (u y) (h x) (h y) :=
      fun hxy => foot_comm (R.cross_ne_zero hxy)
    have Ci := R.out_side hG1 hij hik hjk hPi hPj hPk hPin hmaxT hmaxD' hG2' hAA' hA hA' hτA hPA
      hoA hBB' hB hB' hτB hPB hoB
    have Cj := R.out_side hG1 hij.symm hjk hik hPj hPi hPk hPin hmaxT hmaxD'
      (fun l h1 h2 h3 => hG2' l h2 h1 h3) hAA' (by rw [hA, Finset.pair_comm])
      (by rw [hA', Finset.pair_comm]) hτA hPA (by rw [fc hij]; exact hoA) hCC' hC hC' hτC hPC hoC
    have Ck := R.out_side hG1 hik.symm hjk.symm hij hPk hPi hPj hPin hmaxT hmaxD'
      (fun l h1 h2 h3 => hG2' l h2 h3 h1) hBB' (by rw [hB, Finset.pair_comm])
      (by rw [hB', Finset.pair_comm]) hτB hPB (by rw [fc hik]; exact hoB) hCC'
      (by rw [hC, Finset.pair_comm]) (by rw [hC', Finset.pair_comm]) hτC hPC
      (by rw [fc hjk]; exact hoC)
    -- orientations at the corners
    set Δ := det3 (u i) (u j) (u k)
    have Ni := dot_self_pos (R.u_ne_zero i)
    have Nj := dot_self_pos (R.u_ne_zero j)
    have Nk := dot_self_pos (R.u_ne_zero k)
    have ha0 : a' ≠ 0 := by intro e; rw [e, zero_mul] at ha; exact lt_irrefl _ ha
    have hb0 : b' ≠ 0 := by intro e; rw [e, zero_mul] at hb; exact lt_irrefl _ hb
    have hc0 : c' ≠ 0 := by intro e; rw [e, zero_mul] at hc; exact lt_irrefl _ hc
    have eAB : orient (u i) (pt XA) (pt XB) P = a' * b' * Δ * (u i ⬝ᵥ u i) := by
      rw [hpA, hpB]; exact orient_corner _ _ _ _ _ _
    have eBC : orient (u k) (pt XB) (pt XC) P = b' * c' * Δ * (u k ⬝ᵥ u k) := by
      rw [hpB, hpC]; exact orient_corner2 _ _ _ _ _ _
    have eAC : orient (u j) (pt XA) (pt XC) P = a' * c' * Δ * (u j ⬝ᵥ u j) := by
      rw [orient_swap, hpC, hpA, orient_corner3]; ring
    have nAB : -orient (u i) (pt XA) (pt XB) P ≠ 0 := by
      rw [eAB, neg_ne_zero]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hΔ) Ni.ne'
    have nBC : -orient (u k) (pt XB) (pt XC) P ≠ 0 := by
      rw [eBC, neg_ne_zero]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hb0 hc0) hΔ) Nk.ne'
    have nAC : -orient (u j) (pt XA) (pt XC) P ≠ 0 := by
      rw [eAC, neg_ne_zero]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hc0) hΔ) Nj.ne'
    have hdiff : ∀ {x y : A.Crossing} {p q r s : Fin n},
        Arrangement.Crossing.curves A x = {p, q} → Arrangement.Crossing.curves A y = {r, s} →
        ({p, q} : Finset (Fin n)) ≠ {r, s} → x ≠ y :=
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
    have flip : ∀ {o x : ℝ}, 0 < x * o → x * -o < 0 := fun h' => by linarith
    obtain ⟨eAB', eBA', hAB1, hAB2, hAB3, hBA1, hBA2, hBA3, αAB, αBA⟩ :=
      R.heading_pair_r (mem hA).1 (mem hB).1 dAB nAB (fun z h1 h2 h3 => flip (Ci z h1 h2 h3))
    obtain ⟨eBC', eCB', hBC1, hBC2, hBC3, hCB1, hCB2, hCB3, αBC, αCB⟩ :=
      R.heading_pair_r (mem hB).2 (mem hC).2 dBC nBC (fun z h1 h2 h3 => flip (Ck z h1 h2 h3))
    obtain ⟨eAC', eCA', hAC1, hAC2, hAC3, hCA1, hCA2, hCA3, αAC, αCA⟩ :=
      R.heading_pair_r (mem hA).2 (mem hC).1 dAC nAC (fun z h1 h2 h3 => flip (Cj z h1 h2 h3))
    have sAB1 := (sign_choice nAB).1
    have sBC1 := (sign_choice nBC).1
    have sAC1 := (sign_choice nAC).1
    have XB0 : 0 < -b' * det3 (u i) (u k) (pt XB) := by rw [det3_cross]; linarith
    have XC0 : 0 < -c' * det3 (u j) (u k) (pt XC) := by rw [det3_cross]; linarith
    have XA0 : 0 < -a' * det3 (u i) (u j) (pt XA) := by rw [det3_cross]; linarith
    have KB : 0 < sgn eBA' * sgn eBC' * det3 (u i) (u k) (pt XB) * (a' * b' * c') :=
      corner_sign (o₁ := orient (u i) (pt XA) (pt XB) P) (o₂ := -orient (u k) (pt XB) (pt XC) P)
        (by rw [hBA3]; linarith) (by rw [hBC3]; exact sBC1) XB0
        (show 0 < b' ^ 2 * Δ ^ 2 * (u i ⬝ᵥ u i) * (u k ⬝ᵥ u k) by positivity)
        (by rw [eAB, eBC]; ring)
    have KC : 0 < sgn eCB' * sgn eCA' * det3 (u j) (u k) (pt XC) * (-(a' * b' * c')) :=
      corner_sign (o₁ := orient (u k) (pt XB) (pt XC) P) (o₂ := orient (u j) (pt XA) (pt XC) P)
        (by rw [hCB3]; linarith) (by rw [hCA3]; linarith) XC0
        (show 0 < c' ^ 2 * Δ ^ 2 * (u j ⬝ᵥ u j) * (u k ⬝ᵥ u k) by positivity)
        (by rw [eBC, eAC]; ring)
    have KA : 0 < sgn eAC' * sgn eAB' * det3 (u i) (u j) (pt XA) * (-(a' * b' * c')) :=
      corner_sign (o₁ := -orient (u j) (pt XA) (pt XC) P) (o₂ := -orient (u i) (pt XA) (pt XB) P)
        (by rw [hAC3]; exact sAC1) (by rw [hAB3]; exact sAB1) XA0
        (show 0 < a' ^ 2 * Δ ^ 2 * (u i ⬝ᵥ u i) * (u j ⬝ᵥ u j) by positivity)
        (by rw [eAC, eAB]; ring)
    have habc : a' * b' * c' ≠ 0 := mul_ne_zero (mul_ne_zero ha0 hb0) hc0
    have sN : ∀ {Y q : ℝ}, 0 < Y * q → q < 0 → Y < 0 := fun hYq hq => by
      by_contra hc'; push_neg at hc'; nlinarith
    have sP : ∀ {Y q : ℝ}, 0 < Y * q → 0 < q → 0 < Y := fun hYq hq => pos_of_mul_pos_left hYq hq.le
    have krupp : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → u x ⬝ᵥ P = h x → u y ⬝ᵥ P = h y →
        u z ⬝ᵥ P = h z → IsKrupp A x y z := fun x y z hxy hxz hyz hx hy hz =>
      (R.fact1 hxy hxz hyz).2 ⟨hG1 x y z hxy hxz hyz, P, hx, hy, hz, hPin⟩
    rcases lt_or_gt_of_ne habc with hneg | hpos
    · -- the triangle `C → B → A → C`
      have σB : A.σ eBC' = eBA' := R.σ_eq_of_det (by rw [hBC1, hBA1])
        (by rw [hBC2, hBA2]; exact hik)
        (by
          rw [hBA2, hBC2, hBC1, det3_swap]
          have := sN KB hneg
          have e : sgn eBC' * sgn eBA' * -det3 (u i) (u k) (pt XB) =
            -(sgn eBA' * sgn eBC' * det3 (u i) (u k) (pt XB)) := by ring
          rw [e]; linarith)
      have σA : A.σ eAB' = eAC' := R.σ_eq_of_det (by rw [hAB1, hAC1])
        (by rw [hAB2, hAC2]; exact hij.symm)
        (by
          rw [hAC2, hAB2, hAB1]
          have := sP KA (by linarith)
          have e : sgn eAB' * sgn eAC' * det3 (u i) (u j) (pt XA) =
            sgn eAC' * sgn eAB' * det3 (u i) (u j) (pt XA) := by ring
          rw [e]; exact this)
      have σC : A.σ eCA' = eCB' := R.σ_eq_of_det (by rw [hCA1, hCB1])
        (by rw [hCA2, hCB2]; exact hjk.symm)
        (by
          rw [hCB2, hCA2, hCA1]
          have := sP KC (by linarith)
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
      exact htri _ hT k i j hcur (krupp k i j hik.symm hjk.symm hij hPk hPi hPj)
    · -- the triangle `A → B → C → A`
      have σB : A.σ eBA' = eBC' := R.σ_eq_of_det (by rw [hBC1, hBA1])
        (by rw [hBC2, hBA2]; exact hik.symm)
        (by rw [hBA2, hBC2, hBA1]; exact sP KB hpos)
      have σC : A.σ eCB' = eCA' := R.σ_eq_of_det (by rw [hCA1, hCB1])
        (by rw [hCA2, hCB2]; exact hjk)
        (by rw [hCB2, hCA2, hCB1, det3_swap]; have := sN KC (by linarith); linarith)
      have σA : A.σ eAC' = eAB' := R.σ_eq_of_det (by rw [hAB1, hAC1])
        (by rw [hAB2, hAC2]; exact hij)
        (by rw [hAC2, hAB2, hAC1, det3_swap]; have := sN KA (by linarith); linarith)
      have φ1 : A.φ eAB' = eBC' := by rw [Arrangement.φ_apply, αAB, σB]
      have φ2 : A.φ eBC' = eCA' := by rw [Arrangement.φ_apply, αBC, σC]
      have φ3 : A.φ eCA' = eAB' := by rw [Arrangement.φ_apply, αCA, σA]
      have hT : A.IsTriangle (A.cellOf eAB') := isTriangle_of_φ3 (by rw [φ1, φ2, φ3])
        (by rw [φ1]; intro e; apply dAB; rw [← hAB1, ← hBC1, e])
        (by rw [φ1, φ2]; intro e; apply dAC; rw [← hAB1, ← hCA1, e])
      have hcur := curves_triangle hT hAB2 (by rw [φ1, hBC2]) (by rw [φ1, φ2, hCA2]) hik hij
        (Ne.symm hjk)
      exact htri _ hT i k j hcur (krupp i k j hik hij hjk.symm hPi hPk hPj)
  · ------------------------------------------------------------ Case D
    push_neg at hcase
    have hmaxT : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → IsKrupp A x y z → ∀ Q : V,
        u x ⬝ᵥ Q = h x → u y ⬝ᵥ Q = h y → u z ⬝ᵥ Q = h z → Q ⬝ᵥ Q < FD (a, b) := by
      intro x y z hxy hxz hyz hk Q h1 h2 h3
      rw [hQ x y z hxy hxz hyz Q h1 h2 h3]
      exact hcase (x, y, z) (by simp [ST, hxy, hxz, hyz, hk])
    have hw := R.cross_ne_zero hab
    have hsym : foot (u b) (u a) (h b) (h a) ⬝ᵥ foot (u b) (u a) (h b) (h a) =
        foot (u a) (u b) (h a) (h b) ⬝ᵥ foot (u a) (u b) (h a) (h b) := foot_norm_comm hw
    have hGc : ∀ {x y : Fin n}, x ≠ y → u y ⬝ᵥ center (u x) (h x) - h y ≠ 0 := by
      intro x y hxy e
      apply hG3 x y hxy
      have hpos := dot_self_pos (R.u_ne_zero x)
      have e' : u y ⬝ᵥ center (u x) (h x) = h x * (u x ⬝ᵥ u y) / (u x ⬝ᵥ u x) := by
        rw [center, dotProduct_smul, smul_eq_mul, dotProduct_comm (u y)]; ring
      rw [e'] at e
      field_simp at e
      linarith
    have Da := R.digon_side hG1 hab (fun c d hcd => hmaxD c d hcd) hmaxT (hGc hab)
    have Db := R.digon_side hG1 hab.symm (fun c d hcd => by rw [hsym]; exact hmaxD c d hcd)
      (fun x y z hxy hxz hyz hk Q h1 h2 h3 => by rw [hsym]; exact hmaxT x y z hxy hxz hyz hk Q h1 h2 h3)
      (hGc hab.symm)
    obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair A hab
    obtain ⟨l, hl0, ex, ey, -⟩ := R.pair_lam hab hxy hx hy
    set κ := -2 * l
    have hyx : pt y = pt x + κ • (u a ⨯₃ u b) := by
      rw [ex, ey]; ext k; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, κ]
      ring
    have hyx' : pt y = pt x + (-κ) • (u b ⨯₃ u a) := by
      rw [hyx, ← cross_anticomm, smul_neg, neg_smul]
    have hκ : κ ≠ 0 := by simp only [κ]; exact mul_ne_zero (by norm_num) hl0
    obtain ⟨hxa, hxb⟩ := R.onCirc_pair' hx
    have Na := dot_self_pos (R.u_ne_zero a)
    have Nb := dot_self_pos (R.u_ne_zero b)
    have notin : ∀ {z : A.Crossing} {p q : Fin n}, p ≠ q → p ∈ Arrangement.Crossing.curves A z →
        z ≠ x → z ≠ y → ({p, q} : Finset (Fin n)) = {a, b} → q ∉ Arrangement.Crossing.curves A z :=
      fun hpq hp hzx hzy hpq' hq => by
        have := A.curves_eq_pair hp hq hpq
        rw [hpq'] at this
        rcases eq_or_eq_of_pair hxy hx hy this with e | e
        · exact hzx e
        · exact hzy e
    refine (R.digon_of_sides hab hxy hx hy (ra := κ * (u a ⬝ᵥ u a) *
      (u b ⬝ᵥ center (u a) (h a) - h b)) (rb := -κ * (u b ⬝ᵥ u b) *
      (u a ⬝ᵥ center (u b) (h b) - h a)) ?_ ?_ ?_ ?_).elim (fun f hf => hdig f hf)
    · exact mul_ne_zero (mul_ne_zero hκ Na.ne') (hGc hab)
    · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hκ) Nb.ne') (hGc hab.symm)
    · intro z hz hzx hzy
      have hzb := notin hab hz hzx hzy rfl
      have hd := Da z hz hzb
      have hza := (R.onCirc hz).2
      rw [hyx, orient_chord, hza, hxa.2, hxb.2, sub_self, mul_zero, add_zero]
      nlinarith [mul_pos (mul_pos (mul_self_pos.2 hκ) (mul_pos Na Na)) hd]
    · intro z hz hzx hzy
      have hza := notin hab.symm hz hzx hzy (Finset.pair_comm _ _)
      have hd := Db z hz hza
      have hzb := (R.onCirc hz).2
      rw [hyx', orient_chord, hzb, hxb.2, hxa.2, sub_self, mul_zero, add_zero]
      nlinarith [mul_pos (mul_pos (mul_self_pos.2 hκ) (mul_pos Nb Nb)) hd]

end Pca.Circ
