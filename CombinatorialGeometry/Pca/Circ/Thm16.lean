/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 16, the two extremal cases (`doc/pca/circ.md`, C-D6)

Static form of the paper's outward sweep ("move planes away from the origin; the first event is a
triangle flip or a digon collapse"). In a generic representation (C-D4) let `M_T` be the largest
norm of a Krupp triple point (inside the sphere) and `M_D` the largest norm of the foot point of a
line `E_a ∩ E_b`.

* Case T (`out_side`): a Krupp triple with the largest triple point `P`, `|P| ≥ M_D`. The
  crossings `A, B` of the circle `i` on the lines through `P` "outward" from `P` (away from the foot
  points) are consecutive: a crossing beyond the chord `A B` gives a Krupp triple point farther out
  or a foot point farther out.
* Case D (`digon_side`): a pair `a, b` with the largest foot point `m`, all Krupp triple points
  closer. On the circle `a` every crossing lies on the side of the plane `E_b` of the center `c_a`:
  otherwise a Krupp triple point on the chord `E_a ∩ E_b` (norm `≥ |m|`) or a foot point farther
  out.
-/
import Pca.Circ.Thm19Main
import Pca.Circ.Generic2

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The center of the circle of the plane `⟨u, x⟩ = h`. -/
noncomputable def center (u : V) (h : ℝ) : V := (h / (u ⬝ᵥ u)) • u

theorem center_perp {u v : V} {h : ℝ} (hv : u ⬝ᵥ v = 0) : center u h ⬝ᵥ v = 0 := by
  rw [center, smul_dotProduct, hv, smul_zero]

theorem dot_center_self {u : V} (hu : u ≠ 0) (h : ℝ) : u ⬝ᵥ center u h = h := by
  rw [center, dotProduct_smul, smul_eq_mul]; field_simp [(dot_self_pos hu).ne']

/-- Points of the plane: `|x|² = |c|² + |x - c|²`. -/
theorem norm_plane {u x : V} {h : ℝ} (hu : u ≠ 0) (hx : u ⬝ᵥ x = h) :
    x ⬝ᵥ x = center u h ⬝ᵥ center u h + (x - center u h) ⬝ᵥ (x - center u h) := by
  have : center u h ⬝ᵥ (x - center u h) = 0 :=
    center_perp (by rw [dotProduct_sub, hx, dot_center_self hu, sub_self])
  simp only [sub_dotProduct, dotProduct_sub] at this ⊢
  rw [dotProduct_comm x (center u h)]
  linarith

/-- An inner point and a point of the sphere: the segment stays inside. -/
theorem seg_inside {P x : V} (hP : P ⬝ᵥ P < 1) (hx : x ⬝ᵥ x = 1) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t < 1) : (P + t • (x - P)) ⬝ᵥ (P + t • (x - P)) < 1 := by
  have hPx : P ⬝ᵥ x < 1 := by
    have := dot_self_nonneg (P - x)
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hx, dotProduct_comm x P] at this
    linarith
  have e : (P + t • (x - P)) ⬝ᵥ (P + t • (x - P)) =
      (1 - t) ^ 2 * (P ⬝ᵥ P) + 2 * t * (1 - t) * (P ⬝ᵥ x) + t ^ 2 * (x ⬝ᵥ x) := by
    simp only [dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [e, hx]
  have h2 : 0 < (1 - t) ^ 2 := by have : 0 < 1 - t := by linarith
                                  positivity
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h0) (by linarith : 0 ≤ 1 - t)]

/-- The foot point is the closest point of the line. -/
theorem foot_le {ui uj q : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0) (hqi : ui ⬝ᵥ q = hi)
    (hqj : uj ⬝ᵥ q = hj) : foot ui uj hi hj ⬝ᵥ foot ui uj hi hj ≤ q ⬝ᵥ q := by
  have key := eq_smul_cross_of_perp (v := q - foot ui uj hi hj) hw
    (by rw [dotProduct_sub, hqi, dot_foot_left _ _ _ _ hw, sub_self])
    (by rw [dotProduct_sub, hqj, dot_foot_right _ _ _ _ hw, sub_self])
  set κ := ((ui ⨯₃ uj) ⬝ᵥ (q - foot ui uj hi hj)) / ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj))
  have hq : q = foot ui uj hi hj + κ • (ui ⨯₃ uj) := by rw [← key]; abel
  have hmw := cross_dot_foot ui uj hi hj
  rw [hq]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (foot ui uj hi hj) (ui ⨯₃ uj), hmw]
  nlinarith [dot_self_nonneg (ui ⨯₃ uj), sq_nonneg κ]

/-- Orientation along the chord of two circles is the side of the second plane. -/
theorem orient_chord (ua ub x p : V) (κ : ℝ) :
    orient ua x (x + κ • (ua ⨯₃ ub)) p =
      -κ * (ua ⬝ᵥ ua) * (ub ⬝ᵥ p - ub ⬝ᵥ x) + κ * (ua ⬝ᵥ ub) * (ua ⬝ᵥ p - ua ⬝ᵥ x) := by
  simp only [orient, det3_eq, dot_eq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cross_0, cross_1, cross_2]; ring

/-- Beyond the chord `p₁ p₂` (away from the inner point `P`), the affine function
`f x = ⟨x - P, P - c⟩` is positive if it is positive at `p₁, p₂`. -/
theorem far_pos {u P p₁ p₂ x c : V} {h : ℝ} (hu : u ≠ 0) (c1 : OnCirc u h p₁) (c2 : OnCirc u h p₂)
    (hx : OnCirc u h x) (h12 : p₁ ≠ p₂) (hPi : u ⬝ᵥ P = h) (hPin : P ⬝ᵥ P < 1)
    (f1 : 0 < (p₁ - P) ⬝ᵥ (P - c)) (f2 : 0 < (p₂ - P) ⬝ᵥ (P - c))
    (hxneg : orient u p₁ p₂ x * orient u p₁ p₂ P < 0) : 0 < (x - P) ⬝ᵥ (P - c) := by
  set ox := orient u p₁ p₂ x
  set oP := orient u p₁ p₂ P
  have nP : oP ≠ 0 := by intro e; rw [e, mul_zero] at hxneg; exact lt_irrefl _ hxneg
  have hd : oP - ox ≠ 0 := by
    intro e; have : oP = ox := sub_eq_zero.1 e; rw [this] at hxneg; nlinarith [sq_nonneg ox]
  set t := oP / (oP - ox)
  have ht : 0 < t ∧ t < 1 := by
    rcases lt_or_gt_of_ne nP with h1 | h1
    · have h2 : 0 < ox := by by_contra h3; push_neg at h3; nlinarith
      exact ⟨div_pos_of_neg_of_neg h1 (by linarith), (div_lt_one_of_neg (by linarith)).2
        (by linarith)⟩
    · have h2 : ox < 0 := by by_contra h3; push_neg at h3; nlinarith
      exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  set q := P + t • (x - P)
  have hq0 : orient u p₁ p₂ q = 0 := by
    simp only [q]; rw [orient_affine]; simp only [t]; field_simp; ring
  have hqi : u ⬝ᵥ q = h := by
    simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, hPi, hx.2, sub_self,
      smul_zero, add_zero]
  have hqin : q ⬝ᵥ q < 1 := seg_inside hPin hx.1 ht.1.le ht.2
  have key := eq_smul_of_det3_eq_zero hu (sub_ne_zero.2 h12.symm)
    (by rw [dotProduct_sub, c2.2, c1.2, sub_self]) (by rw [dotProduct_sub, hqi, c1.2, sub_self])
    hq0
  set μ := ((p₂ - p₁) ⬝ᵥ (q - p₁)) / ((p₂ - p₁) ⬝ᵥ (p₂ - p₁))
  have hqμ : q = p₁ + μ • (p₂ - p₁) := by rw [← key]; abel
  have hμ := mem_Ioo_of_inside c1.1 c2.1 h12 (t := μ) (by rw [← hqμ]; exact hqin)
  have e1 : (q - P) ⬝ᵥ (P - c) = (1 - μ) * ((p₁ - P) ⬝ᵥ (P - c)) + μ * ((p₂ - P) ⬝ᵥ (P - c)) := by
    rw [hqμ]; simp only [dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have e2 : (q - P) ⬝ᵥ (P - c) = t * ((x - P) ⬝ᵥ (P - c)) := by
    simp only [q, dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hμ1 : 0 < 1 - μ := by linarith [hμ.2]
  have : 0 < (q - P) ⬝ᵥ (P - c) := by
    rw [e1]; nlinarith [mul_pos hμ1 f1, mul_pos hμ.1 f2]
  rw [e2] at this
  exact pos_of_mul_pos_right this ht.1.le

/-- A point of the plane of `P` with `f > 0` is farther from the origin than `P`. -/
theorem farther {u P q : V} {h : ℝ} (hPi : u ⬝ᵥ P = h) (hqi : u ⬝ᵥ q = h)
    (hf : 0 < (q - P) ⬝ᵥ (P - center u h)) : P ⬝ᵥ P < q ⬝ᵥ q := by
  have hcperp : center u h ⬝ᵥ (q - P) = 0 := center_perp (by rw [dotProduct_sub, hqi, hPi, sub_self])
  have e : q ⬝ᵥ q = P ⬝ᵥ P + 2 * ((q - P) ⬝ᵥ (P - center u h)) +
      2 * (center u h ⬝ᵥ (q - P)) + (q - P) ⬝ᵥ (q - P) := by
    simp only [dot_eq, Pi.sub_apply]; ring
  rw [e, hcperp]
  nlinarith [dot_self_nonneg (q - P)]

/-- Two crossing chords: an affine function vanishing at both ends of one chord changes sign on
the other. -/
theorem chord_cross_sign {u p₁ p₂ z z' ul : V} {h hl : ℝ} (hu : u ≠ 0) (c1 : OnCirc u h p₁)
    (c2 : OnCirc u h p₂) (cz : OnCirc u h z) (cz' : OnCirc u h z') (hzz : z ≠ z') (h12 : p₁ ≠ p₂)
    (hsep : orient u p₁ p₂ z * orient u p₁ p₂ z' < 0) (hgz : ul ⬝ᵥ z - hl = 0)
    (hgz' : ul ⬝ᵥ z' - hl = 0) (h12' : 0 < (ul ⬝ᵥ p₁ - hl) * (ul ⬝ᵥ p₂ - hl)) : False := by
  obtain ⟨t, μ, -, -, hμ0, hμ1, he⟩ := chord_meet hu cz cz' c1 c2 hzz h12 hsep
  have h1 : ul ⬝ᵥ (z + t • (z' - z)) - hl = 0 := by
    have : ul ⬝ᵥ (z + t • (z' - z)) - hl = (ul ⬝ᵥ z - hl) + t * ((ul ⬝ᵥ z' - hl) - (ul ⬝ᵥ z - hl)) := by
      simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
    rw [this, hgz, hgz']; ring
  have h2 : ul ⬝ᵥ (p₁ + μ • (p₂ - p₁)) - hl =
      (1 - μ) * (ul ⬝ᵥ p₁ - hl) + μ * (ul ⬝ᵥ p₂ - hl) := by
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
  rw [he, h2] at h1
  have hμ' : 0 < 1 - μ := by linarith
  rcases lt_or_gt_of_ne (show ul ⬝ᵥ p₁ - hl ≠ 0 by
      intro e; rw [e, zero_mul] at h12'; exact lt_irrefl _ h12') with q1 | q1
  · have q2 : ul ⬝ᵥ p₂ - hl < 0 := by by_contra q3; push_neg at q3; nlinarith
    nlinarith [mul_pos hμ' (neg_pos.2 q1), mul_pos hμ0 (neg_pos.2 q2)]
  · have q2 : 0 < ul ⬝ᵥ p₂ - hl := by by_contra q3; push_neg at q3; nlinarith
    nlinarith [mul_pos hμ' q1, mul_pos hμ0 q2]

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}
variable (R : IsCircleRep A u h pt sgn)
include R

/-- The two crossings of a pair are `m ± l w`. -/
theorem pair_lam {a b : Fin n} (hab : a ≠ b) {x y : A.Crossing} (hxy : x ≠ y)
    (hx : Arrangement.Crossing.curves A x = {a, b}) (hy : Arrangement.Crossing.curves A y = {a, b}) :
    ∃ l : ℝ, l ≠ 0 ∧ pt x = foot (u a) (u b) (h a) (h b) + l • (u a ⨯₃ u b) ∧
      pt y = foot (u a) (u b) (h a) (h b) - l • (u a ⨯₃ u b) ∧
      l ^ 2 * ((u a ⨯₃ u b) ⬝ᵥ (u a ⨯₃ u b)) =
        1 - foot (u a) (u b) (h a) (h b) ⬝ᵥ foot (u a) (u b) (h a) (h b) := by
  obtain ⟨hxa, hxb⟩ := R.onCirc_pair' hx
  obtain ⟨hya, hyb⟩ := R.onCirc_pair' hy
  have hw := R.cross_ne_zero hab
  obtain ⟨l, hl, hl2⟩ := exists_lam hw hxa.1 hxa.2 hxb.2
  obtain ⟨l', hl', hl2'⟩ := exists_lam hw hya.1 hya.2 hyb.2
  have hpos := dot_self_pos hw
  have hne : l ≠ l' := fun e => hxy (R.inj (by rw [hl, hl', e]))
  have hsq : l ^ 2 = l' ^ 2 := by
    have : (l ^ 2 - l' ^ 2) * ((u a ⨯₃ u b) ⬝ᵥ (u a ⨯₃ u b)) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_right hpos.ne']
  have hl'eq : l' = -l := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq.symm with e | e
    · exact absurd e.symm hne
    · exact e
  refine ⟨l, fun e => hne (by rw [hl'eq, e, neg_zero]), hl, by rw [hl', hl'eq, neg_smul,
    ← sub_eq_add_neg], hl2⟩

/-- **Case D.** For the pair `a, b` with the farthest foot point, every crossing of the circle
`a` lies on the side of `E_b` of the center of the circle `a`. -/
theorem digon_side (hG1 : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → det3 (u a) (u b) (u c) ≠ 0)
    {a b : Fin n} (hab : a ≠ b)
    (hmaxD : ∀ c d : Fin n, c ≠ d → foot (u c) (u d) (h c) (h d) ⬝ᵥ foot (u c) (u d) (h c) (h d) ≤
      foot (u a) (u b) (h a) (h b) ⬝ᵥ foot (u a) (u b) (h a) (h b))
    (hmaxT : ∀ c d e : Fin n, c ≠ d → c ≠ e → d ≠ e → IsKrupp A c d e → ∀ Q : V,
      u c ⬝ᵥ Q = h c → u d ⬝ᵥ Q = h d → u e ⬝ᵥ Q = h e →
      Q ⬝ᵥ Q < foot (u a) (u b) (h a) (h b) ⬝ᵥ foot (u a) (u b) (h a) (h b))
    (hGc : u b ⬝ᵥ center (u a) (h a) - h b ≠ 0)
    (z : A.Crossing) (hza : a ∈ Arrangement.Crossing.curves A z)
    (hzb : b ∉ Arrangement.Crossing.curves A z) :
    0 < (u b ⬝ᵥ pt z - h b) * (u b ⬝ᵥ center (u a) (h a) - h b) := by
  have hua := R.u_ne_zero a
  set m := foot (u a) (u b) (h a) (h b)
  set c := center (u a) (h a)
  set g : V → ℝ := fun p => u b ⬝ᵥ p - h b
  have hw := R.cross_ne_zero hab
  have hgz : g (pt z) ≠ 0 := by
    intro e
    have := R.curves_eq_of_on hab (R.onCirc hza).2 (sub_eq_zero.1 e)
    exact hzb (by rw [this]; simp)
  -- far from the center beyond `E_b`
  have far : ∀ p : V, u a ⬝ᵥ p = h a → g p * g c < 0 → m ⬝ᵥ m < p ⬝ᵥ p := by
    intro p hp hneg
    have hne : g c - g p ≠ 0 := by
      intro e; have : g c = g p := sub_eq_zero.1 e; rw [this] at hneg; nlinarith [sq_nonneg (g p)]
    set t := g c / (g c - g p)
    have ht : 0 < t ∧ t < 1 := by
      rcases lt_or_gt_of_ne (show g c ≠ 0 from hGc) with h1 | h1
      · have h2 : 0 < g p := by by_contra h3; push_neg at h3; nlinarith
        exact ⟨div_pos_of_neg_of_neg h1 (by linarith), (div_lt_one_of_neg (by linarith)).2
          (by linarith)⟩
      · have h2 : g p < 0 := by by_contra h3; push_neg at h3; nlinarith
        exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    set q := c + t • (p - c)
    have hca : u a ⬝ᵥ c = h a := dot_center_self hua _
    have hqa : u a ⬝ᵥ q = h a := by
      simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, hp, hca,
        sub_self, smul_zero, add_zero]
    have hqb : u b ⬝ᵥ q = h b := by
      have : g q = g c + t * (g p - g c) := by
        simp only [g, q, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
      have h0 : g c + t * (g p - g c) = 0 := by simp only [t]; field_simp; ring
      simp only [g] at this; linarith
    have hm := foot_le hw hqa hqb
    have e1 := norm_plane hua hqa
    have e2 := norm_plane hua hp
    have e3 : q - c = t • (p - c) := by simp only [q]; abel
    rw [e3, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e1
    have hpc : 0 < (p - c) ⬝ᵥ (p - c) := dot_self_pos (by
      intro e; rw [sub_eq_zero.1 e] at hneg; nlinarith [sq_nonneg (g c)])
    nlinarith [mul_pos (mul_pos ht.1 ht.1) hpc, mul_lt_mul_of_pos_right
      (show t * t < 1 by nlinarith) hpc]
  by_contra hcon
  push_neg at hcon
  have hcz : g (pt z) * g c < 0 := lt_of_le_of_ne hcon (mul_ne_zero hgz hGc)
  -- the other curve `l` of `z` and the other crossing `z'` of `a, l`
  obtain ⟨d, hdz, hda⟩ := exists_dart_of_mem hza
  set l := A.curve (A.σ d)
  have hzl : Arrangement.Crossing.curves A z = {a, l} := by
    rw [← hdz, A.curves_crossingOf, hda]
  have hal : a ≠ l := fun e => A.isArrangement.curve_σ d (by rw [hda]; exact e.symm)
  have hbl : b ≠ l := fun e => hzb (by rw [hzl, e]; simp)
  obtain ⟨z', hzz', hz'⟩ : ∃ z', z ≠ z' ∧ Arrangement.Crossing.curves A z' = {a, l} := by
    obtain ⟨x₁, x₂, h12, hx₁, hx₂⟩ := exists_pair A hal
    rcases eq_or_eq_of_pair h12 hx₁ hx₂ hzl with rfl | rfl
    · exact ⟨x₂, h12, hx₂⟩
    · exact ⟨x₁, h12.symm, hx₁⟩
  obtain ⟨hz'a, -⟩ := R.onCirc_pair' hz'
  have hgz' : g (pt z') ≠ 0 := by
    intro e
    have := R.curves_eq_of_on hab hz'a.2 (sub_eq_zero.1 e)
    rw [hz'] at this
    have : b ∈ ({a, l} : Finset (Fin n)) := by rw [this]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hab e'.symm; exact hbl e']
  have hzl' := (R.onCirc_pair' hzl).2
  have hz'l := (R.onCirc_pair' hz').2
  rcases lt_or_gt_of_ne (mul_ne_zero hgz' hGc) with hneg | hpos
  · -- both on the far side: the foot point of `a, l` is farther out
    obtain ⟨l0, -, e1, e2, -⟩ := R.pair_lam hal hzz' hzl hz'
    have hmid : foot (u a) (u l) (h a) (h l) = (1 / 2 : ℝ) • (pt z + pt z') := by
      rw [e1, e2]; ext k; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hg : g (foot (u a) (u l) (h a) (h l)) = (g (pt z) + g (pt z')) / 2 := by
      rw [hmid]; simp only [g, dotProduct_smul, dotProduct_add, smul_eq_mul]; ring
    have hfa : u a ⬝ᵥ foot (u a) (u l) (h a) (h l) = h a :=
      dot_foot_left _ _ _ _ (R.cross_ne_zero hal)
    have := far _ hfa (by rw [hg]; nlinarith)
    have := hmaxD a l hal
    linarith
  · -- opposite sides: a Krupp triple point on the chord of `a, b`
    have hne : g (pt z) - g (pt z') ≠ 0 := by
      intro e; have : g (pt z) = g (pt z') := sub_eq_zero.1 e
      rw [this] at hcz; nlinarith
    set t := g (pt z) / (g (pt z) - g (pt z'))
    have ht : 0 < t ∧ t < 1 := by
      have hzz : g (pt z) * g (pt z') < 0 := by
        have e : g (pt z) * g c * (g (pt z') * g c) = (g (pt z) * g (pt z')) * (g c * g c) := by
          ring
        have := mul_neg_of_neg_of_pos hcz hpos
        rw [e] at this
        exact neg_of_mul_neg_left this (mul_self_nonneg _)
      rcases lt_or_gt_of_ne hgz with h1 | h1
      · have h2 : 0 < g (pt z') := by by_contra h3; push_neg at h3; nlinarith
        exact ⟨div_pos_of_neg_of_neg h1 (by linarith), (div_lt_one_of_neg (by linarith)).2
          (by linarith)⟩
      · have h2 : g (pt z') < 0 := by by_contra h3; push_neg at h3; nlinarith
        exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    set q := pt z + t • (pt z' - pt z)
    have hqa : u a ⬝ᵥ q = h a := by
      simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, (R.onCirc hza).2, hz'a.2,
        sub_self, smul_zero, add_zero]
    have hql : u l ⬝ᵥ q = h l := by
      simp only [q, dotProduct_add, dotProduct_smul, dotProduct_sub, hzl'.2, hz'l.2,
        sub_self, smul_zero, add_zero]
    have hqb : u b ⬝ᵥ q = h b := by
      have : g q = g (pt z) + t * (g (pt z') - g (pt z)) := by
        simp only [g, q, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
      have h0 : g (pt z) + t * (g (pt z') - g (pt z)) = 0 := by simp only [t]; field_simp; ring
      simp only [g] at this; linarith
    have hqin : q ⬝ᵥ q < 1 := chord_inside (R.on_sphere z) (R.on_sphere z')
      (fun e => hzz' (R.inj e)) ht.1 ht.2
    have hk : IsKrupp A a b l := (R.fact1 hab hal hbl).2 ⟨hG1 a b l hab hal hbl, q, hqa, hqb, hql,
      hqin⟩
    have h1 := hmaxT a b l hab hal hbl hk q hqa hqb hql
    have h2 := foot_le hw hqa hqb
    linarith

/-- Moving from `P` towards an outward crossing `X` of `i, v`, the plane `E_l` gives a Krupp
triple point farther out. -/
theorem contra_out (hG1 : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → det3 (u a) (u b) (u c) ≠ 0)
    {i v l : Fin n} (hiv : i ≠ v) (hil : i ≠ l) (hvl : v ≠ l) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPv : u v ⬝ᵥ P = h v) (hPin : P ⬝ᵥ P < 1)
    (hmaxT : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → IsKrupp A a b c → ∀ Q : V,
      u a ⬝ᵥ Q = h a → u b ⬝ᵥ Q = h b → u c ⬝ᵥ Q = h c → Q ⬝ᵥ Q ≤ P ⬝ᵥ P)
    {X : A.Crossing} (hX : Arrangement.Crossing.curves A X = {i, v})
    (hout : 0 < (pt X - P) ⬝ᵥ (P - foot (u i) (u v) (h i) (h v)))
    (hsep : (u l ⬝ᵥ P - h l) * (u l ⬝ᵥ pt X - h l) < 0) : False := by
  obtain ⟨hXi, hXv⟩ := R.onCirc_pair' hX
  set gP := u l ⬝ᵥ P - h l
  set gX := u l ⬝ᵥ pt X - h l
  have hne : gP - gX ≠ 0 := by
    intro e; have : gP = gX := sub_eq_zero.1 e; rw [this] at hsep; nlinarith [sq_nonneg gX]
  set s := gP / (gP - gX) with hs
  have hs01 : 0 < s ∧ s < 1 := by
    rcases lt_or_gt_of_ne (show gP ≠ 0 by intro e; rw [e, zero_mul] at hsep; exact lt_irrefl _ hsep)
      with h1 | h1
    · have h2 : 0 < gX := by by_contra h3; push_neg at h3; nlinarith
      exact ⟨div_pos_of_neg_of_neg h1 (by linarith), (div_lt_one_of_neg (by linarith)).2
        (by linarith)⟩
    · have h2 : gX < 0 := by by_contra h3; push_neg at h3; nlinarith
      exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  set Rp := P + s • (pt X - P)
  have hRi : u i ⬝ᵥ Rp = h i := by
    simp only [Rp, dotProduct_add, dotProduct_smul, dotProduct_sub, hPi, hXi.2, sub_self,
      smul_zero, add_zero]
  have hRv : u v ⬝ᵥ Rp = h v := by
    simp only [Rp, dotProduct_add, dotProduct_smul, dotProduct_sub, hPv, hXv.2, sub_self,
      smul_zero, add_zero]
  have hRl : u l ⬝ᵥ Rp = h l := by
    have : u l ⬝ᵥ Rp - h l = gP + s * (gX - gP) := by
      simp only [Rp, gP, gX, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; ring
    have h0 : gP + s * (gX - gP) = 0 := by rw [hs]; field_simp; ring
    linarith
  have hRin : Rp ⬝ᵥ Rp < 1 := seg_inside hPin hXi.1 hs01.1.le hs01.2
  -- `Rp` is farther out than `P`
  have hw := R.cross_ne_zero hiv
  have hperp := eq_smul_cross_of_perp hw (v := pt X - P)
    (by rw [dotProduct_sub, hXi.2, hPi, sub_self]) (by rw [dotProduct_sub, hXv.2, hPv, sub_self])
  have hXm : (pt X - P) ⬝ᵥ foot (u i) (u v) (h i) (h v) = 0 := by
    rw [hperp, smul_dotProduct, cross_dot_foot, smul_zero]
  have hRP : P ⬝ᵥ P < Rp ⬝ᵥ Rp := by
    have e : Rp ⬝ᵥ Rp = P ⬝ᵥ P + 2 * s * ((pt X - P) ⬝ᵥ P) + s ^ 2 * ((pt X - P) ⬝ᵥ (pt X - P)) := by
      simp only [Rp, dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have e2 : (pt X - P) ⬝ᵥ P = (pt X - P) ⬝ᵥ (P - foot (u i) (u v) (h i) (h v)) := by
      rw [dotProduct_sub, hXm, sub_zero]
    rw [e, e2]
    nlinarith [dot_self_nonneg (pt X - P), mul_pos hs01.1 hout, sq_nonneg s]
  have hk : IsKrupp A i v l := (R.fact1 hiv hil hvl).2 ⟨hG1 i v l hiv hil hvl, Rp, hRi, hRv, hRl,
    hRin⟩
  have := hmaxT i v l hiv hil hvl hk Rp hRi hRv hRl
  linarith

/-- **Case T.** On the circle `i`, every crossing other than the outward crossings `X₁` (of `i, j`)
and `X₂` (of `i, k`) lies on the side of the chord `X₁ X₂` of the Krupp triple point `P`. -/
theorem out_side (hG1 : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → det3 (u a) (u b) (u c) ≠ 0)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPj : u j ⬝ᵥ P = h j) (hPk : u k ⬝ᵥ P = h k) (hPin : P ⬝ᵥ P < 1)
    (hmaxT : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → IsKrupp A a b c → ∀ Q : V,
      u a ⬝ᵥ Q = h a → u b ⬝ᵥ Q = h b → u c ⬝ᵥ Q = h c → Q ⬝ᵥ Q ≤ P ⬝ᵥ P)
    (hmaxD : ∀ a b : Fin n, a ≠ b →
      foot (u a) (u b) (h a) (h b) ⬝ᵥ foot (u a) (u b) (h a) (h b) ≤ P ⬝ᵥ P)
    (hG2 : ∀ l : Fin n, l ≠ i → l ≠ j → l ≠ k → u l ⬝ᵥ P ≠ h l)
    {X₁ X₁' X₂ X₂' : A.Crossing} {τ₁ τ₂ : ℝ} (h11 : X₁ ≠ X₁')
    (hX₁ : Arrangement.Crossing.curves A X₁ = {i, j})
    (hX₁' : Arrangement.Crossing.curves A X₁' = {i, j}) (hτ₁ : 0 < τ₁)
    (hP₁ : P = pt X₁ + τ₁ • (pt X₁' - pt X₁))
    (ho₁ : 0 < (pt X₁ - P) ⬝ᵥ (P - foot (u i) (u j) (h i) (h j))) (h22 : X₂ ≠ X₂')
    (hX₂ : Arrangement.Crossing.curves A X₂ = {i, k})
    (hX₂' : Arrangement.Crossing.curves A X₂' = {i, k}) (hτ₂ : 0 < τ₂)
    (hP₂ : P = pt X₂ + τ₂ • (pt X₂' - pt X₂))
    (ho₂ : 0 < (pt X₂ - P) ⬝ᵥ (P - foot (u i) (u k) (h i) (h k)))
    (z : A.Crossing) (hzi : i ∈ Arrangement.Crossing.curves A z) (hz1 : z ≠ X₁) (hz2 : z ≠ X₂) :
    0 < orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) P := by
  have hu := R.u_ne_zero i
  have c1 := (R.onCirc_pair' hX₁).1
  have c1' := (R.onCirc_pair' hX₁').1
  have c2 := (R.onCirc_pair' hX₂).1
  have c2' := (R.onCirc_pair' hX₂').1
  have cz := R.onCirc hzi
  have hne : ∀ {x y : A.Crossing}, x ≠ y → pt x ≠ pt y := fun hxy e => hxy (R.inj e)
  have hdiff : ∀ {x y : A.Crossing}, Arrangement.Crossing.curves A x = {i, j} →
      Arrangement.Crossing.curves A y = {i, k} → x ≠ y := fun hx hy e => by
    rw [e, hy] at hx
    have : k ∈ ({i, j} : Finset (Fin n)) := by rw [← hx]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e'
    · exact hik e'.symm
    · exact hjk e'.symm
  have d12 := hdiff hX₁ hX₂
  have d1'2 := hdiff hX₁' hX₂
  have d12' := hdiff hX₁ hX₂'
  have oP1 : orient (u i) (pt X₁) (pt X₂) P = τ₁ * orient (u i) (pt X₁) (pt X₂) (pt X₁') := by
    rw [hP₁]; exact orient_third _ _ _ _ _
  have oP2 : orient (u i) (pt X₁) (pt X₂) P = τ₂ * orient (u i) (pt X₁) (pt X₂) (pt X₂') := by
    conv_lhs => rw [hP₂]
    exact orient_third' _ _ _ _ _
  have n1 : orient (u i) (pt X₁) (pt X₂) (pt X₁') ≠ 0 :=
    c1.orient_ne_zero hu c2 c1' (hne d12) (hne h11) (hne d1'2).symm
  have nz : orient (u i) (pt X₁) (pt X₂) (pt z) ≠ 0 :=
    c1.orient_ne_zero hu c2 cz (hne d12) (hne hz1.symm) (hne hz2.symm)
  have nP : orient (u i) (pt X₁) (pt X₂) P ≠ 0 := by rw [oP1]; exact mul_ne_zero hτ₁.ne' n1
  by_contra hc
  push_neg at hc
  have hneg : orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) P < 0 :=
    lt_of_le_of_ne hc (mul_ne_zero nz nP)
  have hz1' : z ≠ X₁' := by
    rintro rfl; rw [oP1] at hneg
    nlinarith [mul_pos (mul_self_pos.2 nz) hτ₁]
  have hz2' : z ≠ X₂' := by
    rintro rfl; rw [oP2] at hneg
    nlinarith [mul_pos (mul_self_pos.2 nz) hτ₂]
  obtain ⟨d, hdz, hdi⟩ := exists_dart_of_mem hzi
  set l := A.curve (A.σ d)
  have hcz : Arrangement.Crossing.curves A z = {i, l} := by
    rw [← hdz, A.curves_crossingOf, hdi]
  have hli : l ≠ i := fun e => A.isArrangement.curve_σ d (by rw [hdi]; exact e)
  have hlj : l ≠ j := by
    intro e; rw [e] at hcz
    rcases eq_or_eq_of_pair h11 hX₁ hX₁' hcz with e' | e'
    · exact hz1 e'
    · exact hz1' e'
  have hlk : l ≠ k := by
    intro e; rw [e] at hcz
    rcases eq_or_eq_of_pair h22 hX₂ hX₂' hcz with e' | e'
    · exact hz2 e'
    · exact hz2' e'
  set g : V → ℝ := fun p => u l ⬝ᵥ p - h l
  have hgz : g (pt z) = 0 := by
    have := R.on_plane (A.σ d); rw [A.crossingOf_σ, hdz] at this; simp only [g]; rw [this, sub_self]
  have hgP : g P ≠ 0 := fun e => hG2 l hli hlj hlk (sub_eq_zero.1 e)
  have hgX : ∀ {X : A.Crossing} {v : Fin n}, Arrangement.Crossing.curves A X = {i, v} → l ≠ v →
      g (pt X) ≠ 0 := by
    intro X v hX hlv e
    have := R.curves_eq_of_on hli.symm (R.onCirc_pair' hX).1.2 (sub_eq_zero.1 e)
    rw [hX] at this
    have : l ∈ ({i, v} : Finset (Fin n)) := by rw [this]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hli e'; exact hlv e']
  have hg1 := hgX hX₁ hlj
  have hg2 := hgX hX₂ hlk
  by_cases s1 : g P * g (pt X₁) < 0
  · exact R.contra_out hG1 hij (Ne.symm hli) (Ne.symm hlj) hPi hPj hPin hmaxT hX₁ ho₁ s1
  by_cases s2 : g P * g (pt X₂) < 0
  · exact R.contra_out hG1 hik (Ne.symm hli) (Ne.symm hlk) hPi hPk hPin hmaxT hX₂ ho₂ s2
  push_neg at s1 s2
  have p1 : 0 < g P * g (pt X₁) := lt_of_le_of_ne s1 (mul_ne_zero hgP hg1).symm
  have p2 : 0 < g P * g (pt X₂) := lt_of_le_of_ne s2 (mul_ne_zero hgP hg2).symm
  have p12 : 0 < g (pt X₁) * g (pt X₂) := by
    have e : g P * g (pt X₁) * (g P * g (pt X₂)) = (g (pt X₁) * g (pt X₂)) * (g P * g P) := by ring
    have := mul_pos p1 p2; rw [e] at this
    exact pos_of_mul_pos_left this (mul_self_nonneg _)
  -- the other crossing `z'` of `i, l`
  have hil : i ≠ l := Ne.symm hli
  obtain ⟨z', hzz', hz'⟩ : ∃ z', z ≠ z' ∧ Arrangement.Crossing.curves A z' = {i, l} := by
    obtain ⟨x₁, x₂, h12, hx₁, hx₂⟩ := exists_pair A hil
    rcases eq_or_eq_of_pair h12 hx₁ hx₂ hcz with rfl | rfl
    · exact ⟨x₂, h12, hx₂⟩
    · exact ⟨x₁, h12.symm, hx₁⟩
  obtain ⟨cz', hz'l⟩ := R.onCirc_pair' hz'
  have hz'1 : z' ≠ X₁ := fun e => hlj (by
    rw [e, hX₁] at hz'
    have : l ∈ ({i, j} : Finset (Fin n)) := by rw [hz']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact absurd e' hli; exact e'])
  have hz'2 : z' ≠ X₂ := fun e => hlk (by
    rw [e, hX₂] at hz'
    have : l ∈ ({i, k} : Finset (Fin n)) := by rw [hz']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact absurd e' hli; exact e'])
  have nz' : orient (u i) (pt X₁) (pt X₂) (pt z') ≠ 0 :=
    c1.orient_ne_zero hu c2 cz' (hne d12) (hne hz'1.symm) (hne hz'2.symm)
  have hgz' : g (pt z') = 0 := by simp only [g]; rw [hz'l.2, sub_self]
  rcases lt_or_gt_of_ne (mul_ne_zero nz' nP) with hneg' | hpos'
  · -- both beyond the chord: the foot point of `i, l` is farther out than `P`
    have hfX : ∀ {X : A.Crossing} {v : Fin n}, i ≠ v → Arrangement.Crossing.curves A X = {i, v} →
        0 < (pt X - P) ⬝ᵥ (P - foot (u i) (u v) (h i) (h v)) → u v ⬝ᵥ P = h v →
        0 < (pt X - P) ⬝ᵥ (P - center (u i) (h i)) := by
      intro X v hiv hX ho hPv
      obtain ⟨hXi, hXv⟩ := R.onCirc_pair' hX
      have hperp := eq_smul_cross_of_perp (R.cross_ne_zero hiv) (v := pt X - P)
        (by rw [dotProduct_sub, hXi.2, hPi, sub_self]) (by rw [dotProduct_sub, hXv.2, hPv, sub_self])
      have e1 : (pt X - P) ⬝ᵥ foot (u i) (u v) (h i) (h v) = 0 := by
        rw [hperp, smul_dotProduct, cross_dot_foot, smul_zero]
      have e2 : (pt X - P) ⬝ᵥ center (u i) (h i) = 0 := by
        rw [dotProduct_comm]; exact center_perp (by rw [dotProduct_sub, hXi.2, hPi, sub_self])
      have : (pt X - P) ⬝ᵥ (P - center (u i) (h i)) =
          (pt X - P) ⬝ᵥ (P - foot (u i) (u v) (h i) (h v)) := by
        rw [dotProduct_sub, dotProduct_sub, e1, e2]
      rw [this]; exact ho
    have f1 := hfX hij hX₁ ho₁ hPj
    have f2 := hfX hik hX₂ ho₂ hPk
    have fz := far_pos hu c1 c2 cz (hne d12) hPi hPin f1 f2 hneg
    have fz' := far_pos hu c1 c2 cz' (hne d12) hPi hPin f1 f2 hneg'
    obtain ⟨l0, -, e1, e2, -⟩ := R.pair_lam hil hzz' hcz hz'
    have hmid : foot (u i) (u l) (h i) (h l) = (1 / 2 : ℝ) • (pt z + pt z') := by
      rw [e1, e2]; ext k; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hfm : 0 < (foot (u i) (u l) (h i) (h l) - P) ⬝ᵥ (P - center (u i) (h i)) := by
      rw [hmid]
      have e : ((1 / 2 : ℝ) • (pt z + pt z') - P) ⬝ᵥ (P - center (u i) (h i)) =
          ((pt z - P) ⬝ᵥ (P - center (u i) (h i)) + (pt z' - P) ⬝ᵥ (P - center (u i) (h i))) / 2 := by
        simp only [dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]; linarith
    have := farther hPi (dot_foot_left _ _ _ _ (R.cross_ne_zero hil)) hfm
    have := hmaxD i l hil
    linarith
  · -- `z'` on the side of `P`: the chord `z z'` crosses the chord `X₁ X₂`
    have hsep' : orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) (pt z') < 0 := by
      have e : orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) P *
          (orient (u i) (pt X₁) (pt X₂) (pt z') * orient (u i) (pt X₁) (pt X₂) P) =
          (orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) (pt z')) *
          (orient (u i) (pt X₁) (pt X₂) P * orient (u i) (pt X₁) (pt X₂) P) := by ring
      have := mul_neg_of_neg_of_pos hneg hpos'
      rw [e] at this
      exact neg_of_mul_neg_left this (mul_self_nonneg _)
    exact chord_cross_sign hu c1 c2 cz cz' (hne hzz') (hne d12) hsep' hgz hgz' p12

end IsCircleRep

end Pca.Circ
