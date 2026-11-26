/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 19 (`doc/pca/circ.md`, decision C-D5)

Source: arXiv:1712.02149 (v6), Theorem 19: "Let `𝒜` be an intersecting arrangement of
pseudocircles which is not an arrangement of great-pseudocircles. If every triple of pseudocircles
which forms a triangle is Krupp, then `𝒜` is not circularizable."

Proof (C-D5, a static form of the paper's sweep "move the planes towards the origin; the first
event is a triangle flip of a NonKrupp triangle"). Take a generic representation (C-D4). Among the
NonKrupp triples choose one whose triple point `P` (outside the sphere, Fact 1) has minimal norm;
this is the triple of the first event of the paper's inward scaling. Let `A, B, C` be the
intersection points of the three lines `E_i ∩ E_j` closest to `P` (the corners of the triangle
facing `P`). On the circle `i`, every crossing `z ≠ A, B` lies on the far side of the chord `A B`
(`near_side`): otherwise `z` lies inside the planar triangle `P A B`, the plane `E_l` of the other
curve through `z` separates `P` from `A` or `B`, and its intersection with that segment is the
triple point of a NonKrupp triple closer to the origin. So `A B`, `B C`, `C A` are segments of the
arrangement, and an orientation computation shows that they bound a cell, a NonKrupp triangle.
-/
import Pca.Circ.Cone

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A dart whose face orbit closes after three distinct steps bounds a triangle. -/
theorem isTriangle_of_φ3 {d : D} (h3 : A.φ (A.φ (A.φ d)) = d) (h1 : A.φ d ≠ d)
    (h2 : A.φ (A.φ d) ≠ d) : A.IsTriangle (A.cellOf d) := by
  unfold Arrangement.IsTriangle Arrangement.IsKCell
  rw [A.size_cellOf]
  unfold period
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by simpa using h3⟩, fun m hm ⟨hm0, hmd⟩ => ?_⟩
  interval_cases m
  · exact h1 (by simpa using hmd)
  · exact h2 (by simpa using hmd)

theorem sign_choice {o : ℝ} (ho : o ≠ 0) :
    (if 0 < o then (-1 : ℝ) else 1) * o < 0 ∧
      ((if 0 < o then (-1 : ℝ) else 1) = 1 ∨ (if 0 < o then (-1 : ℝ) else 1) = -1) := by
  split_ifs with h
  · exact ⟨by linarith, Or.inr rfl⟩
  · exact ⟨by rcases lt_or_gt_of_ne ho with h' | h' <;> [linarith; exact absurd h' h], Or.inl rfl⟩

theorem sign_choice_neg {o : ℝ} (ho : o ≠ 0) :
    (if 0 < -o then (-1 : ℝ) else 1) = -(if 0 < o then (-1 : ℝ) else 1) := by
  rcases lt_or_gt_of_ne ho with h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]
  · rw [if_neg (by linarith), if_pos h]; norm_num

/-- Sign bookkeeping at a corner of the triangle. -/
theorem corner_sign {s₁ s₂ o₁ o₂ β X q M : ℝ} (h₁ : s₁ * o₁ < 0) (h₂ : s₂ * o₂ < 0)
    (h₃ : 0 < β * X) (hM : 0 < M) (he : o₁ * o₂ * β = q * M) : 0 < s₁ * s₂ * X * q := by
  have h := mul_pos (mul_pos_of_neg_of_neg h₁ h₂) h₃
  have e : s₁ * o₁ * (s₂ * o₂) * (β * X) = (s₁ * s₂ * X * q) * M := by
    rw [mul_assoc (s₁ * s₂ * X) q M, ← he]; ring
  rw [e] at h
  exact pos_of_mul_pos_left h hM.le

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}
variable (R : IsCircleRep A u h pt sgn)
include R

/-- The triple point of a NonKrupp triple lies outside the sphere. -/
theorem one_lt_of_nonKrupp {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hk : ¬ IsKrupp A a b c) (hd : det3 (u a) (u b) (u c) ≠ 0) {Q : V} (ha : u a ⬝ᵥ Q = h a)
    (hb : u b ⬝ᵥ Q = h b) (hc : u c ⬝ᵥ Q = h c) : 1 < Q ⬝ᵥ Q := by
  rcases lt_trichotomy (Q ⬝ᵥ Q) 1 with h1 | h1 | h1
  · exact absurd ((R.fact1 hab hac hbc).2 ⟨hd, Q, ha, hb, hc, h1⟩) hk
  · obtain ⟨x, hx⟩ := R.surj a b Q hab h1 ha hb
    have e1 := R.curves_eq_of_on hab (hx ▸ ha) (hx ▸ hb)
    have e2 := R.curves_eq_of_on hac (hx ▸ ha) (hx ▸ hc)
    have : c ∈ ({a, b} : Finset (Fin n)) := by rw [← e1, e2]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e | e
    · exact absurd e.symm hac
    · exact absurd e.symm hbc
  · exact h1

/-- The crossing of a pair nearest to a point `P` outside the sphere on both planes. -/
theorem exists_near {i j : Fin n} (hij : i ≠ j) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPj : u j ⬝ᵥ P = h j) (hP : 1 < P ⬝ᵥ P) :
    ∃ (X X' : A.Crossing) (τ : ℝ), X ≠ X' ∧ Arrangement.Crossing.curves A X = {i, j} ∧
      Arrangement.Crossing.curves A X' = {i, j} ∧ τ < 0 ∧ P = pt X + τ • (pt X' - pt X) := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair A hij
  obtain ⟨hxi, hxj⟩ := R.onCirc_pair' hx
  obtain ⟨hyi, hyj⟩ := R.onCirc_pair' hy
  have hp : pt x ≠ pt y := fun e => hxy (R.inj e)
  obtain ⟨t, ht⟩ := exists_smul_of_perp (R.cross_ne_zero hij) (v := P - pt x)
    (v' := pt y - pt x) (by rw [dotProduct_sub, hPi, hxi.2, sub_self])
    (by rw [dotProduct_sub, hPj, hxj.2, sub_self]) (by rw [dotProduct_sub, hyi.2, hxi.2, sub_self])
    (by rw [dotProduct_sub, hyj.2, hxj.2, sub_self]) (sub_ne_zero.2 hp.symm)
  have hPt : P = pt x + t • (pt y - pt x) := by rw [← ht]; abel
  have hl := dot_line (pt x) (pt y) hxi.1 hyi.1 t
  rw [← hPt] at hl
  have hc := dot_lt_one_of_ne hxi.1 hyi.1 hp
  have ht' : t * (1 - t) < 0 := by nlinarith
  by_cases h0 : t < 0
  · exact ⟨x, y, t, hxy, hx, hy, h0, hPt⟩
  · refine ⟨y, x, 1 - t, hxy.symm, hy, hx, ?_, ?_⟩
    · push_neg at h0
      by_contra h2; push_neg at h2
      nlinarith
    · rw [hPt]; ext k; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

/-- The near parameter: `P - X = a (u_i ⨯₃ u_j)` with `a` of the sign of `⟨u_i ⨯₃ u_j, X⟩`. -/
theorem near_param {i j : Fin n} (hij : i ≠ j) {X X' : A.Crossing} (hXX' : X ≠ X')
    (hX : Arrangement.Crossing.curves A X = {i, j}) (hX' : Arrangement.Crossing.curves A X' = {i, j})
    {τ : ℝ} (hτ : τ < 0) {P : V} (hP : P = pt X + τ • (pt X' - pt X)) :
    ∃ a : ℝ, pt X = P - a • (u i ⨯₃ u j) ∧ 0 < a * ((u i ⨯₃ u j) ⬝ᵥ pt X) := by
  obtain ⟨hXi, hXj⟩ := R.onCirc_pair' hX
  obtain ⟨hX'i, hX'j⟩ := R.onCirc_pair' hX'
  have hw := R.cross_ne_zero hij
  obtain ⟨l, hl, hl2⟩ := exists_lam hw hXi.1 hXi.2 hXj.2
  obtain ⟨l', hl', hl2'⟩ := exists_lam hw hX'i.1 hX'i.2 hX'j.2
  have hpos := dot_self_pos hw
  have hne : l ≠ l' := fun e => hXX' (R.inj (by rw [hl, hl', e]))
  have hsq : l ^ 2 = l' ^ 2 := by
    have : (l ^ 2 - l' ^ 2) * ((u i ⨯₃ u j) ⬝ᵥ (u i ⨯₃ u j)) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_right hpos.ne']
  have hl'eq : l' = -l := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq.symm with e | e
    · exact absurd e.symm hne
    · exact e
  have hl0 : l ≠ 0 := fun e => hne (by rw [hl'eq, e, neg_zero])
  refine ⟨-2 * τ * l, ?_, ?_⟩
  · rw [hP, hl', hl, hl'eq]; ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  · have e : (u i ⨯₃ u j) ⬝ᵥ pt X = l * ((u i ⨯₃ u j) ⬝ᵥ (u i ⨯₃ u j)) := by
      rw [hl, dotProduct_add, cross_dot_foot, zero_add, dotProduct_smul, smul_eq_mul]
    rw [e]
    have : 0 < l ^ 2 := by positivity
    nlinarith [mul_pos (mul_pos this hpos) (show 0 < -τ by linarith)]

/-- Minimality hypothesis: no NonKrupp triple point is closer to the origin than `P`. -/
def IsMinPt (u : Fin n → V) (h : Fin n → ℝ) (A : Arrangement n D) (P : V) : Prop :=
  ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ¬ IsKrupp A a b c → ∀ Q : V, u a ⬝ᵥ Q = h a →
    u b ⬝ᵥ Q = h b → u c ⬝ᵥ Q = h c → P ⬝ᵥ P ≤ Q ⬝ᵥ Q

/-- A plane `E_l` separating `P` from a near crossing `X` of `i, v` gives a closer NonKrupp
triple point. -/
theorem contra_of_sep (hG1 : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → det3 (u a) (u b) (u c) ≠ 0)
    {i v l : Fin n} (hiv : i ≠ v) (hil : i ≠ l) (hvl : v ≠ l) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPv : u v ⬝ᵥ P = h v) (hmin : IsMinPt u h A P) {X X' : A.Crossing} (hXX' : X ≠ X')
    (hX : Arrangement.Crossing.curves A X = {i, v})
    (hX' : Arrangement.Crossing.curves A X' = {i, v}) {τ : ℝ} (hτ : τ < 0)
    (hP : P = pt X + τ • (pt X' - pt X))
    (hsep : (u l ⬝ᵥ P - h l) * (u l ⬝ᵥ pt X - h l) < 0) : False := by
  obtain ⟨hXi, hXv⟩ := R.onCirc_pair' hX
  obtain ⟨hX'i, -⟩ := R.onCirc_pair' hX'
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
  set t := (1 - s) * τ
  have hRt : Rp = pt X + t • (pt X' - pt X) := by
    simp only [Rp, t]; rw [hP]; ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hc := dot_lt_one_of_ne hXi.1 hX'i.1 (fun e => hXX' (R.inj e))
  have hRR := dot_line (pt X) (pt X') hXi.1 hX'i.1 t
  have hPP := dot_line (pt X) (pt X') hXi.1 hX'i.1 τ
  rw [← hRt] at hRR
  rw [← hP] at hPP
  have ht0 : t < 0 := by simp only [t]; nlinarith
  have htτ : τ < t := by simp only [t]; nlinarith
  have hc' : 0 < 1 - pt X ⬝ᵥ pt X' := by linarith
  have hR1 : 1 < Rp ⬝ᵥ Rp := by
    rw [hRR]; nlinarith [mul_pos (mul_pos (show 0 < -t by linarith) (show 0 < 1 - t by linarith))
      hc']
  have hRP : Rp ⬝ᵥ Rp < P ⬝ᵥ P := by
    rw [hRR, hPP]
    nlinarith [mul_pos (mul_pos (sub_pos.2 htτ) (show 0 < 1 - t - τ by linarith)) hc']
  have hnk : ¬ IsKrupp A i v l := by
    intro hk
    obtain ⟨hd, Q, hQi, hQv, hQl, hQ⟩ := (R.fact1 hiv hil hvl).1 hk
    have : Q = Rp := eq_of_three_planes hd (by rw [hQi, hRi]) (by rw [hQv, hRv]) (by rw [hQl, hRl])
    rw [this] at hQ
    linarith
  have := hmin i v l hiv hil hvl hnk Rp hRi hRv hRl
  linarith

/-- **No crossing on the near side.** On the circle `i`, every crossing other than the near
crossings `X₁` (of `i, j`) and `X₂` (of `i, k`) lies on the far side of the chord `X₁ X₂`. -/
theorem near_side (hG1 : ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → det3 (u a) (u b) (u c) ≠ 0)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPj : u j ⬝ᵥ P = h j) (hPk : u k ⬝ᵥ P = h k) (hmin : IsMinPt u h A P)
    (hG2 : ∀ l : Fin n, l ≠ i → l ≠ j → l ≠ k → u l ⬝ᵥ P ≠ h l)
    {X₁ X₁' X₂ X₂' : A.Crossing} {τ₁ τ₂ : ℝ} (h11 : X₁ ≠ X₁')
    (hX₁ : Arrangement.Crossing.curves A X₁ = {i, j})
    (hX₁' : Arrangement.Crossing.curves A X₁' = {i, j}) (hτ₁ : τ₁ < 0)
    (hP₁ : P = pt X₁ + τ₁ • (pt X₁' - pt X₁)) (h22 : X₂ ≠ X₂')
    (hX₂ : Arrangement.Crossing.curves A X₂ = {i, k})
    (hX₂' : Arrangement.Crossing.curves A X₂' = {i, k}) (hτ₂ : τ₂ < 0)
    (hP₂ : P = pt X₂ + τ₂ • (pt X₂' - pt X₂))
    (z : A.Crossing) (hzi : i ∈ Arrangement.Crossing.curves A z) (hz1 : z ≠ X₁) (hz2 : z ≠ X₂) :
    orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) P < 0 := by
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
  have n2 : orient (u i) (pt X₁) (pt X₂) (pt X₂') ≠ 0 :=
    c1.orient_ne_zero hu c2 c2' (hne d12) (hne d12') (hne h22)
  have nz : orient (u i) (pt X₁) (pt X₂) (pt z) ≠ 0 :=
    c1.orient_ne_zero hu c2 cz (hne d12) (hne hz1.symm) (hne hz2.symm)
  by_contra hc
  push_neg at hc
  have hpos : 0 < orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) P :=
    lt_of_le_of_ne hc (mul_ne_zero nz (by rw [oP1]; exact mul_ne_zero hτ₁.ne n1)).symm
  -- `z` is not a far crossing
  have hz1' : z ≠ X₁' := by
    rintro rfl; rw [oP1] at hpos; nlinarith [sq_nonneg (orient (u i) (pt X₁) (pt X₂) (pt z)),
      mul_pos (sq_pos_of_ne_zero nz) (show 0 < -τ₁ by linarith)]
  have hz2' : z ≠ X₂' := by
    rintro rfl; rw [oP2] at hpos; nlinarith [sq_nonneg (orient (u i) (pt X₁) (pt X₂) (pt z)),
      mul_pos (sq_pos_of_ne_zero nz) (show 0 < -τ₂ by linarith)]
  -- the other curve `l` of `z`
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
  -- `z` is inside the planar triangle `P X₁ X₂`
  have sep1 : orient (u i) (pt X₁) (pt X₂) (pt z) * orient (u i) (pt X₁) (pt X₂) (pt X₁') < 0 := by
    rw [oP1] at hpos; nlinarith
  have ss1 := same_side_of_sep hu c1 c2 cz c1' (hne h11) (hne hz2) (hne hz1) (hne hz1')
    (hne d12).symm (hne d1'2).symm sep1
  have sep2 : orient (u i) (pt X₂) (pt X₁) (pt z) * orient (u i) (pt X₂) (pt X₁) (pt X₂') < 0 := by
    rw [orient_swap, orient_swap (u i) (pt X₁) (pt X₂) (pt X₂')]
    rw [oP2] at hpos; nlinarith
  have ss2 := same_side_of_sep hu c2 c1 cz c2' (hne h22) (hne hz1) (hne hz2) (hne hz2')
    (hne d12) (hne d12') sep2
  set D0 := orient (u i) P (pt X₁) (pt X₂)
  set wP := orient (u i) (pt z) (pt X₁) (pt X₂)
  set wA := orient (u i) P (pt z) (pt X₂)
  set wB := orient (u i) P (pt X₁) (pt z)
  have eD : D0 = orient (u i) (pt X₁) (pt X₂) P := (orient_cyc _ _ _ _).symm
  have hwP : 0 < wP * D0 := by
    rw [eD, show wP = orient (u i) (pt X₁) (pt X₂) (pt z) from (orient_cyc _ _ _ _).symm]; exact hpos
  have eB1 : wB = -τ₁ * orient (u i) (pt X₁) (pt X₁') (pt z) := by
    simp only [wB]; rw [hP₁]; exact orient_apex _ _ _ _ _
  have eB2 : D0 = -τ₁ * orient (u i) (pt X₁) (pt X₁') (pt X₂) := by
    simp only [D0]; rw [hP₁]; exact orient_apex _ _ _ _ _
  have hwB : 0 < wB * D0 := by
    rw [eB1, eB2]; nlinarith [mul_pos (mul_pos (show 0 < -τ₁ by linarith)
      (show 0 < -τ₁ by linarith)) ss1]
  have eA1 : wA = τ₂ * orient (u i) (pt X₂) (pt X₂') (pt z) := by
    simp only [wA]; rw [orient_swap23 (u i) P (pt X₂) (pt z), hP₂, orient_apex]; ring
  have eA2 : D0 = τ₂ * orient (u i) (pt X₂) (pt X₂') (pt X₁) := by
    simp only [D0]; rw [orient_swap23 (u i) P (pt X₂) (pt X₁), hP₂, orient_apex]; ring
  have hwA : 0 < wA * D0 := by
    rw [eA1, eA2]; nlinarith [mul_pos (mul_pos_of_neg_of_neg hτ₂ hτ₂) ss2]
  -- the affine function of `E_l`
  set gP := u l ⬝ᵥ P - h l
  set g1 := u l ⬝ᵥ pt X₁ - h l
  set g2 := u l ⬝ᵥ pt X₂ - h l
  have hgz : u l ⬝ᵥ pt z - h l = 0 := by
    have := R.on_plane (A.σ d); rw [A.crossingOf_σ, hdz] at this; rw [this, sub_self]
  have hb : D0 * (u l ⬝ᵥ pt z - h l) - (wP * gP + wA * g1 + wB * g2) =
      det3 (pt X₁ - P) (pt X₂ - P) (pt z - P) * (u l ⬝ᵥ u i) :=
    bary (u i) (u l) P (pt X₁) (pt X₂) (pt z) (h l)
  rw [det3_eq_zero_of_perp hu (by rw [dotProduct_sub, c1.2, hPi, sub_self])
    (by rw [dotProduct_sub, c2.2, hPi, sub_self]) (by rw [dotProduct_sub, cz.2, hPi, sub_self]),
    zero_mul, hgz, mul_zero, zero_sub, neg_eq_zero] at hb
  have hgP : gP ≠ 0 := fun e => hG2 l hli hlj hlk (sub_eq_zero.1 e)
  have hg1 : g1 ≠ 0 := by
    intro e
    have := R.curves_eq_of_on hli.symm c1.2 (sub_eq_zero.1 e)
    rw [hX₁] at this
    have : l ∈ ({i, j} : Finset (Fin n)) := by rw [this]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hli e'; exact hlj e']
  have hg2 : g2 ≠ 0 := by
    intro e
    have := R.curves_eq_of_on hli.symm c2.2 (sub_eq_zero.1 e)
    rw [hX₂] at this
    have : l ∈ ({i, k} : Finset (Fin n)) := by rw [this]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e' | e' <;> [exact hli e'; exact hlk e']
  by_cases s1 : gP * g1 < 0
  · exact R.contra_of_sep hG1 hij (Ne.symm hli) (Ne.symm hlj) hPi hPj hmin h11 hX₁ hX₁' hτ₁ hP₁ s1
  by_cases s2 : gP * g2 < 0
  · exact R.contra_of_sep hG1 hik (Ne.symm hli) (Ne.symm hlk) hPi hPk hmin h22 hX₂ hX₂' hτ₂ hP₂ s2
  push_neg at s1 s2
  have p1 : 0 < gP * g1 := lt_of_le_of_ne s1 (mul_ne_zero hgP hg1).symm
  have p2 : 0 < gP * g2 := lt_of_le_of_ne s2 (mul_ne_zero hgP hg2).symm
  have key : D0 * gP * (wP * gP + wA * g1 + wB * g2) =
      (wP * D0) * (gP * gP) + (wA * D0) * (gP * g1) + (wB * D0) * (gP * g2) := by ring
  rw [hb, mul_zero] at key
  have := mul_pos hwP (mul_self_pos.2 hgP)
  nlinarith [mul_pos hwA p1, mul_pos hwB p2]

end IsCircleRep

end Pca.Circ
