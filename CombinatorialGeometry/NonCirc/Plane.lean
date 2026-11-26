/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Sign

/-! # Plane circle realizations and their lift to `R^{3,1}`

The statement of every non-circularizability theorem in `NonCirc` is about circles in the plane
(`IsCircleRealization`). A circle realization on `S²` gives one in the plane by stereographic
projection from a point that lies on no circle; this step, and reading the side table off the
fingerprint, are not formalized (see `doc/pca/noncirc.md`).

Internally a circle with centre `c`, radius `r` and orientation `ε` becomes the spacelike vector
`ε (2 c.1, 2 c.2, q - 1, q + 1)`, `q = |c|² - r²`, and a plane point `x` the future null vector
`(2 x.1, 2 x.2, |x|² - 1, |x|² + 1)` (inverse stereographic projection, scaled), as in
`noncirc/realization.py`. Then `<v, p> = 2 ε (r² - |x - c|²)`.
-/

namespace NonCirc

/-- Squared Euclidean distance in the plane. -/
def dist2 (x y : ℝ × ℝ) : ℝ := (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- A circle realization in the plane of an intersecting arrangement of `n` circles
(labelled `1..n`) with the side table `side` of its fingerprint:

* circle `i` has centre `c i`, radius `r i > 0` and orientation `ε i = ±1`
  (`ε i = 1`: counterclockwise, so the left side of circle `i` is its interior);
* every two circles cross (two transversal intersection points);
* `P j k s` (`j < k`, `s = ±1`) is a point on circles `j` and `k` (in the fingerprint,
  `s = 1` is the crossing `p⁺_jk` where `k` crosses `j` from right to left);
* `side j k s m = 1` means that `P j k s` is to the left of circle `m`, `-1` to the right,
  `0` is "no condition". Left of circle `m` = inside if `ε m = 1`, outside if `ε m = -1`. -/
structure IsCircleRealization (n : ℕ) (side : ℕ → ℕ → ℤ → ℕ → ℤ)
    (c : ℕ → ℝ × ℝ) (r : ℕ → ℝ) (ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ) : Prop where
  radius_pos : ∀ i, 1 ≤ i → i ≤ n → 0 < r i
  orientation : ∀ i, 1 ≤ i → i ≤ n → ε i = 1 ∨ ε i = -1
  cross : ∀ i j, 1 ≤ i → i < j → j ≤ n →
    (r i - r j) ^ 2 < dist2 (c i) (c j) ∧ dist2 (c i) (c j) < (r i + r j) ^ 2
  on_circles : ∀ j k s, 1 ≤ j → j < k → k ≤ n → (s = 1 ∨ s = -1) →
    dist2 (P j k s) (c j) = r j ^ 2 ∧ dist2 (P j k s) (c k) = r k ^ 2
  sides : ∀ j k s m, side j k s m ≠ 0 →
    0 < (side j k s m : ℝ) * (ε m * (r m ^ 2 - dist2 (P j k s) (c m)))

/-- The Lorentz vector of an oriented plane circle. -/
def circVec (c : ℝ × ℝ) (r ε : ℝ) : Vec :=
  ![ε * (2 * c.1), ε * (2 * c.2), ε * (c.1 ^ 2 + c.2 ^ 2 - r ^ 2 - 1),
    ε * (c.1 ^ 2 + c.2 ^ 2 - r ^ 2 + 1)]

/-- The lift of a plane point to a future null vector. -/
def liftPt (x : ℝ × ℝ) : Vec :=
  ![2 * x.1, 2 * x.2, x.1 ^ 2 + x.2 ^ 2 - 1, x.1 ^ 2 + x.2 ^ 2 + 1]

lemma ip_circVec_liftPt (c : ℝ × ℝ) (r ε : ℝ) (x : ℝ × ℝ) :
    ip (circVec c r ε) (liftPt x) = 2 * (ε * (r ^ 2 - dist2 x c)) := by
  simp [ip, circVec, liftPt, dist2]; ring

lemma ip_liftPt_liftPt (x y : ℝ × ℝ) : ip (liftPt x) (liftPt y) = -2 * dist2 x y := by
  simp [ip, liftPt, dist2]; ring

lemma dist2_pos {x y : ℝ × ℝ} (h : x ≠ y) : 0 < dist2 x y := by
  unfold dist2
  by_contra hc
  apply h
  have h1 := sq_nonneg (x.1 - y.1)
  have h2 := sq_nonneg (x.2 - y.2)
  have e1 : x.1 - y.1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have e2 : x.2 - y.2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  exact Prod.ext (by linarith) (by linarith)

lemma isPoint_liftPt (x : ℝ × ℝ) : IsPoint (liftPt x) := by
  refine ⟨?_, ?_⟩
  · simp [ip, liftPt]; ring
  · simp [liftPt]; positivity

lemma D2_circVec (c c' : ℝ × ℝ) (r r' ε ε' : ℝ) :
    D2 (circVec c r ε) (circVec c' r' ε') =
      4 * (ε * ε') ^ 2 * ((dist2 c c' - (r - r') ^ 2) * ((r + r') ^ 2 - dist2 c c')) := by
  simp [D2, ip, circVec, dist2]; ring

/-! ## At most two sign changes along a circle (family 1) -/

/-- Orientation determinant of three plane points (`> 0` iff counterclockwise). -/
def det3 (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

lemma det3_rot (p q r : ℝ × ℝ) : det3 p q r = det3 q r p := by unfold det3; ring

lemma ne_of_det3_ne_zero {a b c : ℝ × ℝ} (h : det3 a b c ≠ 0) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h <;> unfold det3 <;> ring


/-- For four points on one circle, the values of `x ↦ <lift x, u>` satisfy the
Cramer relation of four points in the plane (the function is affine on the circle). -/
lemma f1_identity (u : Vec) (c : ℝ × ℝ) (r : ℝ) {x1 x2 x3 x4 : ℝ × ℝ}
    (h1 : dist2 x1 c = r ^ 2) (h2 : dist2 x2 c = r ^ 2) (h3 : dist2 x3 c = r ^ 2)
    (h4 : dist2 x4 c = r ^ 2) :
    det3 x2 x3 x4 * ip (liftPt x1) u - det3 x1 x3 x4 * ip (liftPt x2) u
      + det3 x1 x2 x4 * ip (liftPt x3) u - det3 x1 x2 x3 * ip (liftPt x4) u = 0 := by
  simp only [dist2] at h1 h2 h3 h4
  simp [det3, ip, liftPt]
  linear_combination (((x3.1 - x2.1) * (x4.2 - x2.2) - (x3.2 - x2.2) * (x4.1 - x2.1)) * (u 2 - u 3)) * h1
    - (((x3.1 - x1.1) * (x4.2 - x1.2) - (x3.2 - x1.2) * (x4.1 - x1.1)) * (u 2 - u 3)) * h2
    + (((x2.1 - x1.1) * (x4.2 - x1.2) - (x2.2 - x1.2) * (x4.1 - x1.1)) * (u 2 - u 3)) * h3
    - (((x2.1 - x1.1) * (x3.2 - x1.2) - (x2.2 - x1.2) * (x3.1 - x1.1)) * (u 2 - u 3)) * h4

/-- Family 1: if `x1, x2, x3, x4` lie on a circle in this cyclic order (all four triples have
the orientation `e ≠ 0`), the signs of `<lift x_t, u>` satisfy `NAE [s1, -s2, s3, -s4]`;
for nonzero values this excludes exactly the alternating patterns `+-+-` and `-+-+`. -/
lemma f1_nae (u : Vec) (c : ℝ × ℝ) (r e : ℝ) {x1 x2 x3 x4 : ℝ × ℝ}
    (h1 : dist2 x1 c = r ^ 2) (h2 : dist2 x2 c = r ^ 2) (h3 : dist2 x3 c = r ^ 2)
    (h4 : dist2 x4 c = r ^ 2) (o123 : 0 < e * det3 x1 x2 x3) (o124 : 0 < e * det3 x1 x2 x4)
    (o134 : 0 < e * det3 x1 x3 x4) (o234 : 0 < e * det3 x2 x3 x4) :
    NAE [SignType.sign (ip (liftPt x1) u), -SignType.sign (ip (liftPt x2) u),
      SignType.sign (ip (liftPt x3) u), -SignType.sign (ip (liftPt x4) u)] := by
  have h := nae_of_sum [e * det3 x2 x3 x4 * ip (liftPt x1) u, -(e * det3 x1 x3 x4 * ip (liftPt x2) u),
      e * det3 x1 x2 x4 * ip (liftPt x3) u, -(e * det3 x1 x2 x3 * ip (liftPt x4) u)] (by
    simp only [List.sum_cons, List.sum_nil]
    linear_combination e * f1_identity u c r h1 h2 h3 h4)
  simpa only [List.map_cons, List.map_nil, Left.sign_neg, sign_mul, sign_pos o123, sign_pos o124,
    sign_pos o134, sign_pos o234, one_mul] using h

namespace IsCircleRealization

variable {n : ℕ} {side : ℕ → ℕ → ℤ → ℕ → ℤ} {c : ℕ → ℝ × ℝ} {r ε : ℕ → ℝ}
  {P : ℕ → ℕ → ℤ → ℝ × ℝ}

/-- The Lorentz vector of circle `i`. -/
def V (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (i : ℕ) : Vec := circVec (c i) (r i) (ε i)

/-- The Lorentz vector of the crossing point `P j k s`. -/
def Pt (P : ℕ → ℕ → ℤ → ℝ × ℝ) (j k : ℕ) (s : ℤ) : Vec := liftPt (P j k s)

lemma isPoint (P : ℕ → ℕ → ℤ → ℝ × ℝ) (j k : ℕ) (s : ℤ) : IsPoint (Pt P j k s) :=
  isPoint_liftPt _

lemma D2_pos (R : IsCircleRealization n side c r ε P) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n) : 0 < D2 (V c r ε i) (V c r ε j) := by
  have hc := R.cross i j hi hij hj
  have hεi : (ε i) ^ 2 = 1 := by
    rcases R.orientation i hi (by omega) with h | h <;> rw [h] <;> norm_num
  have hεj : (ε j) ^ 2 = 1 := by
    rcases R.orientation j (by omega) hj with h | h <;> rw [h] <;> norm_num
  rw [V, V, D2_circVec, mul_pow, hεi, hεj]
  have := mul_pos (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  linarith

lemma pair (R : IsCircleRealization n side c r ε P) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    (hk : k ≤ n) : Pair (V c r ε j) (V c r ε k) (Pt P j k 1) (Pt P j k (-1)) := by
  have h1 := R.on_circles j k 1 hj hjk hk (Or.inl rfl)
  have h2 := R.on_circles j k (-1) hj hjk hk (Or.inr rfl)
  refine ⟨?_, ?_, ?_, ?_, (isPoint P j k 1).1, (isPoint P j k (-1)).1⟩ <;>
    simp only [V, Pt, ip_circVec_liftPt, h1.1, h1.2, h2.1, h2.2, sub_self, mul_zero]

lemma ip_pos (R : IsCircleRealization n side c r ε P) {j k m : ℕ} {s : ℤ}
    (h : side j k s m = 1) : 0 < ip (V c r ε m) (Pt P j k s) := by
  have := R.sides j k s m (by rw [h]; norm_num)
  rw [h] at this
  simp only [V, Pt, ip_circVec_liftPt]
  push_cast at this
  linarith

lemma ip_neg (R : IsCircleRealization n side c r ε P) {j k m : ℕ} {s : ℤ}
    (h : side j k s m = -1) : ip (V c r ε m) (Pt P j k s) < 0 := by
  have := R.sides j k s m (by rw [h]; norm_num)
  rw [h] at this
  simp only [V, Pt, ip_circVec_liftPt]
  push_cast at this
  linarith

end IsCircleRealization

end NonCirc
