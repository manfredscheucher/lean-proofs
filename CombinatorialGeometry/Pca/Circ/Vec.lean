/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: vector algebra in `ℝ³` (`doc/pca/circ.md`)

Source: S. Felsner, M. Scheucher, *Arrangements of Pseudocircles: On Circularizability*,
https://arxiv.org/abs/1712.02149 (v6), section 2 (circles on the sphere as intersections with
planes).

Vectors are `Fin 3 → ℝ` with `⬝ᵥ` and `⨯₃` (Mathlib). The unit sphere is `p ⬝ᵥ p = 1`.

* `det3 a b c = a ⬝ᵥ (b ⨯₃ c)` (triple product), `orient u p q r = det3 (q - p) (r - p) u`
  (orientation of three points of a plane with normal `u`),
* parallelism lemmas (Lagrange identity), strict convexity of the ball,
* `interPt`: the two intersection points of two circles on the sphere, as explicit formula.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Matrix

namespace Pca.Circ

/-- Vectors of `ℝ³`. -/
abbrev V := Fin 3 → ℝ

/-- The triple product `a ⬝ᵥ (b ⨯₃ c) = det (a, b, c)`. -/
def det3 (a b c : V) : ℝ := a ⬝ᵥ (b ⨯₃ c)

/-- The orientation of the points `p, q, r` of a plane with normal `u`: positive iff `p, q, r` are
counter-clockwise seen from the tip of `u`. -/
def orient (u p q r : V) : ℝ := det3 (q - p) (r - p) u

section coords

/-- Expand dot and cross products into coordinates. -/
theorem dot_eq (a b : V) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_three]

@[simp] theorem cross_0 (a b : V) : (a ⨯₃ b) 0 = a 1 * b 2 - a 2 * b 1 := by
  rw [cross_apply]; rfl
@[simp] theorem cross_1 (a b : V) : (a ⨯₃ b) 1 = a 2 * b 0 - a 0 * b 2 := by
  rw [cross_apply]; rfl
@[simp] theorem cross_2 (a b : V) : (a ⨯₃ b) 2 = a 0 * b 1 - a 1 * b 0 := by
  rw [cross_apply]; rfl

theorem det3_eq (a b c : V) : det3 a b c =
    a 0 * (b 1 * c 2 - b 2 * c 1) + a 1 * (b 2 * c 0 - b 0 * c 2) +
      a 2 * (b 0 * c 1 - b 1 * c 0) := by
  rw [det3, dot_eq, cross_0, cross_1, cross_2]

theorem cross_eq (a b : V) : a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0] := cross_apply a b

end coords

theorem det3_cyc (a b c : V) : det3 b c a = det3 a b c := by
  rw [det3_eq, det3_eq]; ring

theorem det3_swap (a b c : V) : det3 b a c = - det3 a b c := by
  rw [det3_eq, det3_eq]; ring

theorem det3_swap23 (a b c : V) : det3 a c b = - det3 a b c := by
  rw [det3_eq, det3_eq]; ring

theorem det3_cross (a b c : V) : det3 a b c = (a ⨯₃ b) ⬝ᵥ c := by
  rw [det3_eq, dot_eq, cross_0, cross_1, cross_2]; ring

theorem orient_cyc (u p q r : V) : orient u q r p = orient u p q r := by
  simp only [orient, det3_eq, Pi.sub_apply]; ring

theorem orient_swap (u p q r : V) : orient u q p r = - orient u p q r := by
  simp only [orient, det3_eq, Pi.sub_apply]; ring

theorem orient_swap23 (u p q r : V) : orient u p r q = - orient u p q r := by
  simp only [orient, det3_eq, Pi.sub_apply]; ring

/-- `orient` is affine in the last point. -/
theorem orient_affine (u p q a b : V) (t : ℝ) :
    orient u p q (a + t • (b - a)) = (1 - t) * orient u p q a + t * orient u p q b := by
  simp only [orient, det3_eq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem orient_self_left (u p q : V) (s : ℝ) : orient u p q (p + s • (q - p)) = 0 := by
  simp only [orient, det3_eq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem dot_self_nonneg (a : V) : 0 ≤ a ⬝ᵥ a := by
  rw [dot_eq]; nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1), mul_self_nonneg (a 2)]

theorem eq_zero_of_dot_self {a : V} (h : a ⬝ᵥ a = 0) : a = 0 :=
  dotProduct_self_eq_zero.1 h

theorem dot_self_pos {a : V} (h : a ≠ 0) : 0 < a ⬝ᵥ a :=
  lt_of_le_of_ne (dot_self_nonneg a) (fun h' => h (eq_zero_of_dot_self h'.symm))

/-- Lagrange's identity. -/
theorem lagrange (a b : V) : (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
  rw [cross_dot_cross, dotProduct_comm b a]; ring

/-- `a ≠ 0`, `a ⨯₃ b = 0`: `b` is a multiple of `a`. -/
theorem eq_smul_of_cross_eq_zero {a b : V} (ha : a ≠ 0) (h : a ⨯₃ b = 0) :
    b = ((a ⬝ᵥ b) / (a ⬝ᵥ a)) • a := by
  have hl := lagrange a b
  rw [h, zero_dotProduct] at hl
  have hpos := dot_self_pos ha
  set c := (a ⬝ᵥ b) / (a ⬝ᵥ a) with hc
  have hca : c * (a ⬝ᵥ a) = a ⬝ᵥ b := by rw [hc]; field_simp
  have key : (b - c • a) ⬝ᵥ (b - c • a) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm b a]
    have : (b ⬝ᵥ b) * (a ⬝ᵥ a) = (a ⬝ᵥ b) ^ 2 := by linarith
    have h2 : ((b ⬝ᵥ b) - 2 * c * (a ⬝ᵥ b) + c * (c * (a ⬝ᵥ a))) * (a ⬝ᵥ a) = 0 := by
      rw [hca]; linear_combination this - (a ⬝ᵥ b) * hca
    have h3 := (mul_eq_zero.1 h2).resolve_right hpos.ne'
    linarith
  exact (sub_eq_zero.1 (eq_zero_of_dot_self key))

/-- A vector orthogonal to `u₁` and `u₂` is a multiple of `u₁ ⨯₃ u₂` (if that is `≠ 0`). -/
theorem eq_smul_cross_of_perp {u₁ u₂ v : V} (hw : u₁ ⨯₃ u₂ ≠ 0) (h₁ : u₁ ⬝ᵥ v = 0)
    (h₂ : u₂ ⬝ᵥ v = 0) :
    v = (((u₁ ⨯₃ u₂) ⬝ᵥ v) / ((u₁ ⨯₃ u₂) ⬝ᵥ (u₁ ⨯₃ u₂))) • (u₁ ⨯₃ u₂) := by
  apply eq_smul_of_cross_eq_zero hw
  rw [dot_eq] at h₁ h₂
  ext i; fin_cases i <;> simp [cross_eq]
  · linear_combination (u₂ 0) * h₁ - (u₁ 0) * h₂
  · linear_combination (u₂ 1) * h₁ - (u₁ 1) * h₂
  · linear_combination (u₂ 2) * h₁ - (u₁ 2) * h₂

/-- Two vectors of a plane with normal `u ≠ 0` with vanishing `det3 v v' u` are parallel. -/
theorem eq_smul_of_det3_eq_zero {u v v' : V} (hu : u ≠ 0) (hv : v ≠ 0) (h₁ : u ⬝ᵥ v = 0)
    (h₂ : u ⬝ᵥ v' = 0) (h : det3 v v' u = 0) : v' = ((v ⬝ᵥ v') / (v ⬝ᵥ v)) • v := by
  apply eq_smul_of_cross_eq_zero hv
  set x := v ⨯₃ v' with hx
  have hxu : x ⬝ᵥ u = 0 := by rw [← det3_cross]; exact h
  have hxc : x ⨯₃ u = 0 := by
    rw [dot_eq] at h₁ h₂
    rw [hx]; ext i; fin_cases i <;> simp [cross_eq]
    · linear_combination (v' 0) * h₁ - (v 0) * h₂
    · linear_combination (v' 1) * h₁ - (v 1) * h₂
    · linear_combination (v' 2) * h₁ - (v 2) * h₂
  have hl := lagrange x u
  rw [hxc, zero_dotProduct, hxu] at hl
  have hpos := dot_self_pos hu
  have : x ⬝ᵥ x = 0 := by
    rcases mul_eq_zero.1 (show (x ⬝ᵥ x) * (u ⬝ᵥ u) = 0 by nlinarith [hl]) with h' | h'
    · exact h'
    · exact absurd h' hpos.ne'
  exact eq_zero_of_dot_self this

/-- Norm of a point of the line through two points of the unit sphere. -/
theorem dot_line (x y : V) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (t : ℝ) :
    (x + t • (y - x)) ⬝ᵥ (x + t • (y - x)) = 1 - 2 * t * (1 - t) * (1 - x ⬝ᵥ y) := by
  simp only [dot_eq] at hx hy ⊢
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (1 - t) ^ 2 * hx + t ^ 2 * hy

theorem dot_lt_one_of_ne {x y : V} (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (h : x ≠ y) :
    x ⬝ᵥ y < 1 := by
  have hp := dot_self_pos (sub_ne_zero.2 h)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hx, hy, dotProduct_comm y x] at hp
  linarith

/-- Strict convexity of the ball: inner points of a chord are inside. -/
theorem chord_inside {x y : V} (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (h : x ≠ y) {t : ℝ}
    (h0 : 0 < t) (h1 : t < 1) : (x + t • (y - x)) ⬝ᵥ (x + t • (y - x)) < 1 := by
  rw [dot_line x y hx hy]
  have := dot_lt_one_of_ne hx hy h
  have : 0 < 2 * t * (1 - t) * (1 - x ⬝ᵥ y) := by
    apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

/-- A point of the line through two points of the sphere is inside only between them. -/
theorem mem_Ioo_of_inside {x y : V} (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (h : x ≠ y) {t : ℝ}
    (ht : (x + t • (y - x)) ⬝ᵥ (x + t • (y - x)) < 1) : 0 < t ∧ t < 1 := by
  rw [dot_line x y hx hy] at ht
  have h1 := dot_lt_one_of_ne hx hy h
  have hpos : 0 < t * (1 - t) := by
    by_contra hc
    push_neg at hc
    nlinarith
  constructor <;> nlinarith

/-- A point of the line through two points of the sphere on the sphere is one of them. -/
theorem eq_of_on_sphere {x y : V} (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (h : x ≠ y) {t : ℝ}
    (ht : (x + t • (y - x)) ⬝ᵥ (x + t • (y - x)) = 1) : t = 0 ∨ t = 1 := by
  rw [dot_line x y hx hy] at ht
  have h1 := dot_lt_one_of_ne hx hy h
  have : t * (1 - t) = 0 := by
    have h2 : 2 * (t * (1 - t)) * (1 - x ⬝ᵥ y) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · linarith
  rcases mul_eq_zero.1 this with h3 | h3
  · left; exact h3
  · right; linarith

/-- Three distinct points of a circle (sphere ∩ plane with normal `u ≠ 0`) are not collinear. -/
theorem orient_ne_zero {u x y z : V} {h : ℝ} (hu : u ≠ 0) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1)
    (hz : z ⬝ᵥ z = 1) (hux : u ⬝ᵥ x = h) (huy : u ⬝ᵥ y = h) (huz : u ⬝ᵥ z = h) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : orient u x y z ≠ 0 := by
  intro h0
  have hv : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have key := eq_smul_of_det3_eq_zero hu hv (by rw [dotProduct_sub, hux, huy, sub_self])
    (by rw [dotProduct_sub, hux, huz, sub_self]) h0
  set t := ((y - x) ⬝ᵥ (z - x)) / ((y - x) ⬝ᵥ (y - x))
  have hzt : z = x + t • (y - x) := by rw [← key]; abel
  rcases eq_of_on_sphere hx hy hxy (t := t) (by rw [← hzt]; exact hz) with h1 | h1
  · exact hxz (by rw [hzt, h1, zero_smul, add_zero])
  · exact hyz (by rw [hzt, h1, one_smul]; abel)

/-! ## The intersection points of two circles -/

/-- The foot point of the line `E_i ∩ E_j` (planes `⟨u_i, x⟩ = h_i`, `⟨u_j, x⟩ = h_j`): the
point of the line in the span of `u_i`, `u_j`. -/
noncomputable def foot (ui uj : V) (hi hj : ℝ) : V :=
  (1 / ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj))) • (hi • (uj ⨯₃ (ui ⨯₃ uj)) + hj • ((ui ⨯₃ uj) ⨯₃ ui))

/-- The intersection point of the circles `E_i ∩ S`, `E_j ∩ S` on the side `ε = ±1`, i.e. with
`sign (det3 u_i u_j p) = ε`. -/
noncomputable def interPt (ui uj : V) (hi hj ε : ℝ) : V :=
  foot ui uj hi hj + (ε * Real.sqrt ((1 - foot ui uj hi hj ⬝ᵥ foot ui uj hi hj) /
    ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)))) • (ui ⨯₃ uj)

theorem dot_foot_left (ui uj : V) (hi hj : ℝ) (hw : ui ⨯₃ uj ≠ 0) :
    ui ⬝ᵥ foot ui uj hi hj = hi := by
  have hpos := dot_self_pos hw
  unfold foot
  rw [dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  have e1 : ui ⬝ᵥ (uj ⨯₃ (ui ⨯₃ uj)) = (ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj) := by
    rw [← det3, ← det3_cross]
  have e2 : ui ⬝ᵥ ((ui ⨯₃ uj) ⨯₃ ui) = 0 := dot_cross_self _ _
  rw [e1, e2, mul_zero, add_zero]; field_simp

theorem dot_foot_right (ui uj : V) (hi hj : ℝ) (hw : ui ⨯₃ uj ≠ 0) :
    uj ⬝ᵥ foot ui uj hi hj = hj := by
  have hpos := dot_self_pos hw
  unfold foot
  rw [dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  have e1 : uj ⬝ᵥ (uj ⨯₃ (ui ⨯₃ uj)) = 0 := dot_self_cross _ _
  have e2 : uj ⬝ᵥ ((ui ⨯₃ uj) ⨯₃ ui) = (ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj) := by
    rw [← det3, det3_cyc, ← det3_cross]
  rw [e1, e2, mul_zero, zero_add]; field_simp

theorem cross_dot_foot (ui uj : V) (hi hj : ℝ) : (ui ⨯₃ uj) ⬝ᵥ foot ui uj hi hj = 0 := by
  unfold foot
  rw [dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, dot_self_cross,
    dot_cross_self]
  simp

/-- `interPt` lies on both planes. -/
theorem dot_interPt_left (ui uj : V) (hi hj ε : ℝ) (hw : ui ⨯₃ uj ≠ 0) :
    ui ⬝ᵥ interPt ui uj hi hj ε = hi := by
  unfold interPt
  rw [dotProduct_add, dotProduct_smul, dot_self_cross, smul_zero, add_zero,
    dot_foot_left _ _ _ _ hw]

theorem dot_interPt_right (ui uj : V) (hi hj ε : ℝ) (hw : ui ⨯₃ uj ≠ 0) :
    uj ⬝ᵥ interPt ui uj hi hj ε = hj := by
  unfold interPt
  rw [dotProduct_add, dotProduct_smul, dot_cross_self, smul_zero, add_zero,
    dot_foot_right _ _ _ _ hw]

theorem det3_interPt (ui uj : V) (hi hj ε : ℝ) :
    det3 ui uj (interPt ui uj hi hj ε) = (ε * Real.sqrt ((1 - foot ui uj hi hj ⬝ᵥ
      foot ui uj hi hj) / ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)))) * ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)) := by
  rw [det3_cross]; unfold interPt
  rw [dotProduct_add, cross_dot_foot, zero_add, dotProduct_smul, smul_eq_mul]

/-- `interPt` lies on the sphere if `ε = ±1` and the foot point is in the closed ball. -/
theorem interPt_on_sphere (ui uj : V) (hi hj ε : ℝ) (hw : ui ⨯₃ uj ≠ 0) (hε : ε ^ 2 = 1)
    (hm : foot ui uj hi hj ⬝ᵥ foot ui uj hi hj ≤ 1) :
    interPt ui uj hi hj ε ⬝ᵥ interPt ui uj hi hj ε = 1 := by
  have hpos := dot_self_pos hw
  set m := foot ui uj hi hj
  set w := ui ⨯₃ uj
  have hmw : w ⬝ᵥ m = 0 := cross_dot_foot ui uj hi hj
  have hs := Real.sq_sqrt (show 0 ≤ (1 - m ⬝ᵥ m) / (w ⬝ᵥ w) from
    div_nonneg (by linarith) hpos.le)
  unfold interPt
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm m w, hmw]
  set r := Real.sqrt ((1 - m ⬝ᵥ m) / (w ⬝ᵥ w))
  have : r ^ 2 * (w ⬝ᵥ w) = 1 - m ⬝ᵥ m := by rw [hs]; field_simp
  linear_combination (w ⬝ᵥ w) * r ^ 2 * hε + this

/-- Every point of the sphere on both planes is `interPt` with `ε` the sign of `det3 u_i u_j p`.
-/
theorem eq_interPt {ui uj p : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0) (hp : p ⬝ᵥ p = 1)
    (hpi : ui ⬝ᵥ p = hi) (hpj : uj ⬝ᵥ p = hj) (hd : det3 ui uj p ≠ 0) :
    p = interPt ui uj hi hj (if 0 < det3 ui uj p then 1 else -1) := by
  have hpos := dot_self_pos hw
  set m := foot ui uj hi hj
  set w := ui ⨯₃ uj
  have hmw : w ⬝ᵥ m = 0 := cross_dot_foot ui uj hi hj
  have key := eq_smul_cross_of_perp (v := p - m) hw
    (by rw [dotProduct_sub, hpi, dot_foot_left _ _ _ _ hw, sub_self])
    (by rw [dotProduct_sub, hpj, dot_foot_right _ _ _ _ hw, sub_self])
  rw [dotProduct_sub, hmw, sub_zero] at key
  have hdet : det3 ui uj p = w ⬝ᵥ p := det3_cross _ _ _
  set l := (w ⬝ᵥ p) / (w ⬝ᵥ w) with hl
  have hpm : p = m + l • w := by rw [← key]; abel
  -- `l² (w⬝w) = 1 - m⬝m`
  have hnorm : l ^ 2 * (w ⬝ᵥ w) = 1 - m ⬝ᵥ m := by
    have := hp
    rw [hpm] at this
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at this
    rw [dotProduct_comm m w, hmw] at this
    linarith
  have hr : Real.sqrt ((1 - m ⬝ᵥ m) / (w ⬝ᵥ w)) = |l| := by
    rw [← hnorm, mul_div_assoc, div_self hpos.ne', mul_one, Real.sqrt_sq_eq_abs]
  unfold interPt
  rw [hr]
  conv_lhs => rw [hpm]
  congr 2
  have hl0 : l ≠ 0 := by
    rw [hl]; exact div_ne_zero (by rw [← hdet]; exact hd) hpos.ne'
  have hsign : (0 < det3 ui uj p) ↔ 0 < l := by
    rw [hl, hdet]; exact ⟨fun h => div_pos h hpos, fun h => by
      by_contra hc; push_neg at hc; exact absurd h (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hc hpos.le))⟩
  split_ifs with h
  · rw [abs_of_pos (hsign.1 h), one_mul]
  · have : l < 0 := lt_of_le_of_ne (not_lt.1 (fun h' => h (hsign.2 h'))) hl0
    rw [abs_of_neg this]; ring

/-- Three planes with independent normals meet in at most one point. -/
theorem eq_of_three_planes {ua ub uc p q : V} (hd : det3 ua ub uc ≠ 0)
    (ha : ua ⬝ᵥ p = ua ⬝ᵥ q) (hb : ub ⬝ᵥ p = ub ⬝ᵥ q) (hc : uc ⬝ᵥ p = uc ⬝ᵥ q) : p = q := by
  rw [det3_eq] at hd
  rw [dot_eq, dot_eq] at ha hb hc
  have e : ∀ i, p i = q i := by
    intro i
    have h0 : (p 0 - q 0) * (ua 0 * (ub 1 * uc 2 - ub 2 * uc 1) + ua 1 * (ub 2 * uc 0 -
        ub 0 * uc 2) + ua 2 * (ub 0 * uc 1 - ub 1 * uc 0)) = 0 := by
      linear_combination (ub 1 * uc 2 - ub 2 * uc 1) * ha + (ua 2 * uc 1 - ua 1 * uc 2) * hb +
        (ua 1 * ub 2 - ua 2 * ub 1) * hc
    have h1 : (p 1 - q 1) * (ua 0 * (ub 1 * uc 2 - ub 2 * uc 1) + ua 1 * (ub 2 * uc 0 -
        ub 0 * uc 2) + ua 2 * (ub 0 * uc 1 - ub 1 * uc 0)) = 0 := by
      linear_combination (ub 2 * uc 0 - ub 0 * uc 2) * ha + (ua 0 * uc 2 - ua 2 * uc 0) * hb +
        (ua 2 * ub 0 - ua 0 * ub 2) * hc
    have h2 : (p 2 - q 2) * (ua 0 * (ub 1 * uc 2 - ub 2 * uc 1) + ua 1 * (ub 2 * uc 0 -
        ub 0 * uc 2) + ua 2 * (ub 0 * uc 1 - ub 1 * uc 0)) = 0 := by
      linear_combination (ub 0 * uc 1 - ub 1 * uc 0) * ha + (ua 1 * uc 0 - ua 0 * uc 1) * hb +
        (ua 0 * ub 1 - ua 1 * ub 0) * hc
    fin_cases i
    · exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hd)
    · exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hd)
    · exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hd)
  funext i; exact e i

end Pca.Circ

namespace Pca.Circ

/-- The orientation of the tangents of two circles at a common point `p`. -/
theorem det3_cross_cross (a b p : V) :
    det3 (a ⨯₃ p) (b ⨯₃ p) p = (p ⬝ᵥ p) * det3 a b p := by
  rw [det3_eq, det3_eq, dot_eq]; simp only [cross_0, cross_1, cross_2]; ring

theorem det3_smul_smul (s s' : ℝ) (a b p : V) :
    det3 (s • a) (s' • b) p = s * s' * det3 a b p := by
  rw [det3_eq, det3_eq]; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Two vectors orthogonal to `u₁, u₂` (with `u₁ ⨯₃ u₂ ≠ 0`) are parallel. -/
theorem exists_smul_of_perp {u₁ u₂ v v' : V} (hw : u₁ ⨯₃ u₂ ≠ 0) (h₁ : u₁ ⬝ᵥ v = 0)
    (h₂ : u₂ ⬝ᵥ v = 0) (h₁' : u₁ ⬝ᵥ v' = 0) (h₂' : u₂ ⬝ᵥ v' = 0) (hv' : v' ≠ 0) :
    ∃ t : ℝ, v = t • v' := by
  set w := u₁ ⨯₃ u₂
  set α := (w ⬝ᵥ v) / (w ⬝ᵥ w)
  set β := (w ⬝ᵥ v') / (w ⬝ᵥ w)
  have e : v = α • w := eq_smul_cross_of_perp hw h₁ h₂
  have e' : v' = β • w := eq_smul_cross_of_perp hw h₁' h₂'
  have hβ : β ≠ 0 := by
    intro h0; apply hv'; rw [e', h0, zero_smul]
  refine ⟨α / β, ?_⟩
  rw [e, e', smul_smul, div_mul_cancel₀ _ hβ]

end Pca.Circ

namespace Pca.Circ

/-- A point of the sphere on two planes is `foot + l • (u_i ⨯₃ u_j)` with
`l² ⟨w, w⟩ = 1 - ⟨m, m⟩`. -/
theorem exists_lam {ui uj p : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0) (hp : p ⬝ᵥ p = 1)
    (hpi : ui ⬝ᵥ p = hi) (hpj : uj ⬝ᵥ p = hj) :
    ∃ l : ℝ, p = foot ui uj hi hj + l • (ui ⨯₃ uj) ∧
      l ^ 2 * ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)) = 1 - foot ui uj hi hj ⬝ᵥ foot ui uj hi hj := by
  set m := foot ui uj hi hj
  set w := ui ⨯₃ uj
  have hmw : w ⬝ᵥ m = 0 := cross_dot_foot ui uj hi hj
  have key := eq_smul_cross_of_perp (v := p - m) hw
    (by rw [dotProduct_sub, hpi, dot_foot_left _ _ _ _ hw, sub_self])
    (by rw [dotProduct_sub, hpj, dot_foot_right _ _ _ _ hw, sub_self])
  set l := (w ⬝ᵥ (p - m)) / (w ⬝ᵥ w)
  have hpm : p = m + l • w := by rw [← key]; abel
  refine ⟨l, hpm, ?_⟩
  have := hp
  rw [hpm] at this
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul] at this
  rw [dotProduct_comm m w, hmw] at this
  linarith

/-- Two circles of the sphere meet in at most two points. -/
theorem not_three_on_two_planes {ui uj p q r : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0)
    (hp : p ⬝ᵥ p = 1) (hpi : ui ⬝ᵥ p = hi) (hpj : uj ⬝ᵥ p = hj)
    (hq : q ⬝ᵥ q = 1) (hqi : ui ⬝ᵥ q = hi) (hqj : uj ⬝ᵥ q = hj)
    (hr : r ⬝ᵥ r = 1) (hri : ui ⬝ᵥ r = hi) (hrj : uj ⬝ᵥ r = hj)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : False := by
  obtain ⟨a, ha, ha2⟩ := exists_lam hw hp hpi hpj
  obtain ⟨b, hb, hb2⟩ := exists_lam hw hq hqi hqj
  obtain ⟨c, hc, hc2⟩ := exists_lam hw hr hri hrj
  have hpos := dot_self_pos hw
  have hab : a ≠ b := fun e => hpq (by rw [ha, hb, e])
  have hac : a ≠ c := fun e => hpr (by rw [ha, hc, e])
  have hbc : b ≠ c := fun e => hqr (by rw [hb, hc, e])
  have e1 : a ^ 2 = b ^ 2 := by
    have : (a ^ 2 - b ^ 2) * ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_right hpos.ne']
  have e2 : a ^ 2 = c ^ 2 := by
    have : (a ^ 2 - c ^ 2) * ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_right hpos.ne']
  have hb' : b = -a := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e1.symm with h | h
    · exact absurd h.symm hab
    · exact h
  have hc' : c = -a := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2.symm with h | h
    · exact absurd h.symm hac
    · exact h
  exact hbc (hb'.trans hc'.symm)

end Pca.Circ
