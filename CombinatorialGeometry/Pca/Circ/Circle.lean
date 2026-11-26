/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: points on one circle (`doc/pca/circ.md`)

Facts about points of one circle `{p | p ⬝ᵥ p = 1, u ⬝ᵥ p = h}` of the unit sphere, in terms of the
orientation `orient u`:

* `orient_mul_pos_of_sep`: four points of a circle are in convex position: if `z₁, z₂` lie on the
  same side of the line `x y`, then `x, y` lie on the same side of the line `z₁ z₂`
  (strict convexity of the ball),
* `chord_meet`: if `x, y` lie on different sides of the line `z₁ z₂`, then the chords `x y` and
  `z₁ z₂` meet inside the ball.
-/
import Pca.Circ.Vec

open Matrix

namespace Pca.Circ

/-- `p` lies on the circle `{p | p ⬝ᵥ p = 1, u ⬝ᵥ p = h}`. -/
def OnCirc (u : V) (h : ℝ) (p : V) : Prop := p ⬝ᵥ p = 1 ∧ u ⬝ᵥ p = h

theorem OnCirc.orient_ne_zero {u : V} {h : ℝ} (hu : u ≠ 0) {x y z : V} (hx : OnCirc u h x)
    (hy : OnCirc u h y) (hz : OnCirc u h z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    orient u x y z ≠ 0 :=
  Pca.Circ.orient_ne_zero hu hx.1 hy.1 hz.1 hx.2 hy.2 hz.2 hxy hxz hyz

/-- If `x, y` (on the circle) are on different sides of the line `z₁ z₂`, the chord `x y` meets the
line `z₁ z₂` in a point `q = x + t (y - x) = z₁ + μ (z₂ - z₁)` with `t, μ ∈ (0, 1)`. -/
theorem chord_meet {u : V} {h : ℝ} (hu : u ≠ 0) {x y z₁ z₂ : V} (hx : OnCirc u h x)
    (hy : OnCirc u h y) (hz₁ : OnCirc u h z₁) (hz₂ : OnCirc u h z₂) (hxy : x ≠ y)
    (hz : z₁ ≠ z₂) (hneg : orient u z₁ z₂ x * orient u z₁ z₂ y < 0) :
    ∃ t μ : ℝ, 0 < t ∧ t < 1 ∧ 0 < μ ∧ μ < 1 ∧ x + t • (y - x) = z₁ + μ • (z₂ - z₁) := by
  set ox := orient u z₁ z₂ x
  set oy := orient u z₁ z₂ y
  have hne : ox - oy ≠ 0 := by
    intro h0; have : ox = oy := sub_eq_zero.1 h0; rw [this] at hneg; nlinarith [sq_nonneg oy]
  set t := ox / (ox - oy) with ht
  have ht01 : 0 < t ∧ t < 1 := by
    rcases lt_or_gt_of_ne (show ox ≠ 0 by intro h0; rw [h0, zero_mul] at hneg; exact lt_irrefl _ hneg)
      with h1 | h1
    · have h2 : 0 < oy := by
        by_contra h3; push_neg at h3; nlinarith
      have h4 : ox - oy < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg h1 h4, (div_lt_one_of_neg h4).2 (by linarith)⟩
    · have h2 : oy < 0 := by
        by_contra h3; push_neg at h3; nlinarith
      have h4 : 0 < ox - oy := by linarith
      exact ⟨div_pos h1 h4, (div_lt_one h4).2 (by linarith)⟩
  set q := x + t • (y - x) with hq
  have hq0 : orient u z₁ z₂ q = 0 := by
    rw [hq, orient_affine]
    change (1 - t) * ox + t * oy = 0
    rw [ht]; field_simp; ring
  have hqin : q ⬝ᵥ q < 1 := chord_inside hx.1 hy.1 hxy ht01.1 ht01.2
  have hqu : u ⬝ᵥ q = h := by
    rw [hq, dotProduct_add, dotProduct_smul, dotProduct_sub, hx.2, hy.2, sub_self, smul_zero,
      add_zero]
  have hv : z₂ - z₁ ≠ 0 := sub_ne_zero.2 hz.symm
  have key := eq_smul_of_det3_eq_zero hu hv (by rw [dotProduct_sub, hz₁.2, hz₂.2, sub_self])
    (by rw [dotProduct_sub, hqu, hz₁.2, sub_self]) hq0
  set μ := ((z₂ - z₁) ⬝ᵥ (q - z₁)) / ((z₂ - z₁) ⬝ᵥ (z₂ - z₁))
  have hqμ : q = z₁ + μ • (z₂ - z₁) := by rw [← key]; abel
  have hμ := mem_Ioo_of_inside hz₁.1 hz₂.1 hz (t := μ) (by rw [← hqμ]; exact hqin)
  exact ⟨t, μ, ht01.1, ht01.2, hμ.1, hμ.2, hqμ⟩

/-- **Convex position.** For four distinct points of a circle: if `z₁, z₂` are on the same side of
the line `x y`, then `x, y` are on the same side of the line `z₁ z₂`. -/
theorem orient_mul_pos_of_sep {u : V} {h : ℝ} (hu : u ≠ 0) {x y z₁ z₂ : V} (hx : OnCirc u h x)
    (hy : OnCirc u h y) (hz₁ : OnCirc u h z₁) (hz₂ : OnCirc u h z₂) (hxy : x ≠ y)
    (hz : z₁ ≠ z₂) (hx₁ : x ≠ z₁) (hx₂ : x ≠ z₂) (hy₁ : y ≠ z₁) (hy₂ : y ≠ z₂)
    (hsame : 0 < orient u x y z₁ * orient u x y z₂) :
    0 < orient u z₁ z₂ x * orient u z₁ z₂ y := by
  have ox := hz₁.orient_ne_zero hu hz₂ hx hz hx₁.symm hx₂.symm
  have oy := hz₁.orient_ne_zero hu hz₂ hy hz hy₁.symm hy₂.symm
  by_contra hc
  push_neg at hc
  have hneg : orient u z₁ z₂ x * orient u z₁ z₂ y < 0 :=
    lt_of_le_of_ne hc (mul_ne_zero ox oy)
  obtain ⟨t, μ, -, -, hμ0, hμ1, he⟩ := chord_meet hu hx hy hz₁ hz₂ hxy hz hneg
  have h0 : orient u x y (x + t • (y - x)) = 0 := orient_self_left u x y t
  rw [he, orient_affine] at h0
  set P := orient u x y z₁
  set Q := orient u x y z₂
  rcases lt_or_gt_of_ne (show P ≠ 0 by intro h'; rw [h', zero_mul] at hsame; exact lt_irrefl _ hsame)
    with h1 | h1
  · have hQ : Q < 0 := by by_contra h3; push_neg at h3; nlinarith
    nlinarith
  · have hQ : 0 < Q := by by_contra h3; push_neg at h3; nlinarith
    nlinarith

/-- Three points of a circle meeting the chord through two others: if `x, y` are on different
sides of the line `z₁ z₂`, then the chord `x y` contains a point of the line `z₁ z₂` inside the
ball. -/
theorem chord_meet_inside {u : V} {h : ℝ} (hu : u ≠ 0) {x y z₁ z₂ : V} (hx : OnCirc u h x)
    (hy : OnCirc u h y) (hz₁ : OnCirc u h z₁) (hz₂ : OnCirc u h z₂) (hxy : x ≠ y)
    (hz : z₁ ≠ z₂) (hneg : orient u z₁ z₂ x * orient u z₁ z₂ y < 0) :
    ∃ q : V, q ⬝ᵥ q < 1 ∧ (∃ t : ℝ, q = x + t • (y - x)) ∧ ∃ μ : ℝ, q = z₁ + μ • (z₂ - z₁) := by
  obtain ⟨t, μ, ht0, ht1, -, -, he⟩ := chord_meet hu hx hy hz₁ hz₂ hxy hz hneg
  exact ⟨x + t • (y - x), chord_inside hx.1 hy.1 hxy ht0 ht1, ⟨t, rfl⟩, ⟨μ, he⟩⟩

end Pca.Circ
