/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Layer 1: Lorentz space `R^{3,1}`, brackets, and the sign rules used by the certificates

Circles on `S²` are spacelike vectors and points are future null vectors of `R^{3,1}`
(see the (unpublished) realizability notes, section "The algebraic model"). This file contains only
general facts about vectors; nothing here refers to a particular arrangement.

* `ip`: the Lorentz form `x0 y0 + x1 y1 + x2 y2 - x3 y3` (time coordinate last).
* `br a b c d`: the bracket, `Matrix.det` of the matrix with rows `a, b, c, d`.
* `hodge a b c`: the Lorentz dual, `br a b c w = ip (hodge a b c) w`.
* Identities (all by `ring`, for arbitrary vectors): the five-vector dependency `dep5`, the
  3-term Grassmann-Plücker relation `gp3`, Cauchy-Binet for the Gram determinant.
* Type-3 tie (`tie3`): if `p` is null and orthogonal to `a, b`, then `br a b p x * ip w p =
  br a b p w * ip x p` for all `w, x` (scalar form of `[a b p ·] = c_p <p, ·>`; no
  nondegeneracy needed).
* Sign rules: `type3_sign`, `pairgp_sign` (lemma "exactly one of abc, abd is Krupp" of the
  notes), `krupp_sign` (the Krupp tie: `[abc q]` has the same sign for all points `q`).
-/

namespace NonCirc

/-- Vectors of `R^{3,1}`; coordinate `3` is the time coordinate. -/
abbrev Vec := Fin 4 → ℝ

/-- The Lorentz form of signature `(3,1)`. -/
def ip (x y : Vec) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - x 3 * y 3

/-- The bracket of four vectors: the determinant of the matrix with rows `a, b, c, d`. -/
def br (a b c d : Vec) : ℝ := Matrix.det (Matrix.of ![a, b, c, d])

/-- A point of `S²`: a future null vector. -/
def IsPoint (p : Vec) : Prop := ip p p = 0 ∧ 0 < p 3

/-- The Gram determinant of two vectors; `> 0` iff the two circles cross. -/
def D2 (a b : Vec) : ℝ := ip a a * ip b b - ip a b ^ 2

lemma ip_comm (x y : Vec) : ip x y = ip y x := by unfold ip; ring

/-! ## Expansion of the determinant -/

theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
      - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
      + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
      - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
          + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  ring

lemma br_expand (a b c d : Vec) :
    br a b c d =
      a 0 * (b 1 * (c 2 * d 3 - c 3 * d 2) - b 2 * (c 1 * d 3 - c 3 * d 1)
          + b 3 * (c 1 * d 2 - c 2 * d 1))
      - a 1 * (b 0 * (c 2 * d 3 - c 3 * d 2) - b 2 * (c 0 * d 3 - c 3 * d 0)
          + b 3 * (c 0 * d 2 - c 2 * d 0))
      + a 2 * (b 0 * (c 1 * d 3 - c 3 * d 1) - b 1 * (c 0 * d 3 - c 3 * d 0)
          + b 3 * (c 0 * d 1 - c 1 * d 0))
      - a 3 * (b 0 * (c 1 * d 2 - c 2 * d 1) - b 1 * (c 0 * d 2 - c 2 * d 0)
          + b 2 * (c 0 * d 1 - c 1 * d 0)) := by
  unfold br
  rw [det_fin_four]
  simp

/-! ## Alternation -/

lemma br_swap01 (a b c d : Vec) : br b a c d = -br a b c d := by
  rw [br_expand, br_expand]; ring

lemma br_swap12 (a b c d : Vec) : br a c b d = -br a b c d := by
  rw [br_expand, br_expand]; ring

lemma br_swap23 (a b c d : Vec) : br a b d c = -br a b c d := by
  rw [br_expand, br_expand]; ring

lemma br_rep03 (a b c : Vec) : br a b c a = 0 := by rw [br_expand]; ring

lemma br_rep13 (a b c : Vec) : br a b c b = 0 := by rw [br_expand]; ring

lemma br_rep23 (a b c : Vec) : br a b c c = 0 := by rw [br_expand]; ring

/-! ## The Lorentz dual -/

/-- The Lorentz dual of three vectors: `br a b c w = ip (hodge a b c) w` (`br_eq_ip_hodge`). -/
def hodge (a b c : Vec) : Vec :=
  ![-(a 1 * (b 2 * c 3 - b 3 * c 2) - a 2 * (b 1 * c 3 - b 3 * c 1) + a 3 * (b 1 * c 2 - b 2 * c 1)),
    a 0 * (b 2 * c 3 - b 3 * c 2) - a 2 * (b 0 * c 3 - b 3 * c 0) + a 3 * (b 0 * c 2 - b 2 * c 0),
    -(a 0 * (b 1 * c 3 - b 3 * c 1) - a 1 * (b 0 * c 3 - b 3 * c 0) + a 3 * (b 0 * c 1 - b 1 * c 0)),
    -(a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0))]

lemma br_eq_ip_hodge (a b c w : Vec) : br a b c w = ip w (hodge a b c) := by
  rw [br_expand]; simp [ip, hodge]; ring

/-! ## Identities -/

/-- Five vectors in `R^4` are dependent (Cramer): `Σ (-1)^t [X \ x_t] <x_t, y> = 0`. -/
lemma dep5 (x0 x1 x2 x3 x4 y : Vec) :
    -br x1 x2 x3 x4 * ip x0 y + br x0 x2 x3 x4 * ip x1 y - br x0 x1 x3 x4 * ip x2 y
      + br x0 x1 x2 x4 * ip x3 y - br x0 x1 x2 x3 * ip x4 y = 0 := by
  simp only [br_expand, ip]; ring

/-- The 3-term Grassmann-Plücker relation. -/
lemma gp3 (a b c d e f : Vec) :
    br a b c d * br a b e f - br a b c e * br a b d f + br a b c f * br a b d e = 0 := by
  have h := dep5 a b d e f (hodge a b c)
  simp only [← br_eq_ip_hodge, br_rep03, br_rep13] at h
  linear_combination -h

/-- Five-term Grassmann-Plücker relation for `A = (a, b, p, q, x)`, `B = (a, b, c)`
(only the nonvanishing terms). -/
lemma gp5_abc (a b c p q x : Vec) :
    -br a b q x * br a b c p + br a b p x * br a b c q - br a b p q * br a b c x = 0 := by
  have h := dep5 a b p q x (hodge a b c)
  simp only [← br_eq_ip_hodge, br_rep03, br_rep13] at h
  linear_combination h

/-- Cauchy-Binet: the Gram determinant of four vectors is `-(bracket)^2`. -/
lemma gram_det (X : Fin 4 → Vec) :
    (Matrix.of fun i j => ip (X i) (X j)).det = -(Matrix.of X).det ^ 2 := by
  have h : (Matrix.of fun i j => ip (X i) (X j)) =
      Matrix.of X * Matrix.diagonal ![1, 1, 1, -1] * (Matrix.of X).transpose := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_four, ip, Matrix.diagonal_apply]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]
  ring

/-- If `p, q` are null and orthogonal to `a, b`, then `[a b p q]^2 = D2 a b * <p,q>^2`. -/
lemma br_sq_of_orth {a b p q : Vec} (hap : ip a p = 0) (hbp : ip b p = 0) (haq : ip a q = 0)
    (hbq : ip b q = 0) (hp : ip p p = 0) (hq : ip q q = 0) :
    br a b p q ^ 2 = D2 a b * ip p q ^ 2 := by
  have h := gram_det ![a, b, p, q]
  rw [det_fin_four] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.cons_val_two, Matrix.cons_val_three] at h
  rw [ip_comm p a, ip_comm p b, ip_comm q a, ip_comm q b, ip_comm q p, ip_comm b a] at h
  rw [hap, hbp, haq, hbq, hp, hq] at h
  unfold D2
  have hbr : br a b p q = (Matrix.of ![a, b, p, q]).det := rfl
  rw [hbr]
  linear_combination h

/-! ## Type-3 tie -/

/-- If `p` is null and orthogonal to `a` and `b`, the functional `[a b p ·]` is a multiple of
`<p, ·>`; in scalar form, without any nondegeneracy assumption. -/
lemma tie3 {a b p : Vec} (hap : ip a p = 0) (hbp : ip b p = 0) (hp : ip p p = 0) (w x : Vec) :
    br a b p x * ip w p = br a b p w * ip x p := by
  linear_combination dep5 a b p w x p + br b p w x * hap - br a p w x * hbp + br a b w x * hp

/-! ## Points -/

lemma point_identity {p q : Vec} (hp : IsPoint p) (hq : IsPoint q) :
    2 * p 3 * q 3 * ip p q = -((p 0 * q 3 - q 0 * p 3) ^ 2 + (p 1 * q 3 - q 1 * p 3) ^ 2
      + (p 2 * q 3 - q 2 * p 3) ^ 2) := by
  have h1 := hp.1
  have h2 := hq.1
  unfold ip at *
  linear_combination q 3 ^ 2 * h1 + p 3 ^ 2 * h2

/-- Two points have `<p, q> ≤ 0`. -/
lemma ip_points_nonpos {p q : Vec} (hp : IsPoint p) (hq : IsPoint q) : ip p q ≤ 0 := by
  have h := point_identity hp hq
  have h3 : 0 < 2 * p 3 * q 3 := by have := hp.2; have := hq.2; positivity
  nlinarith [sq_nonneg (p 0 * q 3 - q 0 * p 3), sq_nonneg (p 1 * q 3 - q 1 * p 3),
    sq_nonneg (p 2 * q 3 - q 2 * p 3)]

/-- Two points with `<p, q> = 0` are proportional: `<v, p> q₃ = <v, q> p₃` for every `v`. -/
lemma proportional_of_ip_zero {p q : Vec} (hp : IsPoint p) (hq : IsPoint q) (h : ip p q = 0)
    (v : Vec) : ip v p * q 3 = ip v q * p 3 := by
  have hid := point_identity hp hq
  rw [h, mul_zero] at hid
  have s0 := sq_nonneg (p 0 * q 3 - q 0 * p 3)
  have s1 := sq_nonneg (p 1 * q 3 - q 1 * p 3)
  have s2 := sq_nonneg (p 2 * q 3 - q 2 * p 3)
  have e0 : p 0 * q 3 - q 0 * p 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have e1 : p 1 * q 3 - q 1 * p 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have e2 : p 2 * q 3 - q 2 * p 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  unfold ip; linear_combination v 0 * e0 + v 1 * e1 + v 2 * e2

/-- Two points separated by some vector `v` (opposite signs of `<v, ·>`) have `<p, q> < 0`. -/
lemma ip_points_neg {p q v : Vec} (hp : IsPoint p) (hq : IsPoint q)
    (hsep : ip v p * ip v q < 0) : ip p q < 0 := by
  rcases (ip_points_nonpos hp hq).lt_or_eq with h | h
  · exact h
  exfalso
  have key := proportional_of_ip_zero hp hq h v
  have hq3 := hq.2
  have hp3 := hp.2
  have : ip v p * ip v q * q 3 = ip v q ^ 2 * p 3 := by linear_combination ip v q * key
  nlinarith [sq_nonneg (ip v q), mul_pos (neg_pos.mpr hsep) hq3]

/-- Two points distinguished by some vector `v` (`<v, p> = 0 ≠ <v, q>`) have `<p, q> < 0`. -/
lemma ip_points_neg' {p q v : Vec} (hp : IsPoint p) (hq : IsPoint q)
    (hvp : ip v p = 0) (hvq : ip v q ≠ 0) : ip p q < 0 := by
  rcases (ip_points_nonpos hp hq).lt_or_eq with h | h
  · exact h
  exfalso
  have key := proportional_of_ip_zero hp hq h v
  rw [hvp, zero_mul] at key
  exact hvq ((mul_eq_zero.mp key.symm).resolve_right hp.2.ne')

/-! ## Sign rules -/

/-- Data of a crossing pair: two null vectors `P, Q` orthogonal to `a` and `b`. -/
structure Pair (a b P Q : Vec) : Prop where
  aP : ip a P = 0
  bP : ip b P = 0
  aQ : ip a Q = 0
  bQ : ip b Q = 0
  PP : ip P P = 0
  QQ : ip Q Q = 0

/-- `K = [a b P Q] ≠ 0` for crossing circles (`D2 a b > 0`) and distinct points. -/
lemma Pair.K_ne {a b P Q : Vec} (h : Pair a b P Q) (hD : 0 < D2 a b) (hPQ : ip P Q ≠ 0) :
    br a b P Q ≠ 0 := by
  intro hK
  have := br_sq_of_orth h.aP h.bP h.aQ h.bQ h.PP h.QQ
  rw [hK] at this
  have : 0 < D2 a b * ip P Q ^ 2 := mul_pos hD (by positivity)
  linarith

lemma Pair.tieP {a b P Q : Vec} (h : Pair a b P Q) (x : Vec) :
    br a b x P * ip P Q = -(br a b P Q * ip x P) := by
  have := tie3 h.aP h.bP h.PP Q x
  rw [br_swap23 a b x P, ip_comm Q P] at *
  linear_combination -this

lemma Pair.tieQ {a b P Q : Vec} (h : Pair a b P Q) (x : Vec) :
    br a b x Q * ip P Q = br a b P Q * ip x Q := by
  have := tie3 h.aQ h.bQ h.QQ P x
  rw [br_swap23 a b x Q, br_swap23 a b Q P] at *
  linear_combination -this

/-- Type 3: `[a b x P]` has the sign of `K <x, P>` (`K = [a b P Q]`, `<P, Q> < 0`). -/
lemma Pair.type3_sign {a b P Q : Vec} (h : Pair a b P Q) (hK : br a b P Q ≠ 0)
    (hPQ : ip P Q < 0) {x : Vec} (hx : ip x P ≠ 0) :
    0 < br a b x P * br a b P Q * ip x P := by
  have t := h.tieP x
  have hKx : 0 < (br a b P Q * ip x P) ^ 2 := by positivity
  have e : br a b x P * br a b P Q * ip x P * ip P Q = -(br a b P Q * ip x P) ^ 2 := by
    linear_combination (br a b P Q * ip x P) * t
  nlinarith

/-- Lemma "exactly one of `abc`, `abd` is Krupp": if `<c,P><d,Q>` and `<c,Q><d,P>` have
opposite signs, then `[a b c d]` has the sign of `-K <c,P> <d,Q>`. -/
lemma Pair.pairgp_sign {a b P Q : Vec} (h : Pair a b P Q) (hK : br a b P Q ≠ 0)
    (hPQ : ip P Q ≠ 0) {c d : Vec} (hsep : ip c P * ip d Q * (ip c Q * ip d P) < 0) :
    br a b c d * br a b P Q * (ip c P * ip d Q) < 0 := by
  set K := br a b P Q
  set π := ip P Q
  have E : K * (br a b c d * π ^ 2 + K * (ip c P * ip d Q - ip c Q * ip d P)) = 0 := by
    linear_combination π ^ 2 * gp3 a b c d P Q + (br a b d Q * π) * h.tieP c
      + (-K * ip c P) * h.tieQ d - (br a b d P * π) * h.tieQ c - (K * ip c Q) * h.tieP d
  have E' : br a b c d * π ^ 2 = -K * (ip c P * ip d Q - ip c Q * ip d P) := by
    have := (mul_eq_zero.mp E).resolve_left hK
    linear_combination this
  set A := ip c P * ip d Q
  set B := ip c Q * ip d P
  have hπ2 : 0 < π ^ 2 := by positivity
  have hAB : 0 < A * (A - B) := by nlinarith [sq_nonneg A]
  have hK2 : 0 < K ^ 2 := by positivity
  have : br a b c d * K * A * π ^ 2 = -(K ^ 2 * (A * (A - B))) := by
    linear_combination K * A * E'
  have : br a b c d * K * A * π ^ 2 < 0 := by rw [this]; nlinarith [mul_pos hK2 hAB]
  nlinarith

/-- Identity behind the Krupp tie: `<P,Q> [a b c x] = <x,Q> [a b c P] + <x,P> [a b c Q]`. -/
lemma Pair.krupp_identity {a b P Q : Vec} (h : Pair a b P Q) (hK : br a b P Q ≠ 0)
    (c x : Vec) :
    ip P Q * br a b c x = ip x Q * br a b c P + ip x P * br a b c Q := by
  have E : br a b P Q * (ip P Q * br a b c x - (ip x Q * br a b c P + ip x P * br a b c Q)) = 0 := by
    have g := gp5_abc a b c P Q x
    have tP := h.tieP x
    have tQ := h.tieQ x
    have s1 := br_swap23 a b x Q
    have s2 := br_swap23 a b x P
    linear_combination (-ip P Q) * g - (ip P Q * br a b c P) * s1 + (ip P Q * br a b c Q) * s2
      + br a b c P * tQ - br a b c Q * tP
  have := (mul_eq_zero.mp E).resolve_left hK
  linear_combination this

/-- Krupp tie: if `c` separates the two crossings `P, Q` of `a, b` (the triple `abc` is Krupp),
then `[a b c q]` has the same sign as `[a b c P]` for every point `q` with `<P,q> ≤ 0`,
`<Q,q> ≤ 0`, one of them strict. -/
lemma Pair.krupp_sign {a b P Q : Vec} (h : Pair a b P Q) (hK : br a b P Q ≠ 0)
    (hPQ : ip P Q < 0) {c q : Vec} (hkr : ip c P * ip c Q < 0)
    (hPq : ip q P ≤ 0) (hQq : ip q Q ≤ 0) (hst : ip q P < 0 ∨ ip q Q < 0) :
    0 < br a b c q * br a b c P := by
  have ic := h.krupp_identity hK c c
  rw [br_rep23] at ic
  set Y := br a b c P
  set Z := br a b c Q
  have hY : Y ≠ 0 := by
    intro hY0
    have t := h.tieP c
    rw [show br a b c P = Y from rfl, hY0, zero_mul] at t
    have : ip c P ≠ 0 := by intro h0; rw [h0, zero_mul] at hkr; exact lt_irrefl 0 hkr
    exact (mul_ne_zero hK this) (by linarith)
  have hYZ : 0 < Y * Z := by
    have hY2 : 0 < Y ^ 2 := by positivity
    have : ip c P ^ 2 * (Y * Z) = -(ip c P * ip c Q) * Y ^ 2 := by
      linear_combination (-(Y * ip c P)) * ic
    have hcP : 0 < ip c P ^ 2 := by
      have : ip c P ≠ 0 := by intro h0; rw [h0, zero_mul] at hkr; exact lt_irrefl 0 hkr
      positivity
    nlinarith [mul_pos (neg_pos.mpr hkr) hY2]
  have iq := h.krupp_identity hK c q
  have : ip P Q * (br a b c q * Y) = ip q Q * Y ^ 2 + ip q P * (Y * Z) := by
    linear_combination Y * iq
  have hY2 : 0 < Y ^ 2 := by positivity
  have hrhs : ip q Q * Y ^ 2 + ip q P * (Y * Z) < 0 := by
    rcases hst with hs | hs
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hQq hY2.le]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hPq hYZ.le]
  nlinarith

/-! ## Sign bookkeeping: `0 < x * y` means "same sign", `x * y < 0` "opposite signs" -/

lemma ss_trans {x y z : ℝ} (h1 : 0 < x * y) (h2 : 0 < y * z) : 0 < x * z := by
  by_contra h; replace h := not_lt.mp h; nlinarith [mul_pos h1 h2, mul_nonneg (sq_nonneg y) (neg_nonneg.mpr h)]

lemma so_trans {x y z : ℝ} (h1 : 0 < x * y) (h2 : y * z < 0) : x * z < 0 := by
  by_contra h; replace h := not_lt.mp h; nlinarith [mul_pos h1 (neg_pos.mpr h2), mul_nonneg (sq_nonneg y) h]

lemma os_trans {x y z : ℝ} (h1 : x * y < 0) (h2 : 0 < y * z) : x * z < 0 := by
  have := so_trans (x := z) (y := y) (z := x) (by linarith) (by linarith)
  linarith

lemma oo_trans {x y z : ℝ} (h1 : x * y < 0) (h2 : y * z < 0) : 0 < x * z := by
  by_contra h; replace h := not_lt.mp h
  nlinarith [mul_pos (neg_pos.mpr h1) (neg_pos.mpr h2), mul_nonneg (sq_nonneg y) (neg_nonneg.mpr h)]

lemma cancel_pos {x s : ℝ} (h : 0 < x * s) (hs : 0 < s) : 0 < x := by
  by_contra h'; replace h' := not_lt.mp h'; nlinarith [mul_nonneg (neg_nonneg.mpr h') hs.le]

lemma cancel_neg {x s : ℝ} (h : 0 < x * s) (hs : s < 0) : x < 0 := by
  by_contra h'; replace h' := not_lt.mp h'; nlinarith [mul_nonneg h' (neg_nonneg.mpr hs.le)]

lemma cancel_pos' {x s : ℝ} (h : x * s < 0) (hs : 0 < s) : x < 0 := by
  by_contra h'; replace h' := not_lt.mp h'; nlinarith [mul_nonneg h' hs.le]

lemma cancel_neg' {x s : ℝ} (h : x * s < 0) (hs : s < 0) : 0 < x := by
  by_contra h'; replace h' := not_lt.mp h'; nlinarith [mul_nonneg (neg_nonneg.mpr h') (neg_nonneg.mpr hs.le)]

end NonCirc
