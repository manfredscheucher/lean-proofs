/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 4: fans (`lem:fan` and `lem:fan-cons` of the notes)

A **fan** (`Arrangement.Fan`) is given by a dart `a` such that the three consecutive cells
`cellOf a`, `cellOf (σ a)`, `cellOf (σ² a)` at the crossing `u` of `a` are triangles. All
other parts of the configuration of the notes (`u`, `C_i`, `C_j`, `C_k`, `v_1, …, v_4`,
`T_1, T_2, T_3`, `N`, `R`, `S`, `R'`, `u'`, the far sides) are defined from `a`; see
`doc/pca/model.md`, section 6.

For `n ≥ 4`:

* `Arrangement.fan_lemma`: `t u ≥ 3` implies `t u = 3` and `u` is the center of a fan,
* `Arrangement.Fan.nbrs_eq`, `.crossings_eq`, `.nbrs_eq_crossings`: the four neighbours of `u`
  are `v_1, …, v_4`, exactly the four crossings of `C_k` with `C_i` and `C_j`,
* `Arrangement.Fan.corners_T₁`, `.corners_T₂`, `.corners_T₃`, `.straight_f₃`, `.straight_f₂`:
  `T_1 = u v_1 v_2`, `T_2 = u v_2 v_3`, `T_3 = u v_3 v_4`, and `v_4, v_3, v_2, v_1` are
  consecutive on `C_k`,
* `Arrangement.t_le_three`, `Arrangement.excess_eq_X'_sub_deficiency_of_four_le`:
  `t x ≤ 3` and `e = |X'| - def`,
* `Arrangement.Fan.cons_a` … `.cons_e`: parts (a)-(e) of `lem:fan-cons`.
-/
import Pca.Digon

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-! ## Triangles at a crossing -/

/-- If the cell of `σ b` (the cell to the left of `b`) is a triangle, its side after `b`'s
reverse is the far side `φ (σ b)`, and `α (φ (σ b)) = σ³ (α b)`. -/
theorem α_φ_σ_of_triangle {b : D} (h : A.IsTriangle (A.cellOf (A.σ b))) :
    A.α (A.φ (A.σ b)) = A.σ (A.σ (A.σ (A.α b))) := by
  have h3 := A.φ_φ_φ_of_triangle h
  rw [← φ_α] at h3
  have h2 : A.φ (A.φ (A.φ (A.α b))) = A.α b := A.φ.injective h3
  rw [φ_α, A.φ_apply (A.φ (A.σ b))] at h2
  exact A.eq_σσσ_of_σ_eq h2

/-- In the triangle of `b`: `α (φ² b) = σ³ b`. -/
theorem α_φ_φ_of_triangle {b : D} (h : A.IsTriangle (A.cellOf b)) :
    A.α (A.φ (A.φ b)) = A.σ (A.σ (A.σ b)) := by
  have h3 := A.φ_φ_φ_of_triangle h
  rw [A.φ_apply (A.φ (A.φ b))] at h3
  exact A.eq_σσσ_of_σ_eq h3

/-- Two triangles sharing the side of `b` at its start: the far side of the triangle of `σ b`
is followed straight by the far side `φ b` of the cell of `b` (the far sides lie on one curve,
the second curve through the other end of `b`). -/
theorem straight_φ_σ {b : D} (h : A.IsTriangle (A.cellOf (A.σ b))) :
    A.straight (A.φ (A.σ b)) = A.φ b := by
  rw [straight_apply, α_φ_σ_of_triangle A h, σ5, φ_apply]

/-- The corners of a triangle. -/
theorem corners_of_triangle {b : D} (h : A.IsTriangle (A.cellOf b)) :
    Cell.corners A (A.cellOf b) =
      {A.crossingOf b, A.crossingOf (A.φ b), A.crossingOf (A.φ (A.φ b))} := by
  have hp := A.period_of_size h
  have hl : orbitList A.φ b = [b, A.φ b, A.φ (A.φ b)] := by
    simp [orbitList, hp, List.range_succ]
  rw [Cell.corners, cellOf, Orbit.darts_mk, orbitFinset, hl]
  simp [image_insert]

/-- The number of triangles at the crossing of `b`, angle by angle. -/
theorem tAngles_crossingOf (b : D) : A.tAngles (A.crossingOf b) =
    (if A.InTriangle b then 1 else 0) + (if A.InTriangle (A.σ b) then 1 else 0) +
    (if A.InTriangle (A.σ (A.σ b)) then 1 else 0) +
    (if A.InTriangle (A.σ (A.σ (A.σ b))) then 1 else 0) := by
  rw [tAngles, crossingOf, Orbit.darts_mk, orbitFinset,
    card_filter_toFinset (orbitList_nodup A.σ b), orbitList_σ]
  by_cases h0 : A.InTriangle b <;> by_cases h1 : A.InTriangle (A.σ b) <;>
    by_cases h2 : A.InTriangle (A.σ (A.σ b)) <;>
    by_cases h3 : A.InTriangle (A.σ (A.σ (A.σ b))) <;>
    simp [h0, h1, h2, h3]

/-- No crossing is incident to four triangles (`n ≥ 4`): the four far sides would form all of
one curve, which carries `2(n-1) ≥ 6` crossings. -/
theorem not_four_triangles (hn : 4 ≤ n) {b : D} (h0 : A.IsTriangle (A.cellOf b))
    (h1 : A.IsTriangle (A.cellOf (A.σ b))) (h2 : A.IsTriangle (A.cellOf (A.σ (A.σ b))))
    (h3 : A.IsTriangle (A.cellOf (A.σ (A.σ (A.σ b))))) : False := by
  have k4 : A.straight (A.φ b) = A.φ (A.σ (A.σ (A.σ b))) := by
    have := A.straight_φ_σ (b := A.σ (A.σ (A.σ b))) (by rw [A.σ_σ_σ_σ]; exact h0)
    rwa [A.σ_σ_σ_σ] at this
  refine A.straight_iterate_ne (d := A.φ (A.σ (A.σ (A.σ b)))) (k := 4) (by norm_num)
    (by omega) ?_
  show A.straight (A.straight (A.straight (A.straight _))) = _
  rw [A.straight_φ_σ h3, A.straight_φ_σ h2, A.straight_φ_σ h1, k4]

/-- The cell on the far side of a triangle: if the cell of `b` is a triangle and the cell
`cellOf (α (φ b))` on the other side of its far side `φ b` is a triangle too, then the third
corner `z` of the latter is the far end of `σ² (α b)` (the continuation of `b` through its end),
`z` lies on the curves of `b` and `σ b`, `z` is not the crossing of `b` (`n ≥ 3`), and a dart
`r` at `z` on the curve of `σ b` ends at the end of `φ b`. -/
theorem far_triangle (hn : 3 ≤ n) {b : D} (hT : A.IsTriangle (A.cellOf b))
    (hR : A.IsTriangle (A.cellOf (A.α (A.φ b)))) :
    Cell.corners A (A.cellOf (A.α (A.φ b))) =
      {A.crossingOf (A.α (A.φ b)), A.crossingOf (A.φ b),
        A.crossingOf (A.α (A.σ (A.σ (A.α b))))} ∧
    Crossing.curves A (A.crossingOf (A.α (A.σ (A.σ (A.α b))))) =
      {A.curve b, A.curve (A.σ b)} ∧
    A.crossingOf (A.α (A.σ (A.σ (A.α b)))) ≠ A.crossingOf b ∧
    ∃ r, A.crossingOf r = A.crossingOf (A.α (A.σ (A.σ (A.α b)))) ∧
      A.curve r = A.curve (A.σ b) ∧ A.crossingOf (A.α r) = A.crossingOf (A.α (A.φ b)) := by
  have hφ1 : A.φ (A.α (A.φ b)) = A.σ (A.σ (A.α b)) := by rw [φ_α, φ_apply]
  have hz : A.crossingOf (A.φ (A.φ (A.α (A.φ b)))) =
      A.crossingOf (A.α (A.σ (A.σ (A.α b)))) := by
    rw [crossingOf_φ, hφ1]
  have hr := A.α_φ_φ_of_triangle hR
  have hcr : A.curve (A.φ (A.φ (A.α (A.φ b)))) = A.curve (A.σ b) := by
    rw [← curve_α, hr, curve_σσσ, ← φ_apply, ← curve_α, A.α_φ_φ_of_triangle hT, curve_σσσ]
  refine ⟨?_, ?_, ?_, A.φ (A.φ (A.α (A.φ b))), hz, hcr, ?_⟩
  · rw [corners_of_triangle A hR, hz, hφ1, crossingOf_σσ, A.crossingOf_φ b]
  · refine A.curves_eq_pair ?_ ?_ (A.isArrangement.curve_σ b).symm
    · have := A.mem_curves_end (A.σ (A.σ (A.α b)))
      rwa [curve_σσ, curve_α] at this
    · rw [← hz, ← hcr]; exact A.mem_curves_crossingOf _
  · have := A.crossingOf_α_σσ_ne hn (A.α b)
    rwa [α_α] at this
  · rw [hr, crossingOf_σσσ]

/-! ## Fans -/

/-- A **fan** (the configuration of `lem:fan`): a dart `a` at a crossing `u` such that the
three consecutive cells `T_1 = cellOf a`, `T_2 = cellOf (σ a)`, `T_3 = cellOf (σ² a)` at `u`
are triangles. `T_1` and `T_2` share the side of `a` (on `C_j`), `T_2` and `T_3` share the side
of `σ a` (on `C_i`). Everything else is defined from `a` (section `Fan` below). -/
structure Fan where
  /-- the dart at the center `u` along `C_j` towards `v_2`, the side shared by `T_1`, `T_2` -/
  a : D
  isTriangle₁ : A.IsTriangle (A.cellOf a)
  isTriangle₂ : A.IsTriangle (A.cellOf (A.σ a))
  isTriangle₃ : A.IsTriangle (A.cellOf (A.σ (A.σ a)))

namespace Fan

variable {A} (F : A.Fan)

/-- The center `u`. -/
def u : A.Crossing := A.crossingOf F.a
/-- `C_j`: the curve of `a` (the side `u v_2` shared by `T_1` and `T_2`). -/
def Cj : Fin n := A.curve F.a
/-- `C_i`: the curve of `σ a` (the side `u v_3` shared by `T_2` and `T_3`). -/
def Ci : Fin n := A.curve (A.σ F.a)
/-- `C_k`: the third pseudocircle, the curve of the far sides. -/
def Ck : Fin n := A.curve (A.φ F.a)
/-- The neighbour `v_1` of `u` on `C_i` (end of `σ³ a`), a crossing of `C_i` and `C_k`. -/
def v₁ : A.Crossing := A.crossingOf (A.α (A.σ (A.σ (A.σ F.a))))
/-- The neighbour `v_2` of `u` on `C_j` (end of `a`), a crossing of `C_j` and `C_k`. -/
def v₂ : A.Crossing := A.crossingOf (A.α F.a)
/-- The neighbour `v_3` of `u` on `C_i` (end of `σ a`), a crossing of `C_i` and `C_k`. -/
def v₃ : A.Crossing := A.crossingOf (A.α (A.σ F.a))
/-- The neighbour `v_4` of `u` on `C_j` (end of `σ² a`), a crossing of `C_j` and `C_k`. -/
def v₄ : A.Crossing := A.crossingOf (A.α (A.σ (A.σ F.a)))
/-- The far side of `T_1`, a dart of `C_k` from `v_2` to `v_1`. -/
def f₁ : D := A.φ F.a
/-- The far side of `T_2`, a dart of `C_k` from `v_3` to `v_2`. -/
def f₂ : D := A.φ (A.σ F.a)
/-- The far side of `T_3`, a dart of `C_k` from `v_4` to `v_3`. -/
def f₃ : D := A.φ (A.σ (A.σ F.a))
/-- `T_1 = u v_1 v_2`. -/
def T₁ : A.Cell := A.cellOf F.a
/-- `T_2 = u v_2 v_3`, the middle triangle. -/
def T₂ : A.Cell := A.cellOf (A.σ F.a)
/-- `T_3 = u v_3 v_4`. -/
def T₃ : A.Cell := A.cellOf (A.σ (A.σ F.a))
/-- `N`: the fourth cell at `u` (between `σ³ a` and `a`, with corners `v_4, u, v_1`). -/
def N : A.Cell := A.cellOf (A.σ (A.σ (A.σ F.a)))
/-- `R`: the cell on the other side of the far side `v_1 v_2` of `T_1`. -/
def R : A.Cell := A.cellOf (A.α F.f₁)
/-- `S`: the cell on the other side of the far side `v_2 v_3` of `T_2`. -/
def S : A.Cell := A.cellOf (A.α F.f₂)
/-- `R'`: the cell on the other side of the far side `v_3 v_4` of `T_3`. -/
def R' : A.Cell := A.cellOf (A.α F.f₃)
/-- `u'`: the second crossing of `C_i` and `C_j` (axiom 6; chosen, it is unique). -/
noncomputable def u' : A.Crossing := Classical.choose (A.exists_ne_curves_eq F.u)

/-! ### Darts and crossings of the configuration -/

theorem α_f₂ : A.α F.f₂ = A.σ (A.σ (A.σ (A.α F.a))) := A.α_φ_σ_of_triangle F.isTriangle₂

theorem α_f₃ : A.α F.f₃ = A.σ (A.σ (A.σ (A.α (A.σ F.a)))) :=
  A.α_φ_σ_of_triangle F.isTriangle₃

theorem φ_f₁ : A.φ F.f₁ = A.α (A.σ (A.σ (A.σ F.a))) := by
  rw [← A.α_φ_φ_of_triangle F.isTriangle₁, α_α]; rfl

/-- `v_4, v_3, v_2, v_1` are consecutive on `C_k`: the far side of `T_3` is followed straight
by the far side of `T_2`, ... -/
theorem straight_f₃ : A.straight F.f₃ = F.f₂ := A.straight_φ_σ F.isTriangle₃

/-- ... and the far side of `T_2` by the far side of `T_1`. -/
theorem straight_f₂ : A.straight F.f₂ = F.f₁ := A.straight_φ_σ F.isTriangle₂

theorem curve_f₁ : A.curve F.f₁ = F.Ck := rfl

theorem curve_f₂ : A.curve F.f₂ = F.Ck := by rw [← A.curve_straight, F.straight_f₂]; rfl

theorem curve_f₃ : A.curve F.f₃ = F.Ck := by rw [← A.curve_straight, F.straight_f₃, curve_f₂]

theorem crossingOf_f₁ : A.crossingOf F.f₁ = F.v₂ := A.crossingOf_φ _
theorem crossingOf_f₂ : A.crossingOf F.f₂ = F.v₃ := A.crossingOf_φ _
theorem crossingOf_f₃ : A.crossingOf F.f₃ = F.v₄ := A.crossingOf_φ _

theorem end_f₁ : A.crossingOf (A.α F.f₁) = F.v₁ := by
  rw [v₁, ← φ_f₁, crossingOf_φ]

theorem end_f₂ : A.crossingOf (A.α F.f₂) = F.v₂ := by rw [α_f₂, crossingOf_σσσ]; rfl
theorem end_f₃ : A.crossingOf (A.α F.f₃) = F.v₃ := by rw [α_f₃, crossingOf_σσσ]; rfl

theorem σσ_f₁ : A.σ (A.σ F.f₁) = A.α F.f₂ := by rw [α_f₂]; rfl
theorem σσ_f₂ : A.σ (A.σ F.f₂) = A.α F.f₃ := by rw [α_f₃]; rfl

theorem crossingOf_a : A.crossingOf F.a = F.u := rfl
theorem crossingOf_σ_a : A.crossingOf (A.σ F.a) = F.u := A.crossingOf_σ _
theorem crossingOf_σσ_a : A.crossingOf (A.σ (A.σ F.a)) = F.u := A.crossingOf_σσ _
theorem crossingOf_σσσ_a : A.crossingOf (A.σ (A.σ (A.σ F.a))) = F.u := A.crossingOf_σσσ _

/-! ### Curves -/

theorem curves_u : Crossing.curves A F.u = {F.Cj, F.Ci} := A.curves_crossingOf _

theorem Ci_ne_Cj : F.Ci ≠ F.Cj := A.isArrangement.curve_σ _

theorem Ck_ne_Cj : F.Ck ≠ F.Cj := A.curve_φ_ne _

theorem Ck_ne_Ci : F.Ck ≠ F.Ci := by rw [← curve_f₂]; exact A.curve_φ_ne _

theorem Ck_not_mem_u : F.Ck ∉ Crossing.curves A F.u := by
  rw [curves_u, mem_insert, mem_singleton, not_or]
  exact ⟨F.Ck_ne_Cj, F.Ck_ne_Ci⟩

theorem curves_v₁ : Crossing.curves A F.v₁ = {F.Ci, F.Ck} := by
  refine A.curves_eq_pair ?_ ?_ F.Ck_ne_Ci.symm
  · have := A.mem_curves_end (A.σ (A.σ (A.σ F.a)))
    rwa [curve_σσσ] at this
  · rw [← end_f₁]; exact A.mem_curves_end _

theorem curves_v₂ : Crossing.curves A F.v₂ = {F.Cj, F.Ck} := by
  refine A.curves_eq_pair (A.mem_curves_end _) ?_ F.Ck_ne_Cj.symm
  rw [← crossingOf_f₁]; exact A.mem_curves_crossingOf _

theorem curves_v₃ : Crossing.curves A F.v₃ = {F.Ci, F.Ck} := by
  refine A.curves_eq_pair (A.mem_curves_end _) ?_ F.Ck_ne_Ci.symm
  rw [← crossingOf_f₂, ← curve_f₂]; exact A.mem_curves_crossingOf _

theorem curves_v₄ : Crossing.curves A F.v₄ = {F.Cj, F.Ck} := by
  refine A.curves_eq_pair ?_ ?_ F.Ck_ne_Cj.symm
  · have := A.mem_curves_end (A.σ (A.σ F.a))
    rwa [curve_σσ] at this
  · rw [← crossingOf_f₃, ← curve_f₃]; exact A.mem_curves_crossingOf _

/-! ### Distinctness and uniqueness -/

theorem v₁_ne_v₃ (hn : 4 ≤ n) : F.v₁ ≠ F.v₃ := A.crossingOf_α_σσ_ne (by omega) _

theorem v₂_ne_v₄ (hn : 4 ≤ n) : F.v₂ ≠ F.v₄ := (A.crossingOf_α_σσ_ne (by omega) _).symm

theorem odd_ne_even {x y : A.Crossing} (hx : Crossing.curves A x = {F.Ci, F.Ck})
    (hy : Crossing.curves A y = {F.Cj, F.Ck}) : x ≠ y := by
  rintro rfl
  have : F.Ci ∈ ({F.Cj, F.Ck} : Finset (Fin n)) := hy ▸ hx ▸ mem_insert_self _ _
  rw [mem_insert, mem_singleton] at this
  exact this.elim F.Ci_ne_Cj F.Ck_ne_Ci.symm

theorem ne_u_of_Ck_mem {x : A.Crossing} (hx : F.Ck ∈ Crossing.curves A x) : x ≠ F.u := by
  rintro rfl; exact F.Ck_not_mem_u hx

theorem eq_v₁_or_v₃ (hn : 4 ≤ n) {x : A.Crossing} (hx : Crossing.curves A x = {F.Ci, F.Ck}) :
    x = F.v₁ ∨ x = F.v₃ :=
  A.eq_or_eq_of_curves F.Ck_ne_Ci.symm F.curves_v₁ F.curves_v₃ hx (F.v₁_ne_v₃ hn)

theorem eq_v₂_or_v₄ (hn : 4 ≤ n) {x : A.Crossing} (hx : Crossing.curves A x = {F.Cj, F.Ck}) :
    x = F.v₂ ∨ x = F.v₄ :=
  A.eq_or_eq_of_curves F.Ck_ne_Cj.symm F.curves_v₂ F.curves_v₄ hx (F.v₂_ne_v₄ hn)

theorem u'_ne_u : F.u' ≠ F.u := (Classical.choose_spec (A.exists_ne_curves_eq F.u)).1

theorem curves_u' : Crossing.curves A F.u' = {F.Cj, F.Ci} := by
  exact (Classical.choose_spec (A.exists_ne_curves_eq F.u)).2.trans F.curves_u

theorem eq_u_or_u' {x : A.Crossing} (hx : Crossing.curves A x = {F.Cj, F.Ci}) :
    x = F.u ∨ x = F.u' :=
  A.eq_or_eq_of_curves F.Ci_ne_Cj.symm F.curves_u F.curves_u' hx F.u'_ne_u.symm

theorem eq_u'_of {x : A.Crossing} (hx : Crossing.curves A x = {F.Cj, F.Ci}) (hu : x ≠ F.u) :
    x = F.u' :=
  (F.eq_u_or_u' hx).resolve_left hu

/-- Every neighbour of the center lies on `C_k`. -/
theorem Ck_mem_curves_end {c : D} (hc : A.crossingOf c = F.u) :
    F.Ck ∈ Crossing.curves A (A.crossingOf (A.α c)) := by
  have hc' : A.crossingOf F.a = A.crossingOf c := hc.symm
  rw [crossingOf_eq_iff] at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl
  · rw [show A.crossingOf (A.α F.a) = F.v₂ from rfl, curves_v₂]; simp
  · rw [show A.crossingOf (A.α (A.σ F.a)) = F.v₃ from rfl, curves_v₃]; simp
  · rw [show A.crossingOf (A.α (A.σ (A.σ F.a))) = F.v₄ from rfl, curves_v₄]; simp
  · rw [show A.crossingOf (A.α (A.σ (A.σ (A.σ F.a)))) = F.v₁ from rfl, curves_v₁]; simp

/-! ### The cells at `v_2` and `v_3` -/

theorem cellOf_α_a : A.cellOf (A.α F.a) = F.T₂ := (A.cellOf_σ _).symm
theorem cellOf_σ_α_a : A.cellOf (A.σ (A.α F.a)) = F.T₁ := A.cellOf_φ _
theorem cellOf_σσ_α_a : A.cellOf (A.σ (A.σ (A.α F.a))) = F.R := A.cellOf_σ F.f₁
theorem cellOf_σσσ_α_a : A.cellOf (A.σ (A.σ (A.σ (A.α F.a)))) = F.S := by rw [← α_f₂]; rfl

theorem cellOf_α_σ_a : A.cellOf (A.α (A.σ F.a)) = F.T₃ := (A.cellOf_σ _).symm
theorem cellOf_σ_α_σ_a : A.cellOf (A.σ (A.α (A.σ F.a))) = F.T₂ := A.cellOf_φ _
theorem cellOf_σσ_α_σ_a : A.cellOf (A.σ (A.σ (A.α (A.σ F.a)))) = F.S := A.cellOf_σ F.f₂
theorem cellOf_σσσ_α_σ_a : A.cellOf (A.σ (A.σ (A.σ (A.α (A.σ F.a))))) = F.R' := by
  rw [← α_f₃]; rfl

/-! ### `lem:fan` -/

/-- `N` is not a triangle: otherwise `u` would be incident to four triangles. -/
theorem N_not_triangle (hn : 4 ≤ n) : ¬ A.IsTriangle F.N := fun h =>
  A.not_four_triangles hn F.isTriangle₁ F.isTriangle₂ F.isTriangle₃ h

/-- The center is incident to exactly three triangles. -/
theorem t_u (hn : 4 ≤ n) : A.t F.u = 3 := by
  have hN : ¬ A.IsTriangle (A.cellOf (A.σ (A.σ (A.σ F.a)))) := F.N_not_triangle hn
  have h1 := F.isTriangle₁
  have h2 := F.isTriangle₂
  have h3 := F.isTriangle₃
  rw [t_eq_tAngles, u, tAngles_crossingOf]
  simp only [InTriangle] at *
  simp [h1, h2, h3, hN]

/-- The four neighbours of the center, with multiplicity, are `v_1, v_2, v_3, v_4`. -/
theorem nbrs_eq : A.nbrs F.u = {F.v₁, F.v₂, F.v₃, F.v₄} := by
  rw [nbrs, u, crossingOf, Orbit.darts_mk, orbitFinset, List.toFinset_val,
    (orbitList_nodup _ _).dedup, orbitList_σ, Multiset.map_coe]
  show (([F.v₂, F.v₃, F.v₄] ++ [F.v₁] : List A.Crossing) : Multiset A.Crossing) =
    (([F.v₁] ++ [F.v₂, F.v₃, F.v₄] : List A.Crossing) : Multiset A.Crossing)
  exact Multiset.coe_eq_coe.2 List.perm_append_comm

/-- The crossings of `C_k` with `C_i` and with `C_j` are exactly `v_1, v_2, v_3, v_4`. -/
theorem crossings_eq (hn : 4 ≤ n) :
    univ.filter (fun x : A.Crossing => Crossing.curves A x = {F.Ci, F.Ck} ∨
      Crossing.curves A x = {F.Cj, F.Ck}) = {F.v₁, F.v₂, F.v₃, F.v₄} := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro (h | h)
    · rcases F.eq_v₁_or_v₃ hn h with h | h <;> simp [h]
    · rcases F.eq_v₂_or_v₄ hn h with h | h <;> simp [h]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl F.curves_v₁
    · exact Or.inr F.curves_v₂
    · exact Or.inl F.curves_v₃
    · exact Or.inr F.curves_v₄

/-- `v_1, v_2, v_3, v_4` are pairwise distinct. -/
theorem v_pairwise_ne (hn : 4 ≤ n) :
    F.v₁ ≠ F.v₂ ∧ F.v₁ ≠ F.v₃ ∧ F.v₁ ≠ F.v₄ ∧ F.v₂ ≠ F.v₃ ∧ F.v₂ ≠ F.v₄ ∧ F.v₃ ≠ F.v₄ :=
  ⟨F.odd_ne_even F.curves_v₁ F.curves_v₂, F.v₁_ne_v₃ hn, F.odd_ne_even F.curves_v₁ F.curves_v₄,
    (F.odd_ne_even F.curves_v₃ F.curves_v₂).symm, F.v₂_ne_v₄ hn,
    F.odd_ne_even F.curves_v₃ F.curves_v₄⟩

/-- **`lem:fan`**, neighbours: the four neighbours of the center `u` (with multiplicity) are
exactly the four crossings of `C_k` with `C_i` and `C_j`. -/
theorem nbrs_eq_crossings (hn : 4 ≤ n) :
    A.nbrs F.u = (univ.filter (fun x : A.Crossing => Crossing.curves A x = {F.Ci, F.Ck} ∨
      Crossing.curves A x = {F.Cj, F.Ck})).val := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := F.v_pairwise_ne hn
  rw [crossings_eq F hn, nbrs_eq]
  rw [insert_val_of_notMem (by simp [h12, h13, h14]), insert_val_of_notMem (by simp [h23, h24]),
    insert_val_of_notMem (by simp [h34])]
  rfl

theorem corners_T₁ : Cell.corners A F.T₁ = {F.u, F.v₂, F.v₁} := by
  rw [T₁, corners_of_triangle A F.isTriangle₁, crossingOf_φ (d := A.φ F.a)]
  rw [show A.φ F.a = F.f₁ from rfl, end_f₁, crossingOf_f₁]; rfl

theorem corners_T₂ : Cell.corners A F.T₂ = {F.u, F.v₃, F.v₂} := by
  rw [T₂, corners_of_triangle A F.isTriangle₂, crossingOf_φ (d := A.φ (A.σ F.a))]
  rw [show A.φ (A.σ F.a) = F.f₂ from rfl, end_f₂, crossingOf_f₂, crossingOf_σ_a]

theorem corners_T₃ : Cell.corners A F.T₃ = {F.u, F.v₄, F.v₃} := by
  rw [T₃, corners_of_triangle A F.isTriangle₃, crossingOf_φ (d := A.φ (A.σ (A.σ F.a)))]
  rw [show A.φ (A.σ (A.σ F.a)) = F.f₃ from rfl, end_f₃, crossingOf_f₃, crossingOf_σσ_a]

end Fan

/-- Every crossing with at least three triangles is the center of a fan. -/
theorem exists_fan {x : A.Crossing} (h : 3 ≤ A.t x) : ∃ F : A.Fan, F.u = x := by
  obtain ⟨b, rfl⟩ := x.exists_mk
  rw [← crossingOf, t_eq_tAngles, tAngles_crossingOf] at h
  by_cases h0 : A.InTriangle b <;> by_cases h1 : A.InTriangle (A.σ b) <;>
    by_cases h2 : A.InTriangle (A.σ (A.σ b)) <;>
    by_cases h3 : A.InTriangle (A.σ (A.σ (A.σ b))) <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] at h <;>
    first
    | exact ⟨⟨b, h0, h1, h2⟩, rfl⟩
    | exact ⟨⟨A.σ b, h1, h2, h3⟩, A.crossingOf_σ b⟩
    | exact ⟨⟨A.σ (A.σ b), h2, h3, by rw [A.σ_σ_σ_σ]; exact h0⟩, A.crossingOf_σσ b⟩
    | exact ⟨⟨A.σ (A.σ (A.σ b)), h3, by rw [A.σ_σ_σ_σ]; exact h0, by rw [A.σ5]; exact h1⟩,
        A.crossingOf_σσσ b⟩
    | omega

/-- **`lem:fan`** (`n ≥ 4`): if `t u ≥ 3`, then `t u = 3` and `u` is the center of a fan (whose
structure is described by `Fan.nbrs_eq_crossings`, `Fan.corners_T₁`, `Fan.corners_T₂`,
`Fan.corners_T₃`, `Fan.straight_f₃`, `Fan.straight_f₂`). -/
theorem fan_lemma (hn : 4 ≤ n) {u : A.Crossing} (h : 3 ≤ A.t u) :
    A.t u = 3 ∧ ∃ F : A.Fan, F.u = u := by
  obtain ⟨F, rfl⟩ := A.exists_fan h
  exact ⟨F.t_u hn, F, rfl⟩

/-- `t x ≤ 3` for every crossing (`n ≥ 4`). -/
theorem t_le_three (hn : 4 ≤ n) (x : A.Crossing) : A.t x ≤ 3 := by
  by_contra h
  have := (A.fan_lemma hn (u := x) (by omega)).1
  omega

/-- `e = |X'| - def` (`n ≥ 4`), the hypothesis of `excess_eq_X'_sub_deficiency` discharged. -/
theorem excess_eq_X'_sub_deficiency_of_four_le (hn : 4 ≤ n) :
    A.excess = (A.X'.card : ℤ) - A.deficiency :=
  A.excess_eq_X'_sub_deficiency (A.t_le_three hn)

theorem mem_X' {x : A.Crossing} : x ∈ A.X' ↔ A.t x = 3 := by simp [X']

/-! ## `lem:fan-cons` -/

namespace Fan

variable {A} (F : A.Fan)

/-- **`lem:fan-cons` (a)**: `N` is neither a digon nor a triangle, and none of `R`, `S`, `R'`
is a digon (a digon and a triangle do not share a side). -/
theorem cons_a (hn : 4 ≤ n) :
    ¬ A.IsDigon F.N ∧ ¬ A.IsTriangle F.N ∧ ¬ A.IsDigon F.R ∧ ¬ A.IsDigon F.S ∧
      ¬ A.IsDigon F.R' := by
  refine ⟨fun h => ?_, F.N_not_triangle hn, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [N, cellOf_σ] at h
    have := A.not_triangle_α_of_digon h
    rw [α_α] at this
    exact this F.isTriangle₃
  · have := A.not_triangle_α_of_digon h
    rw [α_α, f₁, cellOf_φ] at this
    exact this F.isTriangle₁
  · have := A.not_triangle_α_of_digon h
    rw [α_α, f₂, cellOf_φ] at this
    exact this F.isTriangle₂
  · have := A.not_triangle_α_of_digon h
    rw [α_α, f₃, cellOf_φ] at this
    exact this F.isTriangle₃

/-- **`lem:fan-cons` (b)**, `v_1`: if `v_1 ∈ X'`, the fan at `v_1` has third pseudocircle
`C_j` (because of the neighbour `u`), so the neighbour of `v_1` on `C_k` beyond `v_2` is `v_4`;
then `v_1` and `v_3` have the same neighbours `v_2`, `v_4` on `C_k`. -/
theorem v₁_not_mem_X' (hn : 4 ≤ n) : F.v₁ ∉ A.X' := by
  intro hX
  obtain ⟨-, G, hG⟩ := A.fan_lemma hn (u := F.v₁) (by rw [(A.mem_X').1 hX])
  -- the third pseudocircle of the fan at `v_1` is `C_j`
  have hCk : G.Ck = F.Cj := by
    have h1 := G.Ck_mem_curves_end (c := A.α (A.σ (A.σ (A.σ F.a)))) hG.symm
    rw [α_α, crossingOf_σσσ_a, curves_u, mem_insert, mem_singleton] at h1
    refine h1.resolve_right fun h => G.Ck_not_mem_u ?_
    rw [hG, curves_v₁, h]; exact mem_insert_self _ _
  -- the neighbour `w` of `v_1` on `C_k` beyond `v_2`
  have hg : A.crossingOf (A.σ (A.σ (A.α F.f₁))) = G.u := by
    rw [crossingOf_σσ, end_f₁, hG]
  have hw := G.Ck_mem_curves_end hg
  rw [hCk] at hw
  have hw' : F.Ck ∈ Crossing.curves A (A.crossingOf (A.α (A.σ (A.σ (A.α F.f₁))))) := by
    have := A.mem_curves_end (A.σ (A.σ (A.α F.f₁)))
    rwa [curve_σσ, curve_α] at this
  have hw4 : A.crossingOf (A.α (A.σ (A.σ (A.α F.f₁)))) = F.v₄ := by
    rcases F.eq_v₂_or_v₄ hn (A.curves_eq_pair hw hw' F.Ck_ne_Cj.symm) with h | h
    · refine absurd h ?_
      have := A.crossingOf_α_σσ_ne (by omega) (A.α F.f₁)
      rwa [α_α, crossingOf_f₁] at this
    · exact h
  refine A.square hn (b := A.α F.f₁) (b' := A.σ (A.σ F.f₂)) ?_ ?_ ?_ ?_
  · rw [end_f₁, crossingOf_σσ, crossingOf_f₂]; exact F.v₁_ne_v₃ hn
  · rw [curve_α, curve_σσ, curve_f₁, curve_f₂]
  · rw [A.σ_σ_σ_σ, α_α, crossingOf_f₁, end_f₂]
  · rw [hw4, σσ_f₂, α_α, crossingOf_f₃]

/-- **`lem:fan-cons` (b)**, `v_4`: symmetric to `v_1`; then `v_4` and `v_2` have the same
neighbours `v_3`, `v_1` on `C_k`. -/
theorem v₄_not_mem_X' (hn : 4 ≤ n) : F.v₄ ∉ A.X' := by
  intro hX
  obtain ⟨-, G, hG⟩ := A.fan_lemma hn (u := F.v₄) (by rw [(A.mem_X').1 hX])
  -- the third pseudocircle of the fan at `v_4` is `C_i`
  have hCk : G.Ck = F.Ci := by
    have h1 := G.Ck_mem_curves_end (c := A.α (A.σ (A.σ F.a))) hG.symm
    rw [α_α, crossingOf_σσ_a, curves_u, mem_insert, mem_singleton] at h1
    refine h1.resolve_left fun h => G.Ck_not_mem_u ?_
    rw [hG, curves_v₄, h]; exact mem_insert_self _ _
  -- the neighbour `w` of `v_4` on `C_k` beyond `v_3`
  have hg : A.crossingOf (A.σ (A.σ F.f₃)) = G.u := by
    rw [crossingOf_σσ, crossingOf_f₃, hG]
  have hw := G.Ck_mem_curves_end hg
  rw [hCk] at hw
  have hw' : F.Ck ∈ Crossing.curves A (A.crossingOf (A.α (A.σ (A.σ F.f₃)))) := by
    have := A.mem_curves_end (A.σ (A.σ F.f₃))
    rwa [curve_σσ, curve_f₃] at this
  have hw1 : A.crossingOf (A.α (A.σ (A.σ F.f₃))) = F.v₁ := by
    rcases F.eq_v₁_or_v₃ hn (A.curves_eq_pair hw hw' F.Ck_ne_Ci.symm) with h | h
    · exact h
    · refine absurd h ?_
      have := A.crossingOf_α_σσ_ne (by omega) F.f₃
      rwa [end_f₃] at this
  refine A.square hn (b := F.f₃) (b' := F.f₁) ?_ ?_ ?_ ?_
  · rw [crossingOf_f₃, crossingOf_f₁]; exact (F.v₂_ne_v₄ hn).symm
  · rw [curve_f₃, curve_f₁]
  · rw [end_f₃, σσ_f₁, α_α, crossingOf_f₂]
  · rw [hw1, end_f₁]

/-- **`lem:fan-cons` (b)**: `v_1, v_4 ∉ X'`. -/
theorem cons_b (hn : 4 ≤ n) : F.v₁ ∉ A.X' ∧ F.v₄ ∉ A.X' :=
  ⟨F.v₁_not_mem_X' hn, F.v₄_not_mem_X' hn⟩

/-- `u' ∉ X'` as soon as `u'` has a neighbour among `v_1`, `v_3` along `C_i`: the fan at `u'`
would have third pseudocircle `C_k`, so `u` and `u'` would have the same neighbours `v_1`, `v_3`
on `C_i`. -/
theorem u'_not_mem_X'_of (hn : 4 ≤ n) {c : D} (hc : A.crossingOf c = F.u')
    (hcC : A.curve c = F.Ci) (hv : A.crossingOf (A.α c) = F.v₁ ∨ A.crossingOf (A.α c) = F.v₃) :
    F.u' ∉ A.X' := by
  intro hX
  obtain ⟨-, G, hG⟩ := A.fan_lemma hn (u := F.u') (by rw [(A.mem_X').1 hX])
  have hcurves : Crossing.curves A (A.crossingOf (A.α c)) = {F.Ci, F.Ck} := by
    rcases hv with h | h <;> rw [h]
    · exact F.curves_v₁
    · exact F.curves_v₃
  -- the third pseudocircle of the fan at `u'` is `C_k`
  have hCk : G.Ck = F.Ck := by
    have h1 := G.Ck_mem_curves_end (hc.trans hG.symm)
    rw [hcurves, mem_insert, mem_singleton] at h1
    refine h1.resolve_left fun h => G.Ck_not_mem_u ?_
    rw [hG, F.curves_u', h]; exact mem_insert_of_mem (mem_singleton_self _)
  -- the other neighbour of `u'` on `C_i`
  have hw := G.Ck_mem_curves_end (c := A.σ (A.σ c)) (by rw [crossingOf_σσ, hc, hG])
  rw [hCk] at hw
  have hw' := A.mem_curves_end (A.σ (A.σ c))
  rw [curve_σσ, hcC] at hw'
  have hne := A.crossingOf_α_σσ_ne (by omega) c
  have hu : A.crossingOf (A.σ F.a) ≠ A.crossingOf c := by
    rw [crossingOf_σ_a, hc]; exact F.u'_ne_u.symm
  rcases F.eq_v₁_or_v₃ hn (A.curves_eq_pair hw' hw F.Ck_ne_Ci.symm) with h | h <;>
    rcases hv with h' | h'
  · exact hne (h.trans h'.symm)
  · refine A.square hn (b := A.σ F.a) (b' := A.σ (A.σ c)) ?_ ?_ ?_ ?_
    · rwa [crossingOf_σσ]
    · rw [curve_σσ, hcC]; rfl
    · rw [A.σ_σ_σ_σ, h']; rfl
    · rw [h]; rfl
  · refine A.square hn (b := A.σ F.a) (b' := c) hu (by rw [hcC]; rfl) ?_ ?_
    · rw [h]; rfl
    · rw [h']; rfl
  · exact hne (h.trans h'.symm)

/-- **`lem:fan-cons` (c)** for `R`: if `R` is a triangle, its corners are `v_1, v_2, u'`, and
`u' ∉ X'`. -/
theorem cons_c_R (hn : 4 ≤ n) (h : A.IsTriangle F.R) :
    Cell.corners A F.R = {F.v₁, F.v₂, F.u'} ∧ F.u' ∉ A.X' := by
  obtain ⟨hcorners, hcurves, hne, r, hr, hrC, hrv⟩ :=
    A.far_triangle (by omega) F.isTriangle₁ h
  have hz := F.eq_u'_of hcurves hne
  refine ⟨?_, F.u'_not_mem_X'_of hn (c := r) (hr.trans hz) hrC (Or.inl ?_)⟩
  · rw [R, show A.φ F.a = F.f₁ from rfl] at *
    rw [hcorners, end_f₁, crossingOf_f₁, hz]
  · rw [hrv]; exact F.end_f₁

/-- **`lem:fan-cons` (c)** for `S`: if `S` is a triangle, its corners are `v_2, v_3, u'`, and
`u' ∉ X'`. -/
theorem cons_c_S (hn : 4 ≤ n) (h : A.IsTriangle F.S) :
    Cell.corners A F.S = {F.v₂, F.v₃, F.u'} ∧ F.u' ∉ A.X' := by
  obtain ⟨hcorners, hcurves, hne, -⟩ := A.far_triangle (by omega) F.isTriangle₂ h
  rw [curve_σσ, pair_comm] at hcurves
  rw [crossingOf_σ_a] at hne
  have hz := F.eq_u'_of hcurves hne
  refine ⟨?_, F.u'_not_mem_X'_of hn (c := A.α (A.σ (A.σ (A.α (A.σ F.a))))) hz ?_ (Or.inr ?_)⟩
  · rw [S, show A.φ (A.σ F.a) = F.f₂ from rfl] at *
    rw [hcorners, end_f₂, crossingOf_f₂, hz]
  · rw [curve_α, curve_σσ, curve_α]; rfl
  · rw [α_α, crossingOf_σσ]; rfl

/-- **`lem:fan-cons` (c)** for `R'`: if `R'` is a triangle, its corners are `v_3, v_4, u'`,
and `u' ∉ X'`. -/
theorem cons_c_R' (hn : 4 ≤ n) (h : A.IsTriangle F.R') :
    Cell.corners A F.R' = {F.v₃, F.v₄, F.u'} ∧ F.u' ∉ A.X' := by
  obtain ⟨hcorners, hcurves, hne, r, hr, hrC, hrv⟩ :=
    A.far_triangle (by omega) F.isTriangle₃ h
  rw [curve_σσ, curve_σσσ] at hcurves
  rw [crossingOf_σσ_a] at hne
  have hz := F.eq_u'_of hcurves hne
  refine ⟨?_, F.u'_not_mem_X'_of hn (c := r) (hr.trans hz) ?_ (Or.inr ?_)⟩
  · rw [R', show A.φ (A.σ (A.σ F.a)) = F.f₃ from rfl] at *
    rw [hcorners, end_f₃, crossingOf_f₃, hz]
  · rw [hrC, curve_σσσ]; rfl
  · rw [hrv]; exact F.end_f₃

/-- **`lem:fan-cons` (c)**: if one of `R`, `S`, `R'` is a triangle, its third corner (the
corner off `C_k`) is `u'`, and `u' ∉ X'`. -/
theorem cons_c (hn : 4 ≤ n) :
    (A.IsTriangle F.R → Cell.corners A F.R = {F.v₁, F.v₂, F.u'} ∧ F.u' ∉ A.X') ∧
    (A.IsTriangle F.S → Cell.corners A F.S = {F.v₂, F.v₃, F.u'} ∧ F.u' ∉ A.X') ∧
    (A.IsTriangle F.R' → Cell.corners A F.R' = {F.v₃, F.v₄, F.u'} ∧ F.u' ∉ A.X') :=
  ⟨F.cons_c_R hn, F.cons_c_S hn, F.cons_c_R' hn⟩

/-- **`lem:fan-cons` (d)**: at most one of `R`, `S`, `R'` is a triangle. -/
theorem cons_d (hn : 4 ≤ n) :
    ¬ (A.IsTriangle F.R ∧ A.IsTriangle F.S) ∧ ¬ (A.IsTriangle F.S ∧ A.IsTriangle F.R') ∧
      ¬ (A.IsTriangle F.R ∧ A.IsTriangle F.R') := by
  refine ⟨fun ⟨hR, hS⟩ => ?_, fun ⟨hS, hR'⟩ => ?_, fun ⟨hR, hR'⟩ => ?_⟩
  · -- `t v_2 = 4`
    refine A.not_four_triangles hn (b := A.α F.a) ?_ ?_ ?_ ?_
    · rw [cellOf_α_a]; exact F.isTriangle₂
    · rw [cellOf_σ_α_a]; exact F.isTriangle₁
    · rw [cellOf_σσ_α_a]; exact hR
    · rw [cellOf_σσσ_α_a]; exact hS
  · -- `t v_3 = 4`
    refine A.not_four_triangles hn (b := A.α (A.σ F.a)) ?_ ?_ ?_ ?_
    · rw [cellOf_α_σ_a]; exact F.isTriangle₃
    · rw [cellOf_σ_α_σ_a]; exact F.isTriangle₂
    · rw [cellOf_σσ_α_σ_a]; exact hS
    · rw [cellOf_σσσ_α_σ_a]; exact hR'
  · -- `u` and `u'` would have the same neighbours `v_1`, `v_3` on `C_i`
    obtain ⟨-, hc, hne, r, hr, hrC, hrv⟩ := A.far_triangle (by omega) F.isTriangle₁ hR
    obtain ⟨-, hc', hne', r', hr', hrC', hrv'⟩ := A.far_triangle (by omega) F.isTriangle₃ hR'
    rw [curve_σσ, curve_σσσ] at hc'
    rw [crossingOf_σσ_a] at hne'
    have hz := F.eq_u'_of hc hne
    have hz' := F.eq_u'_of hc' hne'
    rw [curve_σσσ] at hrC'
    rw [show A.φ F.a = F.f₁ from rfl, end_f₁] at hrv
    rw [show A.φ (A.σ (A.σ F.a)) = F.f₃ from rfl, end_f₃] at hrv'
    rcases A.eq_or_eq_σσ ((hr.trans hz).trans (hr'.trans hz').symm) (hrC.trans hrC'.symm)
      with h | h
    · subst h; exact F.v₁_ne_v₃ hn (hrv.symm.trans hrv')
    · refine A.square hn (b := A.σ F.a) (b' := r) ?_ (hrC.symm) ?_ ?_
      · rw [crossingOf_σ_a, hr, hz]; exact F.u'_ne_u.symm
      · rw [← h, hrv']; rfl
      · rw [hrv]; rfl

/-- `t v_2 = 2 + [R triangle] + [S triangle]` and `t v_3 = 2 + [S triangle] + [R' triangle]`. -/
theorem t_v₂ : A.t F.v₂ =
    2 + (if A.IsTriangle F.R then 1 else 0) + (if A.IsTriangle F.S then 1 else 0) := by
  rw [t_eq_tAngles, v₂, tAngles_crossingOf]
  simp only [InTriangle, cellOf_α_a, cellOf_σ_α_a, cellOf_σσ_α_a, cellOf_σσσ_α_a,
    ↓reduceIte, show A.IsTriangle F.T₁ from F.isTriangle₁,
    show A.IsTriangle F.T₂ from F.isTriangle₂]

theorem t_v₃ : A.t F.v₃ =
    2 + (if A.IsTriangle F.S then 1 else 0) + (if A.IsTriangle F.R' then 1 else 0) := by
  rw [t_eq_tAngles, v₃, tAngles_crossingOf]
  simp only [InTriangle, cellOf_α_σ_a, cellOf_σ_α_σ_a, cellOf_σσ_α_σ_a, cellOf_σσσ_α_σ_a,
    ↓reduceIte, show A.IsTriangle F.T₂ from F.isTriangle₂,
    show A.IsTriangle F.T₃ from F.isTriangle₃]

/-- **`lem:fan-cons` (e)**: `v_2 ∈ X'` iff `R` or `S` is a triangle, and `v_3 ∈ X'` iff `S` or
`R'` is a triangle. -/
theorem cons_e (hn : 4 ≤ n) :
    (F.v₂ ∈ A.X' ↔ A.IsTriangle F.R ∨ A.IsTriangle F.S) ∧
      (F.v₃ ∈ A.X' ↔ A.IsTriangle F.S ∨ A.IsTriangle F.R') := by
  obtain ⟨hRS, hSR', -⟩ := F.cons_d hn
  rw [mem_X', mem_X', t_v₂, t_v₃]
  constructor
  · by_cases hR : A.IsTriangle F.R <;> by_cases hS : A.IsTriangle F.S <;> simp_all
  · by_cases hS : A.IsTriangle F.S <;> by_cases hR' : A.IsTriangle F.R' <;> simp_all

end Fan

end Pca.Arrangement
