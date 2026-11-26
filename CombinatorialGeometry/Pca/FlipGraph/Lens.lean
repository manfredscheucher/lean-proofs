/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): lenses in graph language

FROS, preliminaries: "A lens in an arrangement is a bounded region in a subarrangement formed by
two intersecting pseudocircles. An arc is a contiguous subset of a pseudocircle, starting and
ending at a vertex of the arrangement. Let `Q` be (the closure of) a lens bounded by two arcs `L`
and `R`. An arc of `Q` is an arc of a pseudocircle `C` which has both endpoints on the boundary of
`Q` and whose relative interior lies in the interior of `Q`. [...] Otherwise the arc has one
endpoint on `L` and one on `R`, in this case we call the arc transversal."

Graph language (`Lens`): a set `Q` of cells; its **boundary darts** (dart with its cell in `Q` and
the cell across not in `Q`) are split into the two arcs `L` and `R`; `L` is a straight run of
darts of one curve `S` (the arc that is swept). The complement of `Q` is connected. The arcs of
`Q` (the *chords*) are the maximal straight runs of **chord darts** (both cells in `Q`); a chord
ends where the dart `σ (α y)` at the end of its last dart `y` is a boundary dart (in `L` or `R`).
`Lens.Transversal`: every chord has one end on `L` and one on `R`.

The lens of two curves (`twoLens`): `Q` = the cells on given sides of two crossing curves `C_L`,
`C_R` (one of the four regions of the subarrangement `{C_L, C_R}`), `L` / `R` its boundary darts on
`C_L` / `C_R`. FROS always use this case; the general form is also used for the first curve in the
proof of Theorem 4 (both arcs on the same curve, `doc/pca/flipgraph.md`).
-/
import Pca.FlipGraph.Region
import Pca.FlipGraph.Walk

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- A **lens** in graph language (see the module docstring). -/
structure Lens (A : Arrangement n D) where
  /-- the cells of the lens -/
  Q : A.Cell → Prop
  /-- the arc `L` (boundary darts, swept) -/
  L : D → Prop
  /-- the arc `R` (boundary darts) -/
  R : D → Prop
  /-- the curve of `L` -/
  S : Fin n
  L_curve : ∀ y, L y → A.curve y = S
  L_bd : ∀ y, L y → Q (A.cellOf y) ∧ ¬ Q (A.cellOf (A.α y))
  R_bd : ∀ y, R y → Q (A.cellOf y) ∧ ¬ Q (A.cellOf (A.α y))
  /-- every boundary dart lies on `L` or on `R` -/
  bd : ∀ y, Q (A.cellOf y) → ¬ Q (A.cellOf (A.α y)) → L y ∨ R y
  disj : ∀ y, ¬ (L y ∧ R y)
  /-- `L` is one straight run of darts of `S` -/
  L_run : ∃ (y₀ : D) (k : ℕ), ∀ y, L y ↔ ∃ i ≤ k, y = (A.straight ^ i) y₀
  /-- the complement of `Q` is connected -/
  compl_conn : ∀ f g, ¬ Q f → ¬ Q g →
    Relation.EqvGen (AdjBy A fun y => ¬ Q (A.cellOf y) ∧ ¬ Q (A.cellOf (A.α y))) f g

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- A **chord dart**: both cells of the dart lie in `Q` (a dart of an arc of `Q`). -/
def Chord (y : D) : Prop := Λ.Q (A.cellOf y) ∧ Λ.Q (A.cellOf (A.α y))

/-- A **vertex of `Q`**: a crossing all of whose darts are chord darts (a vertex in the interior
of `Q`). -/
def IsVertex (x : A.Crossing) : Prop := ∀ y ∈ x.darts, Λ.Chord y

/-- Walking forward along the chord of the chord dart `y`, the chord ends on `L` (`R` for
`EndsOn Λ.R`): after `k` further chord darts it reaches a crossing at which the dart `σ (α ·)`
is a boundary dart in the given arc. -/
def EndsOn (P : D → Prop) (y : D) : Prop :=
  ∃ k, (∀ i ≤ k, Λ.Chord ((A.straight ^ i) y)) ∧ P (A.σ (A.α ((A.straight ^ k) y)))

/-- **All arcs of `Q` are transversal**: every chord has one end on `L` and one on `R` (walking
backward along the chord of `y` is walking forward from `α y`). -/
def Transversal : Prop :=
  ∀ y, Λ.Chord y → (Λ.EndsOn Λ.L y ↔ Λ.EndsOn Λ.R (A.α y))

/-- `d` spans a **source triangle**: `d ∈ L` and the cell of `d` (inside `Q`) is a triangle whose
third corner (the apex, at the end of `φ d`) is a vertex of `Q`. Flipping it sweeps `L` over the
apex. -/
def SourceTri (d : D) : Prop :=
  Λ.L d ∧ A.IsTriangle (A.cellOf d) ∧ Λ.IsVertex (A.crossingOf (A.φ (A.φ d)))

end Lens

/-! ## The lens of two curves -/

namespace Marked

variable (M : Marked n D)

/-- The cells on the sides `pL` of `C_L` and `pR` of `C_R` (`pL`, `pR` say "inside"). -/
def TwoQ (C_L C_R : Fin n) (pL pR : Prop) (f : M.A.Cell) : Prop :=
  (M.Inside C_L f ↔ pL) ∧ (M.Inside C_R f ↔ pR)

theorem twoQ_α_of_ne {C_L C_R : Fin n} {pL pR : Prop} (y : D) (hL : M.A.curve y ≠ C_L)
    (hR : M.A.curve y ≠ C_R) :
    M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y)) ↔ M.TwoQ C_L C_R pL pR (M.A.cellOf y) := by
  unfold TwoQ
  rw [M.inside_α C_L y, M.inside_α C_R y]
  simp only [hL, hR, ne_eq, not_false_eq_true, iff_true]

theorem not_twoQ_α_of_L {C_L C_R : Fin n} {pL pR : Prop} (y : D) (hy : M.A.curve y = C_L)
    (hq : M.TwoQ C_L C_R pL pR (M.A.cellOf y)) :
    ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y)) := by
  unfold TwoQ at *
  rw [M.inside_α C_L y]
  simp only [hy, ne_eq, not_true_eq_false, iff_false]
  tauto

theorem not_twoQ_α_of_R {C_L C_R : Fin n} {pL pR : Prop} (y : D) (hy : M.A.curve y = C_R)
    (hq : M.TwoQ C_L C_R pL pR (M.A.cellOf y)) :
    ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y)) := by
  unfold TwoQ at *
  rw [M.inside_α C_R y]
  simp only [hy, ne_eq, not_true_eq_false, iff_false]
  tauto

/-- An equivalence along steps that preserve a property restricts to the cells with the
property. -/
theorem eqvGen_restrict {α : Type*} {r r' : α → α → Prop} {I : α → Prop}
    (hI : ∀ a b, r a b → (I a ↔ I b)) (hr : ∀ a b, r a b → I a → r' a b) {a b : α}
    (h : Relation.EqvGen r a b) : (I a ↔ I b) ∧ (I a → Relation.EqvGen r' a b) := by
  induction h with
  | rel a b h => exact ⟨hI a b h, fun ha => Relation.EqvGen.rel _ _ (hr a b h ha)⟩
  | refl a => exact ⟨Iff.rfl, fun _ => Relation.EqvGen.refl a⟩
  | symm a b _ ih => exact ⟨ih.1.symm, fun hb => (ih.2 (ih.1.2 hb)).symm⟩
  | trans a b c _ _ ih1 ih2 =>
    exact ⟨ih1.1.trans ih2.1, fun ha => (ih1.2 ha).trans _ _ _ (ih2.2 (ih1.1.1 ha))⟩

/-- Two distinct curves cross: some dart `y` of `C_L` has `σ y` on `C_R`. -/
theorem exists_cross_dart {C_L C_R : Fin n} (h : C_L ≠ C_R) :
    ∃ y, M.A.curve y = C_L ∧ M.A.curve (M.A.σ y) = C_R := by
  classical
  have h2 := M.A.isArrangement.intersecting C_L C_R h
  obtain ⟨x, hx⟩ := card_pos.1 (show 0 < _ by rw [h2]; norm_num)
  rw [mem_filter] at hx
  obtain ⟨y₀, rfl⟩ := x.exists_mk
  have hc : Arrangement.Crossing.curves M.A (M.A.crossingOf y₀) = {C_L, C_R} := hx.2
  rw [M.A.curves_crossingOf] at hc
  obtain ⟨y, hyL, hyR⟩ : ∃ y, M.A.curve y = C_L ∧ M.A.curve (M.A.σ y) = C_R := by
    by_cases hy : M.A.curve y₀ = C_L
    · refine ⟨y₀, hy, ?_⟩
      have : M.A.curve (M.A.σ y₀) ∈ ({C_L, C_R} : Finset (Fin n)) := by
        rw [← hc]; simp
      rcases mem_insert.1 this with h' | h'
      · exact absurd (h'.trans hy.symm) (M.A.isArrangement.curve_σ y₀)
      · exact mem_singleton.1 h'
    · have h0 : M.A.curve y₀ ∈ ({C_L, C_R} : Finset (Fin n)) := by rw [← hc]; simp
      have hR : M.A.curve y₀ = C_R := by
        rcases mem_insert.1 h0 with h' | h'
        · exact absurd h' hy
        · exact mem_singleton.1 h'
      have h1 : M.A.curve (M.A.σ y₀) = C_L := by
        have : M.A.curve (M.A.σ y₀) ∈ ({C_L, C_R} : Finset (Fin n)) := by rw [← hc]; simp
        rcases mem_insert.1 this with h' | h'
        · exact h'
        · exact absurd ((mem_singleton.1 h').trans hR.symm) (M.A.isArrangement.curve_σ y₀)
      exact ⟨M.A.σ y₀, h1, by rw [M.A.curve_σσ, hR]⟩
  exact ⟨y, hyL, hyR⟩

/-- At a crossing of two curves the four cells lie on all four combinations of sides. -/
theorem exists_cell_sides {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) :
    ∃ f : M.A.Cell, (M.Inside C_L f ↔ pL) ∧ (M.Inside C_R f ↔ pR) := by
  obtain ⟨y, hyL, hyR⟩ := M.exists_cross_dart h
  -- the cells `cellOf y`, `cellOf (σ y) = cellOf (α y)`, `cellOf (σ² y)`, `cellOf (σ³ y)`
  have e1 := M.inside_α C_L y
  have e2 := M.inside_α C_R y
  have e3 := M.inside_α C_L (M.A.σ y)
  have e4 := M.inside_α C_R (M.A.σ y)
  have e5 := M.inside_α C_L (M.A.σ (M.A.σ y))
  have e6 := M.inside_α C_R (M.A.σ (M.A.σ y))
  rw [← M.A.cellOf_σ] at e1 e2 e3 e4 e5 e6
  have c2 : M.A.curve (M.A.σ (M.A.σ y)) = C_L := by rw [M.A.curve_σσ, hyL]
  simp only [hyL, hyR, c2, ne_eq, not_true_eq_false, iff_false, not_false_eq_true, iff_true,
    h, Ne.symm h] at e1 e2 e3 e4 e5 e6
  by_cases a : (M.Inside C_L (M.A.cellOf y) ↔ pL) <;>
    by_cases b : (M.Inside C_R (M.A.cellOf y) ↔ pR)
  · exact ⟨_, a, b⟩
  · refine ⟨M.A.cellOf (M.A.σ (M.A.σ (M.A.σ y))), ?_, ?_⟩
    · rw [e5, e3, e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [e6, e4, e2]; clear e1 e2 e3 e4 e5 e6; tauto
  · refine ⟨M.A.cellOf (M.A.σ y), ?_, ?_⟩
    · rw [e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [e2]; clear e1 e2 e3 e4 e5 e6; tauto
  · refine ⟨M.A.cellOf (M.A.σ (M.A.σ y)), ?_, ?_⟩
    · rw [e3, e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [e4, e2]; clear e1 e2 e3 e4 e5 e6; tauto

theorem prop_aux1 {A B p : Prop} (h1 : ¬ A ↔ B) (h2 : A ↔ p) (h3 : B ↔ p) : False := by tauto

theorem prop_aux2 {A p : Prop} (h1 : A ↔ p) (h2 : A ↔ ¬ p) : False := by tauto

theorem prop_aux3 {A p : Prop} (h : A ↔ p) : ¬ (¬ A ↔ p) := by tauto

theorem prop_aux4 {X F p : Prop} : ((X ↔ ¬ F) ↔ p) ↔ ((X ↔ p) ↔ ¬ F) := by tauto

theorem iff_of_iff_of_iff {A B p : Prop} (h1 : A ↔ p) (h2 : B ↔ p) : A ↔ B := h1.trans h2.symm

/-- The four cells at a crossing of `C_L` and `C_R` are the cells of the four darts of `C_L`
there and at the other ends of their segments: every combination of sides is the cell of a dart
of `C_L`. -/
theorem exists_dart_sides {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) :
    ∃ y, M.A.curve y = C_L ∧ (M.Inside C_L (M.A.cellOf y) ↔ pL) ∧
      (M.Inside C_R (M.A.cellOf y) ↔ pR) := by
  obtain ⟨y, hyL, hyR⟩ := M.exists_cross_dart h
  have e1 := M.inside_α C_L y
  have e2 := M.inside_α C_R y
  have e3 := M.inside_α C_L (M.A.σ y)
  have e4 := M.inside_α C_R (M.A.σ y)
  have e5 := M.inside_α C_L (M.A.σ (M.A.σ y))
  have e6 := M.inside_α C_R (M.A.σ (M.A.σ y))
  rw [← M.A.cellOf_σ] at e1 e2 e3 e4 e5 e6
  have c2 : M.A.curve (M.A.σ (M.A.σ y)) = C_L := by rw [M.A.curve_σσ, hyL]
  simp only [hyL, hyR, c2, ne_eq, not_true_eq_false, iff_false, not_false_eq_true, iff_true,
    h, Ne.symm h] at e1 e2 e3 e4 e5 e6
  by_cases a : (M.Inside C_L (M.A.cellOf y) ↔ pL) <;>
    by_cases b : (M.Inside C_R (M.A.cellOf y) ↔ pR)
  · exact ⟨y, hyL, a, b⟩
  · refine ⟨M.A.α (M.A.σ (M.A.σ y)), by rw [M.A.curve_α, c2], ?_, ?_⟩
    · rw [← M.A.cellOf_σ, e5, e3, e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [← M.A.cellOf_σ, e6, e4, e2]; clear e1 e2 e3 e4 e5 e6; tauto
  · refine ⟨M.A.α y, by rw [M.A.curve_α, hyL], ?_, ?_⟩
    · rw [← M.A.cellOf_σ, e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [← M.A.cellOf_σ, e2]; clear e1 e2 e3 e4 e5 e6; tauto
  · refine ⟨M.A.σ (M.A.σ y), c2, ?_, ?_⟩
    · rw [e3, e1]; clear e1 e2 e3 e4 e5 e6; tauto
    · rw [e4, e2]; clear e1 e2 e3 e4 e5 e6; tauto

/-- Walking straight along a dart of `C`, the interior status of `C` does not change. -/
theorem inside_pow_of_curve {C : Fin n} {y : D} (hy : M.A.curve y = C) (i : ℕ) :
    M.Inside C (M.A.cellOf ((M.A.straight ^ i) y)) ↔ M.Inside C (M.A.cellOf y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Walk.pow_succ_apply, M.inside_straight, ih]
    have : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y))) ≠ C := by
      have := M.A.isArrangement.curve_σ (M.A.α ((M.A.straight ^ i) y))
      rwa [M.A.curve_α, Walk.curve_pow, hy] at this
    simp only [ne_eq, this, not_false_eq_true, iff_true]

/-- The arc `L` of the lens of two curves is **one straight run** of darts of `C_L` (FROS: an arc
is a contiguous subset of a pseudocircle). The darts of `C_L` with the cell on side `pL` form one
straight walk; on it, the side of `C_R` changes at the two crossings with `C_R` only, so the
darts on side `pR` form one arc (`Sweep.SConf.upper_arc` for the sweep configuration with sweep
curve `C_R`). -/
theorem twoQ_run {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) :
    ∃ (y₀ : D) (k : ℕ), ∀ y, (M.A.curve y = C_L ∧ M.TwoQ C_L C_R pL pR (M.A.cellOf y)) ↔
      ∃ i ≤ k, y = (M.A.straight ^ i) y₀ := by
  classical
  set P : D → Prop := fun y => M.A.curve y = C_L ∧ M.TwoQ C_L C_R pL pR (M.A.cellOf y) with hP
  obtain ⟨y₁, hy₁c, hy₁l, hy₁r⟩ := M.exists_dart_sides h pL pR
  obtain ⟨y₂, hy₂c, hy₂l, hy₂r⟩ := M.exists_dart_sides h pL (¬ pR)
  have hsc : M.A.straight.SameCycle y₂ y₁ := by
    rcases M.A.isArrangement.straight y₂ y₁ (hy₂c.trans hy₁c.symm) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨j, -, hj⟩ := Walk.exists_idx M.A h'
      have h1 := M.inside_pow_of_curve hy₂c j
      rw [hj, M.A.cellOf_σ] at h1
      have h2 := M.inside_α C_L (M.A.σ y₁)
      have h3 := M.inside_α C_L y₁
      have hσ : M.A.curve (M.A.σ y₁) ≠ C_L := by
        have := M.A.isArrangement.curve_σ y₁; rwa [hy₁c] at this
      rw [← M.A.cellOf_σ] at h3
      simp only [hσ, hy₁c, ne_eq, not_false_eq_true, iff_true, not_true_eq_false,
        iff_false] at h2 h3
      rw [h2, h3] at h1
      exact prop_aux1 h1 hy₁l hy₂l
  obtain ⟨j₁, -, hj₁⟩ := Walk.exists_idx M.A hsc
  have exA : ∃ a, P ((M.A.straight ^ a) y₂) := ⟨j₁, by rw [hj₁]; exact ⟨hy₁c, hy₁l, hy₁r⟩⟩
  set a := Nat.find exA with ha
  have hPa : P ((M.A.straight ^ a) y₂) := Nat.find_spec exA
  have hnP2 : ¬ P y₂ := fun hp => prop_aux2 hp.2.2 hy₂r
  have ha0 : a ≠ 0 := fun h0 => hnP2 (by rw [h0] at hPa; exact hPa)
  set y₀ := (M.A.straight ^ a) y₂ with hy₀
  have hy₀c : M.A.curve y₀ = C_L := hPa.1
  obtain ⟨t, -, ht⟩ := Walk.exists_idx M.A
    (show M.A.straight.SameCycle y₀ y₂ from ⟨-(a : ℤ), by
      rw [hy₀, ← zpow_natCast, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
        Perm.one_apply]⟩)
  have ht0 : t ≠ 0 := fun h0 => hnP2 (by rw [← ht, h0]; exact hPa)
  have exK : ∃ j, ¬ P ((M.A.straight ^ (j + 1)) y₀) :=
    ⟨t - 1, by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht0), ht]; exact hnP2⟩
  set k := Nat.find exK with hk
  have hnk : ¬ P ((M.A.straight ^ (k + 1)) y₀) := Nat.find_spec exK
  have inL : ∀ i ≤ k, P ((M.A.straight ^ i) y₀) := by
    intro i hi
    induction i with
    | zero => exact hPa
    | succ i _ => exact not_not.1 (Nat.find_min exK (by omega))
  -- the sweep configuration with sweep curve `C_R`, upper side the side of `y₀`
  obtain ⟨s, hs⟩ := M.A.exists_isSide C_R
  obtain ⟨yR, hyR, hyb⟩ := M.A.exists_dart_on_side hs (s (M.A.cellOf y₀))
  set Γ := sconfOf M.A C_R s hs (s (M.A.cellOf y₀)) yR hyR hyb with hΓ
  have key : ∀ a b c : ZMod 2, ((a ≠ c) ↔ (b ≠ c)) → a = b := by decide
  have abP : ∀ d, M.A.curve d = C_L → (M.Inside C_L (M.A.cellOf d) ↔ pL) → (Γ.Above d ↔ P d) := by
    intro d hd hdl
    rw [hΓ, sconfOf_above]
    have hr := M.inside_iff hs (M.A.cellOf d)
    have hr0 := M.inside_iff hs (M.A.cellOf y₀)
    have hy0r := hPa.2.2
    constructor
    · rintro ⟨-, hb⟩
      refine ⟨hd, hdl, ?_⟩
      rw [hr, hb, ← hr0]; exact hy0r
    · rintro ⟨-, -, hdr⟩
      refine ⟨by rw [hd]; exact h, key _ _ (s M.z) ?_⟩
      rw [← hr, ← hr0]; exact iff_of_iff_of_iff hdr hy0r
  have hside : ∀ d i, M.A.curve d = C_L → (M.Inside C_L (M.A.cellOf d) ↔ pL) →
      (M.Inside C_L (M.A.cellOf ((M.A.straight ^ i) d)) ↔ pL) := fun d i hd hdl => by
    rw [M.inside_pow_of_curve hd]; exact hdl
  have hcurve : ∀ d (i : ℕ), M.A.curve d = C_L → M.A.curve ((M.A.straight ^ i) d) = C_L :=
    fun d i hd => by rw [Walk.curve_pow, hd]
  have hy₀l : M.Inside C_L (M.A.cellOf y₀) ↔ pL := hPa.2.1
  refine ⟨y₀, k, fun e => ⟨fun he => ?_, ?_⟩⟩
  · have hAe : Γ.Above e := (abP e he.1 he.2.1).2 he
    have hA0 : Γ.Above y₀ := (abP y₀ hy₀c hy₀l).2 hPa
    have hαe : ¬ (M.Inside C_L (M.A.cellOf (M.A.α e)) ↔ pL) := by
      rw [M.inside_α]; simp only [he.1, ne_eq, not_true_eq_false, iff_false]
      exact prop_aux3 he.2.1
    rcases Sweep.SConf.upper_arc hA0 hAe (by rw [hΓ]; exact hy₀c.trans he.1.symm) with
      ⟨t, hall, hte⟩ | ⟨t, hall, hte⟩ | ⟨t, -, hte⟩ | ⟨t, -, hte⟩
    · rw [hΓ, sconfOf_straight] at hall hte
      refine ⟨t, ?_, hte.symm⟩
      by_contra hc
      exact hnk ((abP _ (hcurve _ _ hy₀c) (hside _ _ hy₀c hy₀l)).1 (hall (k + 1) (by omega)))
    · rw [hΓ, sconfOf_straight] at hall hte
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, pow_zero, Perm.one_apply] at hte
        exact ⟨0, Nat.zero_le _, by rw [pow_zero, Perm.one_apply, hte]⟩
      · exfalso
        have hPt : P ((M.A.straight ^ (t - 1)) e) :=
          (abP _ (hcurve _ _ he.1) (hside _ _ he.1 he.2.1)).1 (hall (t - 1) (by omega))
        have heq : (M.A.straight ^ (t - 1)) e = (M.A.straight ^ (a - 1)) y₂ := by
          apply M.A.straight.injective
          rw [← Walk.pow_succ_apply, ← Walk.pow_succ_apply, Nat.sub_add_cancel h0,
            Nat.sub_add_cancel (Nat.pos_of_ne_zero ha0), hte]
        rw [heq] at hPt
        exact Nat.find_min exA (show a - 1 < a by omega) hPt
    · change (M.A.straight ^ t) y₀ = M.A.α e at hte
      exact absurd (by rw [← hte]; exact hside _ _ hy₀c hy₀l) hαe
    · change (M.A.straight ^ t) (M.A.α e) = y₀ at hte
      have := M.inside_pow_of_curve (show M.A.curve (M.A.α e) = C_L by rw [M.A.curve_α, he.1]) t
      rw [hte] at this
      exact absurd (this.symm.trans hy₀l) hαe
  · rintro ⟨i, hi, rfl⟩
    exact inL i hi

/-- Cells outside the lens on the same side of one of its curves are connected outside the lens. -/
theorem compl_conn_aux {C_L C_R : Fin n} {pL pR : Prop} (C : Fin n) (p : Prop)
    (hC : ∀ f, ¬ (M.Inside C f ↔ p) → ¬ M.TwoQ C_L C_R pL pR f) {f g : M.A.Cell}
    (hf : ¬ (M.Inside C f ↔ p)) (hg : ¬ (M.Inside C g ↔ p)) :
    Relation.EqvGen (AdjBy M.A fun y => ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf y) ∧
      ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y))) f g := by
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  have hfg : s f = s g := by
    have h1 := M.inside_iff hs f
    have h2 := M.inside_iff hs g
    have key : ∀ a b c : ZMod 2, ((a ≠ c) ↔ (b ≠ c)) → a = b := by decide
    exact key _ _ (s M.z) (by rw [← h1, ← h2]; tauto)
  have hI : ∀ a b, AdjBy M.A (fun y => M.A.curve y ≠ C) a b →
      (¬ (M.Inside C a ↔ p) ↔ ¬ (M.Inside C b ↔ p)) := by
    rintro a b ⟨y, hy, rfl, rfl⟩
    rw [M.inside_α C y]
    simp only [hy, ne_eq, not_false_eq_true, iff_true]
  refine (eqvGen_restrict hI (fun a b hab ha => ?_) (side_connected hs hfg)).2 hf
  obtain ⟨y, hy, rfl, rfl⟩ := hab
  exact ⟨y, ⟨hC _ ha, hC _ ((hI _ _ ⟨y, hy, rfl, rfl⟩).1 ha)⟩, rfl, rfl⟩

/-- **The lens of two curves**: the region `TwoQ` of the subarrangement `{C_L, C_R}`, bounded by
its darts on `C_L` (the arc `L`) and on `C_R` (the arc `R`). -/
noncomputable def twoLens {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) : Lens M.A where
  Q := M.TwoQ C_L C_R pL pR
  L := fun y => M.A.curve y = C_L ∧ M.TwoQ C_L C_R pL pR (M.A.cellOf y)
  R := fun y => M.A.curve y = C_R ∧ M.TwoQ C_L C_R pL pR (M.A.cellOf y)
  S := C_L
  L_curve := fun _ hy => hy.1
  L_bd := fun y hy => ⟨hy.2, M.not_twoQ_α_of_L y hy.1 hy.2⟩
  R_bd := fun y hy => ⟨hy.2, M.not_twoQ_α_of_R y hy.1 hy.2⟩
  bd := fun y hq hq' => by
    by_cases hL : M.A.curve y = C_L
    · exact Or.inl ⟨hL, hq⟩
    by_cases hR : M.A.curve y = C_R
    · exact Or.inr ⟨hR, hq⟩
    exact absurd ((M.twoQ_α_of_ne y hL hR).2 hq) hq'
  disj := fun _ hy => h (hy.1.1.symm.trans hy.2.1)
  L_run := M.twoQ_run h pL pR
  compl_conn := fun f g hf hg => by
    obtain ⟨h₀, h₁, h₂⟩ := M.exists_cell_sides h (¬ pL) (¬ pR)
    have hL : ∀ f, ¬ (M.Inside C_L f ↔ pL) → ¬ M.TwoQ C_L C_R pL pR f := fun f hf hq => hf hq.1
    have hR : ∀ f, ¬ (M.Inside C_R f ↔ pR) → ¬ M.TwoQ C_L C_R pL pR f := fun f hf hq => hf hq.2
    have hub : ∀ f, ¬ M.TwoQ C_L C_R pL pR f → Relation.EqvGen (AdjBy M.A fun y =>
        ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf y) ∧
        ¬ M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y))) f h₀ := by
      intro f hf
      by_cases hfL : M.Inside C_L f ↔ pL
      · have hfR : ¬ (M.Inside C_R f ↔ pR) := fun hfR => hf ⟨hfL, hfR⟩
        exact M.compl_conn_aux C_R pR hR hfR (by tauto)
      · exact M.compl_conn_aux C_L pL hL hfL (by tauto)
    exact (hub f hf).trans _ _ _ (hub g hg).symm

/-- The crossing `x` lies in the interior of `C` (all its cells do; for `x` not on `C` the four
cells at `x` are on the same side of `C`). -/
def CrossInside (C : Fin n) (x : M.A.Crossing) : Prop :=
  ∀ y ∈ x.darts, M.Inside C (M.A.cellOf y)

/-- A crossing not on `C` lies inside `C` iff one of its cells does. -/
theorem crossInside_iff {C : Fin n} {y : D}
    (hx : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y)) :
    M.CrossInside C (M.A.crossingOf y) ↔ M.Inside C (M.A.cellOf y) := by
  have hc : ∀ w, M.A.crossingOf w = M.A.crossingOf y → M.A.curve w ≠ C := fun w hw h =>
    hx (by rw [← hw, ← h]; exact M.A.mem_curves_crossingOf w)
  have step : ∀ w, M.A.crossingOf w = M.A.crossingOf y →
      (M.Inside C (M.A.cellOf (M.A.σ w)) ↔ M.Inside C (M.A.cellOf w)) := fun w hw => by
    rw [M.A.cellOf_σ, M.inside_α C w]; simp only [hc w hw, ne_eq, not_false_eq_true, iff_true]
  have h1 : M.A.crossingOf (M.A.σ y) = M.A.crossingOf y := M.A.crossingOf_σ y
  have h2 : M.A.crossingOf (M.A.σ (M.A.σ y)) = M.A.crossingOf y := M.A.crossingOf_σσ y
  constructor
  · intro h; exact h y (Orbit.mem_darts.2 rfl)
  · intro h w hw
    rw [Orbit.mem_darts] at hw
    change M.A.crossingOf w = M.A.crossingOf y at hw
    rcases List.mem_cons.1 ((M.A.crossingOf_eq_iff).1 hw.symm) with rfl | hw'
    · exact h
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact (step y rfl).2 h
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact (step _ h1).2 ((step y rfl).2 h)
    · rcases List.mem_singleton.1 hw' with rfl
      exact (step _ h2).2 ((step _ h1).2 ((step y rfl).2 h))

/-- **Crossing form of transversality** for the lens of two curves: every other curve `c` either
crosses `C_L` only on `L` and `C_R` only on `R`, or it meets neither arc (then it does not enter
the lens). Implies `Transversal` (`twoLens_transversal`). -/
def TwoTransversal (C_L C_R : Fin n) (pL pR : Prop) : Prop :=
  ∀ c : Fin n, c ≠ C_L → c ≠ C_R →
    ((∀ x : M.A.Crossing, Arrangement.Crossing.curves M.A x = {c, C_L} → (M.CrossInside C_R x ↔ pR)) ∧
      (∀ x : M.A.Crossing, Arrangement.Crossing.curves M.A x = {c, C_R} → (M.CrossInside C_L x ↔ pL))) ∨
    ((∀ x : M.A.Crossing, Arrangement.Crossing.curves M.A x = {c, C_L} → ¬ (M.CrossInside C_R x ↔ pR)) ∧
      (∀ x : M.A.Crossing, Arrangement.Crossing.curves M.A x = {c, C_R} → ¬ (M.CrossInside C_L x ↔ pL)))

theorem twoLens_transversal {C_L C_R : Fin n} (h : C_L ≠ C_R) {pL pR : Prop}
    (ht : M.TwoTransversal C_L C_R pL pR) : (M.twoLens h pL pR).Transversal := by
  classical
  rintro y ⟨hq, hq'⟩
  change M.TwoQ C_L C_R pL pR (M.A.cellOf y) at hq
  change M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α y)) at hq'
  have hcL : M.A.curve y ≠ C_L := fun hc => M.not_twoQ_α_of_L y hc hq hq'
  have hcR : M.A.curve y ≠ C_R := fun hc => M.not_twoQ_α_of_R y hc hq hq'
  -- the walk of `y` (indexed by `ℤ`) and the four sequences
  set w : ℤ → D := fun i => (M.A.straight ^ i) y with hw
  set p := period M.A.straight y with hp
  set fl : ℤ → Prop := fun i => M.A.curve (M.A.σ (M.A.α (w i))) = C_L with hfl
  set fr : ℤ → Prop := fun i => M.A.curve (M.A.σ (M.A.α (w i))) = C_R with hfr
  set l : ℤ → Prop := fun i => M.Inside C_L (M.A.cellOf (w i)) ↔ pL with hl
  set r : ℤ → Prop := fun i => M.Inside C_R (M.A.cellOf (w i)) ↔ pR with hr
  have wc : ∀ i, M.A.curve (w i) = M.A.curve y := fun i => Walk.curve_zpow M.A y i
  have wp : ∀ i : ℤ, w (i + p) = w i := fun i => Walk.zpow_add_period M.A y i
  have ws : ∀ i, w (i + 1) = M.A.straight (w i) := fun i => by
    simp only [hw]; rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
  have wn : ∀ i : ℕ, w i = (M.A.straight ^ i) y := fun i => by simp only [hw, zpow_natCast]
  have wa : ∀ i : ℕ, (M.A.straight ^ i) (M.A.α y) = M.A.α (w (-i)) := fun i => by
    rw [← zpow_natCast, Walk.zpow_α]
  have hQα : ∀ i, M.TwoQ C_L C_R pL pR (M.A.cellOf (M.A.α (w i))) ↔
      M.TwoQ C_L C_R pL pR (M.A.cellOf (w i)) := fun i =>
    M.twoQ_α_of_ne _ (by rw [wc]; exact hcL) (by rw [wc]; exact hcR)
  have hcs : ∀ i, M.A.curve (M.A.σ (w (i + 1))) = M.A.curve (M.A.σ (M.A.α (w i))) := fun i => by
    rw [ws, M.A.straight_apply, M.A.curve_σσσ]
  have pfl : ∀ i, fl (i + p) ↔ fl i := fun i => by simp only [hfl]; rw [wp]
  have pfr : ∀ i, fr (i + p) ↔ fr i := fun i => by simp only [hfr]; rw [wp]
  have pl : ∀ i, l (i + p) ↔ l i := fun i => by simp only [hl]; rw [wp]
  have pr : ∀ i, r (i + p) ↔ r i := fun i => by simp only [hr]; rw [wp]
  have sl : ∀ i, l (i + 1) ↔ (l i ↔ ¬ fl i) := fun i => by
    simp only [hl, hfl]; rw [ws, M.inside_straight]; exact prop_aux4
  have sr : ∀ i, r (i + 1) ↔ (r i ↔ ¬ fr i) := fun i => by
    simp only [hr, hfr]; rw [ws, M.inside_straight]; exact prop_aux4
  have hdis : ∀ i, ¬ (fl i ∧ fr i) := fun i ⟨a, b⟩ => h (a.symm.trans b)
  have cF : ∀ (C : Fin n) [DecidablePred fun i : ℕ => M.A.curve (M.A.σ (M.A.α (w i))) = C],
      M.A.curve y ≠ C →
      ((range p).filter (fun i : ℕ => M.A.curve (M.A.σ (M.A.α (w i))) = C)).card = 2 := by
    intro C _ hC
    rw [← Walk.card_flipsOn M.A hC]
    congr 1
    ext i
    rw [mem_filter, Walk.mem_flipsOn, mem_range, wn]
  have ex : ∃ k : ℕ, fl k ∨ fr k := by
    obtain ⟨i, hi⟩ := card_pos.1 (show 0 < (Walk.flipsOn M.A C_L y).card by
      rw [Walk.card_flipsOn M.A hcL]; norm_num)
    rw [Walk.mem_flipsOn] at hi
    exact ⟨i, Or.inl (by simp only [hfl]; rw [wn]; exact hi.2)⟩
  -- the crossing at the end of `w i`
  have endX : ∀ i (C : Fin n), M.A.curve (M.A.σ (M.A.α (w i))) = C →
      Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (w i))) = {M.A.curve y, C} :=
    fun i C hi => by rw [M.A.curves_crossingOf, M.A.curve_α, wc, hi]
  have endIn : ∀ i (C C' : Fin n), M.A.curve (M.A.σ (M.A.α (w i))) = C → C' ≠ C →
      M.A.curve y ≠ C' → (M.CrossInside C' (M.A.crossingOf (M.A.α (w i))) ↔
        M.Inside C' (M.A.cellOf (w i))) := fun i C C' hi hC' hy => by
    have hn : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (w i))) := by
      rw [endX i C hi, mem_insert, mem_singleton]
      rintro (e | e)
      · exact hy e.symm
      · exact hC' e
    rw [M.crossInside_iff hn, M.inside_α]
    simp only [wc, ne_eq, hy, not_false_eq_true, iff_true]
  -- translating the two ends of the chord
  have eL : (M.twoLens h pL pR).EndsOn (M.twoLens h pL pR).L y ↔
      ∃ k : ℕ, (∀ i ≤ k, l i ∧ r i) ∧ fl k := by
    constructor
    · rintro ⟨k, hch, hL⟩
      refine ⟨k, fun i hi => ?_, ?_⟩
      · have := (hch i hi).1; rw [← wn] at this; exact this
      · have := hL.1; rw [← wn] at this; exact this
    · rintro ⟨k, hQ, hk⟩
      refine ⟨k, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [← wn]; exact hQ i hi
      · rw [← wn]; exact (hQα i).2 (hQ i hi)
      · rw [← wn]; exact hk
      · show M.TwoQ C_L C_R pL pR _
        rw [M.A.cellOf_σ, M.A.α_α, ← wn]; exact hQ k le_rfl
  have eR : (M.twoLens h pL pR).EndsOn (M.twoLens h pL pR).R (M.A.α y) ↔
      ∃ j : ℕ, (∀ i ≤ j, l (-i) ∧ r (-i)) ∧ fr (-j - 1) := by
    constructor
    · rintro ⟨j, hch, hR⟩
      refine ⟨j, fun i hi => ?_, ?_⟩
      · have := (hch i hi).2; rw [wa, M.A.α_α] at this; exact this
      · have := hR.1; rw [wa, M.A.α_α, show -(j : ℤ) = (-j - 1) + 1 by ring, hcs] at this
        exact this
    · rintro ⟨j, hQ, hj⟩
      refine ⟨j, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [wa]; exact (hQα _).2 (hQ i hi)
      · rw [wa, M.A.α_α]; exact hQ i hi
      · rw [wa, M.A.α_α, show -(j : ℤ) = (-j - 1) + 1 by ring, hcs]; exact hj
      · show M.TwoQ C_L C_R pL pR _
        rw [wa, M.A.α_α, M.A.cellOf_σ]; exact (hQα _).2 (hQ j le_rfl)
  rw [eL, eR]
  rcases ht (M.A.curve y) hcL hcR with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
  · refine cyc_ends (period_pos _ _) pfl pfr pl pr sl sr hdis (cF C_L hcL) (cF C_R hcR)
      (fun i hi => ?_) (fun i hi => ?_) hq
    · have := hA1 _ (endX i C_L hi)
      rwa [endIn i C_L C_R hi h.symm hcR] at this
    · have := hA2 _ (endX i C_R hi)
      rwa [endIn i C_R C_L hi h hcL] at this
  · exfalso
    refine cyc_none sl sr ex (fun i hi => ?_) (fun i hi => ?_) hq
    · have := hB1 _ (endX i C_L hi)
      rwa [endIn i C_L C_R hi h.symm hcR] at this
    · have := hB2 _ (endX i C_R hi)
      rwa [endIn i C_R C_L hi h hcL] at this

end Marked

end Pca.FlipGraph
