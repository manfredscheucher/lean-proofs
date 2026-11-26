/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: the three moves (package M, not needed for `sweepFirstMove`)

A sweep step is a triangle flip or a digon flip (collapse or create), applied to a cell with a
side on `S`:

* **triangle flip** (SH operation 2, "passing an empty triangle", p. 315): the triangle above the
  finite edge of `d` is flipped with the existing flip of `Pca/Flip.lean` (same darts, `σ`,
  `curve` unchanged, `α' = ρ α ρ`, `ρ = swapAlong straight (sideDarts T)`). The triangle ends up
  below `S`; the apex `v` is no longer above; `γ(i)` and `γ(i + 1)` exchange their order on `S`.
* **digon collapse** (SH operation 3, "passing an empty hump", p. 315): `S` and the curve `γ(i)`
  forming the digon above the finite edge of `d` stop crossing at `i` and `i + 1`. The eight darts
  at the two corners are deleted, the three segments of `S` and of `γ(i)` at the digon are joined
  (as in a removal, `Piece`). Cells: the digon disappears (merges with the cell below `[i, i+1]`),
  the cell above the hump loses the corners `i`, `i + 1`, the two cells below `S` beside the digon
  merge. Caveat: if `γ(i)` crosses only `S`, the result is disconnected (two disjoint curves), which
  the dart model cannot represent.
* **digon create** (SH operation 1, "taking a loop", p. 315): inverse of the collapse; `S` is
  pushed across a segment of a curve `γ` that does not intersect the sweep, visible from an edge of
  `S`, creating two crossings and a digon below `S`. Caveat: for a curve that reaches `∞` (crosses
  `S` in the ∞-arc) the result crosses `S` four times on the sphere; SH's plane picture allows this
  (`∞` is not a crossing there).

Only the predicates (`EmptyTriAt`, `EmptyHumpAt`, `CanTakeLoop`, `Pca/Sweep/Basic.lean`) enter
SH's proof and the final theorem; the moves themselves are recorded here for completeness.
-/
import Pca.Sweep.Removal
import Pca.Flip
import Pca.Sweep.M_FlipCount
import Pca.Sweep.M_CollapseArc

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- The darts of the sides of the cell `T` (darts of `T` and their reverses). -/
def sideDarts (T : Γ.Cell) : Finset D :=
  univ.filter (fun y => Γ.cellOf y = T ∨ Γ.cellOf (Γ.α y) = T)

/-- `Γ'` is the **triangle flip** of `Γ` at the empty triangle above the finite edge of `d`. -/
structure IsTriFlip (d : D) (Γ' : SConf n D) : Prop where
  tri : Γ.EmptyTriAt d
  σ_eq : Γ'.σ = Γ.σ
  curve_eq : Γ'.curve = Γ.curve
  S_eq : Γ'.S = Γ.S
  α_eq : ∀ y, Γ'.α y = swapAlong Γ.straight (Γ.sideDarts (Γ.upperCell d))
    (Γ.α (swapAlong Γ.straight (Γ.sideDarts (Γ.upperCell d)) y))
  infArc_eq : Γ'.infStart = Γ.infStart.map (swapAlong Γ.straight (Γ.sideDarts (Γ.upperCell d))) ∧
    Γ'.infLen = Γ.infLen
  /-- the flipped triangle (the cell of `σ² (α d)`) lies below `S` -/
  side_tri : Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) (Γ.σ (Γ.σ (Γ.α d)))) = 0
  /-- darts away from the corners of the triangle keep the side of their cell -/
  side_far : ∀ y, (∀ e ∈ (Γ.upperCell d).darts, Γ.crossingOf e ≠ Γ.crossingOf y) →
    Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) y) = Γ.side (Γ.cellOf y)

/-- `Γ'` (dart embedding `ι`) is the **digon collapse** of `Γ` at the empty hump above the finite
edge of `d`: the two corners of the digon are deleted and the segments through them joined. -/
structure IsDigonCollapse (d : D) {D' : Type u} [Fintype D'] [DecidableEq D'] (Γ' : SConf n D')
    (ι : D' → D) : Prop where
  hump : Γ.EmptyHumpAt d
  inj : Function.Injective ι
  range : ∀ y, (∃ y', ι y' = y) ↔ ∀ e ∈ (Γ.upperCell d).darts, Γ.crossingOf y ≠ Γ.crossingOf e
  curve : ∀ y', Γ'.curve y' = Γ.curve (ι y')
  S : Γ'.S = Γ.S
  σ : ∀ y', ι (Γ'.σ y') = Γ.σ (ι y')
  α : ∀ y', ∃ k : ℕ, (∀ i < k, ∃ e ∈ (Γ.upperCell d).darts,
      Γ.crossingOf e = Γ.crossingOf (Γ.α ((Γ.straight ^ i) (ι y')))) ∧
    ι (Γ'.α y') = Γ.α ((Γ.straight ^ k) (ι y'))
  side : ∀ y', Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) y') = Γ.side (Γ.cellOf (ι y'))

/-- `Γ'` is a **digon create** of `Γ` (taking a loop) iff `Γ` is the digon collapse of `Γ'` at the
new digon, which lies below the old sweep. Stated as the inverse relation. -/
def IsDigonCreate {D' : Type u} [Fintype D'] [DecidableEq D'] (Γ' : SConf n D') : Prop :=
  ∃ (d' : D') (ι : D → D'), Γ'.IsDigonCollapse d' Γ ι

/-- `y` survives the digon collapse at `d`: it is not at a corner of the digon. -/
def CollapseKept (d y : D) : Prop := ∀ e ∈ (Γ.upperCell d).darts, Γ.crossingOf y ≠ Γ.crossingOf e

/-- One step of the map after the digon collapse at `d`, in terms of `Γ`: between surviving
darts, `σ`, or a joined segment (go straight through the deleted corners, as in `IsDigonCollapse`). -/
def CollapseStep (d a b : D) : Prop :=
  Γ.CollapseKept d a ∧ Γ.CollapseKept d b ∧ (b = Γ.σ a ∨
    ∃ k, (∀ i < k, ¬ Γ.CollapseKept d (Γ.α ((Γ.straight ^ i) a))) ∧ b = Γ.α ((Γ.straight ^ k) a))

/-- The map after the digon collapse at `d` is connected. -/
def CollapseConnected (d : D) : Prop :=
  ∀ a b, Γ.CollapseKept d a → Γ.CollapseKept d b → Relation.EqvGen (Γ.CollapseStep d) a b

variable {Γ}

theorem collapseKept_iff {d : D} (h : Γ.EmptyHumpAt d) {y : D} :
    Γ.CollapseKept d y ↔ Γ.mKept d y := by
  have hmem : ∀ e, e ∈ (Γ.upperCell d).darts ↔ e = Γ.α d ∨ e = Γ.σ d := by
    intro e
    have hp : period Γ.φ (Γ.α d) = 2 := by rw [← m_size_cellOf]; exact h.2
    rw [upperCell, Orbit.mem_darts, ← cellOf, m_cellOf_eq_iff, Perm.sameCycle_comm,
      ← mem_orbitList]
    simp [orbitList, hp, List.range_succ, m_φ_α]
  constructor
  · intro H
    exact ⟨fun hx => H (Γ.σ d) ((hmem _).2 (Or.inr rfl)) (hx.trans (Γ.m_crossingOf_σ d).symm),
      H (Γ.α d) ((hmem _).2 (Or.inl rfl))⟩
  · intro hk e he
    rcases (hmem e).1 he with rfl | rfl
    · exact hk.2
    · rw [m_crossingOf_σ]; exact hk.1

/-- Passing an empty triangle is possible: the flip exists (port of `Arrangement.flip`). -/
theorem exists_triFlip {d : D} (h : Γ.EmptyTriAt d) : ∃ Γ', Γ.IsTriFlip d Γ' := by
  refine ⟨Γ.mFlip h, ⟨h, rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl⟩, ?_, ?_⟩⟩
  · show mSide' (m_mTri h) (Orbit.mk _ (Γ.σ (Γ.σ (Γ.α d)))) = 0
    rw [mSide'_σσ, m_side_upper h]; decide
  · intro y hfar
    apply mSide'_of_not_corner
    rintro ⟨e, he, hey⟩
    exact hfar e (Orbit.mem_darts.2 he) hey

/-- The flip passes the apex: one vertex less above the sweep, the vertices on the sweep stay. -/
theorem IsTriFlip.numVertices {d : D} {Γ' : SConf n D} (h : Γ.IsTriFlip d Γ') :
    Γ'.numVertices + 1 = Γ.numVertices :=
  m_flip_numVertices h.tri Γ' h.σ_eq h.curve_eq h.S_eq h.α_eq h.infArc_eq h.side_tri
    (fun y hy => h.side_far y (fun e he hey => hy ⟨e, Orbit.mem_darts.1 he, hey⟩))

/-- **Passing an empty hump** (the digon collapse), with the exact validity hypotheses:
`γ(i) = curve (σ d)` crosses a curve other than `S` (`hc`), `S`
crosses a curve other than `γ(i)` (`hS`), and the map after the collapse is connected (`hconn`).
Without `hS` every dart of `S` is deleted; without `hconn` the result is two separate pieces;
neither is a sweep configuration. -/
theorem exists_digonCollapse_of {d : D} (h : Γ.EmptyHumpAt d)
    (hc : ∃ x : Γ.Crossing, ¬ Γ.OnSweep x ∧ ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧
      Γ.crossingOf e = x)
    (hS : ∃ x : Γ.Crossing, ¬ Γ.OnCurve (Γ.curve (Γ.σ d)) x ∧ ∃ e, Γ.curve e = Γ.S ∧
      Γ.crossingOf e = x)
    (hconn : Γ.CollapseConnected d) :
    ∃ (D' : Type u) (_ : Fintype D') (_ : DecidableEq D') (Γ' : SConf n D') (ι : D' → D),
      Γ.IsDigonCollapse d Γ' ι := by
  have hdarts : ∀ {x : Γ.Crossing} {e : D}, Γ.crossingOf e = x → e ∈ x.darts :=
    fun he => Orbit.mem_darts.2 he
  have hc' : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e := by
    obtain ⟨x, hx, e, he, rfl⟩ := hc
    refine ⟨e, he, m_kept_of_not_onCurve h fun e' he' hS' => hx ?_⟩
    exact mem_image.2 ⟨e', hdarts he', hS'⟩
  have hS' : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e := by
    obtain ⟨x, hx, e, he, rfl⟩ := hS
    refine ⟨e, he, m_kept_of_not_onCurve_γ h fun e' he' hγ => hx ?_⟩
    exact mem_image.2 ⟨e', hdarts he', hγ⟩
  have hstep : Γ.CollapseStep d = Γ.MStep d := by
    funext a b
    simp only [CollapseStep, MStep, collapseKept_iff h]
  have hconn' : ∀ a b, Γ.mKept d a → Γ.mKept d b → Relation.EqvGen (Γ.MStep d) a b := by
    intro a b ha hb
    rw [← hstep]
    exact hconn a b ((collapseKept_iff h).2 ha) ((collapseKept_iff h).2 hb)
  refine ⟨Γ.MK d, inferInstance, inferInstance, mCollapse h hS' hc' hconn', Subtype.val,
    ⟨h, Subtype.val_injective, fun y => ?_, fun _ => rfl, rfl, fun _ => rfl, fun y' => ?_,
      fun _ => rfl⟩⟩
  · rw [show (∀ e ∈ (Γ.upperCell d).darts, Γ.crossingOf y ≠ Γ.crossingOf e) ↔ Γ.mKept d y from
      collapseKept_iff h]
    exact ⟨fun ⟨y', hy'⟩ => hy' ▸ y'.2, fun hk => ⟨⟨y, hk⟩, rfl⟩⟩
  · obtain ⟨k, hk, he⟩ := m_collapse_α_join h hS' hc' hconn' y'
    refine ⟨k, fun i hi => ?_, he⟩
    have := hk i hi
    rw [← collapseKept_iff h, CollapseKept] at this
    push Not at this
    obtain ⟨e, he', hx⟩ := this
    exact ⟨e, he', hx.symm⟩

end SConf

end Pca.Sweep
