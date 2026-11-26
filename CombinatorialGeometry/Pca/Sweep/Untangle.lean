/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: untangling a crossing (package U)

SH Lemma 3.9, Case 1 (p. 320): "We can form a new arrangement `Γ'` without the vertex `v` by
untangling the crossing of curves `γ(i)` and `γ(i+1)` as pictured; essentially, we switch triangle
legs `⟨i, v⟩` and `⟨i + 1, v⟩`." Case 2 (p. 321) does the same. Figure 7: "two faces, marked by
minus signs, lose a vertex, one gains a vertex, and the face bounded by `[i, i + 1]` is unchanged".

In the dart model: `v = crossingOf a` is a vertex above the sweep, the four cells at `v` are
`B = cellOf a` (between the legs, below `v`), `L = cellOf (σ a)`, `T = cellOf (σ² a)` (above `v`)
and `R = cellOf (σ³ a)`. Smoothing `v` so that the legs are exchanged deletes the four darts at `v`
and joins the four segments at `v` in the two pairs that merge `B` and `T` into one cell; `L` and
`R` lose the corner `v`. Upper side: every other cell above `S` keeps its darts.

On the sphere the smoothing alone joins the two closed curves `γ(i)`, `γ(i+1)` into one curve that
crosses `S` four times; to stay in the class the lower side is redrawn (SH Lemma 3.5, in the form of
`Pca/Sweep/Lower.lean`: chords below `S` joining the ends of the new upper arcs, Lemma 3.12's
argument). `Untangle Γ a` records the result by the correspondence `ψ` of the cells above `S`.
Existence is stated where SH use it (`L39Case1.lean`, `L39Case2.lean`), under the hypotheses SH
give there for the two-intersection property.
-/
import Pca.Sweep.Lower
import Pca.Sweep.U_Main
import Pca.Sweep.U_GK

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- The result of untangling the vertex `crossingOf a` (above the sweep), exchanging the legs, so
that the cells `B = cellOf a` and `T = cellOf (σ² a)` merge. -/
structure Untangle (a : D) where
  n' : ℕ
  D' : Type u
  [fin : Fintype D']
  [dec : DecidableEq D']
  Γ' : SConf n' D'
  /-- the correspondence of the cells above the sweep -/
  ψ : Γ.Cell → Γ'.Cell
  up : ∀ f, Γ.Up f → Γ'.Up (ψ f)
  surj : ∀ f', Γ'.Up f' → ∃ f, Γ.Up f ∧ ψ f = f'
  merge : ψ (Γ.cellOf a) = ψ (Γ.cellOf (Γ.σ (Γ.σ a)))
  inj : ∀ f g, Γ.Up f → Γ.Up g → ψ f = ψ g → f = g ∨
    ({f, g} : Finset Γ.Cell) = {Γ.cellOf a, Γ.cellOf (Γ.σ (Γ.σ a))}
  size_merge : (ψ (Γ.cellOf a)).size + 2 =
    (Γ.cellOf a).size + (Γ.cellOf (Γ.σ (Γ.σ a))).size
  size_L : (ψ (Γ.cellOf (Γ.σ a))).size + 1 = (Γ.cellOf (Γ.σ a)).size
  size_R : (ψ (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a))))).size + 1 = (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a)))).size
  size_other : ∀ f, Γ.Up f → (∀ e ∈ f.darts, Γ.crossingOf e ≠ Γ.crossingOf a) →
    (ψ f).size = f.size
  /-- the finite edges of the sweep and the cells above them correspond -/
  finSeg : ∀ d, Γ.IsFinSeg d → ∃ d', Γ'.IsFinSeg d' ∧ Γ'.upperCell d' = ψ (Γ.upperCell d)
  finSeg' : ∀ d', Γ'.IsFinSeg d' → ∃ d, Γ.IsFinSeg d ∧ Γ'.upperCell d' = ψ (Γ.upperCell d)
  /-- one vertex less above the sweep, the same curves -/
  numVertices : Γ'.numVertices + 1 = Γ.numVertices
  numCurves : Γ'.numCurves = Γ.numCurves

attribute [instance] Untangle.fin Untangle.dec

/-! ## Existence (package U, `doc/pca/sweep.md`)

The construction `UHyp.conf` (`Pca/Sweep/U_*.lean`): same darts and rotation; the smoothing of
`v` above `S` together with one new crossing in the cell below the edge `[i, i + 1]`, which keeps
the two curves closed and two-intersecting (no global rebuild of the lower side is needed). -/

variable {Γ} {d a : D} {k : ℕ} {γ : Fin n}

/-- The untangling of `v = crossingOf a` under the hypotheses `UHyp`. -/
noncomputable def UHyp.untangle (H : Γ.UHyp d a k γ) : Γ.Untangle a where
  n' := n
  D' := D
  Γ' := H.conf
  ψ := H.ψ
  up := by
    intro f hf
    obtain ⟨x, rfl, hv⟩ := H.exists_rep f
    change H.conf.Up (H.ψ (Γ.cellOf x))
    rw [H.ψ_spec hf hv]
    change Γ.uSideD a x = 1
    rw [H.uSideD_nv hv]; exact hf
  surj := by
    intro f' hf'
    obtain ⟨y, rfl⟩ := f'.exists_mk
    have hy : Γ.uSideD a y = 1 := hf'
    have hv : Γ.crossingOf y ≠ Γ.crossingOf a := by
      intro h; rw [H.uSideD_v h] at hy; exact absurd hy (by decide)
    rw [H.uSideD_nv hv] at hy
    exact ⟨Γ.cellOf y, hy, H.ψ_spec hy hv⟩
  merge := by
    change H.ψ (Γ.cellOf a) = H.ψ (Γ.cellOf (Γ.σ (Γ.σ a)))
    unfold UHyp.ψ
    exact (if_pos (Or.inl rfl)).trans (if_pos (Or.inr rfl)).symm
  inj := by
    intro f g hf hg hfg
    obtain ⟨x, rfl, hvx⟩ := H.exists_rep f
    obtain ⟨y, rfl, hvy⟩ := H.exists_rep g
    rw [H.ψ_spec hf hvx, H.ψ_spec hg hvy] at hfg
    have hG := congrArg H.Gc hfg
    rw [H.Gc_mk, H.Gc_mk, H.uG_up hf hvx, H.uG_up hg hvy] at hG
    have hBT : Γ.uCell d a 0 ≠ Γ.uCell d a 2 := H.uCell_ne (by decide)
    split_ifs at hG with h1 h2 h2
    · exact Or.inl (h1.trans h2.symm)
    · right; rw [h1, ← hG]; exact pair_comm _ _
    · right; rw [h2, hG]; rfl
    · exact Or.inl hG
  size_merge := H.size_merge
  size_L := H.size_L
  size_R := H.size_R
  size_other := by
    intro f hf hv
    obtain ⟨x, rfl⟩ := f.exists_mk
    change Γ.Up (Γ.cellOf x) at hf
    change ∀ e ∈ (Γ.cellOf x).darts, _ at hv
    have hxv := hv x (Orbit.mem_darts.2 rfl)
    have hc : ∀ c : Fin 7, c.val < 4 → Γ.cellOf x ≠ Γ.uCell d a c := by
      intro c hc he
      have key : ∀ i : Fin 12, i.val < 4 → uCI i = c → False := fun i hi hic =>
        hv _ (by rw [Orbit.mem_darts]; show Γ.cellOf (Γ.uM d a i) = _; rw [H.cell_uM, hic, he])
          (H.v_iff.2 (by fin_cases i <;> simp at hi ⊢))
      fin_cases c <;> simp at hc
      exacts [key 0 (by decide) rfl, key 1 (by decide) rfl, key 2 (by decide) rfl,
        key 3 (by decide) rfl]
    change (H.ψ (Γ.cellOf x)).size = (Γ.cellOf x).size
    rw [H.ψ_spec hf hxv]
    change (orbitFinset H.ph x).card = (orbitFinset Γ.φ x).card
    rw [H.orbit_other hf hc]
  finSeg := by
    intro e he
    refine ⟨e, (H.conf_finSeg e).2 he, ?_⟩
    have hS : Γ.curve e = Γ.S := he.1.1
    change Orbit.mk H.ph (H.α' e) = H.ψ (Γ.cellOf (Γ.α e))
    rw [H.α'_S hS, H.ψ_spec he.1.2 (H.notv_S (by rw [j_curve_α]; exact hS))]
  finSeg' := by
    intro e he
    have he' := (H.conf_finSeg e).1 he
    refine ⟨e, he', ?_⟩
    have hS : Γ.curve e = Γ.S := he'.1.1
    change Orbit.mk H.ph (H.α' e) = H.ψ (Γ.cellOf (Γ.α e))
    rw [H.α'_S hS, H.ψ_spec he'.1.2 (H.notv_S (by rw [j_curve_α]; exact hS))]
  numVertices := H.conf_numVertices
  numCurves := H.conf_numCurves

/-- **Untangling exists** (package U), with SH's two claims about `Γ'` used in Lemma 3.9: it is
not finished (if the legs are crossed, `1 < k`), and no loop can be taken (if every present curve
of `Γ` meets the sweep, SH Lemma 3.4). -/
theorem UHyp.exists_untangle (H : Γ.UHyp d a k γ) (hk : 1 < k)
    (hf1 : Γ.IsFinVertex (Γ.crossingOf d)) (hf2 : Γ.IsFinVertex (Γ.crossingOf (Γ.α d)))
    (hm : ∀ c, Γ.Present c → Γ.MeetsSweep c) :
    ∃ U : Γ.Untangle a, ¬ U.Γ'.Terminal ∧ ¬ U.Γ'.CanTakeLoop :=
  ⟨H.untangle, H.conf_not_terminal hk, H.conf_not_loop hf1 hf2 hm⟩

end SConf

end Pca.Sweep
