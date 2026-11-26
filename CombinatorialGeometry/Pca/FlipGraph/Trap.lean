/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): cuts inside a lens ("trap lemma")

The region arguments of FROS' proof of Lemma 2 ("the region `T` bounded by the subarcs of `a` and
`a'` from `L` to `p` and the corresponding part of `L`") are cuts (`Cut.exists_cut`) along an even
set `E` of segments made of chord segments and `L`-segments. Such a cut is constant on the
complement of the lens (`compl_conn` only uses segments with both cells outside `Q`); normalized
to `0` there (`exists_trap`), the cells of `R`-darts have value `0` (`trap_R`), and a chord walk
keeps its value until it passes a segment of `E` (`Cut.cut_pow`). Tool for `Lens.zipStep`
(`doc/pca/flipgraph.md`, plan for `zipStep`).
-/
import Pca.FlipGraph.Cut
import Pca.FlipGraph.Lens

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- `E` consists of chord segments and `L`-segments. -/
def InLens (E : Finset A.Segment) : Prop :=
  ∀ y, A.segmentOf y ∈ E → Λ.Chord y ∨ Λ.L y ∨ Λ.L (A.α y)

/-- A segment of `E` has a cell in `Q`. -/
theorem InLens.cell {Λ : Lens A} {E : Finset A.Segment} (hE : Λ.InLens E) {y : D}
    (hy : A.segmentOf y ∈ E) : Λ.Q (A.cellOf y) ∨ Λ.Q (A.cellOf (A.α y)) := by
  rcases hE y hy with h | h | h
  · exact Or.inl h.1
  · exact Or.inl (Λ.L_bd y h).1
  · exact Or.inr (Λ.L_bd _ h).1

/-- **Trap lemma**: an even set of chord and `L`-segments is cut by a function vanishing off
`Q`. -/
theorem exists_trap {E : Finset A.Segment} (hev : Cut.IsEven A E) (hE : Λ.InLens E) :
    ∃ r, Cut.IsCut A E r ∧ ∀ f, ¬ Λ.Q f → r f = 0 := by
  obtain ⟨r₀, hr₀⟩ := Cut.exists_cut A E hev
  -- `r₀` is constant on the complement of `Q`
  have hconst : ∀ f g, ¬ Λ.Q f → ¬ Λ.Q g → r₀ f = r₀ g := by
    intro f g hf hg
    have key := Λ.compl_conn f g hf hg
    clear hf hg
    induction key with
    | rel a b h =>
      obtain ⟨y, ⟨hy1, hy2⟩, rfl, rfl⟩ := h
      have hyE : A.segmentOf y ∉ E := fun hm => by
        rcases hE.cell hm with h | h
        · exact hy1 h
        · exact hy2 h
      have := Cut.cut_α hr₀ y
      rw [if_neg hyE, add_zero] at this
      exact this.symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  by_cases hne : ∃ g, ¬ Λ.Q g
  · obtain ⟨g, hg⟩ := hne
    refine ⟨fun f => r₀ f + r₀ g, fun y => ?_, fun f hf => ?_⟩
    · have h := hr₀ y
      have key : ∀ a b c : ZMod 2, a + c + (b + c) = a + b := by decide
      simp only [key, h]
    · show r₀ f + r₀ g = 0
      rw [hconst f g hf hg]; exact Arrangement.zmod2_add_self _
  · push_neg at hne
    exact ⟨r₀, hr₀, fun f hf => absurd (hne f) hf⟩

/-- In a trap, the cell of an `R`-dart has value `0`. -/
theorem trap_R {E : Finset A.Segment} (hE : Λ.InLens E) {r : A.Cell → ZMod 2}
    (hr : Cut.IsCut A E r) (h0 : ∀ f, ¬ Λ.Q f → r f = 0) {u : D} (hu : Λ.R u) :
    r (A.cellOf u) = 0 := by
  have hnot : A.segmentOf u ∉ E := fun hm => by
    rcases hE u hm with h | h | h
    · exact (Λ.R_bd u hu).2 h.2
    · exact Λ.disj u ⟨h, hu⟩
    · exact (Λ.R_bd u hu).2 (Λ.L_bd _ h).1
  have h1 := hr u
  rw [if_neg hnot, h0 _ (Λ.R_bd u hu).2, add_zero] at h1
  exact h1

/-- In a trap, the cell of an `L`-dart has value `1` iff its segment is in `E`. -/
theorem trap_L {E : Finset A.Segment} {r : A.Cell → ZMod 2}
    (hr : Cut.IsCut A E r) (h0 : ∀ f, ¬ Λ.Q f → r f = 0) {u : D} (hu : Λ.L u) :
    r (A.cellOf u) = if A.segmentOf u ∈ E then 1 else 0 := by
  have h1 := hr u
  rw [h0 _ (Λ.L_bd u hu).2, add_zero] at h1
  exact h1

end Lens

end Pca.FlipGraph
