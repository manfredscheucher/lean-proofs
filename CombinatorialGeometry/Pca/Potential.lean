/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 6: the potential lemma (`lem:potential` of the notes)

`|X'| + p_2 ≤ 2n - 2` for `n ≥ 4`, using the digon theorem (`digon_bound`, an axiom).

Proof as in the notes (Step 4): for `u ∈ X'` flip the middle triangle `T_2` of the fan at `u`.

* `Arrangement.Fan.flip_p2`: `p_2` grows by at least `2 + [S is a triangle]` (`T_1`, `T_3` and,
  if it is a triangle, `S` become digons; no digon is destroyed),
* `Arrangement.Fan.flip_X'`: every crossing of `X'` other than `u`, `v_2`, `v_3` stays in `X'`,
* `Arrangement.Fan.card_X'_corners`: at most `2 + [S is a triangle]` of `u, v_2, v_3` are in
  `X'`,
* `Arrangement.Fan.flip_potential`: `ψ = |X'| + p_2` does not decrease and `p_2` grows by `≥ 2`,
* `Arrangement.potential_lemma`: `|X'| + p_2 ≤ 2n - 2` (induction on `2n - 2 - p_2`).
-/
import Pca.Flip
import Pca.DigonAxiom

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Fan

variable (F : A.Fan)

/-- The flipped arrangement: `T_2` flipped. -/
abbrev flipT₂ : Arrangement n D := A.flip (A.σ F.a) F.isTriangle₂

/-- The cell correspondence of the flip of `T_2`. -/
abbrev Φ : A.Cell ≃ F.flipT₂.Cell := flipCellEquiv F.isTriangle₂

/-- A crossing of `A`, seen as a crossing of the flipped arrangement (the same object). -/
def cr (x : A.Crossing) : F.flipT₂.Crossing := x

theorem φ_f₂ : A.φ F.f₂ = A.α F.a := by
  rw [φ_apply, α_f₂, A.σ_σ_σ_σ]

theorem cellOf_f₂ : A.cellOf F.f₂ = F.T₂ := cellOf_φ A _

/-- The darts of `T_2` are `σ a`, `f_2`, `α a`. -/
theorem T₂_cases {c : D} (hc : A.cellOf c = A.cellOf (A.σ F.a)) :
    c = A.σ F.a ∨ c = F.f₂ ∨ c = A.α F.a := by
  have := (tri_mem_iff F.isTriangle₂).1 hc
  rwa [show A.φ (A.φ (A.σ F.a)) = A.α F.a from F.φ_f₂] at this

theorem across_cells {c : D} (hc : A.cellOf c = A.cellOf (A.σ F.a)) :
    A.cellOf (A.α c) = F.T₃ ∨ A.cellOf (A.α c) = F.S ∨ A.cellOf (A.α c) = F.T₁ := by
  rcases F.T₂_cases hc with rfl | rfl | rfl
  · exact Or.inl F.cellOf_α_σ_a
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (by rw [α_α]; rfl))

theorem opposite_cells {c : D} (hc : A.cellOf c = A.cellOf (A.σ F.a)) :
    A.cellOf (A.σ (A.σ c)) = F.N ∨ A.cellOf (A.σ (A.σ c)) = F.R' ∨
      A.cellOf (A.σ (A.σ c)) = F.R := by
  rcases F.T₂_cases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by rw [σσ_f₂]; rfl))
  · exact Or.inr (Or.inr F.cellOf_σσ_α_a)

/-! ### Digons -/

/-- `T_1` becomes a digon. -/
theorem size_T₁ : (F.Φ F.T₁).size = 2 := by
  have h := flip_size_across F.isTriangle₂ (c := A.α F.a) F.cellOf_α_a
  rw [α_α] at h
  have : F.T₁.size = 3 := F.isTriangle₁
  change (F.Φ F.T₁).size + 1 = F.T₁.size at h
  omega

/-- `T_3` becomes a digon. -/
theorem size_T₃ : (F.Φ F.T₃).size = 2 := by
  have h := flip_size_across F.isTriangle₂ (c := A.σ F.a) rfl
  rw [F.cellOf_α_σ_a] at h
  have : F.T₃.size = 3 := F.isTriangle₃
  change (F.Φ F.T₃).size + 1 = F.T₃.size at h
  omega

/-- `S` loses a corner. -/
theorem size_S : (F.Φ F.S).size + 1 = F.S.size :=
  flip_size_across F.isTriangle₂ (c := F.f₂) F.cellOf_f₂

theorem across_ne {c c' : D} (hc : A.cellOf c = A.cellOf (A.σ F.a))
    (hc' : A.cellOf c' = A.cellOf (A.σ F.a)) (hne : c ≠ c') :
    A.cellOf (A.α c) ≠ A.cellOf (A.α c') := fun h =>
  hne ((across_eq_iff (isTriangle_of F.isTriangle₂ hc') (hc.trans hc'.symm)).1 h)

theorem T₂_darts_ne : A.σ F.a ≠ F.f₂ ∧ A.σ F.a ≠ A.α F.a ∧ F.f₂ ≠ A.α F.a := by
  have := tri_darts_ne F.isTriangle₂
  rwa [show A.φ (A.φ (A.σ F.a)) = A.α F.a from F.φ_f₂] at this

theorem T₁_ne_T₃ : F.T₁ ≠ F.T₃ := by
  have := F.across_ne F.cellOf_α_a rfl F.T₂_darts_ne.2.1.symm
  rwa [α_α, F.cellOf_α_σ_a] at this

theorem S_ne_T₁ : F.S ≠ F.T₁ := by
  have := F.across_ne F.cellOf_f₂ F.cellOf_α_a F.T₂_darts_ne.2.2
  rwa [α_α] at this

theorem S_ne_T₃ : F.S ≠ F.T₃ := by
  have := F.across_ne F.cellOf_f₂ rfl F.T₂_darts_ne.1.symm
  rwa [F.cellOf_α_σ_a] at this

/-- No digon is destroyed: a digon is neither across a side of `T_2` (it would share a side with
a triangle) nor opposite to `T_2` (`N`, `R`, `R'` are not digons). -/
theorem size_of_digon (hn : 4 ≤ n) {f : A.Cell} (hf : A.IsDigon f) : (F.Φ f).size = 2 := by
  obtain ⟨-, -, hR, -, hR'⟩ := F.cons_a hn
  have hN := (F.cons_a hn).1
  have := flip_size_of_ne F.isTriangle₂ (f := f) fun c hc => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := A.not_triangle_α_of_digon (d := A.α c) (by rw [← h]; exact hf)
      rw [α_α, hc] at this
      exact this F.isTriangle₂
    · rcases F.opposite_cells hc with e | e | e <;> rw [e] at h <;> rw [h] at hf
      · exact hN hf
      · exact hR' hf
      · exact hR hf
  rw [this]; exact hf

theorem p_flip (k : ℕ) :
    F.flipT₂.p k = (univ.filter (fun f : A.Cell => (F.Φ f).size = k)).card := by
  rw [p]
  symm
  apply card_equiv F.Φ
  intro f
  simp [IsKCell]

/-- **`Δp_2 ≥ 2 + [S is a triangle]`**: `T_1`, `T_3` and (if it is a triangle) `S` become
digons, and every digon stays a digon. -/
theorem flip_p2 (hn : 4 ≤ n) :
    A.p 2 + 2 + (if A.IsTriangle F.S then 1 else 0) ≤ F.flipT₂.p 2 := by
  rw [F.p_flip]
  set Dg := univ.filter (A.IsKCell 2) with hDg
  have hp : A.p 2 = Dg.card := rfl
  have hsub : Dg ⊆ univ.filter (fun f : A.Cell => (F.Φ f).size = 2) := fun f hf => by
    rw [hDg, mem_filter] at hf
    rw [mem_filter]
    exact ⟨mem_univ _, F.size_of_digon hn hf.2⟩
  have hT₁ : F.T₁ ∉ Dg := by
    simp only [hDg, mem_filter, mem_univ, true_and, IsKCell]
    rw [show F.T₁.size = 3 from F.isTriangle₁]; omega
  have hT₃ : F.T₃ ∉ insert F.T₁ Dg := by
    simp only [hDg, mem_insert, mem_filter, mem_univ, true_and, IsKCell, not_or]
    refine ⟨F.T₁_ne_T₃.symm, ?_⟩
    rw [show F.T₃.size = 3 from F.isTriangle₃]; omega
  have hm : ∀ g, (F.Φ g).size = 2 → g ∈ univ.filter (fun f : A.Cell => (F.Φ f).size = 2) :=
    fun g h => by simpa using h
  by_cases hS : A.IsTriangle F.S
  · have hS' : F.S ∉ insert F.T₃ (insert F.T₁ Dg) := by
      simp only [hDg, mem_insert, mem_filter, mem_univ, true_and, IsKCell, not_or]
      refine ⟨F.S_ne_T₃, F.S_ne_T₁, ?_⟩
      rw [show F.S.size = 3 from hS]; omega
    have hc := card_le_card (s := insert F.S (insert F.T₃ (insert F.T₁ Dg)))
      (t := univ.filter (fun f : A.Cell => (F.Φ f).size = 2)) (by
        refine insert_subset (hm _ ?_) (insert_subset (hm _ F.size_T₃)
          (insert_subset (hm _ F.size_T₁) hsub))
        have := F.size_S
        rw [show F.S.size = 3 from hS] at this; omega)
    rw [card_insert_of_notMem hS', card_insert_of_notMem hT₃, card_insert_of_notMem hT₁] at hc
    rw [if_pos hS]; omega
  · have hc := card_le_card (s := insert F.T₃ (insert F.T₁ Dg))
      (t := univ.filter (fun f : A.Cell => (F.Φ f).size = 2))
      (insert_subset (hm _ F.size_T₃) (insert_subset (hm _ F.size_T₁) hsub))
    rw [card_insert_of_notMem hT₃, card_insert_of_notMem hT₁] at hc
    rw [if_neg hS]; omega

/-! ### `X'` -/

/-- **Every crossing of `X'` other than `u`, `v_2`, `v_3` stays in `X'`**: its triangles are not
among the cells that change, since the corners of `T_1`, `T_3` and of a triangle among `S`, `R`,
`R'` other than `u, v_2, v_3` are `v_1`, `v_4`, `u'`, which are not in `X'` (`lem:fan-cons`). -/
theorem flip_X' (hn : 4 ≤ n) {x : A.Crossing} (hx : x ∈ A.X') (hu : x ≠ F.u) (h2 : x ≠ F.v₂)
    (h3 : x ≠ F.v₃) : F.flipT₂.t (F.cr x) = 3 := by
  have hb := F.cons_b hn
  have hcc := F.cons_c hn
  have hN := (F.cons_a hn).2.1
  rw [mem_X'] at hx
  refine le_antisymm (t_le_three F.flipT₂ hn (F.cr x)) ?_
  rw [← hx, t_eq_tAngles, t_eq_tAngles F.flipT₂]
  show (x.darts.filter _).card ≤
    (x.darts.filter (fun d => F.flipT₂.IsTriangle (F.flipT₂.cellOf d))).card
  refine card_le_card fun y hy => ?_
  rw [mem_filter] at hy ⊢
  obtain ⟨hyx, hyT⟩ := hy
  refine ⟨hyx, ?_⟩
  have hcr : A.crossingOf y = x := Orbit.mem_darts.1 hyx
  have hnc : ¬ A.IsCorner (A.σ F.a) y := by
    rw [IsCorner, hcr, show A.cellOf (A.σ F.a) = F.T₂ from rfl, F.corners_T₂]
    simp [hu, h2, h3]
  have hxc : ∀ g : A.Cell, A.cellOf y = g → x ∈ Cell.corners A g := fun g hg =>
    mem_image.2 ⟨y, Orbit.mem_darts.2 hg, hcr⟩
  change F.flipT₂.IsTriangle (F.flipT₂.cellOf y)
  rw [flip_cellOf_of_not_corner F.isTriangle₂ hnc]
  change (F.Φ (A.cellOf y)).size = 3
  rw [flip_size_of_ne F.isTriangle₂]
  · exact hyT
  intro c hc
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases F.across_cells hc with e | e | e <;> rw [e] at h <;> have hx' := hxc _ h
    · rw [corners_T₃] at hx'
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact hu rfl
      · exact hb.2 (by rw [mem_X']; exact hx)
      · exact h3 rfl
    · rw [(hcc.2.1 (h ▸ hyT)).1] at hx'
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact (hcc.2.1 (h ▸ hyT)).2 (by rw [mem_X']; exact hx)
    · rw [corners_T₁] at hx'
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact hu rfl
      · exact h2 rfl
      · exact hb.1 (by rw [mem_X']; exact hx)
  · rcases F.opposite_cells hc with e | e | e <;> rw [e] at h
    · exact hN (h ▸ hyT)
    · have hx' := hxc _ h
      rw [(hcc.2.2 (h ▸ hyT)).1] at hx'
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact h3 rfl
      · exact hb.2 (by rw [mem_X']; exact hx)
      · exact (hcc.2.2 (h ▸ hyT)).2 (by rw [mem_X']; exact hx)
    · have hx' := hxc _ h
      rw [(hcc.1 (h ▸ hyT)).1] at hx'
      simp only [mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact hb.1 (by rw [mem_X']; exact hx)
      · exact h2 rfl
      · exact (hcc.1 (h ▸ hyT)).2 (by rw [mem_X']; exact hx)

/-- At most `2 + [S is a triangle]` of `u, v_2, v_3` lie in `X'` (`lem:fan-cons` (d), (e)). -/
theorem card_X'_corners (hn : 4 ≤ n) :
    (({F.u, F.v₂, F.v₃} : Finset A.Crossing).filter (· ∈ A.X')).card ≤
      2 + (if A.IsTriangle F.S then 1 else 0) := by
  by_cases hS : A.IsTriangle F.S
  · rw [if_pos hS]
    exact (card_filter_le _ _).trans card_le_three
  · rw [if_neg hS]
    obtain ⟨-, -, hRR'⟩ := F.cons_d hn
    obtain ⟨e2, e3⟩ := F.cons_e hn
    by_cases hv2 : F.v₂ ∈ A.X'
    · have hv3 : F.v₃ ∉ A.X' := fun h => hRR' ⟨(e2.1 hv2).resolve_right hS,
        (e3.1 h).resolve_left hS⟩
      refine (card_le_card (t := {F.u, F.v₂}) fun x hx => ?_).trans card_le_two
      simp only [mem_filter, mem_insert, mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl | rfl, h⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h hv3
    · refine (card_le_card (t := {F.u, F.v₃}) fun x hx => ?_).trans card_le_two
      simp only [mem_filter, mem_insert, mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl | rfl, h⟩
      · exact Or.inl rfl
      · exact absurd h hv2
      · exact Or.inr rfl

theorem card_X'_flip :
    F.flipT₂.X'.card = (univ.filter (fun x : A.Crossing => F.flipT₂.t (F.cr x) = 3)).card := rfl

/-- **The potential does not decrease and `p_2` grows by at least 2** when flipping `T_2`. -/
theorem flip_potential (hn : 4 ≤ n) :
    A.X'.card + A.p 2 ≤ F.flipT₂.X'.card + F.flipT₂.p 2 ∧ A.p 2 + 2 ≤ F.flipT₂.p 2 := by
  have hp := F.flip_p2 hn
  have hL := F.card_X'_corners hn
  rw [card_X'_flip]
  have hsub : A.X' ⊆ (univ.filter (fun x : A.Crossing => F.flipT₂.t (F.cr x) = 3)) ∪
      ({F.u, F.v₂, F.v₃} : Finset A.Crossing).filter (· ∈ A.X') := by
    intro x hx
    by_cases hc : x = F.u ∨ x = F.v₂ ∨ x = F.v₃
    · refine mem_union_right _ (mem_filter.2 ⟨?_, hx⟩)
      simp only [mem_insert, mem_singleton]; exact hc
    · simp only [not_or] at hc
      exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, F.flip_X' hn hx hc.1 hc.2.1 hc.2.2⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  constructor <;> omega

end Fan

/-- **Potential lemma** (`lem:potential`, `n ≥ 4`, using the digon theorem `digon_bound`):
`|X'| + p_2 ≤ 2n - 2`. Induction on `2n - 2 - p_2`: while `X' ≠ ∅`, flip `T_2` of a fan;
the potential does not decrease and `p_2` grows (bounded by the digon theorem). -/
theorem potential_lemma (hn : 4 ≤ n) (A : Arrangement n D) : A.X'.card + A.p 2 ≤ 2 * n - 2 := by
  suffices h : ∀ m (B : Arrangement n D), 2 * n - 2 - B.p 2 = m → B.X'.card + B.p 2 ≤ 2 * n - 2 from
    h _ A rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B hm
    have hb := digon_bound B (by omega)
    rcases B.X'.eq_empty_or_nonempty with h | ⟨u, hu⟩
    · rw [h, card_empty]; omega
    · obtain ⟨-, F, rfl⟩ := B.fan_lemma hn (u := u) (by rw [(B.mem_X').1 hu])
      obtain ⟨hψ, hp⟩ := F.flip_potential hn
      have hb' := digon_bound F.flipT₂ (by omega)
      have := ih _ (by omega) F.flipT₂ rfl
      omega

end Pca.Arrangement
