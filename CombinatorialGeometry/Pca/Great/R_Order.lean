/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: local orders in the canonical form (`doc/pca/great.md` section 3.4)

With potential `0`, along every chord the other chords appear in decreasing order of `p`
(`cf_order`), so the positions are determined by `p` (`hpos_count`).
-/
import Pca.Great.R_Table

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

theorem hpos_inj {e f g : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hg : g ≠ F.c0) (hef : e ≠ f)
    (heg : e ≠ g) (h : F.hpos e f = F.hpos e g) : f = g := by
  have := (F.chordSys hA).H_inj ⟨e, he⟩ ⟨f, hf⟩ ⟨g, hg⟩ (fun h' => hef (congrArg Subtype.val h').symm)
    (fun h' => heg (congrArg Subtype.val h').symm) h
  exact congrArg Subtype.val this

/-- For a sorted positive triple, along the middle chord the last one comes first. -/
theorem mid_order (hpot : F.pot = 0) {a b c : Fin n} (ha : a ≠ F.c0) (hb : b ≠ F.c0)
    (hc : c ≠ F.c0) (hab : F.p a < F.p b) (hbc : F.p b < F.p c) : F.hpos b c < F.hpos b a := by
  classical
  have hab' : a ≠ b := fun h => by rw [h] at hab; omega
  have hac' : a ≠ c := fun h => by rw [h] at hab; omega
  have hbc' : b ≠ c := fun h => by rw [h] at hbc; omega
  have hnot : ¬ F.Neg a b c := by
    intro hN
    have : (a, b, c) ∈ univ.filter F.Bad := mem_filter.2 ⟨mem_univ _, ha, hb, hc, hab, hbc, hN⟩
    have := card_pos.2 ⟨_, this⟩
    unfold pot at hpot; omega
  rw [F.neg_iff hA ha hb hc hab' hac' hbc'] at hnot
  have hx : a ∉ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.hpos b c) (F.β b))) := by
    rw [F.curves_hcross hA hb hc hbc', mem_insert, mem_singleton, not_or]; exact ⟨hab', hac'⟩
  rw [crossSide_eq (F.isSide_sR a) hx, F.sR_chord hA ha hb hab' (F.hpos_spec hA hb hc hbc').2.1,
    if_pos hab] at hnot
  have hne : F.hpos b c ≠ F.hpos b a := fun h => hac' (F.hpos_inj hA hb hc ha hbc' (Ne.symm hab') h).symm
  by_contra hlt
  rw [if_pos (by omega)] at hnot
  exact hnot (by decide)

/-- **Local order in the canonical form.** -/
theorem cf_order (hpot : F.pot = 0) {e f g : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0)
    (hg : g ≠ F.c0) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hgf : F.p g < F.p f) :
    F.hpos e f < F.hpos e g := by
  set S := F.chordSys hA
  have hpe : F.p e ≠ F.p f := fun h => hef (F.p_inj hA he hf h)
  have hpe' : F.p e ≠ F.p g := fun h => heg (F.p_inj hA he hg h)
  have hne : F.hpos e f ≠ F.hpos e g := fun h => hfg (F.hpos_inj hA he hf hg hef heg h)
  have sub : ∀ {x y : Fin n} (hx : x ≠ F.c0) (hy : y ≠ F.c0), x ≠ y →
      (⟨x, hx⟩ : F.Ch) ≠ ⟨y, hy⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  rcases Nat.lt_or_gt_of_ne hpe with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hpe' with h2 | h2
  · -- `e` first: triple `(e, g, f)`
    have hm := F.mid_order hA hpot he hg hf h2 hgf
    have r := S.rel ⟨f, hf⟩ ⟨e, he⟩ ⟨g, hg⟩ (sub hf he (Ne.symm hef)) (sub hf hg hfg)
      (sub he hg heg)
    change ((F.p f < F.p e ↔ F.hpos e f ≤ F.hpos e g) ↔ (F.p f < F.p g ↔ F.hpos g f ≤ F.hpos g e)) at r
    have hR : ¬ (F.p f < F.p g ↔ F.hpos g f ≤ F.hpos g e) := fun h => by
      have := h.2 (by omega); omega
    have hL := mt r.1 hR
    by_contra hc
    exact hL ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · -- `e` in the middle: triple `(g, e, f)`
    exact F.mid_order hA hpot hg he hf h2 h1
  · omega
  · -- `e` last: triple `(g, f, e)`
    have hm := F.mid_order hA hpot hg hf he hgf h1
    have r := S.rel ⟨g, hg⟩ ⟨f, hf⟩ ⟨e, he⟩ (sub hg hf (Ne.symm hfg)) (sub hg he (Ne.symm heg))
      (sub hf he (Ne.symm hef))
    change ((F.p g < F.p f ↔ F.hpos f g ≤ F.hpos f e) ↔ (F.p g < F.p e ↔ F.hpos e g ≤ F.hpos e f)) at r
    have hL : ¬ (F.p g < F.p f ↔ F.hpos f g ≤ F.hpos f e) := fun h => by
      have := h.1 hgf; omega
    have hR := mt r.2 hL
    by_contra hc
    exact hR ⟨fun _ => by omega, fun _ => h2⟩

end Frame

end Pca.Great
