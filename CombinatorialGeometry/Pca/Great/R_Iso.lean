/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: two canonical forms are isomorphic (`doc/pca/great.md` section 3.4)
-/
import Pca.Great.R_Uniq

open Equiv Finset

namespace Pca.Great

universe u v

variable {D : Type u} [Fintype D] [DecidableEq D] {D' : Type v} [Fintype D'] [DecidableEq D']
  {n : ℕ} {A : Arrangement n D} {B : Arrangement n D'}

namespace Frame

variable (FA : Frame A) (FB : Frame B) (hA : A.IsGreat) (hB : B.IsGreat)

/-- The relabeling by positions on the frame curve. -/
noncomputable def relab (e : Fin n) : Fin n :=
  if e = FA.c0 then FB.c0 else FB.data.chordAt (FA.p e)

include hA hB

theorem relab_chord {e : Fin n} (he : e ≠ FA.c0) :
    FA.relab FB e ≠ FB.c0 ∧ FB.p (FA.relab FB e) = FA.p e := by
  obtain ⟨e', he', hp⟩ := FB.exists_p hB (k := FA.p e) (by
    have := FA.p_lt hA he
    have h1 := A.two_le_n
    omega)
  unfold relab
  rw [if_neg he, ← hp, FB.chordAt_eq hB he']
  exact ⟨he', rfl⟩

theorem relab_injective : Function.Injective (FA.relab FB) := by
  intro e f h
  by_cases he : e = FA.c0 <;> by_cases hf : f = FA.c0
  · rw [he, hf]
  · exfalso; have := (FA.relab_chord FB hA hB hf).1; rw [← h] at this
    unfold relab at this; rw [if_pos he] at this; exact this rfl
  · exfalso; have := (FA.relab_chord FB hA hB he).1; rw [h] at this
    unfold relab at this; rw [if_pos hf] at this; exact this rfl
  · have h1 := (FA.relab_chord FB hA hB he).2
    have h2 := (FA.relab_chord FB hA hB hf).2
    rw [h] at h1
    exact FA.p_inj hA he hf (h1.symm.trans h2)

/-- The relabeling as a permutation. -/
noncomputable def relabPerm : Perm (Fin n) :=
  Equiv.ofBijective (FA.relab FB) (Finite.injective_iff_bijective.1 (FA.relab_injective FB hA hB))

theorem relabPerm_apply (e : Fin n) : FA.relabPerm FB hA hB e = FA.relab FB e := rfl

theorem relab_c0 : FA.relab FB FA.c0 = FB.c0 := if_pos rfl

theorem relab_ne {e : Fin n} (he : e ≠ FA.c0) : FA.relab FB e ≠ FB.c0 := (FA.relab_chord FB hA hB he).1

theorem relab_p {e : Fin n} (he : e ≠ FA.c0) : FB.p (FA.relab FB e) = FA.p e :=
  (FA.relab_chord FB hA hB he).2

theorem relab_surj (y : Fin n) : ∃ e, FA.relab FB e = y :=
  (Finite.injective_iff_surjective.1 (FA.relab_injective FB hA hB)) y

variable (hpA : FA.pot = 0) (hpB : FB.pot = 0)
include hpA hpB

theorem relab_hpos {e f : Fin n} (he : e ≠ FA.c0) (hf : f ≠ FA.c0) (hef : e ≠ f) :
    FB.hpos (FA.relab FB e) (FA.relab FB f) = FA.hpos e f := by
  classical
  have hinj := FA.relab_injective FB hA hB
  rw [FB.hpos_count hB hpB (FA.relab_ne FB hA hB he) (FA.relab_ne FB hA hB hf)
    (fun h => hef (hinj h)), FA.hpos_count hA hpA he hf hef]
  congr 1
  have hmap : (univ.filter fun g => g ≠ FB.c0 ∧ g ≠ FA.relab FB e ∧
      FB.p (FA.relab FB f) < FB.p g) =
      (univ.filter fun g => g ≠ FA.c0 ∧ g ≠ e ∧ FA.p f < FA.p g).map ⟨FA.relab FB, hinj⟩ := by
    ext y
    obtain ⟨g, rfl⟩ := FA.relab_surj FB hA hB y
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hg0, hge, hlt⟩
      have hg0' : g ≠ FA.c0 := fun h => hg0 (by rw [h, FA.relab_c0 FB hA hB])
      refine ⟨g, ⟨hg0', fun h => hge (by rw [h]), ?_⟩, rfl⟩
      rwa [FA.relab_p FB hA hB hf, FA.relab_p FB hA hB hg0'] at hlt
    · rintro ⟨g', ⟨hg0, hge, hlt⟩, hgg⟩
      have := hinj hgg
      subst this
      refine ⟨FA.relab_ne FB hA hB hg0, fun h => hge (hinj h), ?_⟩
      rwa [FA.relab_p FB hA hB hf, FA.relab_p FB hA hB hg0]
  rw [hmap, card_map]

theorem relab_curveAt {c : Fin n} (hc : c ≠ FA.c0) {k : ℕ} (hk0 : 0 < k) (hk : k < n - 1) :
    FB.data.curveAt (FA.relab FB c) k = FA.relab FB (FA.data.curveAt c k) := by
  obtain ⟨h1, h2, h3⟩ := FA.curveAt_spec hA hc hk0 hk
  obtain ⟨g1, g2, g3⟩ := FB.curveAt_spec hB (FA.relab_ne FB hA hB hc) hk0 hk
  have hinj := FA.relab_injective FB hA hB
  refine FB.hpos_inj hB (FA.relab_ne FB hA hB hc) g1 (FA.relab_ne FB hA hB h1) (Ne.symm g2)
    (fun h => h2 (hinj h).symm) ?_
  rw [g3, FA.relab_hpos FB hA hB hpA hpB hc h1 (Ne.symm h2), h3]

omit hpA hpB in
theorem relab_chordAt {k : ℕ} (hk : k < n - 1) :
    FB.data.chordAt k = FA.relab FB (FA.data.chordAt k) := by
  obtain ⟨e, he, rfl⟩ := FA.exists_p hA hk
  rw [FA.chordAt_eq hA he, ← FA.relab_p FB hA hB he, FB.chordAt_eq hB (FA.relab_ne FB hA hB he)]

theorem relab_tab (c : Fin n) {k : ℕ} (hk : k < 2 * (n - 1)) :
    FB.data.tab (FA.relab FB c) k = (FA.relab FB (FA.data.tab c k).1, (FA.data.tab c k).2.1,
      (FA.data.tab c k).2.2) := by
  have hn := A.two_le_n
  unfold FData.tab
  by_cases hc : c = FA.c0
  · subst hc
    rw [if_pos (show FA.relab FB FA.c0 = FB.data.c0 from FA.relab_c0 FB hA hB),
      if_pos (show FA.c0 = FA.data.c0 from rfl)]
    by_cases hkm : k < n - 1
    · rw [if_pos hkm, if_pos hkm, FA.relab_chordAt FB hA hB hkm]
    · rw [if_neg hkm, if_neg hkm, FA.relab_chordAt FB hA hB (by omega)]
  · have hrc := FA.relab_ne FB hA hB hc
    rw [if_neg (show ¬ FA.relab FB c = FB.data.c0 from hrc),
      if_neg (show ¬ c = FA.data.c0 from hc)]
    have hpc : FB.data.p (FA.relab FB c) = FA.data.p c := FA.relab_p FB hA hB hc
    by_cases hk0 : k = 0
    · rw [if_pos hk0, if_pos hk0, hpc, show FB.data.c0 = FA.relab FB FA.data.c0 from
        (FA.relab_c0 FB hA hB).symm]
    rw [if_neg hk0, if_neg hk0]
    by_cases hkm : k < n - 1
    · rw [if_pos hkm, if_pos hkm, FA.relab_curveAt FB hA hB hpA hpB hc (by omega) hkm]
      obtain ⟨h1, h2, -⟩ := FA.curveAt_spec hA hc (by omega) hkm
      have e1 : FB.data.hp (FA.relab FB (FA.data.curveAt c k)) (FA.relab FB c) =
          FA.data.hp (FA.data.curveAt c k) c := FA.relab_hpos FB hA hB hpA hpB h1 hc h2
      have e2 : FB.data.p (FA.relab FB (FA.data.curveAt c k)) = FA.data.p (FA.data.curveAt c k) :=
        FA.relab_p FB hA hB h1
      rw [e1, e2, hpc]
    rw [if_neg hkm, if_neg hkm]
    by_cases hkm' : k = n - 1
    · rw [if_pos hkm', if_pos hkm', hpc, show FB.data.c0 = FA.relab FB FA.data.c0 from
        (FA.relab_c0 FB hA hB).symm]
    rw [if_neg hkm', if_neg hkm', FA.relab_curveAt FB hA hB hpA hpB hc (by omega) (by omega)]
    obtain ⟨h1, h2, -⟩ := FA.curveAt_spec hA hc (k := k - (n - 1)) (by omega) (by omega)
    have e1 : FB.data.hp (FA.relab FB (FA.data.curveAt c (k - (n - 1)))) (FA.relab FB c) =
        FA.data.hp (FA.data.curveAt c (k - (n - 1))) c := FA.relab_hpos FB hA hB hpA hpB h1 hc h2
    have e2 : FB.data.p (FA.relab FB (FA.data.curveAt c (k - (n - 1)))) =
        FA.data.p (FA.data.curveAt c (k - (n - 1))) := FA.relab_p FB hA hB h1
    rw [e1, e2, hpc]

/-- **Two canonical forms are isomorphic.** -/
theorem cf_iso : Nonempty (Iso A B) := by
  refine iso_of_table A B (FA.relabPerm FB hA hB) FA.βf (fun c => FB.βf (FA.relab FB c))
    (FA.curve_βf hA) (fun c => FB.curve_βf hB _) FA.data.tab (fun c k hk => FA.tab_spec hA c hk)
    (fun c k hk => ?_)
  have h := FB.tab_spec hB (FA.relab FB c) hk
  rw [FA.relab_tab FB hA hB hpA hpB c hk] at h
  exact h

end Frame

end Pca.Great
