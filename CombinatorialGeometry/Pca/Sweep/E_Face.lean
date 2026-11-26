/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package E (SH Lemma 3.7), the boundary of a cell of `Γ − R` in `Γ`

For a dart `b'` of `Γ − R`, its cell `F'` (`m = period φ' b'` darts `eC b' i = φ'^i b'`) is, in `Γ`,
bounded by the closed walk `eW b' u = eNxt^u (ι b')`, `u < eN b'`: the pieces of `eC b' 0`, then
those of `eC b' 1`, and so on (the darts `eC b' i` start at position `eP b' i`).

* Step 2 of `doc/pca/sweep.md` (Jordan for the face): a cut `r` of `Γ` along this walk whose
  value on the cell of `ι e'` is `1` iff `e'` is in `F'` (`e_inside`);
* the **chord lemma** (`e_chord`, for `R = {γ}`): the edge of `γ` that enters `F'` at a port ends
  at another port.
-/
import Pca.Sweep.E_Seg

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)}

theorem e_exists_idx {X : Type*} [Fintype X] [DecidableEq X] {f : Perm X} {a b : X}
    (h : f.SameCycle a b) : ∃ k < period f a, (f ^ k) a = b := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨k, List.mem_range.1 hk, by rw [Perm.coe_pow]⟩

theorem e_pow_inj {X : Type*} [Fintype X] [DecidableEq X] {f : Perm X} {a : X} {i j : ℕ}
    (hi : i < period f a) (hj : j < period f a) (h : (f ^ i) a = (f ^ j) a) : i = j := by
  rw [period_eq_minimalPeriod] at hi hj
  rw [Perm.coe_pow, Perm.coe_pow] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

theorem e_pow_period {X : Type*} [Fintype X] [DecidableEq X] (f : Perm X) (a : X) :
    (f ^ period f a) a = a := by
  rw [Perm.coe_pow]; exact iterate_period f a

namespace Removal

variable (X : Γ.Removal R)

/-- The darts of the cell of `b'` in `Γ − R`. -/
def eC (b' : X.D') (i : ℕ) : X.D' := (X.Γ'.φ ^ i) b'

/-- The position of the first piece of `eC b' i` on the boundary walk. -/
noncomputable def eP (b' : X.D') : ℕ → ℕ
  | 0 => 0
  | i + 1 => eP b' i + X.eJ (X.eC b' i) + 1

/-- The boundary walk of the cell of `b'`, in `Γ`. -/
noncomputable def eW (b' : X.D') (u : ℕ) : D := (Γ.eNxt R)^[u] (X.ι b')

/-- The number of darts of the cell of `b'` in `Γ − R`. -/
noncomputable def eM (b' : X.D') : ℕ := period X.Γ'.φ b'

/-- The length of the boundary walk. -/
noncomputable def eN (b' : X.D') : ℕ := X.eP b' (X.eM b')

variable {X} {b' : X.D'}

theorem e_P_succ (i : ℕ) : X.eP b' (i + 1) = X.eP b' i + X.eJ (X.eC b' i) + 1 := rfl

theorem e_P_mono {i j : ℕ} (h : i ≤ j) : X.eP b' i ≤ X.eP b' j := by
  induction j with
  | zero => rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact le_rfl
    · rw [e_P_succ]; have := ih (by omega); omega

theorem e_P_last_lt {i : ℕ} (hi : i < X.eM b') : X.eP b' i + X.eJ (X.eC b' i) < X.eN b' := by
  have := e_P_mono (X := X) (b' := b') (show i + 1 ≤ X.eM b' by omega)
  rw [e_P_succ] at this
  unfold eN; omega

theorem e_W_succ (u : ℕ) : X.eW b' (u + 1) = Γ.eNxt R (X.eW b' u) :=
  Function.iterate_succ_apply' _ _ _

theorem e_W_P (i : ℕ) : X.eW b' (X.eP b' i) = X.ι (X.eC b' i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    unfold eW at ih ⊢
    rw [e_P_succ, add_assoc, add_comm, Function.iterate_add_apply, ih, e_nxt_iter_succ]
    unfold eC; rw [pow_succ', Perm.mul_apply]

theorem e_W_pos (i : ℕ) {t : ℕ} (ht : t ≤ X.eJ (X.eC b' i)) :
    X.eW b' (X.eP b' i + t) = X.ePc (X.eC b' i) t := by
  unfold eW
  rw [add_comm, Function.iterate_add_apply]
  rw [show (Γ.eNxt R)^[X.eP b' i] (X.ι b') = X.eW b' (X.eP b' i) from rfl, e_W_P,
    e_nxt_iter _ ht]

theorem e_W_N : X.eW b' (X.eN b') = X.eW b' 0 := by
  unfold eN; rw [e_W_P]; unfold eC eM; rw [e_pow_period]; rfl

theorem e_decomp_aux (m : ℕ) {u : ℕ} (hu : u < X.eP b' m) :
    ∃ i < m, ∃ t ≤ X.eJ (X.eC b' i), u = X.eP b' i + t := by
  induction m generalizing u with
  | zero => exact absurd hu (by simp [eP])
  | succ m ih =>
    rw [e_P_succ] at hu
    by_cases h : u < X.eP b' m
    · obtain ⟨i, hi, t, ht, rfl⟩ := ih h
      exact ⟨i, by omega, t, ht, rfl⟩
    · exact ⟨m, by omega, u - X.eP b' m, by omega, by omega⟩

theorem e_decomp {u : ℕ} (hu : u < X.eN b') :
    ∃ i < X.eM b', ∃ t ≤ X.eJ (X.eC b' i), u = X.eP b' i + t := e_decomp_aux _ hu

theorem e_C_cell (i : ℕ) : X.Γ'.cellOf (X.eC b' i) = X.Γ'.cellOf b' := by
  unfold eC
  rw [cellOf, cellOf, Orbit.mk_eq_mk]
  exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm

theorem e_C_of_cell {e' : X.D'} (h : X.Γ'.cellOf e' = X.Γ'.cellOf b') :
    ∃ i < X.eM b', X.eC b' i = e' := by
  have : X.Γ'.φ.SameCycle b' e' := Orbit.mk_eq_mk.1 h.symm
  exact e_exists_idx this

theorem e_C_inj {i j : ℕ} (hi : i < X.eM b') (hj : j < X.eM b') (h : X.eC b' i = X.eC b' j) :
    i = j := e_pow_inj hi hj h

theorem e_W_inj {u v : ℕ} (hu : u < X.eN b') (hv : v < X.eN b') (h : X.eW b' u = X.eW b' v) :
    u = v := by
  obtain ⟨i, hi, t, ht, rfl⟩ := e_decomp hu
  obtain ⟨j, hj, s, hs, rfl⟩ := e_decomp hv
  rw [e_W_pos i ht, e_W_pos j hs] at h
  have hc := e_pc_unique ht hs h
  have hij := e_C_inj hi hj hc
  subst hij
  rw [e_pc_idx ht hs h]

theorem e_W_α {u v : ℕ} (hu : u < X.eN b') (hv : v < X.eN b') :
    Γ.α (X.eW b' u) ≠ X.eW b' v := by
  obtain ⟨i, hi, t, ht, rfl⟩ := e_decomp hu
  obtain ⟨j, hj, s, hs, rfl⟩ := e_decomp hv
  rw [e_W_pos i ht, e_W_pos j hs, e_α_pc _ ht]
  intro h
  have hc := e_pc_unique (by rw [e_eJ_α]; omega) hs h
  apply X.Γ'.cellOf_α_ne (X.eC b' i)
  rw [hc, e_C_cell, e_C_cell]

theorem e_W_curve {u : ℕ} (hu : u < X.eN b') : Γ.curve (X.eW b' u) ∉ R := by
  obtain ⟨i, -, t, ht, rfl⟩ := e_decomp hu
  rw [e_W_pos i ht]; exact e_curve_pc_nmem _ _

theorem e_W_side {u : ℕ} (hu : u < X.eN b') :
    Γ.side (Γ.cellOf (X.eW b' u)) = X.Γ'.side (X.Γ'.cellOf b') := by
  obtain ⟨i, -, t, ht, rfl⟩ := e_decomp hu
  rw [e_W_pos i ht, e_side_pc _ ht, e_C_cell]

theorem e_crossing_W (u : ℕ) :
    Γ.crossingOf (X.eW b' (u + 1)) = Γ.crossingOf (Γ.α (X.eW b' u)) := by
  rw [e_W_succ]; exact e_crossing_nxt _

theorem e_W_succ_port {u : ℕ} (h : ¬ Γ.rK R (Γ.α (X.eW b' u))) :
    X.eW b' (u + 1) = Γ.straight (X.eW b' u) := by
  rw [e_W_succ]; unfold eNxt; rw [if_neg h]

theorem e_W_succ_corner {u : ℕ} (h : Γ.rK R (Γ.α (X.eW b' u))) :
    X.eW b' (u + 1) = Γ.φ (X.eW b' u) := by
  rw [e_W_succ]; unfold eNxt; rw [if_pos h]

/-- The boundary segments of the cell of `b'`, in `Γ`. -/
noncomputable def eE (b' : X.D') : Finset Γ.Segment :=
  (range (X.eN b')).image (fun t => Γ.segmentOf (X.eW b' t))

theorem e_E_even : Γ.IsEven (X.eE b') :=
  e_even _ _ (fun t _ => e_crossing_W t) e_W_N (fun _ hs _ ht h => e_W_inj hs ht h)
    (fun _ hs _ ht => e_W_α hs ht)

theorem e_mem_E {y : D} : Γ.segmentOf y ∈ X.eE b' ↔
    ∃ u < X.eN b', y = X.eW b' u ∨ y = Γ.α (X.eW b' u) := by
  unfold eE
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [j_segmentOf_eq_iff] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h | h⟩
    · exact ⟨u, hu, by rw [h]⟩
    · exact ⟨u, hu, by rw [h, j_segmentOf_α]⟩

/-- The last piece of `e'` lies on the boundary of the cell of `b'` iff `e'` or its reverse is in
that cell. -/
theorem e_last_mem_E (e' : X.D') :
    Γ.segmentOf (X.ePc e' (X.eJ e')) ∈ X.eE b' ↔
      X.Γ'.cellOf e' = X.Γ'.cellOf b' ∨ X.Γ'.cellOf (X.Γ'.α e') = X.Γ'.cellOf b' := by
  rw [e_mem_E]
  constructor
  · rintro ⟨u, hu, h | h⟩
    · obtain ⟨i, -, t, ht, rfl⟩ := e_decomp hu
      rw [e_W_pos i ht] at h
      left; rw [e_pc_unique le_rfl ht h, e_C_cell]
    · obtain ⟨i, -, t, ht, rfl⟩ := e_decomp hu
      rw [e_W_pos i ht] at h
      have h2 : X.ePc (X.Γ'.α e') 0 = X.ePc (X.eC b' i) t := by
        rw [e_pc_zero, e_ι_α', h, j_α_α]
      right; rw [e_pc_unique (Nat.zero_le _) ht h2, e_C_cell]
  · rintro (h | h)
    · obtain ⟨i, hi, rfl⟩ := e_C_of_cell h
      exact ⟨_, e_P_last_lt hi, Or.inl (e_W_pos i le_rfl).symm⟩
    · obtain ⟨i, hi, hc⟩ := e_C_of_cell h
      refine ⟨X.eP b' i, lt_of_le_of_lt (Nat.le_add_right _ _) (e_P_last_lt hi), Or.inr ?_⟩
      rw [e_W_P, hc, e_ι_α', j_α_α]

open Classical in
/-- **Jordan for the cell** (Step 2): a cut of `Γ` along the boundary walk of the cell `F'` of
`b'` that is `1` exactly on the cells of `Γ` of the darts `ι e'`, `e' ∈ F'`. -/
theorem e_inside : ∃ r : Γ.Cell → ZMod 2, Γ.IsCut (X.eE b') r ∧
    ∀ e', r (Γ.cellOf (X.ι e')) = if X.Γ'.cellOf e' = X.Γ'.cellOf b' then 1 else 0 := by
  obtain ⟨r0, hr0⟩ := Γ.exists_cut _ (e_E_even (X := X) (b' := b'))
  have hrR : ∀ w, Γ.curve w ∈ R → r0 (Γ.cellOf (Γ.α w)) = r0 (Γ.cellOf w) := by
    intro w hw
    have h := hr0 w
    rw [if_neg] at h
    · exact (j_zmod2_eq_add_of_add_eq h).trans (add_zero _)
    · rw [e_mem_E]
      rintro ⟨u, hu, h1 | h1⟩
      · exact e_W_curve hu (h1 ▸ hw)
      · exact e_W_curve hu (by rw [← j_curve_α, ← h1]; exact hw)
  set ind : X.D' → ZMod 2 := fun e' => if X.Γ'.cellOf e' = X.Γ'.cellOf b' then 1 else 0
  set H : X.D' → ZMod 2 := fun e' => r0 (Γ.cellOf (X.ι e')) + ind e' with hH
  have hHφ : ∀ e', H (X.Γ'.φ e') = H e' := by
    intro e'
    simp only [hH, ind, X.Γ'.j_cellOf_φ]
    rw [e_ι_φ, Γ.j_cellOf_φ, e_cell_pc r0 hrR e' le_rfl]
  have hHα : ∀ e', H (X.Γ'.α e') = H e' := by
    intro e'
    have h := hr0 (X.ePc e' (X.eJ e'))
    rw [e_cell_pc r0 hrR e' le_rfl, ← e_ι_α'] at h
    have hne : ¬ (X.Γ'.cellOf e' = X.Γ'.cellOf b' ∧
        X.Γ'.cellOf (X.Γ'.α e') = X.Γ'.cellOf b') := fun ⟨h1, h2⟩ =>
      X.Γ'.cellOf_α_ne e' (h2.trans h1.symm)
    simp only [hH, ind]
    by_cases h1 : X.Γ'.cellOf e' = X.Γ'.cellOf b' <;>
      by_cases h2 : X.Γ'.cellOf (X.Γ'.α e') = X.Γ'.cellOf b'
    · exact absurd ⟨h1, h2⟩ hne
    · rw [if_pos ((e_last_mem_E e').2 (Or.inl h1))] at h
      rw [if_pos h1, if_neg h2, add_zero, j_zmod2_eq_add_of_add_eq h]
    · rw [if_pos ((e_last_mem_E e').2 (Or.inr h2))] at h
      rw [if_neg h1, if_pos h2, add_zero, j_zmod2_eq_add_of_add_eq h, add_assoc,
        j_zmod2_add_self, add_zero]
    · rw [if_neg (fun h' => by rcases (e_last_mem_E e').1 h' with h' | h' <;> contradiction)] at h
      rw [if_neg h1, if_neg h2, add_zero, add_zero, j_zmod2_eq_add_of_add_eq h, add_zero]
  have hconst : ∀ e', H e' = H b' := by
    intro e'
    refine X.Γ'.j_eqvGen_rec (P := fun a c => H a = H c) (fun a => ?_) (fun a => (hHα a).symm)
      (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2) e' b'
    show H a = H (X.Γ'.σ a)
    rw [show X.Γ'.σ a = X.Γ'.φ (X.Γ'.α a) by rw [j_φ_apply, j_α_α], hHφ, hHα]
  refine ⟨fun c => r0 c + H b', fun y => ?_, fun e' => ?_⟩
  · show r0 _ + H b' + (r0 _ + H b') = _
    rw [← hr0 y]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
  · show r0 _ + H b' = ind e'
    rw [← hconst e']
    simp only [hH]
    rw [← add_assoc, j_zmod2_add_self, zero_add]

end Removal

end SConf

end Pca.Sweep
