/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-! # A small verified LRAT (RUP) checker

Clauses are lists of nonzero integers (DIMACS literals). `check f prf = true` implies that no
assignment satisfies all clauses of `f` (`check_sound`). The checker is written with `List.rec`
and the assumed literals are kept as two bit sets (`ℕ`, positive and negative literals), so the
kernel evaluates it quickly with `decide +kernel` (no `native_decide`, no extra axioms). Only RUP
steps are supported (cadical's LRAT for these formulas has no RAT steps); deletions are ignored.

`code_sound` translates literals over an arbitrary variable type into integer literals for an
injective code of the variables, and `rename_sound` renames integer variables by a table.
-/

namespace NonCirc.Sat

/-- Truth value of a nonzero integer literal. -/
def evalLit (a : ℕ → Bool) (l : ℤ) : Bool := if 0 < l then a l.natAbs else !a l.natAbs

/-- Truth value of an integer clause. -/
def evalClause (a : ℕ → Bool) (c : List ℤ) : Bool := c.any (evalLit a)

/-- Assumed literals: bit `v` of the first set means `v` is assumed true, of the second `-v`. -/
abbrev Asg := ℕ × ℕ

/-- `l` is assumed. -/
def isAsg (A : Asg) (l : ℤ) : Bool := if 0 < l then A.1.testBit l.natAbs else A.2.testBit l.natAbs

/-- Assume `l`. -/
def addAsg (A : Asg) (l : ℤ) : Asg :=
  if 0 < l then (A.1 ||| 1 <<< l.natAbs, A.2) else (A.1, A.2 ||| 1 <<< l.natAbs)

/-- The clause with id `h` in the database. -/
def lookupCl (db : List (ℕ × List ℤ)) (h : ℕ) : Option (List ℤ) :=
  List.rec (motive := fun _ => Option (List ℤ)) none
    (fun p _ ih => if p.1 == h then some p.2 else ih) db

/-- `cl` contains `0` or an assumed literal. -/
def bad (A : Asg) (cl : List ℤ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun l _ ih => (0 : ℤ) == l || isAsg A l || ih) cl

/-- The literals of `cl` whose negation is not assumed. -/
def surv (A : Asg) (cl : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun l _ ih => if isAsg A (-l) then ih else l :: ih) cl

/-- Unit propagation along the hints. Returns `true` iff a hint clause becomes falsified. -/
def propagate (db : List (ℕ × List ℤ)) (hs : List ℕ) : Asg → Bool :=
  List.rec (motive := fun _ => Asg → Bool) (fun _ => false)
    (fun h _ ih A =>
      match lookupCl db h with
      | none => false
      | some cl =>
        if bad A cl then false
        else
          match surv A cl with
          | [] => true
          | [l] => ih (addAsg A l)
          | _ => false) hs

/-- Assume the negations of the literals of `cl`. -/
def negAsg (cl : List ℤ) : Asg :=
  List.rec (motive := fun _ => Asg) (0, 0) (fun l _ ih => addAsg ih (-l)) cl

/-- `0 ∈ cl`. -/
def hasZero (cl : List ℤ) : Bool := List.rec (motive := fun _ => Bool) false (fun l _ ih => (0 : ℤ) == l || ih) cl

/-- Check the RUP steps `(id, clause, hints)` in order; succeed at the empty clause. -/
def checkSteps (prf : List (ℕ × List ℤ × List ℕ)) : List (ℕ × List ℤ) → Bool :=
  List.rec (motive := fun _ => List (ℕ × List ℤ) → Bool) (fun _ => false)
    (fun st _ ih db =>
      !hasZero st.2.1 && propagate db st.2.2 (negAsg st.2.1) &&
        (st.2.1.isEmpty || ih ((st.1, st.2.1) :: db))) prf

/-- The original clauses with ids `1, 2, ...`. -/
def indexed : ℕ → List (List ℤ) → List (ℕ × List ℤ)
  | _, [] => []
  | i, c :: cs => (i, c) :: indexed (i + 1) cs

/-- The checker. -/
def check (f : List (List ℤ)) (prf : List (ℕ × List ℤ × List ℕ)) : Bool :=
  checkSteps prf (indexed 1 f)

/-! ## Soundness -/

lemma evalLit_neg (a : ℕ → Bool) {l : ℤ} (hl : l ≠ 0) : evalLit a (-l) = !evalLit a l := by
  unfold evalLit
  rcases lt_trichotomy l 0 with h | h | h
  · have : 0 < -l := by omega
    simp [h, not_lt.mpr h.le, Int.natAbs_neg]
  · exact absurd h hl
  · have : ¬ 0 < -l := by omega
    simp [h, h.le, Int.natAbs_neg]

lemma isAsg_addAsg (A : Asg) {l x : ℤ}
    (h : isAsg (addAsg A l) x = true) : isAsg A x = true ∨ x = l := by
  unfold isAsg addAsg at h
  unfold isAsg
  by_cases hl0 : 0 < l <;> by_cases hx0 : 0 < x <;>
    simp only [hl0, hx0, if_true, if_false, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  · rcases h with h | h
    · exact Or.inl h
    · right; omega
  · exact Or.inl h
  · exact Or.inl h
  · rcases h with h | h
    · exact Or.inl h
    · right; omega

lemma bad_cons (A : Asg) (x : ℤ) (cl : List ℤ) :
    bad A (x :: cl) = ((0 : ℤ) == x || isAsg A x || bad A cl) := rfl
lemma surv_cons (A : Asg) (x : ℤ) (cl : List ℤ) :
    surv A (x :: cl) = if isAsg A (-x) then surv A cl else x :: surv A cl := rfl
lemma hasZero_cons (x : ℤ) (cl : List ℤ) : hasZero (x :: cl) = ((0 : ℤ) == x || hasZero cl) := rfl
lemma negAsg_cons (x : ℤ) (cl : List ℤ) : negAsg (x :: cl) = addAsg (negAsg cl) (-x) := rfl
lemma lookupCl_cons (p : ℕ × List ℤ) (db : List (ℕ × List ℤ)) (h : ℕ) :
    lookupCl (p :: db) h = if p.1 == h then some p.2 else lookupCl db h := rfl

/-- All assumed literals are true. -/
def Inv (a : ℕ → Bool) (A : Asg) : Prop := ∀ l : ℤ, l ≠ 0 → isAsg A l = true → evalLit a l = true

lemma Inv.add {a : ℕ → Bool} {A : Asg} (h : Inv a A) {l : ℤ} (hl : l ≠ 0)
    (ht : evalLit a l = true) : Inv a (addAsg A l) := by
  intro x hx hxa
  rcases isAsg_addAsg A hxa with hxa | rfl
  · exact h x hx hxa
  · exact ht

lemma lookupCl_mem (db : List (ℕ × List ℤ)) (h : ℕ) (cl : List ℤ) (e : lookupCl db h = some cl) :
    (h, cl) ∈ db := by
  induction db with
  | nil => simp [lookupCl] at e
  | cons p rest ih =>
    obtain ⟨i, c⟩ := p
    rw [lookupCl_cons] at e
    split_ifs at e with hi
    · cases e; simp at hi; simp [hi]
    · exact List.mem_cons_of_mem _ (ih e)

lemma bad_false {A : Asg} {cl : List ℤ} (h : bad A cl = false) :
    ∀ l ∈ cl, l ≠ 0 ∧ isAsg A l = false := by
  induction cl with
  | nil => simp
  | cons x cl ih =>
    rw [bad_cons] at h
    simp only [Bool.or_eq_false_iff] at h
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · refine ⟨fun e => ?_, h.1.2⟩
      have := h.1.1
      rw [e] at this
      exact absurd this (by decide)
    · exact ih h.2 l hl

lemma mem_surv {A : Asg} {cl : List ℤ} {l : ℤ} (hl : l ∈ cl) (hn : isAsg A (-l) = false) :
    l ∈ surv A cl := by
  induction cl with
  | nil => simp at hl
  | cons x cl ih =>
    rw [surv_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · rw [if_neg (by simp [hn])]; simp
    · split_ifs
      · exact ih hl
      · exact List.mem_cons_of_mem _ (ih hl)

lemma propagate_sound (a : ℕ → Bool) (db : List (ℕ × List ℤ))
    (hdb : ∀ p ∈ db, evalClause a p.2 = true) (hs : List ℕ) :
    ∀ A, Inv a A → propagate db hs A = false := by
  induction hs with
  | nil => intro A _; rfl
  | cons h hs ih =>
    intro A hA
    simp only [propagate] at ih ⊢
    rcases e : lookupCl db h with _ | cl
    · rfl
    · simp only
      have hcl' := hdb _ (lookupCl_mem db h cl e)
      split_ifs with hb
      · rfl
      · have hb' := bad_false (Bool.eq_false_iff.2 hb)
        obtain ⟨l, hl, hlt⟩ := List.any_eq_true.1 hcl'
        have hl0 := (hb' l hl).1
        have hn : isAsg A (-l) = false := by
          by_contra hc
          have := hA (-l) (neg_ne_zero.2 hl0) (by simpa using hc)
          rw [evalLit_neg a hl0, hlt] at this
          exact absurd this (by decide)
        have hsurv := mem_surv hl hn
        split
        · next he => rw [he] at hsurv; simp at hsurv
        · next l' he =>
          rw [he, List.mem_singleton] at hsurv
          subst hsurv
          exact ih (addAsg A l) (hA.add hl0 hlt)
        · rfl

lemma hasZero_false {cl : List ℤ} (h : hasZero cl = false) : ∀ l ∈ cl, l ≠ 0 := by
  induction cl with
  | nil => simp
  | cons x cl ih =>
    rw [hasZero_cons] at h
    simp only [Bool.or_eq_false_iff] at h
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · intro e
      have := h.1
      rw [e] at this
      exact absurd this (by decide)
    · exact ih h.2 l hl

lemma negAsg_inv (a : ℕ → Bool) {cl : List ℤ} (h0 : ∀ l ∈ cl, l ≠ 0)
    (hf : ∀ l ∈ cl, evalLit a l = false) : Inv a (negAsg cl) := by
  induction cl with
  | nil =>
    intro x _ hx
    simp [negAsg, isAsg] at hx
  | cons l cl ih =>
    rw [negAsg_cons]
    have hl0 := h0 l (by simp)
    refine (ih (fun x hx => h0 x (by simp [hx])) (fun x hx => hf x (by simp [hx]))).add
      (neg_ne_zero.2 hl0) ?_
    rw [evalLit_neg a hl0, hf l (by simp)]; rfl

lemma rup_sound (a : ℕ → Bool) (db : List (ℕ × List ℤ))
    (hdb : ∀ p ∈ db, evalClause a p.2 = true) (cl : List ℤ) (hints : List ℕ)
    (h0 : hasZero cl = false) (hp : propagate db hints (negAsg cl) = true) :
    evalClause a cl = true := by
  by_contra hf
  simp only [evalClause, Bool.not_eq_true, List.any_eq_false] at hf
  have := propagate_sound a db hdb hints _ (negAsg_inv a (hasZero_false h0) (by simpa using hf))
  rw [hp] at this
  exact absurd this (by decide)

lemma checkSteps_sound (a : ℕ → Bool) (prf : List (ℕ × List ℤ × List ℕ)) :
    ∀ db : List (ℕ × List ℤ), (∀ p ∈ db, evalClause a p.2 = true) → checkSteps prf db = false := by
  induction prf with
  | nil => intro db _; rfl
  | cons st rest ih =>
    intro db hdb
    obtain ⟨i, cl, hints⟩ := st
    simp only [checkSteps] at ih ⊢
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.or_eq_true, List.isEmpty_iff] at hc
    obtain ⟨⟨h0, hp⟩, hrest⟩ := hc
    have hcl := rup_sound a db hdb cl hints h0 hp
    rcases hrest with he | hrest
    · subst he; simp [evalClause] at hcl
    · have := ih ((i, cl) :: db) (by
        intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hcl
        · exact hdb p hp')
      rw [hrest] at this
      exact absurd this (by decide)

lemma mem_indexed : ∀ (i : ℕ) (f : List (List ℤ)) (p : ℕ × List ℤ), p ∈ indexed i f → p.2 ∈ f
  | _, [], p, h => by simp [indexed] at h
  | i, c :: cs, p, h => by
    simp only [indexed, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_indexed (i + 1) cs p h)

/-- **Soundness of the checker.** -/
theorem check_sound (f : List (List ℤ)) (prf : List (ℕ × List ℤ × List ℕ))
    (h : check f prf = true) (a : ℕ → Bool) : ¬ ∀ c ∈ f, evalClause a c = true := by
  intro hf
  have := checkSteps_sound a prf (indexed 1 f) (fun p hp => hf _ (mem_indexed 1 f p hp))
  unfold check at h
  rw [h] at this
  exact absurd this (by decide)

/-! ## Renaming the variables by a table -/

/-- The literal `±i` renamed to `±(ren[i-1] + 1)`. -/
def unren (ren : List ℕ) (l : ℤ) : ℤ :=
  if 0 < l then ((ren.getD (l.natAbs - 1) 0 + 1 : ℕ) : ℤ) else -((ren.getD (l.natAbs - 1) 0 + 1 : ℕ) : ℤ)

theorem rename_sound (ren : List ℕ) (f g : List (List ℤ)) (hfg : f.map (·.map (unren ren)) = g)
    (prf : List (ℕ × List ℤ × List ℕ)) (h : check f prf = true) (a : ℕ → Bool) :
    ¬ ∀ c ∈ g, evalClause a c = true := by
  intro hg
  apply check_sound f prf h (fun i => a (ren.getD (i - 1) 0 + 1))
  intro c hc
  obtain ⟨l, hl, hlt⟩ := List.any_eq_true.1 (hg _ (hfg ▸ List.mem_map.2 ⟨c, hc, rfl⟩))
  obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
  refine List.any_eq_true.2 ⟨l0, hl0, ?_⟩
  unfold unren evalLit at hlt
  unfold evalLit
  by_cases hp : 0 < l0
  · simp only [hp, if_true] at hlt ⊢
    rw [if_pos (by omega), Int.natAbs_natCast] at hlt
    exact hlt
  · simp only [hp, if_false] at hlt ⊢
    rw [if_neg (by omega), Int.natAbs_neg, Int.natAbs_natCast] at hlt
    exact hlt

/-! ## Numbering the variables by an injective code -/

variable {V : Type}

/-- The integer literal of `(v, polarity)` for an injective variable code. -/
def litOf (code : V → ℕ) (l : V × Bool) : ℤ :=
  if l.2 then ((code l.1 + 1 : ℕ) : ℤ) else -((code l.1 + 1 : ℕ) : ℤ)

open Classical in
/-- An assignment satisfying `f` gives one satisfying every coded clause of `f`. -/
theorem code_sat (code : V → ℕ) (hinj : Function.Injective code) (f : List (List (V × Bool)))
    (cnf : List (List ℤ)) (hsub : ∀ c ∈ cnf, ∃ c0 ∈ f, c = c0.map (litOf code))
    (A : V → Bool) (hf : ∀ c ∈ f, c.any (fun l => A l.1 == l.2) = true) :
    ∃ a : ℕ → Bool, ∀ c ∈ cnf, evalClause a c = true := by
  let a : ℕ → Bool := fun i => if hi : ∃ v, code v + 1 = i then A (Classical.choose hi) else false
  have ha : ∀ v, a (code v + 1) = A v := by
    intro v
    have hi : ∃ w, code w + 1 = code v + 1 := ⟨v, rfl⟩
    simp only [a, dif_pos hi]
    congr 1
    exact hinj (by have := Classical.choose_spec hi; omega)
  refine ⟨a, fun c hc => ?_⟩
  obtain ⟨c0, hc0, rfl⟩ := hsub c hc
  obtain ⟨l, hl, hlt⟩ := List.any_eq_true.1 (hf c0 hc0)
  refine List.any_eq_true.2 ⟨litOf code l, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
  obtain ⟨v, b⟩ := l
  have hpos : (0 : ℤ) < ((code v + 1 : ℕ) : ℤ) := by omega
  cases b
  · simp only [litOf, evalLit, Bool.false_eq_true, if_false]
    rw [if_neg (by omega), Int.natAbs_neg, Int.natAbs_natCast, ha]
    simpa using hlt
  · simp only [litOf, evalLit, if_true]
    rw [if_pos hpos, Int.natAbs_natCast, ha]
    simpa using hlt

end NonCirc.Sat
