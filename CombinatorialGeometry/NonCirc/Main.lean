/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.EncodeSound
import NonCirc.Checker

/-! # From a checked LRAT proof to non-circularizability

`not_circularizable_of_check`: if the verified checker accepts an LRAT proof for some clauses of
the coded encoding of `F` with some tags (selected by position in each tag), then `F` has no plane
circle realization. The checker runs on a literal clause list with small variable numbers; its
renaming by the table `ren` is compared with the selected coded clauses by `decide +kernel`., then `F` has no plane circle realization. Per arrangement, the
hypothesis is discharged by `decide +kernel`.

`emit` (not part of any proof) prints the numbered CNF in DIMACS format, with the index of the
tag that produced each clause, for the script that runs the SAT solver.
-/

namespace NonCirc

/-- The coded clauses of the tags at the given positions (`sels` is aligned with `tags`;
invalid positions are skipped). -/
def selectTags (F : Fingerprint) (tags : List Tag) (sels : List (List ℕ)) : List (List ℤ) :=
  (tags.zip sels).flatMap fun p => p.2.filterMap fun i => ((F.encodeTag p.1)[i]?).map (·.map (Sat.litOf varCode))

lemma mem_selectTags {F : Fingerprint} {tags : List Tag} {sels : List (List ℕ)} {c : List ℤ}
    (h : c ∈ selectTags F tags sels) : ∃ c0 ∈ F.encode tags, c = c0.map (Sat.litOf varCode) := by
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hc
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hi
  exact ⟨c0, List.mem_flatMap.2 ⟨p.1, (List.of_mem_zip hp).1, List.mem_of_getElem? hc0⟩, rfl⟩

theorem not_circularizable_of_check (F : Fingerprint) (tags : List Tag) (sels : List (List ℕ))
    (ren : List ℕ) (cnf : List (List ℤ)) (prf : List (ℕ × List ℤ × List ℕ))
    (hsel : cnf.map (·.map (Sat.unren ren)) = selectTags F tags sels)
    (h : Sat.check cnf prf = true) :
    ¬ ∃ (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ), F.IsCircleRealization c r ε P := by
  rintro ⟨c, r, ε, P, R⟩
  obtain ⟨a, ha⟩ := Sat.code_sat varCode varCode_inj _ (selectTags F tags sels)
    (fun c hc => mem_selectTags hc) (assign c r ε P) (fun cl hcl => R.encode_sound tags cl hcl)
  exact Sat.rename_sound ren cnf _ hsel prf h a ha

/-- The coded CNF, one clause per line, each preceded by `c tag <i>` (the producing tag). -/
def emit (F : Fingerprint) (tags : List Tag) : String :=
  let withTag := (tags.zipIdx).flatMap fun (t, i) => (F.encodeTag t).map fun cl => (i, cl)
  String.intercalate "\n" (withTag.map fun (i, cl) =>
    s!"c tag {i}\n" ++ String.intercalate " " ((cl.map (Sat.litOf varCode)).map toString) ++ " 0")
    ++ "\n"

end NonCirc
