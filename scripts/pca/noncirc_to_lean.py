#!/usr/bin/env python3
"""Generate the Lean proof that N_6^3 is not circularizable (`NonCirc/N63.lean`).

Generated from the fingerprint, not written by hand:

* the side table `side j k s m` (all 30 crossings x 4 circles), read off the fingerprint with
  `noncirc.fingerprint` (which asserts that the two lists through a crossing agree);
* one lemma per side fact the proof uses (`side_J_K_[pm]_M`, direction from the table);
* for every crossing pair used: `pair_J_K`, `pi_J_K` (`<p+, p-> < 0`, with a separating
  circle chosen from the table) and `K_J_K` (`[v_J v_K p+ p-] != 0`);
* `sep_..` lemmas (`<p, q> < 0` for two crossing points, separating circle from the table).

The proof steps (ties, the four applications of the pair lemma, the two final GP relations)
follow the hand proof of Theorem N63 in the (unpublished) realizability notes; they are the fixed
template `PROOF` below (layer 2, generating them from the stage-4 core, is not done yet). If a
side sign assumed by the template disagrees with the table, Lean rejects the file.

Usage (from `pca/lean`):

    python3 scripts/noncirc_to_lean.py [--check]

`--check` compiles the file with `lake env lean` (needs `lake build NonCirc.Plane` first) and
requires the final `#print axioms` to list only Lean's standard axioms.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LEAN_DIR.parent))
from noncirc.fingerprint import parse_fingerprint  # noqa: E402

FP_FILE = Path.home() / "github/rusty-realize/tests/data/all6_digonfree_nonrealizable.txt"
FP_LINE = 3
CERT = "noncirc/certificates/all6_digonfree_nonrealizable_3_F123_P2.txt"
OUT = LEAN_DIR / "NonCirc" / "N63.lean"
STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Proof template. Point `p j k s` is written `𝐩 j k s`, circle vector `𝐯 i`, and
# `𝐊 j k = [v_j v_k p+_jk p-_jk]`. Names side_*, sep_*, pair_*, pi_*, K_* are generated.
PROOF = r"""
/-! ### Type-3 brackets at `p = p⁺₁₂`: `[1 2 k p]` has the sign of `K₁₂` -/

lemma b12k_4 : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1) * 𝐊 1 2 :=
  cancel_pos ((pair_1_2 R).type3_sign (K_1_2 R) (pi_1_2 R) (side_1_2_p_4 R).ne') (side_1_2_p_4 R)

lemma b12k_5 : 0 < br (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 1 2 1) * 𝐊 1 2 :=
  cancel_pos ((pair_1_2 R).type3_sign (K_1_2 R) (pi_1_2 R) (side_1_2_p_5 R).ne') (side_1_2_p_5 R)

lemma b12k_6 : 0 < br (𝐯 1) (𝐯 2) (𝐯 6) (𝐩 1 2 1) * 𝐊 1 2 :=
  cancel_pos ((pair_1_2 R).type3_sign (K_1_2 R) (pi_1_2 R) (side_1_2_p_6 R).ne') (side_1_2_p_6 R)

/-! ### Krupp ties: `K₁₂, K₁₄, K₂₅, K₃₄` have the same sign (the notes' `μ = -sign K₁₂`) -/

/-- Krupp triple 124. -/
lemma tie_12_14 : 0 < 𝐊 1 2 * 𝐊 1 4 := by
  have kr := (pair_1_2 R).krupp_sign (K_1_2 R) (pi_1_2 R) (c := 𝐯 4) (q := 𝐩 1 4 1)
    (mul_neg_of_pos_of_neg (side_1_2_p_4 R) (side_1_2_m_4 R))
    (ip_points_nonpos (isPoint P 1 4 1) (isPoint P 1 2 1))
    (ip_points_nonpos (isPoint P 1 4 1) (isPoint P 1 2 (-1))) (Or.inl (sep_1_4_p_1_2_p R))
  have b := cancel_neg ((pair_1_4 R).type3_sign (K_1_4 R) (pi_1_4 R) (side_1_4_p_2 R).ne)
    (side_1_4_p_2 R)
  rw [br_swap12 (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 4 1)] at b
  have b' : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 4 1) * 𝐊 1 4 := by linarith
  have a := b12k_4 R
  exact ss_trans (ss_trans (by linarith : 0 < 𝐊 1 2 * br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1))
    (by linarith : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1) * br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 4 1))) b'

/-- Krupp triple 125. -/
lemma tie_12_25 : 0 < 𝐊 1 2 * 𝐊 2 5 := by
  have kr := (pair_1_2 R).krupp_sign (K_1_2 R) (pi_1_2 R) (c := 𝐯 5) (q := 𝐩 2 5 1)
    (mul_neg_of_pos_of_neg (side_1_2_p_5 R) (side_1_2_m_5 R))
    (ip_points_nonpos (isPoint P 2 5 1) (isPoint P 1 2 1))
    (ip_points_nonpos (isPoint P 2 5 1) (isPoint P 1 2 (-1))) (Or.inr (sep_2_5_p_1_2_m R))
  have b := cancel_pos ((pair_2_5 R).type3_sign (K_2_5 R) (pi_2_5 R) (side_2_5_p_1 R).ne')
    (side_2_5_p_1 R)
  rw [br_swap12 (𝐯 2) (𝐯 1) (𝐯 5) (𝐩 2 5 1), br_swap01 (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 2 5 1), neg_neg] at b
  have a := b12k_5 R
  exact ss_trans (ss_trans (by linarith : 0 < 𝐊 1 2 * br (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 1 2 1))
    (by linarith : 0 < br (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 1 2 1) * br (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 2 5 1))) b

/-- Krupp triple 134. -/
lemma tie_34_14 : 0 < 𝐊 3 4 * 𝐊 1 4 := by
  have kr := (pair_1_4 R).krupp_sign (K_1_4 R) (pi_1_4 R) (c := 𝐯 3) (q := 𝐩 3 4 1)
    (mul_neg_of_neg_of_pos (side_1_4_p_3 R) (side_1_4_m_3 R))
    (ip_points_nonpos (isPoint P 3 4 1) (isPoint P 1 4 1))
    (ip_points_nonpos (isPoint P 3 4 1) (isPoint P 1 4 (-1))) (Or.inl (sep_3_4_p_1_4_p R))
  rw [br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 3 4 1), br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1)] at kr
  have b := cancel_pos ((pair_3_4 R).type3_sign (K_3_4 R) (pi_3_4 R) (side_3_4_p_1 R).ne')
    (side_3_4_p_1 R)
  rw [br_swap12 (𝐯 3) (𝐯 1) (𝐯 4) (𝐩 3 4 1), br_swap01 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 3 4 1), neg_neg] at b
  have d := cancel_neg ((pair_1_4 R).type3_sign (K_1_4 R) (pi_1_4 R) (side_1_4_p_3 R).ne)
    (side_1_4_p_3 R)
  rw [br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1)] at d
  exact ss_trans (ss_trans (by linarith : 0 < 𝐊 3 4 * br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 3 4 1))
    (by linarith : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 3 4 1) * br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1)))
    (by linarith : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1) * 𝐊 1 4)

lemma tie_12_34 : 0 < 𝐊 1 2 * 𝐊 3 4 := by
  have h1 := tie_12_14 R
  have h2 := tie_34_14 R
  exact ss_trans h1 (by linarith : 0 < 𝐊 1 4 * 𝐊 3 4)

/-! ### Krupp brackets at `p = p⁺₁₂` -/

/-- Krupp triple 134: `[1 3 4 p]` has the sign of `K₁₂`. -/
lemma b134 : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 2 1) * 𝐊 1 2 := by
  have kr := (pair_1_4 R).krupp_sign (K_1_4 R) (pi_1_4 R) (c := 𝐯 3) (q := 𝐩 1 2 1)
    (mul_neg_of_neg_of_pos (side_1_4_p_3 R) (side_1_4_m_3 R))
    (ip_points_nonpos (isPoint P 1 2 1) (isPoint P 1 4 1))
    (ip_points_nonpos (isPoint P 1 2 1) (isPoint P 1 4 (-1))) (Or.inl (sep_1_2_p_1_4_p R))
  rw [br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 2 1), br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1)] at kr
  have d := cancel_neg ((pair_1_4 R).type3_sign (K_1_4 R) (pi_1_4 R) (side_1_4_p_3 R).ne)
    (side_1_4_p_3 R)
  rw [br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1)] at d
  have t := tie_12_14 R
  exact ss_trans (ss_trans (by linarith : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 2 1) *
      br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1))
    (by linarith : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 4 1) * 𝐊 1 4)) (by linarith : 0 < 𝐊 1 4 * 𝐊 1 2)

/-- Krupp triple 146: `[1 4 6 p]` has the sign of `K₁₂`. -/
lemma b146 : 0 < br (𝐯 1) (𝐯 4) (𝐯 6) (𝐩 1 2 1) * 𝐊 1 2 := by
  have kr := (pair_1_4 R).krupp_sign (K_1_4 R) (pi_1_4 R) (c := 𝐯 6) (q := 𝐩 1 2 1)
    (mul_neg_of_pos_of_neg (side_1_4_p_6 R) (side_1_4_m_6 R))
    (ip_points_nonpos (isPoint P 1 2 1) (isPoint P 1 4 1))
    (ip_points_nonpos (isPoint P 1 2 1) (isPoint P 1 4 (-1))) (Or.inl (sep_1_2_p_1_4_p R))
  have d := cancel_pos ((pair_1_4 R).type3_sign (K_1_4 R) (pi_1_4 R) (side_1_4_p_6 R).ne')
    (side_1_4_p_6 R)
  have t := tie_12_14 R
  exact ss_trans (ss_trans kr d) (by linarith : 0 < 𝐊 1 4 * 𝐊 1 2)

/-! ### The four applications of the pair lemma (exactly one of `abc`, `abd` Krupp) -/

/-- `(a,b;c,d) = (1,2;3,4)`. -/
lemma r1 : 0 < br (𝐯 1) (𝐯 2) (𝐯 3) (𝐯 4) * 𝐊 1 2 :=
  cancel_neg' ((pair_1_2 R).pairgp_sign (K_1_2 R) (pi_1_2 R).ne (c := 𝐯 3) (d := 𝐯 4)
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (side_1_2_p_3 R) (side_1_2_m_4 R))
      (mul_pos (side_1_2_m_3 R) (side_1_2_p_4 R))))
    (mul_neg_of_pos_of_neg (side_1_2_p_3 R) (side_1_2_m_4 R))

/-- `(a,b;c,d) = (1,4;2,5)`. -/
lemma r2 : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 5) * 𝐊 1 2 < 0 := by
  have h := cancel_neg' ((pair_1_4 R).pairgp_sign (K_1_4 R) (pi_1_4 R).ne (c := 𝐯 2) (d := 𝐯 5)
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (side_1_4_p_2 R) (side_1_4_m_5 R))
      (mul_pos (side_1_4_m_2 R) (side_1_4_p_5 R))))
    (mul_neg_of_neg_of_pos (side_1_4_p_2 R) (side_1_4_m_5 R))
  rw [br_swap12 (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 5)] at h
  have t := tie_12_14 R
  exact os_trans (by linarith : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 5) * 𝐊 1 4 < 0)
    (by linarith : 0 < 𝐊 1 4 * 𝐊 1 2)

/-- `(a,b;c,d) = (2,5;1,6)`. -/
lemma r3 : br (𝐯 1) (𝐯 2) (𝐯 5) (𝐯 6) * 𝐊 1 2 < 0 := by
  have h := cancel_pos' ((pair_2_5 R).pairgp_sign (K_2_5 R) (pi_2_5 R).ne (c := 𝐯 1) (d := 𝐯 6)
    (mul_neg_of_pos_of_neg (mul_pos (side_2_5_p_1 R) (side_2_5_m_6 R))
      (mul_neg_of_neg_of_pos (side_2_5_m_1 R) (side_2_5_p_6 R))))
    (mul_pos (side_2_5_p_1 R) (side_2_5_m_6 R))
  rw [br_swap12 (𝐯 2) (𝐯 1) (𝐯 5) (𝐯 6), br_swap01 (𝐯 1) (𝐯 2) (𝐯 5) (𝐯 6), neg_neg] at h
  have t := tie_12_25 R
  exact os_trans h (by linarith : 0 < 𝐊 2 5 * 𝐊 1 2)

/-- `(a,b;c,d) = (3,4;1,6)`. -/
lemma r4 : 0 < br (𝐯 1) (𝐯 3) (𝐯 4) (𝐯 6) * 𝐊 1 2 := by
  have h := cancel_neg' ((pair_3_4 R).pairgp_sign (K_3_4 R) (pi_3_4 R).ne (c := 𝐯 1) (d := 𝐯 6)
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (side_3_4_p_1 R) (side_3_4_m_6 R))
      (mul_pos_of_neg_of_neg (side_3_4_m_1 R) (side_3_4_p_6 R))))
    (mul_neg_of_pos_of_neg (side_3_4_p_1 R) (side_3_4_m_6 R))
  rw [br_swap12 (𝐯 3) (𝐯 1) (𝐯 4) (𝐯 6), br_swap01 (𝐯 1) (𝐯 3) (𝐯 4) (𝐯 6), neg_neg] at h
  have t := tie_12_34 R
  exact ss_trans h (by linarith : 0 < 𝐊 3 4 * 𝐊 1 2)

/-! ### The two final Grassmann-Plücker relations give opposite signs for `[1 2 4 6]` -/

/-- GP relation with `(a,b,c,d,e,f) = (1,4,2,3,6,p)`: `[1 2 4 6]` has the sign of `K₁₂`. -/
lemma final1 : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 6) * 𝐊 1 2 := by
  have g := gp3 (𝐯 1) (𝐯 4) (𝐯 2) (𝐯 3) (𝐯 6) (𝐩 1 2 1)
  have e1 : br (𝐯 1) (𝐯 4) (𝐯 2) (𝐯 3) = br (𝐯 1) (𝐯 2) (𝐯 3) (𝐯 4) := by
    rw [br_expand, br_expand]; ring
  rw [e1, br_swap12 (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1), br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐯 6),
    br_swap12 (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 6), br_swap12 (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 2 1)] at g
  have h1 := r1 R
  have h2 := b146 R
  have h3 := b12k_4 R
  have h4 := r4 R
  have h5 := b134 R
  have x1 : 0 < br (𝐯 1) (𝐯 2) (𝐯 3) (𝐯 4) * br (𝐯 1) (𝐯 4) (𝐯 6) (𝐩 1 2 1) :=
    ss_trans h1 (by linarith : 0 < 𝐊 1 2 * br (𝐯 1) (𝐯 4) (𝐯 6) (𝐩 1 2 1))
  have x2 : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1) * br (𝐯 1) (𝐯 3) (𝐯 4) (𝐯 6) :=
    ss_trans h3 (by linarith : 0 < 𝐊 1 2 * br (𝐯 1) (𝐯 3) (𝐯 4) (𝐯 6))
  have x3 : 0 < br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 6) * br (𝐯 1) (𝐯 3) (𝐯 4) (𝐩 1 2 1) := by linarith
  exact ss_trans x3 h5

/-- GP relation with `(a,b,c,d,e,f) = (1,2,4,5,6,p)`: `[1 2 4 6]` has the sign of `-K₁₂`. -/
lemma final2 : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 6) * 𝐊 1 2 < 0 := by
  have g := gp3 (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 5) (𝐯 6) (𝐩 1 2 1)
  have h1 := r2 R
  have h2 := b12k_6 R
  have h3 := b12k_4 R
  have h4 := r3 R
  have h5 := b12k_5 R
  have x1 : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 5) * br (𝐯 1) (𝐯 2) (𝐯 6) (𝐩 1 2 1) < 0 :=
    os_trans h1 (by linarith : 0 < 𝐊 1 2 * br (𝐯 1) (𝐯 2) (𝐯 6) (𝐩 1 2 1))
  have x2 : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐩 1 2 1) * br (𝐯 1) (𝐯 2) (𝐯 5) (𝐯 6) < 0 :=
    so_trans h3 (by linarith : 𝐊 1 2 * br (𝐯 1) (𝐯 2) (𝐯 5) (𝐯 6) < 0)
  have x3 : br (𝐯 1) (𝐯 2) (𝐯 4) (𝐯 6) * br (𝐯 1) (𝐯 2) (𝐯 5) (𝐩 1 2 1) < 0 := by linarith
  exact os_trans x3 h5

end

/-- **`N_6^3` is not circularizable**: there is no plane circle realization of its fingerprint
(`IsCircleRealization`, with the side table `side` generated from the fingerprint). -/
theorem not_circularizable :
    ¬ ∃ (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ),
      IsCircleRealization 6 side c r ε P := by
  rintro ⟨c, r, ε, P, R⟩
  have h1 := final1 R
  have h2 := final2 R
  linarith
"""

TOKEN = re.compile(r"\b(side_(\d)_(\d)_([pm])_(\d)|sep_(\d)_(\d)_([pm])_(\d)_(\d)_([pm])|"
                   r"pair_(\d)_(\d)|pi_(\d)_(\d)|K_(\d)_(\d))\b")


def pt(j: int, k: int, s: str) -> str:
    return f"(𝐩 {j} {k} {'1' if s == 'p' else '(-1)'})"


def pt_arg(j: int, k: int, s: str) -> str:
    return f"{j} {k} {'1' if s == 'p' else '(-1)'}"


def generate() -> str:
    line = FP_FILE.read_text().splitlines()[FP_LINE - 1]
    arr = parse_fingerprint(line)
    n = arr.n

    def side(j: int, k: int, s: str, m: int) -> int:
        return arr.side((j - 1, k - 1, 1 if s == "p" else -1), m - 1)

    entries = [(j + 1, k + 1, sg, c + 1, arr.side((j, k, sg), c))
               for (j, k, sg) in arr.points for c in range(n) if c not in (j, k)]
    table = ",\n   ".join(f"({j}, {k}, {sg}, {m}, {v})" for j, k, sg, m, v in entries)

    def separator(a: tuple[int, int, str], b: tuple[int, int, str]) -> int:
        for m in range(1, n + 1):
            if m in a[:2] or m in b[:2]:
                continue
            if side(*a, m) != side(*b, m):
                return m
        raise AssertionError(f"no circle separates {a} and {b}")

    sides: set[tuple[int, int, str, int]] = set()
    seps: set[tuple] = set()
    pairs: set[tuple[int, int]] = set()
    for m in TOKEN.finditer(PROOF):
        g = m.groups()
        if g[1]:
            sides.add((int(g[1]), int(g[2]), g[3], int(g[4])))
        elif g[5]:
            seps.add(((int(g[5]), int(g[6]), g[7]), (int(g[8]), int(g[9]), g[10])))
        else:
            j, k = next((int(g[i]), int(g[i + 1])) for i in (11, 13, 15) if g[i])
            pairs.add((j, k))
    # separators needed by pi_* and sep_*
    pair_sep = {(j, k): separator((j, k, "p"), (j, k, "m")) for j, k in pairs}
    for (j, k), m in pair_sep.items():
        sides |= {(j, k, "p", m), (j, k, "m", m)}
    sep_circ = {ab: separator(*ab) for ab in seps}
    for (a, b), m in sep_circ.items():
        sides |= {(*a, m), (*b, m)}

    out = [f"""/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Plane

/-! # `N_6^3` is not circularizable

GENERATED by `scripts/noncirc_to_lean.py`; do not edit by hand.

Fingerprint (line {FP_LINE} of rusty-realize `tests/data/{FP_FILE.name}`):
```
{line.strip()}
```

The statement `not_circularizable` is about plane circles (`IsCircleRealization` in
`NonCirc/Plane.lean`): no circles `c i, r i` (`i = 1..6`) with orientations `ε i`, pairwise
crossing, and points `P j k s` on circles `j, k` with the sides of the table `side` below.
The table is read off the fingerprint by the script (via `noncirc.fingerprint`), not by hand.

Proof: Theorem N63 of the (unpublished) realizability notes, i.e. the six core clauses of the stage-4
certificate `{CERT}`:
Krupp ties for the triples 124, 125, 134, 146, four applications of the pair lemma, two final
Grassmann-Plücker relations. No genericity assumption is used; the only
nonvanishing facts are the side signs, `D2 > 0` for crossing circles (from `cross`) and
`<p, q> < 0` for points separated by a circle (proved).
-/

namespace NonCirc.N63

open IsCircleRealization

/-- Side table, generated from the fingerprint: `(j, k, s, m, σ)` means that the crossing point
`p^s_jk` (`s = 1`: `p⁺_jk`, where `k` crosses `j` from right to left) lies to the left (`σ = 1`)
or to the right (`σ = -1`) of circle `m`. All {len(entries)} crossing/circle pairs. -/
def sideList : List (ℕ × ℕ × ℤ × ℕ × ℤ) :=
  [{table}]

/-- `side j k s m`: the entry of `sideList`, `0` if there is none. -/
def side (j k : ℕ) (s : ℤ) (m : ℕ) : ℤ :=
  match sideList.find? (fun e => e.1 == j && e.2.1 == k && e.2.2.1 == s && e.2.2.2.1 == m) with
  | some e => e.2.2.2.2
  | none => 0

/-- Sanity check of the table: every entry is a valid crossing `1 ≤ j < k ≤ {n}`, `s = ±1`, a
circle `m ∉ {{j, k}}`, and a sign `±1`; and there are `{n}·{n - 1}·{n - 2}` entries, one per
crossing point and circle not through it (no duplicates). -/
theorem sideList_valid :
    (∀ e ∈ sideList, 1 ≤ e.1 ∧ e.1 < e.2.1 ∧ e.2.1 ≤ {n} ∧ (e.2.2.1 = 1 ∨ e.2.2.1 = -1) ∧
      1 ≤ e.2.2.2.1 ∧ e.2.2.2.1 ≤ {n} ∧ e.2.2.2.1 ≠ e.1 ∧ e.2.2.2.1 ≠ e.2.1 ∧
      (e.2.2.2.2 = 1 ∨ e.2.2.2.2 = -1)) ∧
    (sideList.map fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1)).Nodup ∧
    sideList.length = {n * (n - 1) * (n - 2)} := by
  decide +kernel

section

variable {{c : ℕ → ℝ × ℝ}} {{r ε : ℕ → ℝ}} {{P : ℕ → ℕ → ℤ → ℝ × ℝ}}
  (R : IsCircleRealization {n} side c r ε P)
include R

set_option hygiene false in
local notation "𝐯" i:max => V c r ε i
set_option hygiene false in
local notation "𝐩" j:max k:max s:max => Pt P j k s
set_option hygiene false in
local notation "𝐊" j:max k:max => br (V c r ε j) (V c r ε k) (Pt P j k 1) (Pt P j k (-1))

/-! ### Side facts used by the proof (direction from the table) -/
"""]
    for j, k, s, m in sorted(sides):
        v = side(j, k, s, m)
        stmt = f"0 < ip (𝐯 {m}) {pt(j, k, s)}" if v > 0 else f"ip (𝐯 {m}) {pt(j, k, s)} < 0"
        out.append(f"lemma side_{j}_{k}_{s}_{m} : {stmt} := R.ip_{'pos' if v > 0 else 'neg'} (by decide)\n")

    out.append("\n/-! ### Crossing pairs: incidences, `<p⁺, p⁻> < 0`, `K ≠ 0` -/\n")
    for j, k in sorted(pairs):
        m = pair_sep[(j, k)]
        sp, sm = side(j, k, "p", m), side(j, k, "m", m)
        mul = "mul_neg_of_pos_of_neg" if sp > 0 else "mul_neg_of_neg_of_pos"
        out.append(f"""lemma pair_{j}_{k} : Pair (𝐯 {j}) (𝐯 {k}) {pt(j, k, 'p')} {pt(j, k, 'm')} :=
  R.pair (by norm_num) (by norm_num) (by norm_num)

/-- Separated by circle {m}. -/
lemma pi_{j}_{k} : ip {pt(j, k, 'p')} {pt(j, k, 'm')} < 0 :=
  ip_points_neg (isPoint P {pt_arg(j, k, 'p')}) (isPoint P {pt_arg(j, k, 'm')}) (v := 𝐯 {m})
    ({mul} (side_{j}_{k}_p_{m} R) (side_{j}_{k}_m_{m} R))

lemma K_{j}_{k} : 𝐊 {j} {k} ≠ 0 :=
  (pair_{j}_{k} R).K_ne (R.D2_pos (by norm_num) (by norm_num) (by norm_num)) (pi_{j}_{k} R).ne
""")
    out.append("\n/-! ### Further pairs of points separated by a circle -/\n")
    for (a, b) in sorted(seps):
        m = sep_circ[(a, b)]
        sa, sb = side(*a, m), side(*b, m)
        mul = "mul_neg_of_pos_of_neg" if sa > 0 else "mul_neg_of_neg_of_pos"
        name = f"sep_{a[0]}_{a[1]}_{a[2]}_{b[0]}_{b[1]}_{b[2]}"
        out.append(f"""/-- Separated by circle {m}. -/
lemma {name} : ip {pt(*a)} {pt(*b)} < 0 :=
  ip_points_neg (isPoint P {pt_arg(*a)}) (isPoint P {pt_arg(*b)}) (v := 𝐯 {m})
    ({mul} (side_{a[0]}_{a[1]}_{a[2]}_{m} R) (side_{b[0]}_{b[1]}_{b[2]}_{m} R))
""")
    out.append(PROOF)
    out.append("\nend NonCirc.N63\n\n-- Must list only Lean's standard axioms (no sorryAx).\n"
               "#print axioms NonCirc.N63.not_circularizable\n")
    return "".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="compile with `lake env lean`")
    args = ap.parse_args()
    OUT.write_text(generate())
    print(f"wrote {OUT}")
    if args.check:
        proc = subprocess.run(["lake", "env", "lean", str(OUT)], cwd=LEAN_DIR, capture_output=True,
                              text=True, timeout=170)
        out = (proc.stdout + proc.stderr).strip()
        ok = proc.returncode == 0 and "error" not in out and out.endswith(f"depends on axioms: {STANDARD_AXIOMS}")
        print(out)
        print("OK" if ok else "FAILED")
        sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
