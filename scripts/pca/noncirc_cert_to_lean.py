#!/usr/bin/env python3
"""Lean proof of non-circularizability from a stage-4 core (layer 2).

Untrusted helper: it only chooses *tags* (instances of identities and sign rules) and finds an
LRAT proof; Lean checks everything (`NonCirc/Main.lean`: the encoding is computed in Lean from
the fingerprint, every tag is validated there, and the LRAT proof is checked by the verified
checker `NonCirc/Checker.lean` via `decide +kernel`).

Steps:
1. read the certificate `.txt` (fingerprint and the decoded core instances F1/F2/F3);
2. tags: the identity instance of every core clause, and for every bracket in it the rule tags
   that tie it to `K_jk = [v_j v_k p+ p-]` (type 3, Krupp) or to its sorted form (type 5),
   the known signs of the Lorentz products, `K != 0`; Krupp ties between the `K`s;
3. Lean emits the numbered three-valued CNF (`NonCirc.emit`), cadical refutes it with LRAT;
   only the tags whose clauses the proof uses are kept, and the CNF is refuted again;
4. writes `NonCirc/Cert/<Name>.lean` and (with --check) compiles it.

Usage (from pca/lean, after `lake build NonCirc.Main`):

    python3 scripts/noncirc_cert_to_lean.py all6_digonfree_nonrealizable_1_F123_P2 N6Delta --check
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent
PCA_DIR = LEAN_DIR.parent
sys.path.insert(0, str(PCA_DIR))
from noncirc.fingerprint import parse_fingerprint  # noqa: E402

CERT_DIR = PCA_DIR / "noncirc" / "certificates"
STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"
SCRATCH = Path(os.environ.get("NONCIRC_SCRATCH", tempfile.gettempdir()))


# ---------------------------------------------------------------------------------------------
# indices: ('c', i) circle, ('p', j, k, s) crossing label (1-based, j < k, s = +-1)
# ---------------------------------------------------------------------------------------------

def parse_name(arr_n: int, name: str):
    m = re.fullmatch(r"c(\d+)", name)
    if m:
        return ("c", int(m.group(1)))
    m = re.fullmatch(r"p(\d+)([+-])(\d+)", name)
    assert m, name
    return ("p", int(m.group(1)), int(m.group(3)), 1 if m.group(2) == "+" else -1)


def lean_idx(x) -> str:
    if x[0] == "c":
        return f"(.circ {x[1]})"
    return f"(.pt {x[1]} {x[2]} {x[3] if x[3] > 0 else '(-1)'})"


def key(x):
    return (0, x[1], 0, 0) if x[0] == "c" else (1, x[1], x[2], -x[3])


class Model:
    def __init__(self, fp_text: str):
        self.arr = parse_fingerprint(fp_text)
        self.n = self.arr.n
        self.lists = self.arr.lists
        self.tags: list[str] = []
        self.seen: set[str] = set()
        self.missing: list[str] = []

    # fingerprint facts (1-based)
    def side(self, p, m: int) -> int:
        return self.arr.side((p[1] - 1, p[2] - 1, p[3]), m - 1)

    def krupp(self, a: int, b: int, c: int) -> bool:
        return self.arr.krupp(*sorted((a - 1, b - 1, c - 1)))

    def on(self, p) -> tuple[int, int]:
        return (p[1], p[2])

    def sep(self, p, q):
        """a circle separating two crossing points (not through either), or None"""
        for w in range(1, self.n + 1):
            if w in self.on(p) or w in self.on(q):
                continue
            if self.side(p, w) * self.side(q, w) == -1:
                return w
        return None

    def dist(self, p, q):
        """a circle distinguishing two distinct crossing points (Lean `distinct`), or None"""
        w = self.sep(p, q)
        if w is not None:
            return w
        for w in range(1, self.n + 1):
            if (w in self.on(p)) != (w in self.on(q)):
                return w
        return None

    def wit(self, p, q):
        """Lean witness that crossings p != q are different points (`Wit`), or None."""
        w = self.dist(p, q)
        if w is not None:
            return f"(.circ {w})"
        for m in set(self.on(p)) & set(self.on(q)):
            order = [self.label(m, e) for e in self.lists[m - 1]]
            i, j = order.index(p), order.index(q)
            k = next(t for t in range(len(order)) if t not in (i, j))
            a, b, c = sorted((i, j, k))
            return f"(.cyc {m} {a} {b} {c})"
        return None

    def add(self, tag: str) -> None:
        if tag not in self.seen:
            self.seen.add(tag)
            self.tags.append(tag)

    # tags
    def perms(self, seq, target) -> None:
        cur = list(seq)
        assert sorted(cur, key=key) == sorted(target, key=key)
        for pos in range(4):
            j = cur.index(target[pos], pos)
            while j > pos:
                self.add(f".perm {' '.join(lean_idx(x) for x in cur)} {j - 1}")
                cur[j - 1], cur[j] = cur[j], cur[j - 1]
                j -= 1

    def ipfact(self, x, y) -> None:
        w = "(.circ 0)"
        if x[0] == "p" and y[0] == "p" and x != y:
            w = self.wit(x, y)
            if w is None:
                self.missing.append(f"no circle separates {x} {y}")
                return
        if x[0] == "c" and y[0] == "c":
            self.missing.append(f"<{x},{y}> of two circles has no known sign")
            return
        self.add(f".ipFact {lean_idx(x)} {lean_idx(y)} {w}")

    def pair_witness(self, a: int, b: int) -> str:
        w = self.wit(("p", a, b, 1), ("p", a, b, -1))
        assert w is not None, f"no witness for the crossings of {a},{b}"
        return w

    def link(self, seq) -> None:
        """tie the sign of the bracket `seq` to K's (types 2, 3) or to its sorted form."""
        seq = tuple(seq)
        assert len(set(seq)) == 4, seq
        circ = [x for x in seq if x[0] == "c"]
        pts = [x for x in seq if x[0] == "p"]
        for P in pts:
            a, b = self.on(P)
            if ("c", a) in seq and ("c", b) in seq:
                x = next(y for y in seq if y not in (("c", a), ("c", b), P))
                w = self.pair_witness(a, b)
                self.perms(seq, (("c", a), ("c", b), x, P))
                self.add(f".type3 {a} {b} {lean_idx(x)} {'true' if P[3] > 0 else 'false'} {w}")
                self.add(f".knz {a} {b} {w}")
                self.ipfact(x, P)
                return
        if len(circ) == 3 and self.krupp(*(x[1] for x in circ)):
            q = pts[0]
            ids = sorted(x[1] for x in circ)
            for a, b, m in ((ids[0], ids[1], ids[2]), (ids[0], ids[2], ids[1]), (ids[1], ids[2], ids[0])):
                if self.side(("p", a, b, 1), m) * self.side(("p", a, b, -1), m) != -1:
                    continue
                for useP in (True, False):
                    tgt = ("p", a, b, 1 if useP else -1)
                    wq = self.wit(q, tgt)
                    if wq is None:
                        continue
                    w = self.pair_witness(a, b)
                    self.perms(seq, (("c", a), ("c", b), ("c", m), q))
                    self.add(f".krupp {a} {b} {m} {lean_idx(q)} {w} {wq} {'true' if useP else 'false'}")
                    self.link((("c", a), ("c", b), ("c", m), ("p", a, b, 1)))
                    return
            self.missing.append(f"Krupp bracket {seq}: no usable base pair")
        self.perms(seq, tuple(sorted(seq, key=key)))

    def krupp_ties(self) -> None:
        """For every Krupp triple: [a b m q] = [a b m p+_ab] (Krupp tag) for q the crossings of the
        other two pairs; both brackets are type 3, so this ties K_ab to K_am and K_bm."""
        for t in range(1, self.n + 1):
            for u in range(t + 1, self.n + 1):
                for v in range(u + 1, self.n + 1):
                    if not self.krupp(t, u, v):
                        continue
                    for a, b, m in ((t, u, v), (t, v, u), (u, v, t)):
                        if self.side(("p", a, b, 1), m) * self.side(("p", a, b, -1), m) != -1:
                            continue
                        w = self.pair_witness(a, b)
                        for c, d in (tuple(sorted((a, m))), tuple(sorted((b, m)))):
                            for s in (1, -1):
                                q = ("p", c, d, s)
                                for useP in (True, False):
                                    wq = self.wit(q, ("p", a, b, 1 if useP else -1))
                                    if wq is None:
                                        continue
                                    self.add(f".krupp {a} {b} {m} {lean_idx(q)} {w} {wq} "
                                             f"{'true' if useP else 'false'}")
                                    self.link((("c", a), ("c", b), ("c", m), q))
                                    self.link((("c", a), ("c", b), ("c", m), ("p", a, b, 1)))
                                    break

    # identity instances from the certificate header
    def instance(self, head: str) -> None:
        if " F1 " in head:
            m = re.match(r"\d+ F1 B=\[([^\]]*)\] circle c(\d+) points (.*)", head)
            B = tuple(parse_name(self.n, x) for x in m.group(1).split())
            l = int(m.group(2))
            pts = [parse_name(self.n, x) for x in m.group(3).split()]
            order = [self.label(l, e) for e in self.lists[l - 1]]
            pos = sorted(order.index(p) for p in pts)
            self.add(f".f1 {' '.join(lean_idx(x) for x in B)} {l} {' '.join(map(str, pos))}")
            for p in pts:
                self.link(B + (p,))
        elif " F2 " in head:
            m = re.match(r"\d+ F2 DEP X=([^ ]*) y=(\S+)", head)
            X = [parse_name(self.n, x) for x in m.group(1).split(",")]
            y = parse_name(self.n, m.group(2))
            self.add(f".dep {' '.join(lean_idx(x) for x in X)} {lean_idx(y)}")
            for t, x in enumerate(X):
                self.link(tuple(z for z in X if z != x))
                self.ipfact(x, y)
        elif " F3 " in head:
            m = re.match(r"\d+ F3 GP S=([^ ]*) a=(\S+) b=(\S+)", head)
            S = [parse_name(self.n, x) for x in m.group(1).split(",")]
            a, b = parse_name(self.n, m.group(2)), parse_name(self.n, m.group(3))
            c, d, e, f = (x for x in S if x not in (a, b))
            self.add(f".gp {' '.join(lean_idx(x) for x in (a, b, c, d, e, f))}")
            for br in ((c, d), (e, f), (c, e), (d, f), (c, f), (d, e)):
                self.link((a, b) + br)
        else:
            assert " xor " in head, head

    @staticmethod
    def label(m: int, e: int):
        d = abs(e)
        return ("p", m, d, 1 if e > 0 else -1) if m < d else ("p", d, m, -1 if e > 0 else 1)


# ---------------------------------------------------------------------------------------------

def parse_cert(path: Path):
    fp, heads = None, []
    for line in path.read_text().splitlines():
        if line.startswith("fingerprint "):
            fp = line.split(" ", 1)[1].strip()
        elif re.match(r"# \d+ (F\d|xor)", line):
            heads.append(line[2:].split(" | ")[0])
    seen, out = set(), []
    for h in heads:
        k = h.split(" ", 1)[1]
        if k not in seen:
            seen.add(k)
            out.append(h)
    return fp, out


def lean_fp(lists) -> str:
    return "[" + ",\n   ".join("[" + ", ".join(str(e) for e in l) + "]" for l in lists) + "]"


def run_emit(fp_lean: str, tags: list[str]) -> tuple[list[list[int]], list[int]]:
    """The coded CNF computed by Lean (`NonCirc.emit`) and the producing tag of every clause."""
    src = (f"import NonCirc.Main\nopen NonCirc\n\ndef F : Fingerprint := {fp_lean}\n\n"
           f"def tags : List Tag := [\n  " + ",\n  ".join(tags) + "]\n\n#eval IO.print (emit F tags)\n")
    path = SCRATCH / "noncirc_emit.lean"
    path.write_text(src)
    proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=LEAN_DIR, capture_output=True,
                          text=True, timeout=170)
    if proc.returncode != 0:
        raise RuntimeError(proc.stdout + proc.stderr)
    clauses, tag_of = [], []
    cur = None
    for line in proc.stdout.splitlines():
        if line.startswith("c tag "):
            cur = int(line.split()[2])
        elif line.strip():
            nums = [int(x) for x in line.split()]
            assert nums[-1] == 0
            clauses.append(nums[:-1])
            tag_of.append(cur)
    return clauses, tag_of


def solve(clauses: list[list[int]]):
    """cadical on the renumbered CNF; returns (LRAT steps in the coded literals, used clause ids)."""
    codes = sorted({abs(l) for c in clauses for l in c})
    ren = {v: i + 1 for i, v in enumerate(codes)}
    back = {i + 1: v for i, v in enumerate(codes)}
    cnf = SCRATCH / "noncirc.cnf"
    prf = SCRATCH / "noncirc.lrat"
    cnf.write_text(f"p cnf {len(codes)} {len(clauses)}\n" + "".join(
        " ".join(str(ren[abs(l)] * (1 if l > 0 else -1)) for l in c) + " 0\n" for c in clauses))
    out = subprocess.run(["cadical", "-q", "--lrat=true", "--binary=false", str(cnf), str(prf)],
                         capture_output=True, text=True, timeout=120).stdout
    if "s UNSATISFIABLE" not in out:
        return None
    m = len(clauses)
    steps = {}
    empty = None
    for line in prf.read_text().splitlines():
        t = line.split()
        if not t or t[1] == "d":
            continue
        nums = [int(x) for x in t]
        z = nums.index(0, 1)
        steps[nums[0]] = ([back[abs(l)] * (1 if l > 0 else -1) for l in nums[1:z]], nums[z + 1:-1])
        if z == 1:
            empty = nums[0]
            break
    used, todo, orig = set(), [empty], set()
    while todo:
        i = todo.pop()
        if i in used:
            continue
        used.add(i)
        if i <= m:
            orig.add(i)
        else:
            todo.extend(steps[i][1])
    proof = [(i, steps[i][0], steps[i][1]) for i in sorted(used) if i > m]
    return proof, orig


CHUNK = 40


def chunked(name: str, typ: str, items: list[str], doc: str) -> str:
    """`def name : typ := c0 ++ c1 ++ ...` with chunks of CHUNK list items."""
    parts = [items[k:k + CHUNK] for k in range(0, len(items), CHUNK)] or [[]]
    out = []
    for k, part in enumerate(parts):
        out.append(f"def {name}{k} : {typ} := [\n  " + ",\n  ".join(part) + "]\n\n")
    out.append(f"/-- {doc} -/\ndef {name} : {typ} := " + " ++ ".join(f"{name}{k}" for k in range(len(parts)))
               + "\n\n")
    return "".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cert", help="certificate basename in noncirc/certificates")
    ap.add_argument("name", help="Lean name, e.g. N6Delta")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--ties", action="store_true", help="add all Krupp ties from the start")
    args = ap.parse_args()

    fp_text, heads = parse_cert(CERT_DIR / f"{args.cert}.txt")
    src = re.search(r"# source: (.*)", (CERT_DIR / f"{args.cert}.txt").read_text())
    source = src.group(1).replace(str(Path.home()), "~") if src else "?"
    M = Model(fp_text)
    for h in heads:
        M.instance(h)
    if args.ties:
        M.krupp_ties()
    fp_lean = lean_fp(M.lists)
    t0 = time.time()
    clauses, tag_of = run_emit(fp_lean, M.tags)
    res = solve(clauses)
    if res is None and not args.ties:
        print("core without Krupp ties is satisfiable; adding ties")
        M.krupp_ties()
        clauses, tag_of = run_emit(fp_lean, M.tags)
        res = solve(clauses)
    if M.missing:
        print("warnings:", *M.missing, sep="\n  ")
    empty_tags = [M.tags[i] for i in range(len(M.tags)) if i not in set(tag_of)]
    if empty_tags:
        print(f"{len(empty_tags)} tags rejected by Lean (no clauses):", *empty_tags[:20], sep="\n  ")
    assert res is not None, "three-valued encoding is SATISFIABLE"
    _, orig = res
    keep = sorted({tag_of[i - 1] for i in orig})
    tags = [M.tags[i] for i in keep]
    clauses, tag_of = run_emit(fp_lean, tags)
    res = solve(clauses)
    assert res is not None
    proof, orig = res
    # keep only the used clauses: ids 1..len(sel) for them, lemma ids after
    sel = sorted(orig)
    new_id = {old: k + 1 for k, old in enumerate(sel)}
    for k, (i, _, _) in enumerate(proof):
        new_id[i] = len(sel) + k + 1
    proof = [(new_id[i], c, [new_id[x] for x in h]) for i, c, h in proof]
    # per-tag positions of the used clauses, and the literal clause list (same order)
    local, cnt = [], {}
    for t in tag_of:
        local.append(cnt.get(t, 0))
        cnt[t] = cnt.get(t, 0) + 1
    sels = [[] for _ in tags]
    for i in sel:
        sels[tag_of[i - 1]].append(local[i - 1])
    cnf_coded = [clauses[i - 1] for i in sel]
    codes = sorted({abs(l) for c in cnf_coded for l in c})
    small = {v: k + 1 for k, v in enumerate(codes)}
    ren = [v - 1 for v in codes]
    sm = lambda l: small[abs(l)] * (1 if l > 0 else -1)
    cnf_lit = [[sm(l) for l in c] for c in cnf_coded]
    proof = [(i, [sm(l) for l in c], h) for i, c, h in proof]
    idxs = sel
    nvars, nclauses = len({abs(l) for c in clauses for l in c}), len(clauses)
    print(f"{len(M.tags)} tags -> {len(tags)} used; CNF {nvars} vars {nclauses} clauses; "
          f"{len(idxs)} clauses used; proof {len(proof)} steps ({time.time() - t0:.0f}s)")

    out = LEAN_DIR / "NonCirc" / "Cert" / f"{args.name}.lean"
    out.parent.mkdir(exist_ok=True)
    prf_items = [f"({i}, [{', '.join(map(str, c))}], [{', '.join(map(str, h))}])" for i, c, h in proof]
    body = [f"""/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Main

/-! # Non-circularizability of {args.name}

GENERATED by `scripts/noncirc_cert_to_lean.py` from the stage-4 certificate
`noncirc/certificates/{args.cert}.txt` (do not edit by hand).
Source of the fingerprint: {source}.

The statement only involves `Fingerprint.IsCircleRealization` (`NonCirc/Fingerprint.lean`) and
the fingerprint `F` below. The tags, clause positions, the clause list and the LRAT proof are
untrusted data: the encoding is computed and validated in Lean and the proof is checked by the verified checker
(`not_circularizable_of_check`), evaluated with `decide +kernel`. Long lists are split into
chunks of {CHUNK} (long list literals elaborate slowly).
-/

namespace NonCirc.Cert.{args.name}

/-- The fingerprint. -/
def F : Fingerprint :=
  {fp_lean}

theorem F_wellFormed : F.WellFormed = true := by decide +kernel

"""]
    body.append(chunked("tags", "List Tag", tags, "Instances of identities and sign rules used by the refutation."))
    body.append(chunked("sels", "List (List ℕ)", ["[" + ", ".join(map(str, x)) + "]" for x in sels],
                        "For every tag, the positions of its clauses used by the proof."))
    body.append(chunked("ren", "List ℕ", [str(x) for x in ren],
                        "Variable `i` of `cnf` is the coded variable `ren[i-1] + 1`."))
    body.append(chunked("cnf", "List (List ℤ)", ["[" + ", ".join(map(str, c)) + "]" for c in cnf_lit],
                        "The selected clauses with small variable numbers (checked against the encoding)."))
    body.append(chunked("proof", "List (ℕ × List ℤ × List ℕ)", prf_items,
                        "LRAT refutation (RUP steps) of the selected clauses."))
    body.append(f"""set_option maxRecDepth 100000 in
theorem sel_ok : cnf.map (·.map (Sat.unren ren)) = selectTags F tags sels := by decide +kernel

set_option maxRecDepth 100000 in
theorem check_ok : Sat.check cnf proof = true := by decide +kernel

/-- **{args.name} is not circularizable**: no plane circle realization of `F`. -/
theorem not_circularizable :
    ¬ ∃ (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ), F.IsCircleRealization c r ε P :=
  not_circularizable_of_check F tags sels ren cnf proof sel_ok check_ok

end NonCirc.Cert.{args.name}

-- Must list only Lean's standard axioms (no sorryAx, no Lean.ofReduceBool).
#print axioms NonCirc.Cert.{args.name}.not_circularizable
""")
    out.write_text("".join(body))
    print(f"wrote {out}")
    if args.check:
        t1 = time.time()
        proc = subprocess.run(["lake", "env", "lean", str(out)], cwd=LEAN_DIR, capture_output=True,
                              text=True, timeout=178)
        o = (proc.stdout + proc.stderr).strip()
        ok = proc.returncode == 0 and "error" not in o and o.endswith(f"depends on axioms: {STANDARD_AXIOMS}")
        print(o[-3000:])
        print(("OK" if ok else "FAILED") + f" ({time.time() - t1:.0f}s)")
        sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
