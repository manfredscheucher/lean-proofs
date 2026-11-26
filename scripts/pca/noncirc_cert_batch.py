#!/usr/bin/env python3
"""Batch: Lean proofs for the stage-4 certificates of missing6_open (resumable).

For every line number in `noncirc/runs/open6_unsat_lines.txt` (certificate
`noncirc/certificates/missing6_open_<line>_F123_P2.*`), runs `noncirc_cert_to_lean.py` (writes
`NonCirc/Cert/Missing6Open<line>.lean`), then `lake env lean` on the file. A certificate is OK iff
Lean reports no error and `#print axioms` lists only `propext, Classical.choice, Quot.sound`.
One TSV row per certificate is appended to `noncirc/runs/lean_certs.tsv`; lines already there are
skipped. Files that fail are moved to `<scratch>/failed/`. A heartbeat line about once per minute.

Usage (from pca/lean, after `lake build NonCirc.Main`):

    nohup python3 scripts/noncirc_cert_batch.py -j 2 > ../noncirc/runs/lean_certs.log 2>&1 &
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent
PCA_DIR = LEAN_DIR.parent
LINES = PCA_DIR / "noncirc" / "runs" / "open6_unsat_lines.txt"
OUT = PCA_DIR / "noncirc" / "runs" / "lean_certs.tsv"
SCRATCH = Path(os.environ.get("NONCIRC_BATCH_SCRATCH", "/tmp/noncirc_batch"))
AXIOMS = "depends on axioms: [propext, Classical.choice, Quot.sound]"
HEADER = "line\ttags_used\ttags_total\tclauses_used\tclauses_encoded\tlrat_steps\tgen_s\tlean_s\tstatus\treason\n"
DONE_ELSEWHERE = {"6012": "N6Delta", "14791": "N63Core", "1129": "Missing6Open1129", "1137": "Missing6Open1137"}

lock = threading.Lock()
stats = {"done": 0, "ok": 0, "fail": 0}


def process(line: str, timeout: int) -> str:
    name = f"Missing6Open{line}"
    scratch = SCRATCH / line
    scratch.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, NONCIRC_SCRATCH=str(scratch))
    row = {"tags_used": "", "tags_total": "", "clauses_used": "", "clauses_encoded": "", "lrat_steps": ""}
    t0 = time.time()
    try:
        g = subprocess.run([sys.executable, "scripts/noncirc_cert_to_lean.py", f"missing6_open_{line}_F123_P2", name],
                           cwd=LEAN_DIR, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return f"{line}\t\t\t\t\t\t{time.time() - t0:.0f}\t\tFAIL\tgenerator timeout\n"
    gen_s = time.time() - t0
    m = re.search(r"(\d+) tags -> (\d+) used; CNF \d+ vars (\d+) clauses; (\d+) clauses used; proof (\d+) steps",
                  g.stdout)
    if g.returncode != 0 or not m:
        err = (g.stdout + g.stderr).strip().splitlines()
        reason = err[-1][:200] if err else "generator failed"
        return f"{line}\t\t\t\t\t\t{gen_s:.0f}\t\tFAIL\tgenerator: {reason}\n"
    row = dict(tags_total=m.group(1), tags_used=m.group(2), clauses_encoded=m.group(3),
               clauses_used=m.group(4), lrat_steps=m.group(5))
    f = LEAN_DIR / "NonCirc" / "Cert" / f"{name}.lean"
    t1 = time.time()
    try:
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=LEAN_DIR, capture_output=True, text=True,
                           timeout=timeout)
        out = (p.stdout + p.stderr).strip()
        ok = p.returncode == 0 and "error" not in out and out.endswith(AXIOMS)
        reason = "" if ok else (out.splitlines()[0][:200] if out else f"exit {p.returncode}")
    except subprocess.TimeoutExpired:
        ok, reason = False, "lean timeout"
    lean_s = time.time() - t1
    if not ok:
        (SCRATCH / "failed").mkdir(exist_ok=True)
        shutil.move(str(f), str(SCRATCH / "failed" / f.name))
    return (f"{line}\t{row['tags_used']}\t{row['tags_total']}\t{row['clauses_used']}\t{row['clauses_encoded']}\t"
            f"{row['lrat_steps']}\t{gen_s:.0f}\t{lean_s:.0f}\t{'OK' if ok else 'FAIL'}\t{reason}\n")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=900, help="seconds per generator / Lean run")
    args = ap.parse_args()
    lines = [l.strip() for l in LINES.read_text().split() if l.strip()]
    done = set()
    if OUT.exists():
        done = {r.split("\t")[0] for r in OUT.read_text().splitlines()[1:] if r}
    else:
        OUT.write_text(HEADER)
    todo = [l for l in lines if l not in done and l not in DONE_ELSEWHERE]
    total = len(todo)
    print(f"{total} certificates to do ({len(done)} already in {OUT.name}, "
          f"{len(DONE_ELSEWHERE)} done elsewhere)", flush=True)
    t_start = time.time()
    stop = threading.Event()

    def heartbeat() -> None:
        while not stop.wait(60):
            with lock:
                d, ok, fail = stats["done"], stats["ok"], stats["fail"]
            el = time.time() - t_start
            eta = el / d * (total - d) if d else float("nan")
            print(f"[heartbeat {time.strftime('%H:%M:%S')}] {d}/{total} done ({ok} OK, {fail} FAIL), "
                  f"elapsed {el / 60:.0f} min, ETA {eta / 60:.0f} min", flush=True)

    threading.Thread(target=heartbeat, daemon=True).start()

    def job(line: str) -> None:
        row = process(line, args.timeout)
        with lock:
            with OUT.open("a") as fh:
                fh.write(row)
            stats["done"] += 1
            stats["ok" if "\tOK\t" in row else "fail"] += 1
            print(row.rstrip("\n"), flush=True)

    with ThreadPoolExecutor(max_workers=args.j) as pool:
        list(pool.map(job, todo))
    stop.set()
    print(f"finished: {stats['ok']} OK, {stats['fail']} FAIL in {(time.time() - t_start) / 60:.0f} min", flush=True)


if __name__ == "__main__":
    main()
