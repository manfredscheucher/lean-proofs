# Conventions for agents

* Public docs are in English and short: one page per library in `doc/<topic>/` (what is proved,
  main declarations, axioms, sources, deviations from the paper). Keep the `README.md` of each
  doc folder up to date when pages are added or renamed.
* Prompts, specs, plans, decision logs, failed attempts and handoffs go only into
  `_private/doc/`, which is not in git. Public docs and code comments do not refer to it or to
  files outside the repository.
* Results from the literature that are not proved here enter only as `axiom`, in a dedicated
  `Axioms` file of the library, with the exact citation. Never commit `sorry`.
* Every file starts with the Mathlib-style header:

  ```
  /-
  Copyright (c) 2026 Manfred Scheucher. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Manfred Scheucher
  -/
  ```

* Build only with `scripts/build.sh` (one Lean process at a time, 1 GB memory limit per
  process), e.g. `scripts/build.sh PcaGreat` or `scripts/build.sh --lean FILE.lean`.
* Probe and scratch files go into `scripts/probe/` (gitignored).
* Commit on `main`, no branches, short commit messages.
