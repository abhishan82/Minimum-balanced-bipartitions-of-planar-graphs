# Session Log

Dated summaries of what got done, found, and blocked in each work session on
this repo. **Append-only** — never edit or delete a past entry, even to
correct it; add a new entry noting the correction instead. Committed and
pushed at the end of every session (see CLAUDE.md).

---

## 2026-07-07

**Done:**
- Diagnosed and fixed `blueprint.yml`'s `lint: true` input, which had no
  registered lint driver in `lakefile.toml` and had caused every run of the
  workflow to fail (0/10 successes) since the initial commit — unrelated to
  any dependabot version bump. Removed the input.
- Disabled `deploy-pages.yml` (renamed to `.disabled`): it raced
  `blueprint.yml` for the same GitHub Pages deployment target on every push
  to `main`, and always won with an unrelated Jekyll "Upstreaming Dashboard"
  page, masking the fact that the actual blueprint site had never deployed.
- Diagnosed and fixed a second `blueprint.yml` failure: `mk_all-check: true`
  requires `Project.lean`'s import list to match `lake exe mk_all`'s
  alphabetical canonical order; the hand-curated dependency order failed the
  check. Reordered only (verified no imports added/removed), and gitignored
  `Project/FormalizationPlan.lean` (a local scratch file that `mk_all` would
  otherwise demand be imported).
- Both fixes verified locally (`lake build`, `lake exe mk_all --check`)
  before pushing.

**Found:**
- After the two fixes, `blueprint.yml`'s "Build and lint project" step
  succeeded for the first time. The workflow then progressed to a new step,
  "Compile blueprint and documentation" (`docgen-action`, `blueprint: true`),
  which failed after ~2 minutes with only a generic `Process completed with
  exit code 255` annotation — no descriptive message, unlike the earlier two
  failures.
- Ruled out `lake exe checkdecls blueprint/lean_decls` as the cause: that
  file is empty (no `\lean{...}` macros currently used in
  `blueprint/src/content.tex`), and running the check locally against the
  empty file exits 0.
- Raw GitHub Actions job logs are auth-gated even for public repos via the
  REST API (confirmed 403); only Checks-API annotations are readable
  unauthenticated, and this failure produced no detailed annotation. The
  likely remaining culprits are the `leanblueprint pdf`/`leanblueprint web`
  LaTeX build or the `pygraphviz`/Alpine package install inside the
  `texlive-full` Docker container step, but this is unconfirmed.

**Blocked:**
- Blueprint site is still not live. Need either authenticated log access
  (`gh run view --log`) to see the real error from the `docgen-action` step,
  or willingness to guess-and-iterate against the LaTeX/pygraphviz build
  without log visibility.
- README's blueprint link remains "pending" — not updated, since the site
  isn't confirmed live per the task's own stop condition.

**Current state:** `main` at `0607f71` (CLAUDE.md added). Repo metadata and
GitHub Pages source (Settings → Pages → Source: GitHub Actions) are set by
the author. `deploy-pages.yml.disabled` parked, not deleted, in case the
dashboard is wanted later at a subpath.

### Update (same day): docgen exit-255 resolved

**Done:**
- Reproduced the `docgen-action` failure locally instead of guessing:
  ran `leanblueprint pdf` (and, gated on that passing, `leanblueprint web`)
  from the repo root with a local MiKTeX/leanblueprint install.
- First local run hit `! Package fontspec Error: The font
  "latinmodern-math" cannot be found`, despite the `lm-math` package being
  installed (`mpm --list`). Diagnosed as a stale local MiKTeX font-name
  database, not a repo bug — confirmed by running `initexmf --update-fndb`
  and retrying, which got past that error entirely.
- With the font-cache red herring cleared, hit the real bug: `! Missing $
  inserted` at `\input{content}` in `print.tex`. Root cause: `\title{minbal_pl}`
  in both `blueprint/src/print.tex` and `blueprint/src/web.tex` has an
  unescaped underscore, which is math-mode-only syntax in LaTeX text mode.
  `\title` defers typesetting to `\maketitle`, so the error only surfaced
  later and got misattributed by the TeX log to the next line read — which
  is exactly why CI's Checks-API annotation was a content-free "exit code
  255" with nothing more specific to go on.
- Fixed by escaping to `\title{minbal\_pl}` in both files. Verified locally:
  `leanblueprint pdf` now exits 0 (produces a real 4-page `print.pdf`, only
  a harmless overfull-hbox warning) and `leanblueprint web` now exits 0
  (produces real `index.html`/`dep_graph_document.html` output). Some
  Windows-local tool warnings (`gswin32c`, `pdf2svg` not found) appeared but
  did not block either command — non-fatal fallback path, not a repo issue.
- Committed (`0fdce7b`) and pushed; resuming the CI watch loop on the newly
  triggered `blueprint.yml` run.

**Found:** the generic, content-free CI failure mode (bare "exit code 255"
with no `::error::`-style annotation) recurs for any raw shell/Docker-
container step failure — worth remembering that *reproducing locally*
beats waiting on CI-log access when the workflow step itself isn't a
GitHub-native action.

### Update (same day): blueprint site deployed successfully

**Done:**
- `blueprint.yml` run `28863890479` (commit `fae3db0`) succeeded end to end
  for the first time ever: build, lint-free compile, `mk_all` check, and
  `docgen-action`'s blueprint/API-doc compile-and-deploy step all passed.
- Confirmed deploy target: no `gh-pages` branch exists on the repo (only
  `main`), so `docgen-action` deployed via the GitHub Actions Pages
  deployment API internally (same mechanism as `actions/deploy-pages`), not
  a branch push.
- Verified the live site thoroughly, not just a 200 on the root: homepage
  (`docgen-action`'s generated landing page, title "minbal_pl | by
  abhishan82", links to blueprint/PDF/docs), `blueprint/` (web version,
  confirmed real Theorem/Proposition/Lemma/Corollary content, not a
  placeholder), `blueprint.pdf`, `blueprint/dep_graph_document.html`, and
  `docs/` (API docs) — all return HTTP 200 with real content.
- Updated `README.md`'s Blueprint section with the live links and removed
  the now-stale "Pages Deployment" troubleshooting section (Pages is
  enabled and working). Committed (`77bea1c`) and pushed.

**Found:** polling this run hit the unauthenticated GitHub REST API's
60-req/hour rate limit repeatedly during the ~35-minute wait for
`docgen-action` to finish (texlive-full container pull + LaTeX + doc-gen4
API docs build). Recovered each time by backing off and checking
`/rate_limit` (which is itself exempt from the limit) before resuming.
Also worth noting: comparing job/step `started_at` timestamps against a
fresh `Date:` response header is a reliable way to gauge real elapsed CI
time — this local sandbox's own clock was unreliable for that purpose
earlier in the session, and rate-limit-reset-cycle counting turned out to
be an unreliable proxy for elapsed time too (both were tried and discarded
as gauges before landing on the timestamp-diff approach).

**Blocked:** nothing outstanding from this task. The full CI pipeline
(`build-project.yml`, `blueprint.yml`) is green, and the blueprint site is
live at
https://abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs/.

**Current state:** `main` at `77bea1c`.

---

## 2026-07-08

**Done:**
- Converted all 9 `axiom` declarations to `theorem ... := sorry` (one
  `noncomputable def ... := sorry` for `NearTriangulation.toConcrete`, since
  `theorem` requires a Prop-valued type and `ConcretePlaneNT G` is a
  structure) per CLAUDE.md's non-negotiable convention. Statements kept
  byte-identical; doc comments extended with the ledger bucket (8× A, 1× C)
  and the reason assumed. Verified: 0 axioms, 9 sorries, `lake build` green
  with exactly 9 "declaration uses `sorry`" warnings.
- Synced the README ledger: renamed "axiom ledger" to "sorry ledger",
  finalized `no_sep_tri_gives_sink` from the provisional "A/B?" to "A"
  (embedding notion, same reasoning as the other Section 4 cases), expanded
  the `toConcrete` citation to the full Jackson–Yu reference.
- Added `\lean{}` tags to 10 blueprint nodes (main_theorem, prop_2_1,
  cor_2_2_concrete, lemma_3_1/3_3/3_5, prop_4_1/4_2/4_3,
  folklore_conjecture), matching the sibling repo
  Pancyclicity-in-4-connected-planar-graphs' pattern. Wrapped the
  folklore-conjecture closing sentence in its own `\begin{corollary}` so it
  has a node to attach `\lean{}` to. Left `cor:conj_4con` untagged — no
  standalone Lean declaration corresponds to it. Regenerated and committed
  `blueprint/lean_decls` so `checkdecls` now actually validates something
  (was an empty file before).
- Verified locally, each command named and its exit code checked
  individually: `lake build` (0), `leanblueprint pdf` (0, real 4-page PDF),
  `leanblueprint web` (0, real HTML output), `lake exe checkdecls
  blueprint/lean_decls` (0, all 10 names resolve).
- Found and fixed a second concurrency bug while watching CI: `blueprint.yml`
  and `build-project.yml` both used the bare `${{ github.ref }}` group, so
  every push had them cancel each other (build-project.yml also triggers on
  `*.lean` pushes) — this is exactly the gotcha already logged in CLAUDE.md's
  CI notes, just not yet applied to the workflow files. Prefixed each group
  with its workflow name (`blueprint-`/`build-`).
- Pushed in 4 commits (axiom conversion, README sync, blueprint tags,
  concurrency fix — after rebasing once on 3 more dependabot merges).
  Watched `blueprint.yml` run `28942582104` to completion: **success**, all
  steps green, ~37 minutes total (docgen-action step alone took a while,
  consistent with a `texlive-full` container pull + doc-gen4 API doc build).

**Found:** nothing new required fixing beyond the concurrency scoping —
the `\lean{}` tags resolved cleanly on the first CI attempt after passing
locally, so no checkdecls-in-CI-only discrepancy this time.

**Blocked:** nothing outstanding. `lake build` green, CI green, blueprint
site reflects the new content.

**Current state:** `main` at `6e07518` before this log entry; the
CLAUDE.md milestone update and this entry are committed together as the
closing commit of the session.
