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

---

## 2026-07-13

**Done:**
- Added a new non-negotiable convention to CLAUDE.md: session startup reads
  `docs/next_session.md` and executes it; session end overwrites it with the
  next session's prompt (agreed with the author) and commits — a session
  isn't finished until its successor is queued.
- Seeded `docs/next_session.md` with the author-agreed prompt for the next
  session: (1) sync the doc-comment/README ledger buckets once the author
  fills in the post-review revisions, (2) rank the bucket-A sorry survivors
  by estimated proof difficulty without attempting any proofs, propose the
  top-ranked one as minbal's first weekly lemma, and draft its proof-session
  prompt (mirroring the sibling repo's lemma-prompt constraints: no new
  axioms/sorries, statement unchanged, search Mathlib+Foundations first,
  3-strategies-then-stop, walkthrough on success, prover_log either way),
  (3) log/commit/push.

**Found:** nothing.

**Blocked:** nothing. The bucket-review revisions are a placeholder
pending the author's Tuesday review — next session should not proceed past
step 1 until that's filled in.

**Current state:** `main` at this commit once pushed.

---

## 2026-07-21

**Statement-faithfulness repair.** The author replaced `docs/next_session.md`
with a full rewrite (a much larger and more specific brief than the bucket-
review placeholder queued 2026-07-13) diagnosing five concrete bugs in the
no-balanced-sep-tri case analysis and prescribing the fix. Restart-and-read
picked up the new prompt correctly. Zero proof work this session — every
touched declaration stays `:= sorry`; `main_theorem`/`folklore_conjecture`
still compile through the whole sorry chain, now with an honest, correctly-
scoped gap instead of a silently-vacuous case.

**Done:**
- **Task 1 — `SinkData`:** new interface structure bundling the sink
  component `S`, `TS : Triangulation (G.induce ↑S)` with `noSepTri : ¬
  Nonempty (SepTri TS)`, a witnessing `sepInG : ∃ st : SepTri T, st.sa ∈ S ∧
  st.sb ∈ S ∧ st.sc ∈ S` (existing `SepTri` predicate reused, nothing
  invented), an opaque `stDegree : ℕ`, and the degree-1 interval data
  (`I`, `hI_small`, `hS_I_tri`, migrated verbatim from the old
  `deg1_sink_bipartition`). Mirrors `NearTriangulation`/`toConcrete`: an
  opaque Type-valued interface, not a construction.
- **Task 2 — `no_sep_tri_gives_sink`:** was `theorem ... : (∃ S I, ...) ∨
  (∃ S, S.card = 4) := sorry` — the right disjunct is true of any graph with
  ≥4 vertices, i.e. vacuous. Restated as `noncomputable def ... : SinkData
  T := sorry` (Type-valued, so `def` not `theorem`, matching `toConcrete`'s
  precedent), directly asserting sink existence.
- **Task 3 — `deg1_sink_bipartition`/`tiny_sink_bipartition`:** both now take
  `(sd : SinkData T)` plus a discriminating hypothesis (`sd.stDegree = 1` /
  `sd.S.card = 4`) instead of a free-floating `S_verts`. `deg1_sink_bipartition`'s
  conclusion corrected to match blueprint `prop:onedegsink` exactly ("both
  parts biconnected near-triangulations" — no block-count clause; the old
  Lean had one that isn't in the paper's stated Prop 4.2).
  `prop_4_2`'s wrapper proof updated mechanically (no new math) to derive
  the block-count bound from biconnectivity via the already-proved
  `biconnected_blockCount_eq_one`. `tiny_sink_bipartition` keeps its
  existing conclusion shape (matches blueprint `prop:sonly4`); its doc
  comment and `prop_4_3`'s now correctly say "Proposition 4.4" instead of
  the former mislabel "4.3" — **did not rename the `prop_4_3` Lean
  identifier itself** (would touch call sites + blueprint `\lean` tag,
  judged out of scope for a statement-only session; flagged below for the
  author).
- **Task 4 — `sink_navigation`:** new honest stub for paper Section 5
  (degree ≥2, |S|≥6), previously entirely absent — the old two-way case
  split silently routed this case through the vacuous `S.card=4` branch.
- **Task 5 — `main_theorem_no_sep_tri`:** rewritten as a genuine three-way
  `by_cases`/`by_cases` split on `sd.stDegree = 1` then `sd.S.card = 4`,
  routing the remaining case through `sink_navigation`. Needed two small
  arithmetic/semantic bridge lemmas (`sd.stDegree ≠ 1 ⟹ ≥ 2`;
  `sd.S.card ≠ 4 ⟹ ≥ 6`), stated as their own sorried declarations per the
  brief's explicit instruction rather than hand-waved — neither is provable
  from Finset arithmetic alone (`stDegree` could be 0; `S.card` could be 5).
- **Task 6 — ledger, blueprint, verification:** README re-bucketed (table
  below); added a prominent standalone "Section 5 not yet formalized"
  callout. Blueprint: added a `%`-comment on `prop:warmup` carrying the
  bug-5 flag (source-only, doesn't change rendered content), and a new
  "Sink Navigation (Section 5)" section with `def:sinkdata` and
  `prop:sinknav` (the latter marked `\notready`). Regenerated
  `blueprint/lean_decls`. Verified locally, each command named:
  `lake build` (0), `leanblueprint pdf` (0, 4-page PDF), `leanblueprint
  web` (0), `lake exe checkdecls blueprint/lean_decls` (0, all 12 names
  resolve including the 2 new ones).
- Committed in 3 pieces: Lean changes (`59df5ea`), README+blueprint
  (`604ee85`), this close-out.

**Bucket table (before → after):**

| Declaration | Before | After | Why |
|---|---|---|---|
| `induce_euler` | A | A | untouched |
| `concretePlaneNT_cut_vertex_decomp_geo` | A | A | untouched |
| `induceData` | A | A | untouched |
| `NearTriangulation.toConcrete` | C | C | untouched |
| `nt_good_vertex_exists` | A | A | untouched |
| `sep_tri_bipartition` | A | A | untouched; conclusion-drift flagged, not fixed |
| `deg1_sink_bipartition` | A | B | now consumes `SinkData`, conclusion corrected to match blueprint |
| `tiny_sink_bipartition` | A | B | now consumes `SinkData`; Prop 4.4 mislabel comment fixed |
| `no_sep_tri_gives_sink` | A | C | restated to return `SinkData T` directly, no longer vacuous |
| `SinkData` (new) | — | C | new opaque interface |
| `sink_navigation` (new) | — | C | new; Section 5, **NOT YET FORMALIZED** |
| `sinkData_stDegree_ge_two_of_ne_one` (new) | — | C | new bridge lemma |
| `sinkData_card_ge_six_of_ne_four` (new) | — | C | new bridge lemma |

Repo-wide: 0 axioms throughout (unchanged); sorries 9 → 12 (net +3: `sink_navigation`
plus the two bridge lemmas; the four restated declarations stay sorried 1-for-1).

**Found (flagged for author, not silently fixed — bug #5 from the brief):**
`sep_tri_bipartition`'s conclusion states `blockCount ≤ internal + 2` with no
biconnectivity requirement on either part. Blueprint `prop:warmup` (the
paper's actual Prop 4.1) states the stronger/different form: `+1` with
`G[V₁]` specifically **biconnected** and `G[V₂]` merely connected. This may
be an intentional weakening on the Lean side that still feeds the final `+2`
bound of Theorem 1.1 through a different route — or it may be a genuine gap.
Left exactly as instructed: noted in the blueprint source (`%` comment on
`prop:warmup`) and here, not silently changed. **Needs an author decision.**

**Also flagged:** `prop_4_3`'s Lean identifier still says "4_3" though it now
correctly documents itself as realizing paper Prop 4.4 (the doc-comment
mislabel is fixed; the identifier is not, since renaming touches call sites
in `main_theorem_no_sep_tri` and the blueprint's `\lean{MinBal.prop_4_3}`
tag at `prop:sonly4` — judged out of scope for a statement-faithfulness-only
session with zero proof work). Author may want a follow-up rename session.

**Blocked:** nothing. `lake build` green throughout every commit (checked
after each of the 3 commits' worth of changes, not just at the end).

**Current state:** `main` at this commit once pushed. Next queued prompt
(see `docs/next_session.md`, overwritten as part of this close-out): begin
formalizing Section 5 (`sink_navigation`) — deliberately NOT started this
session.
