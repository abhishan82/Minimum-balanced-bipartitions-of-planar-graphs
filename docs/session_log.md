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
