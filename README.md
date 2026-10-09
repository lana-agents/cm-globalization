# cm-globalization

CM globalization of finite p-adic fields.

## Status

**Not started.** The repository is the initial project scaffold (a single commit,
2026-07-20). The library `CmGlobalization` contains only the placeholder module
`CmGlobalization/Basic.lean`, which has no declarations: there are no definitions or theorems yet
(and so no `sorry`, `axiom` or `admit`). Everything under *Goals* below is planned, not
formalised.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise the globalization of a finite extension `L/ℚ_p` to a CM number field with a specified `p`-adic completion.

Prove the polynomial-approximation / Krasner step producing a number field `F` with a place `v` such that `F_v ≃ L`, arrange the required archimedean signatures by weak approximation, and pass to a CM extension in which `p` has the desired splitting behaviour.

This is the elementary globalization argument used in *Topics in Absolute Anabelian Geometry III*, Appendix (CM1), and is a prerequisite for later CM realizations of Lubin–Tate characters.

Mathlib already contains Krasner-space infrastructure, number-field finite-place completions, and `NumberField.IsCMField`.

## Established sources

* Krasner's lemma and weak approximation, in standard algebraic-number-theory texts.
* Lang, *Complex Multiplication*.

## Related repositories

Intended as an input to the anabelian machinery of `iut`; not used by it.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `CmGlobalization/`, and every file must be imported from
the root module `CmGlobalization.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib CmGlobalization --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#17](https://taxis.lana.merten.dev/issues/17)

License: Apache 2.0 (see LICENSE).
