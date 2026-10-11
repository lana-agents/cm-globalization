# cm-globalization

CM globalization of finite p-adic fields.

## Status

**Complete** for the scope described in *Goals* (branch `wp-cm`, merged to `main`). The library
contains no `sorry`, `admit` or `axiom`; the main theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`, and `lake build --wfail` passes.

Main result, `CmGlobalization.exists_cmField_globalization` (`CmGlobalization/Main.lean`): for a
prime `p` and a finite extension `L/ℚ_p` (`[Field L] [CharZero L] [Algebra ℚ_[p] L]
[FiniteDimensional ℚ_[p] L]`; `CharZero L` is automatic, see `charZero_of_padic`) there is
`F : IntermediateField ℚ L` with

* `NumberField F` and `NumberField.IsCMField F`;
* the maximal real subfield `F⁺ = maximalRealSubfield F` is dense in `L` for every topology on
  `L` with `IsModuleTopology ℚ_[p] L`;
* `Submodule.span ℚ_[p] F⁺ = ⊤` and `finrank ℚ F⁺ = finrank ℚ_[p] L`, i.e.
  `ℚ_p ⊗_ℚ F⁺ ≅ L`: `p` has exactly one place `v₀` in `F⁺`, and `F⁺_{v₀} ≅ L`;
* complex conjugation `c` of `F` fixes `F⁺`, and there is `γ ∈ F` with `γ² = -(8p - 1)` and
  `γ ∈ ℚ_p ⊆ L` such that no `ℚ_p`-automorphism `τ` of `L` satisfies `τ ∘ ι = ι ∘ c` (`ι` the
  inclusion). So the two embeddings `ι`, `ι ∘ c` of `F` into `L` (both with dense image) give two
  distinct places of `F` above `v₀`, each with completion `L`: `v₀` splits in `F/F⁺`.

"Completion `F_v ≅ L`" is expressed by an embedding `F ↪ L` with dense image (`L` is complete).
Corollary `exists_isCMField_denseRange`: there is a CM number field `F : Type u` with a ring
embedding `F →+* L` of dense range.

The same result in terms of Mathlib's places and completions is
`CmGlobalization.exists_cmField_globalization'` (`CmGlobalization/MainPlaces.lean`), for `L`
with a norm extending the `p`-adic norm (`[NormedField L] [NormedAlgebra ℚ_[p] L]`, e.g. the
spectral norm): there are `w₁ ≠ w₂ : HeightOneSpectrum (𝓞 F)` and
`v₀ : HeightOneSpectrum (𝓞 F⁺)` with

* `w₁`, `w₂` lying over `v₀` (`comap` of the ideals along `𝓞 F⁺ → 𝓞 F`);
* `‖x‖ = |x|_{w₁}^c`, `‖c(x)‖ = |x|_{w₂}^c'`, `‖y‖ = |y|_{v₀}^c''` (`x ∈ F`, `y ∈ F⁺`) for
  positive constants, with `|·|_w = NumberField.FinitePlace.mk w`;
* ring isomorphisms `w₁.adicCompletion F ≃+* L`, `w₂.adicCompletion F ≃+* L`,
  `v₀.adicCompletion F⁺ ≃+* L` that are homeomorphisms and extend `ι`, `ι ∘ c`, `ι|_{F⁺}`.

The general machinery is in `CmGlobalization/Places.lean`: for a number field `F` and
`ι : F →+* L` into an ultrametric normed field with `‖(n : L)‖ < 1` (some `n ≠ 0`),
`place ι` is the height-one prime `{a ∈ 𝓞 F | ‖ι a‖ < 1}`, `isEquiv_place` /
`exists_norm_eq_rpow` compare `x ↦ ‖ι x‖` with the finite place, `exists_adicCompletion_ringEquiv`
identifies the adic completion with `L` when `ι` is dense and `L` complete (uniqueness of
completions, `exists_ringEquiv_of_norm_eq_rpow`), and `exists_ringEquiv_of_place_eq` shows that
dense embeddings defining the same place differ by a continuous automorphism of `L`.

The argument avoids Krasner's lemma: roots of nearby polynomials come from the inverse function
theorem (`CmGlobalization/RootNearby.lean`), and primitive elements form an open set
(`CmGlobalization/Generator.lean`). See `Blueprint.md` for the milestones and proof sketch.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise the globalization of a finite extension `L/ℚ_p` to a CM number field with a specified `p`-adic completion.

Prove the polynomial-approximation / Krasner step producing a number field `F` with a place `v` such that `F_v ≃ L`, arrange the required archimedean signatures by weak approximation, and pass to a CM extension in which `p` has the desired splitting behaviour.

This is the elementary globalization argument used in *Topics in Absolute Anabelian Geometry III*, Appendix (CM1), and is a prerequisite for later CM realizations of Lubin–Tate characters.

Mathlib already contains Krasner-space infrastructure, number-field finite-place completions, and `NumberField.IsCMField`; this project uses `IsCMField.ofCMExtension`, the spectral norm, the inverse function theorem and Hensel's lemma for `ℤ_p`.

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
