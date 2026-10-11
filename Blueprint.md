# Blueprint: CM globalization of finite extensions of `ℚ_p`

Source: [AbsTopIII] Appendix, (CM1). Standard ingredients: Krasner-type approximation,
weak approximation, Hensel's lemma.

## Target statement

Let `p` be a prime and `L` a finite extension of `ℚ_p`
(`[Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]`). Then there is a subfield
`F ⊆ L` (an `IntermediateField ℚ L`) such that

1. `F` is a number field and a CM field (`NumberField F`, `NumberField.IsCMField F`);
2. the maximal totally real subfield `F⁺` (Mathlib's `maximalRealSubfield F`) is dense in `L`
   for the canonical (module) topology of `L` over `ℚ_p`, hence so is `F`;
3. `F⁺` spans `L` over `ℚ_p` and `[F⁺ : ℚ] = [L : ℚ_p]`; equivalently `ℚ_p ⊗_ℚ F⁺ ≅ L`, i.e.
   `p` has exactly one place `v₀` in `F⁺`, and `F⁺_{v₀} ≅ L`;
4. `v₀` splits in `F`: there is `γ ∈ F` with `γ² = -(8p - 1)` and `γ ∈ ℚ_p ⊆ L`; the two
   embeddings `F ↪ L` given by the inclusion `ι` and by `ι ∘ c` (`c` the complex conjugation
   of `F`, `IsCMField.complexConj`) agree on `F⁺`, both have dense image, and are not related
   by any `ℚ_p`-automorphism of `L`, so they define the two distinct places of `F` above `v₀`,
   each with completion `L`.

"Completion `F_v ≅ L`" is expressed as "`F ↪ L` with dense image" (`L` is complete, so `L` is
the completion of `F` for the induced absolute value). The restatement
`exists_cmField_globalization'` (milestone M7) expresses it with Mathlib's
`HeightOneSpectrum` / `FinitePlace` / `adicCompletion` (see "Design choice" below).

## Milestones

All milestones are done (no `sorry`, no axioms beyond `propext`, `Classical.choice`,
`Quot.sound`; `lake build --wfail` passes).

* **M0** (done) `monicOf c = X^n + ∑ c_i X^i`: degree, monicity, evaluation, maps —
  `CmGlobalization/MonicOf.lean`.
* **M1** (done) roots of nearby polynomials via the inverse function theorem over any complete
  nontrivially normed field: `eventually_exists_root` — `CmGlobalization/RootNearby.lean`.
* **M2** (done) primitive elements of `L/K` form an open set
  (`isOpen_setOf_adjoin_simple_eq_top`); a `ℚ`-subalgebra of `L/ℚ_p` containing a primitive
  element is dense (`dense_of_mem_of_adjoin_eq_top`) — `CmGlobalization/Generator.lean`.
* **M3** (done) real roots ⇒ totally real (`isTotallyReal_adjoin_simple`); `x² = -d` impossible
  in totally real fields; `√-d` ⇒ totally complex — `CmGlobalization/RealRoots.lean`.
* **M4** (done) approximation: `exists_generator_root_real` — `CmGlobalization/Approximation.lean`.
* **M5** (done) `1 - 8p` is a square in `ℚ_p` (Hensel): `exists_sq_eq_one_sub_eight_mul` —
  `CmGlobalization/Approximation.lean`.
* **M6** (done) CM packaging `cmField β γ = ℚ⟮β⟯ ⊔ ℚ⟮γ⟯` (`isCMField_cmField`,
  `finrank_maximalRealSubfield_cmField`, `complexConj_gamma_ne`) —
  `CmGlobalization/CMField.lean`; main theorem `exists_cmField_globalization` and corollary
  `exists_isCMField_denseRange` — `CmGlobalization/Main.lean`.
* **M7** (done) places and completions: `place ι`, `isEquiv_place`, `exists_norm_eq_rpow`,
  `exists_ringEquiv_of_norm_eq_rpow`, `exists_adicCompletion_ringEquiv`,
  `exists_ringEquiv_of_place_eq` — `CmGlobalization/Places.lean`; restatement
  `exists_cmField_globalization'` — `CmGlobalization/MainPlaces.lean`.

## Proof sketch

* **M1.** Let `𝕜` be a complete nontrivially normed field and `L` a complete normed
  `𝕜`-algebra which is a field, `α ∈ L` a simple root of `f = monicOf a`. The map
  `Ψ(c, y) = (c, y^n + ∑ c_i y^i)` on `𝕜^n × L` is analytic, with strict derivative
  `(dc, dy) ↦ (dc, D(dc, 0) + f'(α) dy)`, surjective. By `map_nhds_eq_of_surj`, `Ψ` is open at
  `(a, α)`, so every `c` near `a` gives a root of `monicOf c` near `α`.
* **M2.** `y` generates `L/ℚ_p` iff `1, y, …, y^{n-1}` are linearly independent; that is an
  open condition (`isOpen_setOf_linearIndependent`). No Krasner's lemma is needed.
* **M4.** Take a primitive element `α`, `f` its minimal polynomial (separable). M1 gives a
  `ℚ_p`-neighbourhood `W` of the coefficients of `f` all of whose members have a root in the
  open set of generators. Let `h = ∏_{k=1}^n (X - k)`. Choose rational `c₀` near `f` and
  `t = p^N j / (1 + p^N j)` (p-adically small, real close to `1`); then
  `G = (1 - t) monicOf c₀ + t h` has coefficients in `W` (p-adically) and, by M1 over `ℝ`
  applied to each simple root `k` of `h`, has `n` distinct real roots. Its root `β` in `L`
  generates `L/ℚ_p`, so `G = minpoly ℚ β` (degree count).
* **M6.** `E = ℚ(β)` is totally real (all complex roots of `G` are real), `γ = √(1-8p) ∈ ℚ_p`,
  `F = E ⊔ ℚ(γ)`. `[F : E] ≤ 2`, `≠ 1` since `γ ∉ E`; `F` is totally complex since `γ² < 0`.
  `IsCMField.ofCMExtension` gives `IsCMField F`; `E ≤ F⁺`, and `F⁺ ≅ E` gives the degree.
  Density: `F⁺` contains the `ℚ_p`-basis `1, β, …, β^{n-1}` of `L`, and `ℚ` is dense in `ℚ_p`.

## Design choice: how "`F_v ≅ L`" is expressed

The place `v` is encoded by the embedding `ι : F ↪ L` (the inclusion) with dense image; the
place is `x ↦ ‖ι x‖` for any norm on `L` extending that of `ℚ_p`, and since `L` is complete it
is the completion of `F` at that place. This is the form of `exists_cmField_globalization`.

**M7** identifies this with Mathlib's objects (`CmGlobalization/Places.lean`), for `F` a number
field and `ι : F →+* L` into an ultrametric normed field with `‖(n : L)‖ < 1`, `n ≠ 0`:

* `a ∈ 𝓞 F ⇒ ‖ι a‖ ≤ 1` (integral over `ℤ`, ultrametric inequality), so
  `place ι = {a ∈ 𝓞 F | ‖ι a‖ < 1}` is a nonzero prime: a `HeightOneSpectrum (𝓞 F)`.
* Ostrowski-type comparison: two absolute values on `F` that are `≤ 1` on `𝓞 F` and `< 1`
  exactly on `v` are equivalent, since every `x ∈ F` is `n/d` or `d/n` with `n ∈ 𝓞 F`,
  `d ∉ v` (`exists_primeCompl_mul_eq_or_mul_eq`). Hence `FinitePlace.mk (place ι)` is
  equivalent to `x ↦ ‖ι x‖`, i.e. `‖ι x‖ = |x|_v ^ c` with `c > 0`.
* Uniqueness of completions: if `f₁ : F → K₁`, `f₂ : F → K₂` are dense into complete normed
  fields with `‖f₂ x‖ = ‖f₁ x‖ ^ c`, the pulled-back uniform structures on `F` agree; the two
  `AbstractCompletion`s give `K₁ ≃ᵤ K₂` extending the embeddings, which is a ring map by density.
  With `K₁ = v.adicCompletion F` (`FinitePlace.norm_embedding`, `denseRange_algebraMap`) this is
  `exists_adicCompletion_ringEquiv`.
* Distinct places: if `place ι = place (ι ∘ c)`, the comparison gives a continuous automorphism
  `τ` of `L` with `τ ∘ ι = ι ∘ c`; continuity and density of `ℚ` in `ℚ_p` make it
  `ℚ_p`-linear, contradicting clause 4. Lying over `v₀`: `c` fixes `F⁺`.

The isomorphisms `adicCompletion ≃ L` are ring isomorphisms and homeomorphisms; Mathlib gives
`v.adicCompletion F` no `ℚ_p`-algebra structure, so `ℚ_p`-linearity is not stated (it holds
automatically for continuous maps, as in the distinctness argument).
