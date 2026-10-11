/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.Main
import CmGlobalization.Places

/-!
# CM globalization in terms of Mathlib's finite places and adic completions

`CmGlobalization.exists_cmField_globalization'` restates `exists_cmField_globalization` for a
finite extension `L/ℚ_p` equipped with a norm extending the `p`-adic norm (e.g. the spectral
norm `spectralNorm.normedField ℚ_[p] L`; such a norm is unique): there are a CM number field
`F ⊆ L`, height-one primes `w₁ ≠ w₂` of `𝓞 F` and `v₀` of `𝓞 F⁺` (`F⁺ = maximalRealSubfield F`)
such that

* the absolute values of the finite places `w₁`, `w₂`, `v₀` are (up to a positive power)
  `x ↦ ‖x‖`, `x ↦ ‖x̄‖` and `x ↦ ‖x‖`;
* `w₁` and `w₂` lie over `v₀`;
* `w₁.adicCompletion F`, `w₂.adicCompletion F` and `v₀.adicCompletion F⁺` are isomorphic to `L`
  as topological fields (ring isomorphisms which are homeomorphisms), by isomorphisms extending
  `F ↪ L`, `F ↪ L` precomposed with complex conjugation, and `F⁺ ↪ L`.

The places are `CmGlobalization.place ι` (see `CmGlobalization/Places.lean`) for the three
embeddings `ι`. Distinctness `w₁ ≠ w₂` comes from the last clause of
`exists_cmField_globalization`: equal places would give a continuous, hence `ℚ_p`-linear,
automorphism of `L` intertwining `F ↪ L` with its twist by complex conjugation.
-/

open NumberField IsDedekindDomain Module

namespace CmGlobalization

variable (p : ℕ) [Fact p.Prime] (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]

theorem norm_natCast_p_lt_one : ‖((p : ℕ) : L)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] L), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem prime_ne_zero : p ≠ 0 := (Fact.out : p.Prime).ne_zero

variable {p L}

/-- A continuous field automorphism of a normed `ℚ_p`-algebra is `ℚ_p`-linear. -/
theorem algebraMap_eq_of_continuous (τ : L →+* L) (hτ : Continuous τ) (a : ℚ_[p]) :
    τ (algebraMap ℚ_[p] L a) = algebraMap ℚ_[p] L a := by
  have hc : Continuous (algebraMap ℚ_[p] L) := continuous_algebraMap ℚ_[p] L
  refine congrFun ((Padic.denseRange_ratCast p).equalizer (hτ.comp hc) hc
    (funext fun q ↦ ?_)) a
  simp

/-- **CM globalization, with places and completions** ([AbsTopIII], Appendix, (CM1)). Let `L` be
a finite extension of `ℚ_p` with a norm extending the `p`-adic norm. There are a CM number field
`F ⊆ L`, two distinct finite places `w₁ ≠ w₂` of `F` and a finite place `v₀` of `F⁺` such that
`w₁, w₂` lie over `v₀`, the absolute values of `w₁`, `w₂`, `v₀` are equivalent to `x ↦ ‖x‖`,
`x ↦ ‖x̄‖`, `x ↦ ‖x‖` respectively, and the three completions are isomorphic to `L` (as
topological fields, compatibly with these embeddings). In particular `v₀` splits in `F/F⁺`. -/
theorem exists_cmField_globalization' (p : ℕ) [Fact p.Prime] (L : Type*) [NormedField L]
    [CharZero L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    ∃ (F : IntermediateField ℚ L) (_ : NumberField F) (_ : IsCMField F)
      (w₁ w₂ : HeightOneSpectrum (𝓞 F)) (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield F))),
      w₁ ≠ w₂ ∧
      w₁.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) = v₀.asIdeal ∧
      w₂.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) = v₀.asIdeal ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x : F, ‖(x : L)‖ = FinitePlace.mk w₁ x ^ c) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x : F, ‖(IsCMField.complexConj F x : L)‖ = FinitePlace.mk w₂ x ^ c) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x : maximalRealSubfield F, ‖((x : F) : L)‖ = FinitePlace.mk v₀ x ^ c) ∧
      (∃ e : w₁.adicCompletion F ≃+* L, Continuous e ∧ Continuous e.symm ∧
        ∀ x : F, e (algebraMap F _ x) = x) ∧
      (∃ e : w₂.adicCompletion F ≃+* L, Continuous e ∧ Continuous e.symm ∧
        ∀ x : F, e (algebraMap F _ x) = IsCMField.complexConj F x) ∧
      ∃ e : v₀.adicCompletion (maximalRealSubfield F) ≃+* L, Continuous e ∧ Continuous e.symm ∧
        ∀ x : maximalRealSubfield F, e (algebraMap (maximalRealSubfield F) _ x) = (x : F) := by
  haveI : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  obtain ⟨F, hNF, hCM, hdense, -, -, -, -, -, -, hτ⟩ := exists_cmField_globalization p L
  have hdense := @hdense _ (isModuleTopologyOfFiniteDimensional (𝕜 := ℚ_[p]) (E := L))
  let ι₁ : F →+* L := algebraMap F L
  let ι₂ : F →+* L := ι₁.comp (IsCMField.complexConj F).toRingEquiv.toRingHom
  let ι₀ : maximalRealSubfield F →+* L := ι₁.comp (algebraMap (maximalRealSubfield F) F)
  have hd₀ : DenseRange ι₀ := hdense.mono (by rintro _ ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hd₁ : DenseRange ι₁ := hd₀.mono (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩)
  have hd₂ : DenseRange ι₂ := hd₁.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨IsCMField.complexConj F x, by simp [ι₂]⟩)
  have hn0 := prime_ne_zero p
  have hn := norm_natCast_p_lt_one p L
  obtain ⟨c₁, hc₁, h₁⟩ := exists_norm_eq_rpow ι₁ hn0 hn
  obtain ⟨c₂, hc₂, h₂⟩ := exists_norm_eq_rpow ι₂ hn0 hn
  obtain ⟨c₀, hc₀, h₀⟩ := exists_norm_eq_rpow ι₀ hn0 hn
  obtain ⟨e₁, he₁⟩ := exists_adicCompletion_ringEquiv ι₁ hd₁ hn0 hn
  obtain ⟨e₂, he₂⟩ := exists_adicCompletion_ringEquiv ι₂ hd₂ hn0 hn
  obtain ⟨e₀, he₀⟩ := exists_adicCompletion_ringEquiv ι₀ hd₀ hn0 hn
  refine ⟨F, hNF, hCM, place ι₁ hn0 hn, place ι₂ hn0 hn, place ι₀ hn0 hn, fun heq ↦ ?_,
    ?_, ?_, ⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩, ⟨c₀, hc₀, h₀⟩, ⟨e₁, he₁⟩, ⟨e₂, he₂⟩, ⟨e₀, he₀⟩⟩
  · obtain ⟨τ, hτc, -, hτι⟩ := exists_ringEquiv_of_place_eq hd₁ hd₂ hn0 hn heq
    exact hτ ⟨{ τ with commutes' := algebraMap_eq_of_continuous τ.toRingHom hτc }, hτι⟩
  · ext a
    exact Iff.rfl
  · ext a
    have := (IsCMField.complexConj F).commutes (a : maximalRealSubfield F)
    exact Iff.of_eq (congrArg (‖algebraMap F L ·‖ < 1) this)

end CmGlobalization
