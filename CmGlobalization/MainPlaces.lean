/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.Main
import CmGlobalization.PlaceUnique

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
* `v₀` is the only place of `F⁺` above `p`, and `w₁`, `w₂` are the only places of `F` above `p`
  (equivalently, above `v₀`): every height-one prime containing `p` is one of them;
* `w₁.adicCompletion F`, `w₂.adicCompletion F` and `v₀.adicCompletion F⁺` are isomorphic to `L`
  as topological fields (ring isomorphisms which are homeomorphisms), by isomorphisms extending
  `F ↪ L`, `F ↪ L` precomposed with complex conjugation, and `F⁺ ↪ L`.

The places are `CmGlobalization.place ι` (see `CmGlobalization/Places.lean`) for the three
embeddings `ι`. Distinctness `w₁ ≠ w₂` comes from the last clause of
`exists_cmField_globalization`: equal places would give a continuous, hence `ℚ_p`-linear,
automorphism of `L` intertwining `F ↪ L` with its twist by complex conjugation.

Uniqueness of `v₀` is `eq_place_of_natCast_mem` (`CmGlobalization/PlaceUnique.lean`), from
`ℚ_p ⊗_ℚ F⁺ ≅ L` (`F⁺` spans `L`, `[F⁺ : ℚ] = [L : ℚ_p]`) via norms. For `F`: if a prime `w ∋ p`
differs from `w₁`, `w₂`, pick `a ∈ w \ (w₁ ∪ w₂)`; then `b = a · ā ∈ 𝓞 F⁺` lies in `w ∩ 𝓞 F⁺`,
a proper ideal containing `p`, so `‖b‖ < 1` in `L`, but `‖b‖ = ‖a‖ ‖ā‖ = 1`.
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
`w₁, w₂` lie over `v₀`, `v₀` is the only place of `F⁺` above `p`, `w₁, w₂` are the only places
of `F` above `p` (equivalently above `v₀`), the absolute values of `w₁`, `w₂`, `v₀` are equivalent to `x ↦ ‖x‖`,
`x ↦ ‖x̄‖`, `x ↦ ‖x‖` respectively, and the three completions are isomorphic to `L` (as
topological fields, compatibly with these embeddings). In particular `v₀` splits in `F/F⁺`. -/
theorem exists_cmField_globalization' (p : ℕ) [Fact p.Prime] (L : Type*) [NormedField L]
    [CharZero L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    ∃ (F : IntermediateField ℚ L) (_ : NumberField F) (_ : IsCMField F)
      (w₁ w₂ : HeightOneSpectrum (𝓞 F)) (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield F))),
      w₁ ≠ w₂ ∧
      w₁.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) = v₀.asIdeal ∧
      w₂.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) = v₀.asIdeal ∧
      (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield F)),
        (p : 𝓞 (maximalRealSubfield F)) ∈ v.asIdeal ↔ v = v₀) ∧
      (∀ w : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ w.asIdeal ↔ w = w₁ ∨ w = w₂) ∧
      (∀ w : HeightOneSpectrum (𝓞 F),
        w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) = v₀.asIdeal ↔
          w = w₁ ∨ w = w₂) ∧
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
  obtain ⟨F, hNF, hCM, hdense, hspan, hdeg, -, -, -, -, hτ⟩ := exists_cmField_globalization p L
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
  -- `ι₀(F⁺)` spans `L` and `[F⁺ : ℚ] = [L : ℚ_p]`, so `v₀` is the only place of `F⁺` above `p`
  have hspan₀ : Submodule.span ℚ_[p] (Set.range ι₀) = ⊤ := by
    rw [← hspan]
    congr 1
    ext y
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, x.2, hx⟩, fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hx⟩, hxy⟩⟩
  have hv₀ := eq_place_of_natCast_mem ι₀ hspan₀ hdeg hn0 hn
  have hcomap₁ : (place ι₁ hn0 hn).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) =
      (place ι₀ hn0 hn).asIdeal := by
    ext a
    exact Iff.rfl
  have hcomap₂ : (place ι₂ hn0 hn).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) =
      (place ι₀ hn0 hn).asIdeal := by
    ext a
    have := (IsCMField.complexConj F).commutes (a : maximalRealSubfield F)
    exact Iff.of_eq (congrArg (‖algebraMap F L ·‖ < 1) this)
  have hpmem : ∀ ι : F →+* L, (p : 𝓞 F) ∈ (place ι hn0 hn).asIdeal := fun ι ↦ by
    simpa [mem_place_asIdeal] using hn
  have hw : ∀ w : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ w.asIdeal →
      w = place ι₁ hn0 hn ∨ w = place ι₂ hn0 hn := by
    intro w hpw
    by_contra! hne
    haveI := w.isPrime
    have hex : ∀ w' : HeightOneSpectrum (𝓞 F), w ≠ w' → ∃ a ∈ w.asIdeal, a ∉ w'.asIdeal := by
      intro w' hww'
      by_contra! hle
      exact hww' (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle))
    -- an element of `w` outside `w₁` and `w₂`
    obtain ⟨a, haw, ha₁, ha₂⟩ : ∃ a ∈ w.asIdeal, a ∉ (place ι₁ hn0 hn).asIdeal ∧
        a ∉ (place ι₂ hn0 hn).asIdeal := by
      obtain ⟨a₁, ha₁w, ha₁⟩ := hex _ hne.1
      obtain ⟨a₂, ha₂w, ha₂⟩ := hex _ hne.2
      by_cases h₁ : a₁ ∈ (place ι₂ hn0 hn).asIdeal
      · by_cases h₂ : a₂ ∈ (place ι₁ hn0 hn).asIdeal
        · refine ⟨a₁ + a₂, w.asIdeal.add_mem ha₁w ha₂w, fun h ↦ ha₁ ?_, fun h ↦ ha₂ ?_⟩
          · simpa using (place ι₁ hn0 hn).asIdeal.sub_mem h h₂
          · simpa using (place ι₂ hn0 hn).asIdeal.sub_mem h h₁
        · exact ⟨a₂, ha₂w, h₂, ha₂⟩
      · exact ⟨a₁, ha₁w, ha₁, h₁⟩
    -- `b = a * conj a ∈ 𝓞 F⁺` lies in `w ∩ 𝓞 F⁺`, a proper ideal containing `p`
    let σ : F →+* F := (IsCMField.complexConj F).toRingEquiv.toRingHom
    let c : 𝓞 F := ⟨σ a, a.isIntegral_coe.map σ.toIntAlgHom⟩
    have hmem : (a : F) * σ a ∈ maximalRealSubfield F := by
      rw [← IsCMField.complexConj_eq_self_iff, map_mul,
        show σ a = IsCMField.complexConj F a from rfl, IsCMField.complexConj_apply_apply,
        mul_comm]
    have hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield F) :=
      (isIntegral_algHom_iff (algebraMap (maximalRealSubfield F) F).toIntAlgHom
        (algebraMap (maximalRealSubfield F) F).injective).1 ((a * c).isIntegral_coe)
    let b : 𝓞 (maximalRealSubfield F) := ⟨⟨_, hmem⟩, hint⟩
    have hb : b ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) := by
      rw [Ideal.mem_comap, show algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F) b = a * c from rfl]
      exact w.asIdeal.mul_mem_right c haw
    have hp' : (p : 𝓞 (maximalRealSubfield F)) ∈
        w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield F)) (𝓞 F)) := by
      rw [Ideal.mem_comap, map_natCast]
      exact hpw
    have hlt := norm_lt_one_of_mem ι₀ hspan₀ hdeg (Ideal.IsPrime.ne_top inferInstance) hp' hb
    rw [show ι₀ b = ι₁ a * ι₂ a from rfl, norm_mul] at hlt
    rw [mem_place_asIdeal, not_lt] at ha₁ ha₂
    exact hlt.not_ge (one_le_mul_of_one_le_of_one_le ha₁ ha₂)
  refine ⟨F, hNF, hCM, place ι₁ hn0 hn, place ι₂ hn0 hn, place ι₀ hn0 hn, fun heq ↦ ?_,
    hcomap₁, hcomap₂, fun v ↦ ⟨hv₀ v, ?_⟩, fun w ↦ ⟨hw w, ?_⟩, fun w ↦ ⟨fun h ↦ hw w ?_, ?_⟩,
    ⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩, ⟨c₀, hc₀, h₀⟩, ⟨e₁, he₁⟩, ⟨e₂, he₂⟩, ⟨e₀, he₀⟩⟩
  · obtain ⟨τ, hτc, -, hτι⟩ := exists_ringEquiv_of_place_eq hd₁ hd₂ hn0 hn heq
    exact hτ ⟨{ τ with commutes' := algebraMap_eq_of_continuous τ.toRingHom hτc }, hτι⟩
  · rintro rfl
    simpa [mem_place_asIdeal] using hn
  · rintro (rfl | rfl) <;> exact hpmem _
  · have hp₀ : (p : 𝓞 (maximalRealSubfield F)) ∈ (place ι₀ hn0 hn).asIdeal := by
      simpa [mem_place_asIdeal] using hn
    rw [← h, Ideal.mem_comap, map_natCast] at hp₀
    exact hp₀
  · rintro (rfl | rfl)
    exacts [hcomap₁, hcomap₂]

end CmGlobalization
