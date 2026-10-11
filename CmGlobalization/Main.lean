/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.Approximation
import CmGlobalization.CMField

/-!
# CM globalization of finite extensions of `ℚ_p`

This file proves the globalization statement of [AbsTopIII, Appendix, (CM1)]: every finite
extension `L` of `ℚ_p` is the completion of a CM number field at a place above `p`, where
moreover the place splits over the maximal totally real subfield.

## Main result

`CmGlobalization.exists_cmField_globalization`: for a prime `p` and a finite extension `L/ℚ_p`,
there is a subfield `F ⊆ L` such that

* `F` is a number field and a CM field;
* the maximal real subfield `F⁺` (Mathlib's `NumberField.maximalRealSubfield`) is dense in `L`
  for the canonical topology of `L` as a finite-dimensional `ℚ_p`-vector space;
* `F⁺` spans `L` over `ℚ_p` and `[F⁺ : ℚ] = [L : ℚ_p]` (equivalently the natural map
  `ℚ_p ⊗_ℚ F⁺ → L` is an isomorphism: `p` has a unique place `v₀` in `F⁺`, and `F⁺_{v₀} ≅ L`);
* there is `γ ∈ F` with `γ ^ 2 = -(8p - 1)` and `γ ∈ ℚ_p ⊆ L`, and no `ℚ_p`-automorphism of `L`
  intertwines the inclusion `F ↪ L` with its twist by complex conjugation (which fixes `F⁺`).
  Hence the two embeddings `F ↪ L` (both with dense image) define two distinct places of `F`
  above `v₀`, each with completion `L`: `v₀` splits in `F/F⁺`.

Here "the completion of `F` at `v` is `L`" is expressed by a field embedding `F ↪ L` with dense
image: `L` is complete, so it is the completion of `F` for the induced absolute value.

## Implementation

`exists_generator_root_real` (see `CmGlobalization/Approximation.lean`) produces a primitive
element `β` of `L/ℚ_p` whose minimal polynomial over `ℚ` has degree `[L : ℚ_p]` and only real
roots; `exists_sq_eq_one_sub_eight_mul` gives `√(1 - 8p) ∈ ℚ_p`; `cmField β γ = ℚ⟮β⟯ ⊔ ℚ⟮γ⟯`
(see `CmGlobalization/CMField.lean`) is the CM field.
-/

open Polynomial NumberField IntermediateField Module

universe u

namespace CmGlobalization

/-- A `ℚ_p`-algebra which is a field has characteristic zero (so the `[CharZero L]` hypotheses
below are automatic). -/
theorem charZero_of_padic (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L] :
    CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective

/-- The approximation step for a finite extension `L/ℚ_p` without a chosen norm (we use the
spectral norm). -/
theorem exists_generator_root_real' (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [CharZero L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    ∃ (β : L) (c : Fin (finrank ℚ_[p] L) → ℚ), ℚ_[p]⟮β⟯ = ⊤ ∧ aeval β (monicOf c) = 0 ∧
      ∃ s : Finset ℝ, s.card = finrank ℚ_[p] L ∧ ∀ r ∈ s, aeval r (monicOf c) = 0 := by
  letI := spectralNorm.nontriviallyNormedField ℚ_[p] L
  letI := spectralNorm.normedAlgebra ℚ_[p] L
  exact exists_generator_root_real p L

/-- If `β` generates `L/ℚ_p` and is a root of a monic rational polynomial `G` of degree
`[L : ℚ_p]`, then `G` is the minimal polynomial of `β` over `ℚ`. -/
theorem minpoly_eq_monicOf {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharZero L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] {β : L} {c : Fin (finrank ℚ_[p] L) → ℚ}
    (hgen : ℚ_[p]⟮β⟯ = ⊤) (hβ : aeval β (monicOf c) = 0) : minpoly ℚ β = monicOf c := by
  have : IsScalarTower ℚ ℚ_[p] L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hint : IsIntegral ℚ β := ⟨monicOf c, monicOf_monic c, hβ⟩
  have hdegp : (minpoly ℚ_[p] β).natDegree = finrank ℚ_[p] L := by
    rw [← adjoin.finrank (.of_finite ℚ_[p] β), hgen, finrank_top']
  have hle : finrank ℚ_[p] L ≤ (minpoly ℚ β).natDegree := by
    rw [← hdegp]
    exact (natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower ℚ ℚ_[p] β)
      ((minpoly.monic hint).map _).ne_zero).trans_eq (natDegree_map _)
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monicOf_monic c)
    (minpoly.dvd ℚ β hβ) (by rwa [natDegree_monicOf])).symm

/-- **CM globalization** ([AbsTopIII], Appendix, (CM1)). Every finite extension `L` of `ℚ_p`
contains a CM number field `F` whose maximal real subfield `F⁺` is dense in `L`, spans `L` over
`ℚ_p` and has degree `[L : ℚ_p]` over `ℚ` (so `p` has a unique place `v₀` in `F⁺`, with
completion `L`), and such that `v₀` splits in `F`: `F` contains a square root `γ ∈ ℚ_p` of
`-(8p - 1)`, and the inclusion `F ↪ L` and its twist by complex conjugation (which fixes `F⁺`)
are not related by any `ℚ_p`-automorphism of `L`. -/
theorem exists_cmField_globalization (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [CharZero L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    ∃ (F : IntermediateField ℚ L) (_ : NumberField F) (_ : IsCMField F),
      (∀ [TopologicalSpace L] [IsModuleTopology ℚ_[p] L],
        Dense (((↑) : F → L) '' (maximalRealSubfield F : Set F))) ∧
      Submodule.span ℚ_[p] (((↑) : F → L) '' (maximalRealSubfield F : Set F)) = ⊤ ∧
      finrank ℚ (maximalRealSubfield F) = finrank ℚ_[p] L ∧
      (∀ x ∈ maximalRealSubfield F, IsCMField.complexConj F x = x) ∧
      ∃ γ : F, γ ^ 2 = -((8 * p - 1 : ℚ) : F) ∧ (γ : L) ∈ Set.range (algebraMap ℚ_[p] L) ∧
        ¬ ∃ τ : L ≃ₐ[ℚ_[p]] L, ∀ x : F, τ x = IsCMField.complexConj F x := by
  obtain ⟨β, c, hgen, hβ, s, hs, hroot⟩ := exists_generator_root_real' p L
  have hmin := minpoly_eq_monicOf hgen hβ
  have hint : IsIntegral ℚ β := ⟨monicOf c, monicOf_monic c, hβ⟩
  have hE : IsTotallyReal ℚ⟮β⟯ := isTotallyReal_adjoin_simple fun z hz ↦ by
    rw [hmin] at hz
    obtain ⟨r, -, hr⟩ := exists_real_eq_of_aeval_eq_zero (monicOf_monic c).ne_zero s
      (by rw [natDegree_monicOf, hs]) hroot hz
    exact ⟨r, hr⟩
  obtain ⟨s0, hs0⟩ := exists_sq_eq_one_sub_eight_mul p
  set γ : L := algebraMap ℚ_[p] L s0
  set d : ℚ := 8 * p - 1 with hd_def
  have hp : (2 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hd : 0 < d := by rw [hd_def]; linarith
  have hγ : γ ^ 2 = -(d : L) := by
    rw [← map_pow, hs0, hd_def]
    simp only [map_sub, map_one, map_mul, map_ofNat, map_natCast]
    push_cast
    ring
  have hNF := numberField_cmField hint hγ
  have hCM := isCMField_cmField hint hγ hd
  refine ⟨cmField β γ, hNF, hCM, ?_, ?_, ?_, ?_, gamma', ?_, ⟨s0, rfl⟩, ?_⟩
  · -- density
    intro _ _
    refine (dense_of_mem_of_adjoin_eq_top (p := p) (ℚ⟮β⟯).toSubalgebra
      (mem_adjoin_simple_self ℚ β) hgen).mono ?_
    intro x hx
    exact ⟨⟨x, le_cmField_left hx⟩, mem_maximalRealSubfield_cmField hx, rfl⟩
  · -- spanning
    have hli := adjoin_simple_eq_top_iff_linearIndependent.1 hgen
    rw [eq_top_iff, ← hli.span_eq_top_of_card_eq_finrank' (by simp)]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    have hx : β ^ (i : ℕ) ∈ ℚ⟮β⟯ := pow_mem (mem_adjoin_simple_self ℚ β) _
    exact ⟨⟨_, le_cmField_left hx⟩, mem_maximalRealSubfield_cmField hx, rfl⟩
  · -- degree
    rw [finrank_maximalRealSubfield_cmField hint hγ hd, adjoin.finrank hint, hmin,
      natDegree_monicOf]
  · intro x hx
    exact IsCMField.complexConj_apply_eq_self (cmField β γ) ⟨x, hx⟩
  · show (gamma' : cmField β γ) ^ 2 = -((d : ℚ) : cmField β γ)
    ext
    simp [gamma', hγ]
  · rintro ⟨τ, hτ⟩
    refine complexConj_gamma_ne hint hγ hd (Subtype.ext ?_)
    rw [← hτ gamma']
    exact τ.commutes s0

/-- `exists_cmField_globalization` in the form "there is a CM number field `F` with an embedding
`F ↪ L` with dense image" (so `L` is the completion of `F` at the induced place). -/
theorem exists_isCMField_denseRange (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] [CharZero L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [TopologicalSpace L]
    [IsModuleTopology ℚ_[p] L] :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F) (_ : IsCMField F) (ι : F →+* L),
      DenseRange ι := by
  obtain ⟨F, hNF, hCM, hdense, -⟩ := exists_cmField_globalization p L
  refine ⟨↥F, inferInstance, hNF, hCM, F.val.toRingHom, hdense.mono ?_⟩
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

end CmGlobalization
