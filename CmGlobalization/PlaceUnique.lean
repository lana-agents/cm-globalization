/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.Places

/-!
# Uniqueness of the place above `p` when `ℚ_p ⊗_ℚ E ≅ L`

Let `E` be a number field and `ι : E →+* L` an embedding into a finite extension `L/ℚ_p` (with a
norm extending the `p`-adic norm) such that `ι(E)` spans `L` over `ℚ_p` and
`[E : ℚ] = [L : ℚ_p]`, i.e. `ℚ_p ⊗_ℚ E → L` is an isomorphism. Then `place ι` is the only finite
place of `E` above `p`.

## Main results

* `CmGlobalization.algebraNorm_map_eq_of_basis`: if a ring hom `φ : E → L` maps a `K`-basis of
  `E` to a `K'`-basis of `L` (compatibly with `σ : K → K'`), then `N_{L/K'}(φ x) = σ N_{E/K}(x)`.
* `CmGlobalization.norm_algebraNorm_eq`: `|σ N_{E/K}(x)| = |σ c₀|^[E : K(x)]`, where `c₀` is the
  constant coefficient of the minimal polynomial of `x`.
* `CmGlobalization.norm_lt_one_of_mem`: every integer `a ∈ 𝓞 E` lying in a proper ideal
  containing `p` satisfies `‖ι a‖ < 1`.
* `CmGlobalization.eq_place_of_natCast_mem`: every height-one prime of `𝓞 E` containing `p` is
  `place ι`.

## Proof

Let `a ∈ P ∋ p` (`P ≠ ⊤`). The constant coefficient `c₀ ∈ ℤ` of the minimal polynomial of `a`
lies in `P ∩ ℤ = pℤ`, so `|N_{E/ℚ}(a)|_p = |c₀|_p ^ k < 1`. On the other hand
`N_{E/ℚ}(a) = N_{L/ℚ_p}(ι a)` (the multiplication matrices agree in a basis `b` of `E` and the
basis `ι ∘ b` of `L`), and `|N_{L/ℚ_p}(y)|_p = ‖y‖ ^ [L : ℚ_p]` since the norm of `L` is the
spectral norm (`spectralNorm_eq_norm_coeff_zero_rpow`). Hence `‖ι a‖ < 1`.
-/

open NumberField IsDedekindDomain Module IntermediateField Polynomial

namespace CmGlobalization

section Norm

/-- If `φ : E → L` maps a `K`-basis `b` of `E` to a `K'`-basis of `L`, compatibly with
`σ : K → K'`, then `φ` transports coordinates: `b'.repr (φ z) i = σ (b.repr z i)`. -/
theorem repr_map_eq_of_basis {K K' E L : Type*} [CommRing K] [CommRing K'] [CommRing E]
    [CommRing L] [Algebra K E] [Algebra K' L] (σ : K →+* K') (φ : E →+* L)
    (hφ : ∀ c, φ (algebraMap K E c) = algebraMap K' L (σ c)) {ι : Type*} [Fintype ι]
    (b : Basis ι K E) (b' : Basis ι K' L) (hb : ∀ i, b' i = φ (b i)) (z : E) (i : ι) :
    b'.repr (φ z) i = σ (b.repr z i) := by
  conv_lhs => rw [← b.sum_repr z]
  have : φ (∑ j, b.repr z j • b j) = ∑ j, σ (b.repr z j) • b' j := by
    simp only [map_sum, Algebra.smul_def, map_mul, hφ, hb]
  rw [this, b'.repr_sum_self]

/-- **Norms are compatible with base change.** If `φ : E → L` maps a `K`-basis of `E` to a
`K'`-basis of `L`, compatibly with `σ : K → K'`, then `N_{L/K'}(φ x) = σ N_{E/K}(x)`. -/
theorem algebraNorm_map_eq_of_basis {K K' E L : Type*} [CommRing K] [CommRing K'] [CommRing E]
    [CommRing L] [Algebra K E] [Algebra K' L] (σ : K →+* K') (φ : E →+* L)
    (hφ : ∀ c, φ (algebraMap K E c) = algebraMap K' L (σ c)) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι K E) (b' : Basis ι K' L) (hb : ∀ i, b' i = φ (b i)) (x : E) :
    Algebra.norm K' (φ x) = σ (Algebra.norm K x) := by
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul, repr_map_eq_of_basis σ φ hφ b b' hb]

/-- `|σ N_{E/K}(x)| = |σ c₀| ^ [E : K(x)]`, where `c₀` is the constant coefficient of the minimal
polynomial of `x` over `K`. -/
theorem norm_algebraNorm_eq {K E N : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [NormedField N] (σ : K →+* N) (x : E) :
    ‖σ (Algebra.norm K x)‖ = ‖σ ((minpoly K x).coeff 0)‖ ^ finrank K⟮x⟯ E := by
  have hx : IsIntegral K x := .of_finite K x
  rw [Algebra.norm_eq_norm_adjoin, ← adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen hx, minpoly_gen]
  simp

end Norm

section Unique

variable {p : ℕ} [Fact p.Prime] {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] {E : Type*} [Field E] [NumberField E]

omit [FiniteDimensional ℚ_[p] L] in
/-- If `ι(E)` spans `L` over `ℚ_p` and `[E : ℚ] = [L : ℚ_p]`, then `N_{L/ℚ_p}(ι x) = N_{E/ℚ}(x)`.
-/
theorem algebraNorm_map_eq (ι : E →+* L) (hspan : Submodule.span ℚ_[p] (Set.range ι) = ⊤)
    (hdeg : finrank ℚ E = finrank ℚ_[p] L) (x : E) :
    Algebra.norm ℚ_[p] (ι x) = (Algebra.norm ℚ x : ℚ_[p]) := by
  classical
  let b := Module.finBasis ℚ E
  have hle : ⊤ ≤ Submodule.span ℚ_[p] (Set.range (ι ∘ b)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [Algebra.smul_def, map_mul, show ι (algebraMap ℚ E (b.repr z j)) =
      algebraMap ℚ_[p] L (b.repr z j) by simp, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (f := ι ∘ b) j))
  let b' := basisOfTopLeSpanOfCardEqFinrank (ι ∘ b) hle (by simp [hdeg])
  exact algebraNorm_map_eq_of_basis (Rat.castHom ℚ_[p]) ι (fun c ↦ by simp) b b'
    (fun i ↦ by simp [b']) x

/-- `|N_{L/ℚ_p}(y)| ≥ 1` if `‖y‖ ≥ 1`. -/
theorem one_le_norm_algebraNorm {y : L} (hy : 1 ≤ ‖y‖) : 1 ≤ ‖Algebra.norm ℚ_[p] y‖ := by
  have h := norm_algebraNorm_eq (RingHom.id ℚ_[p]) y
  rw [RingHom.id_apply, RingHom.id_apply] at h
  rw [h]
  refine one_le_pow₀ ?_
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p],
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow] at hy
  by_contra! h1
  refine (Real.rpow_lt_one (norm_nonneg _) h1 ?_).not_ge hy
  have := minpoly.natDegree_pos (IsIntegral.of_finite ℚ_[p] y)
  positivity

/-- **Integers in a proper ideal containing `p` are small.** If `ι(E)` spans `L` over `ℚ_p` and
`[E : ℚ] = [L : ℚ_p]`, `P ≠ ⊤` is an ideal of `𝓞 E` containing `p` and `a ∈ P`, then
`‖ι a‖ < 1`. -/
theorem norm_lt_one_of_mem (ι : E →+* L) (hspan : Submodule.span ℚ_[p] (Set.range ι) = ⊤)
    (hdeg : finrank ℚ E = finrank ℚ_[p] L) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤)
    (hp : (p : 𝓞 E) ∈ P) {a : 𝓞 E} (ha : a ∈ P) : ‖ι a‖ < 1 := by
  by_contra! h1
  have hpos := one_le_norm_algebraNorm (p := p) h1
  rw [algebraNorm_map_eq ι hspan hdeg] at hpos
  -- the constant coefficient of the minimal polynomial of `a`
  have hint : IsIntegral ℤ (a : E) := a.isIntegral_coe
  set f := minpoly ℤ (a : E) with hf
  have hmin : minpoly ℚ (a : E) = f.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hc : ((f.coeff 0 : ℤ) : 𝓞 E) ∈ P := by
    obtain ⟨g, hg⟩ := X_dvd_sub_C (p := f)
    have h0 : aeval a f = 0 := by
      apply RingOfIntegers.coe_injective
      rw [← aeval_algebraMap_apply]
      exact minpoly.aeval ℤ (a : E)
    have : aeval a (f - C (f.coeff 0)) = aeval a (X * g) := by rw [hg]
    rw [map_sub, h0, aeval_C, aeval_mul, aeval_X, zero_sub, neg_eq_iff_eq_neg,
      algebraMap_int_eq, eq_intCast] at this
    rw [this]
    exact P.neg_mem (P.mul_mem_right _ ha)
  have hdvd : (p : ℤ) ∣ f.coeff 0 := by
    by_contra hnd
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    obtain ⟨u, w, huw⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
    apply hP
    rw [Ideal.eq_top_iff_one, ← Int.cast_one, ← huw]
    push_cast
    exact P.add_mem (P.mul_mem_left _ (by exact_mod_cast hp)) (P.mul_mem_left _ hc)
  have hlt : ‖((f.coeff 0 : ℤ) : ℚ_[p])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 hdvd
  have h := norm_algebraNorm_eq (Rat.castHom ℚ_[p]) (a : E)
  rw [hmin, coeff_map, Rat.coe_castHom, eq_intCast, Rat.cast_intCast] at h
  rw [h] at hpos
  exact (pow_lt_one₀ (norm_nonneg _) hlt finrank_pos.ne').not_ge hpos

/-- **`place ι` is the only place above `p`.** If `ι(E)` spans `L` over `ℚ_p` and
`[E : ℚ] = [L : ℚ_p]`, every height-one prime of `𝓞 E` containing `p` is `place ι`. -/
theorem eq_place_of_natCast_mem [IsUltrametricDist L] (ι : E →+* L)
    (hspan : Submodule.span ℚ_[p] (Set.range ι) = ⊤)
    (hdeg : finrank ℚ E = finrank ℚ_[p] L) {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1)
    (v : HeightOneSpectrum (𝓞 E)) (hp : (p : 𝓞 E) ∈ v.asIdeal) : v = place ι hn0 hn := by
  ext1
  refine v.isMaximal.eq_of_le (place ι hn0 hn).isPrime.ne_top fun a ha ↦ ?_
  exact norm_lt_one_of_mem ι hspan hdeg v.isPrime.ne_top hp ha

end Unique

end CmGlobalization
