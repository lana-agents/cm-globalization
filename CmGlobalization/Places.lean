/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Finite places and completions from embeddings into ultrametric fields

Let `F` be a number field and `ι : F →+* L` a ring homomorphism into an ultrametric normed field
`L` with `‖(n : L)‖ < 1` for some nonzero natural number `n` (e.g. `L` a normed `ℚ_p`-algebra and
`n = p`). We construct the corresponding finite place of `F` and identify completions.

## Main results

* `CmGlobalization.place ι hn0 hn : HeightOneSpectrum (𝓞 F)`: the height-one prime
  `{a ∈ 𝓞 F | ‖ι a‖ < 1}` (`mem_place_asIdeal`).
* `CmGlobalization.isEquiv_place`: the absolute value of the finite place
  `NumberField.FinitePlace.mk (place ι hn0 hn)` is equivalent to `x ↦ ‖ι x‖`;
  `exists_norm_eq_rpow`: `‖ι x‖ = |x|_v ^ c` for some `c > 0`.
* `CmGlobalization.exists_ringEquiv_of_norm_eq_rpow`: uniqueness of completions — two dense
  embeddings into complete normed fields with `‖f₂ x‖ = ‖f₁ x‖ ^ c` give a ring isomorphism
  (and homeomorphism) of the targets compatible with the embeddings.
* `CmGlobalization.exists_adicCompletion_ringEquiv`: if moreover `ι` has dense image and `L` is
  complete, then `(place ι hn0 hn).adicCompletion F ≃+* L`, a homeomorphism extending `ι`.
* `CmGlobalization.place_eq_iff`: two such places agree iff `‖ι₁ a‖ < 1 ↔ ‖ι₂ a‖ < 1` on `𝓞 F`;
  `exists_ringEquiv_of_place_eq`: two dense embeddings into a complete `L` defining the same
  place differ by a continuous automorphism of `L`.

## Implementation

`a ∈ 𝓞 F` gives `‖ι a‖ ≤ 1` (`norm_le_one_of_isIntegral`); the comparison with the `v`-adic
absolute value uses `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq` (every `x ∈ F` is
`n / d` or `d / n` with `d ∉ v`) and `AbsoluteValue.isEquiv_iff_exists_rpow_eq`. Uniqueness of
completions is `AbstractCompletion.compareEquiv`, applied to the uniform structure on `F` pulled
back along either embedding (they agree since `‖f₂ x‖ = ‖f₁ x‖ ^ c`).
-/

open Filter Topology Uniformity NumberField IsDedekindDomain

namespace CmGlobalization

section Integral

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-- In an ultrametric normed field, elements integral over `ℤ` have norm `≤ 1`. -/
theorem norm_le_one_of_isIntegral {y : L} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨f, hm, hf⟩ := hy
  by_contra! hlt
  have hn : f.natDegree ≠ 0 := fun hn ↦ by
    simp [hm.natDegree_eq_zero.1 hn] at hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun (‖·‖) at hf
  rw [norm_neg, norm_pow] at hf
  refine (hf.symm.trans_lt ?_).false
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ‖y‖ ^ (f.natDegree - 1))
    (by positivity) fun i hi ↦ ?_).trans_lt
    (pow_lt_pow_right₀ hlt (Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos))
  rw [norm_mul, norm_pow]
  refine (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_intCast_le_one _ _)).trans
    (pow_le_pow_right₀ hlt.le (by grind))
end Integral

section Place

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [NumberField F] in
/-- Integers of `F` have norm `≤ 1` under any embedding into an ultrametric normed field. -/
theorem norm_le_one_of_ringOfIntegers (ι : F →+* L) (a : 𝓞 F) : ‖ι a‖ ≤ 1 :=
  norm_le_one_of_isIntegral ((a.isIntegral_coe).map ι.toIntAlgHom)

/-- The prime ideal `{a ∈ 𝓞 F | ‖ι a‖ < 1}` of `𝓞 F`. -/
def placeIdeal (ι : F →+* L) : Ideal (𝓞 F) where
  carrier := {a | ‖ι a‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_ringOfIntegers ι c)).trans_lt ha

omit [NumberField F] in
theorem mem_placeIdeal {ι : F →+* L} {a : 𝓞 F} : a ∈ placeIdeal ι ↔ ‖ι a‖ < 1 := Iff.rfl

omit [NumberField F] in
theorem placeIdeal_isPrime (ι : F →+* L) : (placeIdeal ι).IsPrime := by
  refine ⟨?_, fun {a b} hab ↦ ?_⟩
  · rw [Ideal.ne_top_iff_one]
    simp [mem_placeIdeal]
  · simp only [mem_placeIdeal, map_mul, norm_mul] at hab ⊢
    by_contra! h
    exact hab.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)

/-- The finite place of `F` defined by `x ↦ ‖ι x‖`, as a height-one prime of `𝓞 F`. Here `n`
is a nonzero natural number with `‖(n : L)‖ < 1`, which makes the place nontrivial. -/
def place (ι : F →+* L) {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1) :
    HeightOneSpectrum (𝓞 F) where
  asIdeal := placeIdeal ι
  isPrime := placeIdeal_isPrime ι
  ne_bot := by
    rw [Submodule.ne_bot_iff]
    exact ⟨n, by simpa [mem_placeIdeal] using hn, by exact_mod_cast hn0⟩

end Place

section Equiv

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
private theorem aux (v : HeightOneSpectrum (𝓞 F)) (f : AbsoluteValue F ℝ)
    (h1 : ∀ r : 𝓞 F, f (algebraMap (𝓞 F) F r) ≤ 1)
    (h2 : ∀ r : 𝓞 F, f (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal) (x : F) (n : 𝓞 F)
    (d : v.asIdeal.primeCompl) :
    (x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n → (f x < 1 ↔ n ∈ v.asIdeal)) ∧
      (x * algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F d → ¬ f x < 1) := by
  have hd : f (algebraMap (𝓞 F) F d) = 1 :=
    (h1 d).antisymm (not_lt.1 fun h ↦ d.2 ((h2 d).1 h))
  refine ⟨fun h ↦ ?_, fun h hx ↦ ?_⟩
  · rw [← h2, ← h, map_mul, hd, mul_one]
  · have := congrArg f h
    rw [map_mul, hd] at this
    exact (this.symm.trans_le (mul_le_of_le_one_right (f.nonneg _) (h1 n))).not_gt hx

/-- Two absolute values on a number field which are `≤ 1` on `𝓞 F` and `< 1` exactly on the
same height-one prime are equivalent. -/
theorem isEquiv_of_forall_lt_one_iff (v : HeightOneSpectrum (𝓞 F)) {f g : AbsoluteValue F ℝ}
    (hf1 : ∀ r : 𝓞 F, f (algebraMap (𝓞 F) F r) ≤ 1)
    (hf2 : ∀ r : 𝓞 F, f (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal)
    (hg1 : ∀ r : 𝓞 F, g (algebraMap (𝓞 F) F r) ≤ 1)
    (hg2 : ∀ r : 𝓞 F, g (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal) : f.IsEquiv g := by
  refine AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x ↦ ?_
  obtain ⟨n, d, h | h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := F) x
  · rw [(aux v f hf1 hf2 x n d).1 h, (aux v g hg1 hg2 x n d).1 h]
  · exact iff_of_false ((aux v f hf1 hf2 x n d).2 h) ((aux v g hg1 hg2 x n d).2 h)

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-- The absolute value `x ↦ ‖ι x‖` on `F`. -/
def normAbv (ι : F →+* L) : AbsoluteValue F ℝ where
  toFun x := ‖ι x‖
  map_mul' x y := by simp
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using norm_add_le _ _

omit [NumberField F] [IsUltrametricDist L] in
@[simp] theorem normAbv_apply (ι : F →+* L) (x : F) : normAbv ι x = ‖ι x‖ := rfl

/-- **The finite place defined by `ι`.** The absolute value of the finite place
`FinitePlace.mk (place ι hn0 hn)` is equivalent to `x ↦ ‖ι x‖`. -/
theorem isEquiv_place (ι : F →+* L) {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1) :
    (FinitePlace.mk (place ι hn0 hn)).val.IsEquiv (normAbv ι) := by
  refine isEquiv_of_forall_lt_one_iff (place ι hn0 hn) (fun r ↦ ?_) (fun r ↦ ?_)
    (fun r ↦ norm_le_one_of_ringOfIntegers ι r) (fun r ↦ Iff.rfl)
  · exact FinitePlace.norm_le_one (K := F) (v := place ι hn0 hn) r
  · exact FinitePlace.norm_lt_one_iff_mem (K := F) (v := place ι hn0 hn) r

/-- `‖ι x‖ = |x|_v ^ c` for the finite place `v = place ι hn0 hn` and some `c > 0`. -/
theorem exists_norm_eq_rpow (ι : F →+* L) {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : F, ‖ι x‖ = FinitePlace.mk (place ι hn0 hn) x ^ c := by
  obtain ⟨c, hc, h⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (isEquiv_place ι hn0 hn)
  exact ⟨c, hc, fun x ↦ (congrFun h x).symm⟩

end Equiv

section Completion

variable {F K₁ K₂ : Type*} [Field F] [NormedField K₁] [NormedField K₂] [CompleteSpace K₁]
  [CompleteSpace K₂]

omit [CompleteSpace K₁] [CompleteSpace K₂] in
/-- Two embeddings with `‖f₂ x‖ = ‖f₁ x‖ ^ c` induce the same uniform structure on `F`. -/
theorem comap_uniformity_eq_of_norm_eq_rpow (f₁ : F →+* K₁) (f₂ : F →+* K₂) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, ‖f₂ x‖ = ‖f₁ x‖ ^ c) :
    comap (Prod.map f₂ f₂) (𝓤 K₂) = comap (Prod.map f₁ f₁) (𝓤 K₁) := by
  have key : ∀ x y : F, dist (f₂ x) (f₂ y) = dist (f₁ x) (f₁ y) ^ c := fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, h]
  refine (Metric.uniformity_basis_dist.comap _).ext (Metric.uniformity_basis_dist.comap _)
    (fun ε hε ↦ ⟨ε ^ c⁻¹, by positivity, fun ⟨x, y⟩ hxy ↦ ?_⟩)
    (fun ε hε ↦ ⟨ε ^ c, by positivity, fun ⟨x, y⟩ hxy ↦ ?_⟩)
  · simp only [Set.mem_preimage, Prod.map_apply, Set.mem_setOf_eq] at hxy ⊢
    rw [key]
    calc dist (f₁ x) (f₁ y) ^ c < (ε ^ c⁻¹) ^ c :=
          Real.rpow_lt_rpow dist_nonneg hxy hc
      _ = ε := by rw [← Real.rpow_mul hε.le, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  · simp only [Set.mem_preimage, Prod.map_apply, Set.mem_setOf_eq, key] at hxy ⊢
    exact (Real.rpow_lt_rpow_iff dist_nonneg hε.le hc).1 hxy

/-- **Uniqueness of completions.** Let `f₁ : F → K₁`, `f₂ : F → K₂` be field embeddings with
dense image into complete normed fields with `‖f₂ x‖ = ‖f₁ x‖ ^ c` (`c > 0`). Then there is a
ring isomorphism `K₁ ≃+* K₂`, a homeomorphism, with `e ∘ f₁ = f₂`. -/
theorem exists_ringEquiv_of_norm_eq_rpow (f₁ : F →+* K₁) (f₂ : F →+* K₂) (h₁ : DenseRange f₁)
    (h₂ : DenseRange f₂) {c : ℝ} (hc : 0 < c) (h : ∀ x, ‖f₂ x‖ = ‖f₁ x‖ ^ c) :
    ∃ e : K₁ ≃+* K₂, Continuous e ∧ Continuous e.symm ∧ ∀ x, e (f₁ x) = f₂ x := by
  letI : UniformSpace F := .comap f₁ inferInstance
  let pkg₁ : AbstractCompletion F :=
    ⟨K₁, f₁, inferInstance, inferInstance, inferInstance, ⟨rfl⟩, h₁⟩
  let pkg₂ : AbstractCompletion F :=
    ⟨K₂, f₂, inferInstance, inferInstance, inferInstance,
      ⟨(comap_uniformity_eq_of_norm_eq_rpow f₁ f₂ hc h).trans rfl⟩, h₂⟩
  let e₀ : K₁ ≃ᵤ K₂ := pkg₁.compareEquiv pkg₂
  have he₀ : ∀ x, e₀ (f₁ x) = f₂ x := pkg₁.compare_coe pkg₂
  have hcont := e₀.continuous
  let e : K₁ ≃+* K₂ :=
    { e₀.toEquiv with
      map_mul' := fun a b ↦ by
        refine h₁.induction_on₂ (p := fun a b ↦ e₀ (a * b) = e₀ a * e₀ b)
          (isClosed_eq (hcont.comp continuous_mul)
            ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd))) (fun x y ↦ ?_) a b
        simp only [← map_mul, he₀]
      map_add' := fun a b ↦ by
        refine h₁.induction_on₂ (p := fun a b ↦ e₀ (a + b) = e₀ a + e₀ b)
          (isClosed_eq (hcont.comp continuous_add)
            ((hcont.comp continuous_fst).add (hcont.comp continuous_snd))) (fun x y ↦ ?_) a b
        simp only [← map_add, he₀] }
  exact ⟨e, hcont, e₀.symm.continuous, he₀⟩

end Completion

section AdicCompletion

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem mem_place_asIdeal {ι : F →+* L} {n : ℕ} {hn0 : n ≠ 0} {hn : ‖(n : L)‖ < 1} {a : 𝓞 F} :
    a ∈ (place ι hn0 hn).asIdeal ↔ ‖ι a‖ < 1 := Iff.rfl

/-- **The completion of `F` at `place ι` is `L`**: if `ι` has dense image and `L` is complete,
then `(place ι hn0 hn).adicCompletion F` and `L` are isomorphic as topological fields, by an
isomorphism extending `ι`. -/
theorem exists_adicCompletion_ringEquiv [CompleteSpace L] (ι : F →+* L) (hd : DenseRange ι)
    {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1) :
    ∃ e : (place ι hn0 hn).adicCompletion F ≃+* L, Continuous e ∧ Continuous e.symm ∧
      ∀ x : F, e (algebraMap F _ x) = ι x := by
  obtain ⟨c, hc, h⟩ := exists_norm_eq_rpow ι hn0 hn
  exact exists_ringEquiv_of_norm_eq_rpow (algebraMap F _) ι
    (HeightOneSpectrum.denseRange_algebraMap _ _) hd hc h

theorem place_eq_iff {ι₁ ι₂ : F →+* L} {n : ℕ} {hn0 : n ≠ 0} {hn₁ : ‖(n : L)‖ < 1}
    {hn₂ : ‖(n : L)‖ < 1} :
    place ι₁ hn0 hn₁ = place ι₂ hn0 hn₂ ↔ ∀ a : 𝓞 F, ‖ι₁ a‖ < 1 ↔ ‖ι₂ a‖ < 1 := by
  rw [HeightOneSpectrum.ext_iff, Ideal.ext_iff]
  rfl

/-- If two dense embeddings `ι₁ ι₂ : F → L` into a complete field define the same place, then
they differ by a continuous automorphism of `L`. -/
theorem exists_ringEquiv_of_place_eq [CompleteSpace L] {ι₁ ι₂ : F →+* L} (hd₁ : DenseRange ι₁)
    (hd₂ : DenseRange ι₂) {n : ℕ} (hn0 : n ≠ 0) (hn : ‖(n : L)‖ < 1)
    (heq : place ι₁ hn0 hn = place ι₂ hn0 hn) :
    ∃ τ : L ≃+* L, Continuous τ ∧ Continuous τ.symm ∧ ∀ x : F, τ (ι₁ x) = ι₂ x := by
  have h := isEquiv_of_forall_lt_one_iff (place ι₁ hn0 hn) (f := normAbv ι₁) (g := normAbv ι₂)
    (fun r ↦ norm_le_one_of_ringOfIntegers ι₁ r) (fun r ↦ Iff.rfl)
    (fun r ↦ norm_le_one_of_ringOfIntegers ι₂ r) (fun r ↦ ((place_eq_iff.1 heq) r).symm)
  obtain ⟨c, hc, h⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  exact exists_ringEquiv_of_norm_eq_rpow ι₁ ι₂ hd₁ hd₂ hc fun x ↦ (congrFun h x).symm

end AdicCompletion

end CmGlobalization
