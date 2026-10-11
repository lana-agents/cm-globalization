/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Totally real and totally complex criteria

* `exists_real_eq_of_aeval_eq_zero`: if a rational polynomial of degree `n` has `n` distinct
  real roots, then all of its complex roots are real.
* `isTotallyReal_adjoin_simple`: if all complex roots of the minimal polynomial of `x` over `ℚ`
  are real, then `ℚ⟮x⟯` is totally real.
* `sq_ne_neg_of_isTotallyReal`: in a totally real number field, `x ^ 2 ≠ -d` for `d > 0`.
* `isTotallyComplex_of_sq_eq_neg`: a number field containing a square root of `-d`, `d > 0`, is
  totally complex.
-/

open Polynomial NumberField InfinitePlace IntermediateField

namespace CmGlobalization

/-- A rational polynomial of degree `n` with `n` distinct real roots has only real complex
roots. -/
theorem exists_real_eq_of_aeval_eq_zero {G : ℚ[X]} (hG : G ≠ 0) (s : Finset ℝ)
    (hs : s.card = G.natDegree) (hroot : ∀ r ∈ s, aeval r G = 0) {z : ℂ}
    (hz : aeval z G = 0) : ∃ r ∈ s, (r : ℂ) = z := by
  set Gc := G.map (algebraMap ℚ ℂ) with hGc
  have hGc0 : Gc ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 hG
  set M : Multiset ℂ := s.val.map (fun r : ℝ ↦ (r : ℂ))
  have hMnd : M.Nodup := s.nodup.map Complex.ofReal_injective
  have hMle : M ≤ Gc.roots := by
    refine (Multiset.le_iff_subset hMnd).2 fun w hw ↦ ?_
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hw
    rw [mem_roots hGc0, IsRoot, hGc, eval_map_algebraMap]
    have : aeval ((algebraMap ℝ ℂ) r) G = algebraMap ℝ ℂ (aeval r G) :=
      aeval_algebraMap_apply ℂ r G
    simpa [hroot r hr] using this
  have hMeq : M = Gc.roots := by
    refine Multiset.eq_of_le_of_card_le hMle ?_
    calc Multiset.card Gc.roots ≤ Gc.natDegree := card_roots' Gc
      _ = G.natDegree := natDegree_map _
      _ = Multiset.card M := by simp [M, hs]
  have hzr : z ∈ Gc.roots := by
    rw [mem_roots hGc0, IsRoot, hGc, eval_map_algebraMap]
    exact hz
  rw [← hMeq] at hzr
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hzr
  exact ⟨r, hr, rfl⟩

variable {K : Type*} [Field K] [CharZero K]

/-- A ring homomorphism out of an intermediate field `E` of `K/ℚ`, as a `ℚ`-algebra
homomorphism for the algebra structure `E.algebra'` (which is not syntactically the one coming
from `DivisionRing.toRatAlgebra`). -/
def ringHomToAlgHom {E : IntermediateField ℚ K} (ψ : E →+* ℂ) :
    @AlgHom ℚ E ℂ _ _ _ E.algebra' _ :=
  { ψ with
    commutes' := fun r ↦ by
      exact RingHom.congr_fun (Subsingleton.elim (ψ.comp (algebraMap ℚ E)) (algebraMap ℚ ℂ)) r }

@[simp]
theorem ringHomToAlgHom_apply {E : IntermediateField ℚ K} (ψ : E →+* ℂ) (y : E) : ringHomToAlgHom ψ y = ψ y := rfl

/-- If all complex roots of the minimal polynomial of `x` over `ℚ` are real, then `ℚ⟮x⟯` is
totally real. -/
theorem isTotallyReal_adjoin_simple {x : K}
    (h : ∀ z : ℂ, aeval z (minpoly ℚ x) = 0 → ∃ r : ℝ, (r : ℂ) = z) : IsTotallyReal ℚ⟮x⟯ := by
  constructor
  intro w
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  set φ := w.embedding
  have hroot : aeval (φ (AdjoinSimple.gen ℚ x)) (minpoly ℚ x) = 0 := by
    have := congrArg (ringHomToAlgHom φ) (aeval_gen_minpoly ℚ x)
    rwa [map_zero, ← aeval_algHom_apply, ringHomToAlgHom_apply] at this
  obtain ⟨r, hr⟩ := h _ hroot
  have : ringHomToAlgHom (ComplexEmbedding.conjugate φ) = ringHomToAlgHom φ := by
    refine algHom_ext_of_eq_adjoin ℚ rfl fun y hy ↦ ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [ringHomToAlgHom_apply, ringHomToAlgHom_apply, ComplexEmbedding.conjugate_coe_eq]
    change (starRingEnd ℂ) (φ (AdjoinSimple.gen ℚ y)) = φ (AdjoinSimple.gen ℚ y)
    rw [← hr, Complex.conj_ofReal]
  ext y
  exact congrArg (fun ψ : ℚ⟮x⟯ →ₐ[ℚ] ℂ ↦ ψ y) this

variable [NumberField K]

/-- In a totally real number field, no element squares to a negative rational. -/
theorem sq_ne_neg_of_isTotallyReal [IsTotallyReal K] (x : K) {d : ℚ} (hd : 0 < d) :
    x ^ 2 ≠ -(d : K) := by
  intro hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  set ψ := embedding_of_isReal (IsTotallyReal.isReal w)
  have := congrArg ψ hx
  rw [map_pow, map_neg, map_ratCast] at this
  have h1 := sq_nonneg (ψ x)
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

omit [NumberField K] in
/-- A number field containing a square root of a negative rational is totally complex. -/
theorem isTotallyComplex_of_sq_eq_neg {x : K} {d : ℚ} (hd : 0 < d) (hx : x ^ 2 = -(d : K)) :
    IsTotallyComplex K := by
  constructor
  intro w
  rw [← not_isReal_iff_isComplex]
  intro hw
  set ψ := embedding_of_isReal hw
  have := congrArg ψ hx
  rw [map_pow, map_neg, map_ratCast] at this
  have h1 := sq_nonneg (ψ x)
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

end CmGlobalization
