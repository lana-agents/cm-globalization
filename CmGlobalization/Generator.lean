/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Primitive elements form an open set; dense subfields

For a finite extension `L/K`, an element `y : L` generates `L` over `K` (i.e. `K⟮y⟯ = ⊤`) iff
`1, y, …, y ^ (n - 1)` are `K`-linearly independent, where `n = [L : K]`. When `K` is a
complete normed field and `L` a normed `K`-algebra, linear independence of finitely many
vectors is an open condition, so the primitive elements of `L/K` form an open set. This is what
replaces Krasner's lemma in the globalization argument.

We also show that a `ℚ`-subalgebra of a finite extension `L/ℚ_p` which contains a primitive
element of `L/ℚ_p` is dense in `L` (for the canonical module topology), since `ℚ` is dense in
`ℚ_p`.
-/

open Module IntermediateField Polynomial

namespace CmGlobalization

section Algebraic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `y` generates `L/K` iff its first `[L : K]` powers are linearly independent. -/
theorem adjoin_simple_eq_top_iff_linearIndependent {y : L} :
    K⟮y⟯ = ⊤ ↔ LinearIndependent K (fun i : Fin (finrank K L) ↦ y ^ (i : ℕ)) := by
  constructor
  · intro h
    have hint : IsIntegral K y := .of_finite K y
    have hdeg : (minpoly K y).natDegree = finrank K L := by
      rw [← adjoin.finrank hint, h, finrank_top']
    have := linearIndependent_pow (K := K) y
    rw [hdeg] at this
    exact this
  · intro h
    have hspan := h.span_eq_top_of_card_eq_finrank' (by simp)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span K (Set.range fun i : Fin (finrank K L) ↦ y ^ (i : ℕ)) := by
      rw [hspan]; trivial
    refine (Submodule.span_le (p := (K⟮y⟯).toSubalgebra.toSubmodule)).2 ?_ hx
    rintro _ ⟨i, rfl⟩
    exact pow_mem (mem_adjoin_simple_self K y) _

end Algebraic

section Normed

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L]

/-- The primitive elements of a finite extension of a complete normed field form an open set. -/
theorem isOpen_setOf_adjoin_simple_eq_top : IsOpen {y : L | K⟮y⟯ = ⊤} := by
  simp_rw [adjoin_simple_eq_top_iff_linearIndependent]
  exact isOpen_setOf_linearIndependent.preimage (continuous_pi fun i ↦ continuous_pow _)

end Normed

section Dense

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharZero L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [TopologicalSpace L] [IsModuleTopology ℚ_[p] L]

/-- A `ℚ`-subalgebra of `L` containing a primitive element of `L/ℚ_p` is dense in `L`. -/
theorem dense_of_mem_of_adjoin_eq_top (S : Subalgebra ℚ L) {β : L} (hβ : β ∈ S)
    (hgen : ℚ_[p]⟮β⟯ = ⊤) : Dense (S : Set L) := by
  have := IsModuleTopology.toContinuousAdd ℚ_[p] L
  have hli := adjoin_simple_eq_top_iff_linearIndependent.1 hgen
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)
  let φ : (Fin (finrank ℚ_[p] L) → ℚ_[p]) →ₗ[ℚ_[p]] L := b.equivFun.symm.toLinearMap
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hsurj : Function.Surjective φ := b.equivFun.symm.surjective
  have hdense : DenseRange (φ ∘ Pi.map fun _ (q : ℚ) ↦ (q : ℚ_[p])) :=
    hsurj.denseRange.comp (DenseRange.piMap fun _ ↦ Padic.denseRange_ratCast p) hφ
  refine hdense.mono ?_
  rintro _ ⟨c, rfl⟩
  simp only [Function.comp_apply, φ, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, Pi.map_apply]
  refine Subalgebra.sum_mem _ fun i _ ↦ ?_
  have : ((c i : ℚ_[p]) • b i) = c i • β ^ (i : ℕ) := by
    rw [show b i = β ^ (i : ℕ) by simp [b], Algebra.smul_def, map_ratCast, Rat.smul_def]
  rw [this]
  exact Subalgebra.smul_mem _ (pow_mem hβ _) _

end Dense

end CmGlobalization
