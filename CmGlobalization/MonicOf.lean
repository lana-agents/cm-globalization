/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Monic polynomials with prescribed lower coefficients

For `c : Fin n → R` we write `monicOf c = X ^ n + ∑ i, C (c i) * X ^ i`, the monic polynomial
of degree `n` whose coefficients below the leading one are given by `c`. This parametrises
monic polynomials of degree `n` by the affine space `R ^ n`, which is how we talk about
"nearby polynomials".
-/

open Polynomial

namespace CmGlobalization

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The monic polynomial `X ^ n + ∑ i, c i * X ^ i` of degree `n`. -/
noncomputable def monicOf (c : Fin n → R) : R[X] :=
  X ^ n + ∑ i, C (c i) * X ^ (i : ℕ)

theorem degree_sum_lt (c : Fin n → R) : (∑ i, C (c i) * X ^ (i : ℕ)).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i _ ↦ ?_
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 i.2)

theorem monicOf_monic [Nontrivial R] (c : Fin n → R) : (monicOf c).Monic :=
  monic_X_pow_add (degree_sum_lt c)

theorem natDegree_monicOf [Nontrivial R] (c : Fin n → R) : (monicOf c).natDegree = n := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt] <;> simp [degree_sum_lt c]

theorem aeval_monicOf {A : Type*} [CommRing A] [Algebra R A] (c : Fin n → R) (y : A) :
    aeval y (monicOf c) = y ^ n + ∑ i, c i • y ^ (i : ℕ) := by
  simp [monicOf, Algebra.smul_def]

theorem map_monicOf {S : Type*} [CommRing S] (φ : R →+* S) (c : Fin n → R) :
    (monicOf c).map φ = monicOf (fun i ↦ φ (c i)) := by
  simp [monicOf, Polynomial.map_sum]

theorem coeff_monicOf [Nontrivial R] (c : Fin n → R) (i : Fin n) :
    (monicOf c).coeff i = c i := by
  rw [monicOf, coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ if_neg (by exact_mod_cast (Fin.val_ne_of_ne hj).symm))
    (by simp)]
  simp

/-- Every monic polynomial of degree `n` is `monicOf` of its lower coefficients. -/
theorem Monic.eq_monicOf {f : R[X]} (hf : f.Monic) (hn : f.natDegree = n) :
    f = monicOf (fun i : Fin n ↦ f.coeff i) := by
  conv_lhs => rw [hf.as_sum, hn]
  rw [monicOf, add_comm, Fin.sum_univ_eq_sum_range (fun i ↦ C (f.coeff i) * X ^ i)]
  rw [add_comm]

end CmGlobalization
