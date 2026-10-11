/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.RealRoots

/-!
# Building a CM field from a totally real field and `√-d`

Let `L` be a field of characteristic zero, `β ∈ L` algebraic over `ℚ` with `ℚ⟮β⟯` totally real,
and `γ ∈ L` with `γ ^ 2 = -d` for a positive rational `d`. Then the compositum
`cmField β γ = ℚ⟮β⟯ ⊔ ℚ⟮γ⟯ ⊆ L` is a CM number field whose maximal real subfield contains `β`
and is isomorphic to `ℚ⟮β⟯`; moreover `γ` is not fixed by complex conjugation.
-/

open Polynomial NumberField IntermediateField Module

namespace CmGlobalization

variable {L : Type*} [Field L] [CharZero L]

/-- The compositum `ℚ⟮β⟯ ⊔ ℚ⟮γ⟯` inside `L`. -/
noncomputable def cmField (β γ : L) : IntermediateField ℚ L := ℚ⟮β⟯ ⊔ ℚ⟮γ⟯

variable {β γ : L} {d : ℚ}

theorem le_cmField_left : ℚ⟮β⟯ ≤ cmField β γ := le_sup_left

theorem le_cmField_right : ℚ⟮γ⟯ ≤ cmField β γ := le_sup_right

theorem mem_cmField_left : β ∈ cmField β γ := le_cmField_left (mem_adjoin_simple_self ℚ β)

theorem mem_cmField_right : γ ∈ cmField β γ := le_cmField_right (mem_adjoin_simple_self ℚ γ)

/-- `γ` as an element of `cmField β γ`. -/
def gamma' : cmField β γ := ⟨γ, mem_cmField_right⟩

theorem isIntegral_of_sq_eq (hγ : γ ^ 2 = -(d : L)) : IsIntegral ℚ γ := by
  refine ⟨X ^ 2 + C d, ?_, ?_⟩
  · exact monic_X_pow_add_C _ two_ne_zero
  · rw [← aeval_def]
    simp [hγ, eq_ratCast]

theorem finrank_adjoin_le_two (hγ : γ ^ 2 = -(d : L)) : finrank ℚ ℚ⟮γ⟯ ≤ 2 := by
  rw [adjoin.finrank (isIntegral_of_sq_eq hγ)]
  have hq : (X ^ 2 + C d : ℚ[X]) ≠ 0 := (monic_X_pow_add_C d two_ne_zero).ne_zero
  have := natDegree_le_of_dvd (minpoly.dvd ℚ γ (by simp [hγ, eq_ratCast])) hq
  rwa [natDegree_X_pow_add_C] at this

variable (hβ : IsIntegral ℚ β) (hγ : γ ^ 2 = -(d : L))
include hβ hγ

theorem finiteDimensional_cmField : FiniteDimensional ℚ (cmField β γ) := by
  have := adjoin.finiteDimensional hβ
  have := adjoin.finiteDimensional (isIntegral_of_sq_eq hγ)
  exact IntermediateField.finiteDimensional_sup _ _

theorem numberField_cmField : NumberField (cmField β γ) :=
  have := finiteDimensional_cmField hβ hγ
  NumberField.of_module_finite ℚ _

omit hβ in
theorem finrank_cmField_le : finrank ℚ (cmField β γ) ≤ finrank ℚ ℚ⟮β⟯ * 2 :=
  (finrank_sup_le _ _).trans (Nat.mul_le_mul_left _ (finrank_adjoin_le_two hγ))

omit hβ in
theorem isTotallyComplex_cmField (hd : 0 < d) : IsTotallyComplex (cmField β γ) :=
  isTotallyComplex_of_sq_eq_neg (x := (gamma' : cmField β γ)) hd (by ext; simp [gamma', hγ])

/-- `cmField β γ` as an algebra over `ℚ⟮β⟯`. -/
noncomputable abbrev algebraCmField : Algebra ℚ⟮β⟯ (cmField β γ) :=
  (inclusion le_cmField_left).toRingHom.toAlgebra

theorem isQuadraticExtension_cmField [IsTotallyReal ℚ⟮β⟯] (hd : 0 < d) :
    letI := algebraCmField (β := β) (γ := γ)
    Algebra.IsQuadraticExtension ℚ⟮β⟯ (cmField β γ) := by
  letI := algebraCmField (β := β) (γ := γ)
  have := finiteDimensional_cmField hβ hγ
  have := adjoin.finiteDimensional hβ
  have : NumberField ℚ⟮β⟯ := NumberField.of_module_finite ℚ _
  have : IsScalarTower ℚ ℚ⟮β⟯ (cmField β γ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ⟮β⟯ (cmField β γ) := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : Module.Free ℚ⟮β⟯ (cmField β γ) := Module.Free.of_divisionRing _ _
  have htower := Module.finrank_mul_finrank ℚ ℚ⟮β⟯ (cmField β γ)
  have hle := finrank_cmField_le (β := β) hγ
  have hpos : 0 < finrank ℚ ℚ⟮β⟯ := Module.finrank_pos
  have hpos' : 0 < finrank ℚ⟮β⟯ (cmField β γ) := Module.finrank_pos
  have hne : finrank ℚ⟮β⟯ (cmField β γ) ≠ 1 := by
    intro h1
    have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one).2 h1
    have hmem : (gamma' : cmField β γ) ∈ (⊥ : Subalgebra ℚ⟮β⟯ (cmField β γ)) :=
      hbot ▸ Algebra.mem_top
    obtain ⟨e, he⟩ := Algebra.mem_bot.1 hmem
    have he' : (e : L) = γ := congrArg Subtype.val he
    refine sq_ne_neg_of_isTotallyReal e hd ?_
    ext
    simp [he', hγ]
  constructor
  have : finrank ℚ ℚ⟮β⟯ * finrank ℚ⟮β⟯ (cmField β γ) ≤ finrank ℚ ℚ⟮β⟯ * 2 := htower ▸ hle
  have := Nat.le_of_mul_le_mul_left this hpos
  omega

theorem isCMField_cmField [IsTotallyReal ℚ⟮β⟯] (hd : 0 < d) : IsCMField (cmField β γ) := by
  letI := algebraCmField (β := β) (γ := γ)
  have := numberField_cmField hβ hγ
  have := isTotallyComplex_cmField (β := β) hγ hd
  have := isQuadraticExtension_cmField hβ hγ hd
  exact IsCMField.ofCMExtension ℚ⟮β⟯ (cmField β γ)

/-- A ring isomorphism of fields of characteristic zero is `ℚ`-linear (for any `ℚ`-algebra
structures). -/
def ratLinearEquiv {A B : Type*} [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B] (e : A ≃+* B) :
    A ≃ₗ[ℚ] B :=
  { e with
    map_smul' := fun q x ↦ by
      simp only [Algebra.smul_def, eq_ratCast (algebraMap ℚ A), eq_ratCast (algebraMap ℚ B),
        RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul, map_ratCast,
        RingHom.id_apply] }

/-- The maximal real subfield of `cmField β γ` has the same degree as `ℚ⟮β⟯`. -/
theorem finrank_maximalRealSubfield_cmField [IsTotallyReal ℚ⟮β⟯] (hd : 0 < d) :
    finrank ℚ (maximalRealSubfield (cmField β γ)) = finrank ℚ ℚ⟮β⟯ := by
  letI := algebraCmField (β := β) (γ := γ)
  have := numberField_cmField hβ hγ
  have := isTotallyComplex_cmField (β := β) hγ hd
  have := isQuadraticExtension_cmField hβ hγ hd
  exact (LinearEquiv.finrank_eq
    (ratLinearEquiv (CMExtension.equivMaximalRealSubfield ℚ⟮β⟯ (cmField β γ)))).symm

/-- `γ` is not fixed by the complex conjugation of the CM field `cmField β γ`. -/
theorem complexConj_gamma_ne [IsCMField (cmField β γ)] [Algebra.IsIntegral ℚ (cmField β γ)]
    (hd : 0 < d) : IsCMField.complexConj (cmField β γ) gamma' ≠ gamma' := by
  have := numberField_cmField hβ hγ
  intro h
  rw [IsCMField.complexConj_eq_self_iff] at h
  refine sq_ne_neg_of_isTotallyReal (K := maximalRealSubfield (cmField β γ)) ⟨gamma', h⟩ hd ?_
  ext
  simp [gamma', hγ]

omit hβ hγ in
/-- The elements of `ℚ⟮β⟯` lie in the maximal real subfield of `cmField β γ`. -/
theorem mem_maximalRealSubfield_cmField [IsTotallyReal ℚ⟮β⟯] {x : L} (hx : x ∈ ℚ⟮β⟯) :
    (⟨x, le_cmField_left hx⟩ : cmField β γ) ∈ maximalRealSubfield (cmField β γ) := by
  set ι : ℚ⟮β⟯ →+* cmField β γ := (inclusion le_cmField_left).toRingHom
  have : IsTotallyReal ι.fieldRange := IsTotallyReal.ofRingEquiv ι.rangeRestrictFieldEquiv
  exact IsTotallyReal.le_maximalRealSubfield ι.fieldRange ⟨⟨x, hx⟩, rfl⟩

end CmGlobalization
