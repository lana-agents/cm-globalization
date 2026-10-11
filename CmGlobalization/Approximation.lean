/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.RootNearby
import CmGlobalization.Generator

/-!
# Approximation step: a totally real global generator

Let `L/ℚ_p` be a finite extension, `n = [L : ℚ_p]`, equipped with a norm making it a normed
`ℚ_p`-algebra. We find `β ∈ L` and `c : Fin n → ℚ` such that

* `β` generates `L` over `ℚ_p`;
* `β` is a root of the rational polynomial `G = monicOf c`;
* `G` has `n` distinct real roots.

The construction: take a primitive element `α` with minimal polynomial `f = monicOf a`. By
`eventually_exists_root` every `c` close to `a` gives a polynomial with a root near `α`, hence
(since primitive elements form an open set) a root which is a primitive element. With
`h = ∏_{k=1}^n (X - k)`, we take `G = (1 - t) monicOf c₀ + t h`, where `c₀` is a rational
approximation of `a` and `t = p^N j / (1 + p^N j)` is `p`-adically small and real close to `1`
(weak approximation for the two places `p, ∞` of `ℚ`, done by hand). By `eventually_exists_root`
over `ℝ`, applied at each simple root `k` of `h`, `G` has a real root within `1/2` of each `k`.

We also show (Hensel) that `1 - 8p` is a square in `ℚ_p`.
-/

open Polynomial Filter Topology Module IntermediateField

namespace CmGlobalization

/-- `aeval` of `monicOf` commutes with extending the coefficients along a scalar tower. -/
theorem aeval_monicOf_algebraMap {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] {n : ℕ} (c : Fin n → R)
    (y : A) : aeval y (monicOf (fun i ↦ algebraMap R S (c i))) = aeval y (monicOf c) := by
  rw [← map_monicOf, aeval_map_algebraMap]

/-! ### The auxiliary totally split polynomial `h = ∏_{k=1}^n (X - k)` -/

/-- `∏_{k=1}^n (X - k)`. -/
noncomputable def splitPoly (n : ℕ) : ℚ[X] := ∏ k : Fin n, (X - C ((k : ℚ) + 1))

theorem splitPoly_monic (n : ℕ) : (splitPoly n).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem natDegree_splitPoly (n : ℕ) : (splitPoly n).natDegree = n := by
  rw [splitPoly, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem aeval_splitPoly_eq_zero (n : ℕ) (k : Fin n) :
    aeval ((k : ℝ) + 1) (splitPoly n) = 0 := by
  rw [splitPoly, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

theorem aeval_derivative_splitPoly_ne_zero (n : ℕ) (k : Fin n) :
    aeval ((k : ℝ) + 1) (derivative (splitPoly n)) ≠ 0 := by
  have hsep : (splitPoly n).Separable := by
    refine separable_prod_X_sub_C_iff.2 fun k l hkl ↦ ?_
    exact Fin.ext (by exact_mod_cast add_right_cancel hkl)
  exact hsep.aeval_derivative_ne_zero (aeval_splitPoly_eq_zero n k)

/-! ### The weak-approximation sequence -/

/-- `t_j = p^N j / (1 + p^N j)`: `p`-adically small, real close to `1` for `j` large. -/
noncomputable def approxSeq (p N j : ℕ) : ℚ := (p : ℚ) ^ N * j / (1 + (p : ℚ) ^ N * j)

theorem tendsto_approxSeq (p N : ℕ) (hp : 0 < p) :
    Tendsto (fun j ↦ (approxSeq p N j : ℝ)) atTop (𝓝 1) := by
  have hpos : ∀ j : ℕ, (0 : ℝ) < 1 + (p : ℝ) ^ N * j := fun j ↦ by positivity
  have heq : (fun j : ℕ ↦ (approxSeq p N j : ℝ)) =
      fun j : ℕ ↦ 1 - (1 + (p : ℝ) ^ N * j)⁻¹ := by
    funext j
    have := (hpos j).ne'
    simp only [approxSeq]
    push_cast
    field_simp
    ring
  rw [heq]
  have h1 : Tendsto (fun j : ℕ ↦ 1 + (p : ℝ) ^ N * j) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp h1)

theorem norm_approxSeq_le (p : ℕ) [Fact p.Prime] (N j : ℕ) (hN : 0 < N) :
    ‖((approxSeq p N j : ℚ) : ℚ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ N := by
  have hnum : ‖(p : ℚ_[p]) ^ N * j‖ ≤ ‖(p : ℚ_[p])‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (by exact_mod_cast Padic.norm_int_le_one j)
  have hlt : ‖(p : ℚ_[p]) ^ N * j‖ < 1 :=
    hnum.trans_lt (pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one hN.ne')
  have hden : ‖(1 : ℚ_[p]) + (p : ℚ_[p]) ^ N * j‖ = 1 := by
    rw [Padic.add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne'), norm_one]
    exact max_eq_left hlt.le
  simp only [approxSeq]
  push_cast
  rw [norm_div, hden, div_one]
  exact hnum

/-! ### Hensel: `1 - 8p` is a square in `ℚ_p` -/

theorem exists_sq_eq_one_sub_eight_mul (p : ℕ) [Fact p.Prime] :
    ∃ s : ℚ_[p], s ^ 2 = 1 - 8 * p := by
  set F : ℤ[X] := X ^ 2 - C (1 - 8 * (p : ℤ))
  have hF : aeval (1 : ℤ_[p]) F = 8 * p := by simp [F, map_ofNat]
  have hF' : aeval (1 : ℤ_[p]) (derivative F) = 2 := by simp [F, map_ofNat]
  have h2 : ‖(2 : ℤ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 two_ne_zero
  have hnorm : ‖aeval (1 : ℤ_[p]) F‖ < ‖aeval (1 : ℤ_[p]) (derivative F)‖ ^ 2 := by
    rw [hF, hF', show (8 : ℤ_[p]) * p = 2 ^ 2 * (2 * p) by ring, norm_mul, norm_pow]
    have h2p : ‖(2 : ℤ_[p]) * p‖ < 1 := by
      rw [norm_mul]
      calc ‖(2 : ℤ_[p])‖ * ‖(p : ℤ_[p])‖ ≤ 1 * ‖(p : ℤ_[p])‖ :=
            mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
        _ < 1 := by
          rw [one_mul, PadicInt.norm_p]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    calc ‖(2 : ℤ_[p])‖ ^ 2 * ‖(2 : ℤ_[p]) * p‖ < ‖(2 : ℤ_[p])‖ ^ 2 * 1 :=
          mul_lt_mul_of_pos_left h2p (by positivity)
      _ = _ := mul_one _
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have : (z : ℚ_[p]) ^ 2 - (1 - 8 * p) = 0 := by
    have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz
    simp [F, map_ofNat] at this
    exact_mod_cast this
  linear_combination this

/-! ### The main approximation statement -/

/-- **Approximation step.** There is a primitive element `β` of `L/ℚ_p` which is a root of a
monic rational polynomial `monicOf c` of degree `[L : ℚ_p]` having `[L : ℚ_p]` distinct real
roots. -/
theorem exists_generator_root_real (p : ℕ) [Fact p.Prime] (L : Type*) [NontriviallyNormedField L]
    [CharZero L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    ∃ (β : L) (c : Fin (finrank ℚ_[p] L) → ℚ), ℚ_[p]⟮β⟯ = ⊤ ∧ aeval β (monicOf c) = 0 ∧
      ∃ s : Finset ℝ, s.card = finrank ℚ_[p] L ∧ ∀ r ∈ s, aeval r (monicOf c) = 0 := by
  have : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  have : IsScalarTower ℚ ℚ_[p] L := IsScalarTower.of_algebraMap_eq fun q ↦ by
    rw [eq_ratCast (algebraMap ℚ L), eq_ratCast (algebraMap ℚ ℚ_[p]), map_ratCast]
  set n := finrank ℚ_[p] L
  -- a primitive element and its minimal polynomial
  obtain ⟨α, hαgen⟩ := Field.exists_primitive_element ℚ_[p] L
  have hint : IsIntegral ℚ_[p] α := .of_finite _ _
  set f := minpoly ℚ_[p] α
  have hdeg : f.natDegree = n := by
    rw [← adjoin.finrank hint, hαgen, finrank_top']
  set a : Fin n → ℚ_[p] := fun i ↦ f.coeff i
  have hfa : f = monicOf a := Monic.eq_monicOf (minpoly.monic hint) hdeg
  have hα : aeval α (monicOf a) = 0 := hfa ▸ minpoly.aeval _ _
  have hα' : aeval α (derivative (monicOf a)) ≠ 0 :=
    hfa ▸ (minpoly.irreducible hint).separable.aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- p-adic neighbourhood of `a` all of whose members have a primitive root
  set U : Set L := {y | ℚ_[p]⟮y⟯ = ⊤}
  have hU : U ∈ 𝓝 α := isOpen_setOf_adjoin_simple_eq_top.mem_nhds hαgen
  have hW := eventually_exists_root a hα hα' hU
  -- the totally split polynomial
  set ch : Fin n → ℚ := fun i ↦ (splitPoly n).coeff i
  have hch : splitPoly n = monicOf ch := Monic.eq_monicOf (splitPoly_monic n) (natDegree_splitPoly n)
  set castP : (Fin n → ℚ) → (Fin n → ℚ_[p]) := fun c i ↦ algebraMap ℚ ℚ_[p] (c i)
  set castR : (Fin n → ℚ) → (Fin n → ℝ) := fun c i ↦ algebraMap ℚ ℝ (c i)
  set Φ : ℚ_[p] × (Fin n → ℚ_[p]) → (Fin n → ℚ_[p]) := fun x ↦ (1 - x.1) • x.2 + x.1 • castP ch
  have hΦ : Continuous Φ := by fun_prop
  have hΦ0 : Φ (0, a) = a := by simp [Φ]
  have hpre : Φ ⁻¹' {c | ∃ y ∈ U, aeval y (monicOf c) = 0} ∈ 𝓝 ((0 : ℚ_[p]), a) :=
    hΦ.continuousAt.preimage_mem_nhds (by rw [hΦ0]; exact hW)
  obtain ⟨T0, hT0, W', hW', hTW⟩ := mem_nhds_prod_iff.1 hpre
  -- a rational approximation `c₀` of `a`
  have hdense : DenseRange castP := by
    have h1 : DenseRange (fun q : ℚ ↦ algebraMap ℚ ℚ_[p] q) := by
      rw [show (fun q : ℚ ↦ algebraMap ℚ ℚ_[p] q) = ((↑) : ℚ → ℚ_[p]) from
        funext fun q ↦ eq_ratCast _ q]
      exact Padic.denseRange_ratCast p
    exact DenseRange.piMap fun _ ↦ h1
  obtain ⟨_, hc0W, c0, rfl⟩ := mem_closure_iff_nhds.1 (hdense a) W' hW'
  -- `p`-adic smallness of the weak-approximation parameter
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.1 hT0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := p))
  have hsmall : ∀ j, ((approxSeq p (N + 1) j : ℚ) : ℚ_[p]) ∈ T0 := fun j ↦ by
    refine hεT ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc _ ≤ ‖(p : ℚ_[p])‖ ^ (N + 1) := norm_approxSeq_le p (N + 1) j N.succ_pos
      _ ≤ ‖(p : ℚ_[p])‖ ^ N :=
          pow_le_pow_of_le_one (norm_nonneg _) Padic.norm_p_lt_one.le N.le_succ
      _ < ε := hN
  -- real side: near `h`, every monic polynomial has a root near each `k + 1`
  have hreal : ∀ᶠ c in 𝓝 (castR ch), ∀ k : Fin n,
      ∃ y ∈ Metric.ball ((k : ℝ) + 1) (1 / 2), aeval y (monicOf c) = 0 := by
    refine eventually_all.2 fun k ↦ eventually_exists_root (castR ch) ?_ ?_
      (Metric.ball_mem_nhds _ (by norm_num))
    · rw [aeval_monicOf_algebraMap, ← hch]
      exact aeval_splitPoly_eq_zero n k
    · rw [← map_monicOf, derivative_map, aeval_map_algebraMap, ← hch]
      exact aeval_derivative_splitPoly_ne_zero n k
  set ρ : ℝ → (Fin n → ℝ) := fun t ↦ (1 - t) • castR c0 + t • castR ch
  have hρ : Tendsto ρ (𝓝 1) (𝓝 (castR ch)) := by
    have : Continuous ρ := by fun_prop
    simpa [ρ] using this.tendsto 1
  obtain ⟨j, hj⟩ := ((tendsto_approxSeq p (N + 1) (Fact.out : p.Prime).pos).eventually
    (hρ.eventually hreal)).exists
  -- the polynomial `G = monicOf c`
  set t : ℚ := approxSeq p (N + 1) j
  set c : Fin n → ℚ := (1 - t) • c0 + t • ch
  have hcP : castP c = Φ ((t : ℚ_[p]), castP c0) := by
    funext i; simp [castP, c, Φ]
  have hcR : castR c = ρ t := by
    funext i; simp [castR, c, ρ]
  obtain ⟨β, hβU, hβ⟩ : ∃ y ∈ U, aeval y (monicOf (castP c)) = 0 := by
    rw [hcP]; exact hTW ⟨hsmall j, hc0W⟩
  rw [aeval_monicOf_algebraMap] at hβ
  refine ⟨β, c, hβU, hβ, ?_⟩
  rw [← hcR] at hj
  choose y hyball hyroot using hj
  have hyinj : Function.Injective y := by
    intro k l hkl
    have hk := hyball k
    have hl := hyball l
    rw [hkl, Metric.mem_ball, Real.dist_eq] at hk
    rw [Metric.mem_ball, Real.dist_eq] at hl
    have : |((k : ℝ) + 1) - ((l : ℝ) + 1)| < 1 := by
      have h3 := abs_sub_le ((k : ℝ) + 1) (y l) ((l : ℝ) + 1)
      have h4 : |(k : ℝ) + 1 - y l| = |y l - ((k : ℝ) + 1)| := abs_sub_comm _ _
      linarith
    have : |(k : ℤ) - (l : ℤ)| < 1 := by
      have h' : |((k : ℤ) : ℝ) - ((l : ℤ) : ℝ)| < 1 := by push_cast; simpa using this
      exact_mod_cast h'
    have := abs_lt.1 this
    exact Fin.ext (by omega)
  refine ⟨Finset.univ.image y, by rw [Finset.card_image_of_injective _ hyinj]; simp [n], ?_⟩
  intro r hr
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr
  have := hyroot k
  rwa [aeval_monicOf_algebraMap] at this

end CmGlobalization
