/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CmGlobalization.MonicOf

/-!
# Roots of nearby polynomials

Let `𝕜` be a complete nontrivially normed field and `L` a complete normed field which is a normed
`𝕜`-algebra. If `α ∈ L` is a simple root of the monic polynomial `monicOf a` (`a : Fin n → 𝕜`),
then every monic polynomial `monicOf c` with `c` close enough to `a` has a root close to `α`.

This is proved with the inverse function theorem
(`HasStrictFDerivAt.map_nhds_eq_of_surj`) applied to the analytic map
`Ψ (c, y) = (c, y ^ n + ∑ i, c i • y ^ i)`, whose derivative at `(a, α)` is surjective because
`∂Ψ₂/∂y` is multiplication by `f'(α) ≠ 0`. It is a substitute for the "continuity of roots"
half of Krasner-type arguments, and works over `ℚ_p` and over `ℝ` alike.
-/

open Polynomial Filter Topology

namespace CmGlobalization

variable {𝕜 L : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField L] [NormedAlgebra 𝕜 L] [CompleteSpace L]

/-- **Roots of nearby polynomials.** If `α` is a simple root of `monicOf a`, then for every
neighbourhood `U` of `α`, every `c` close enough to `a` gives a polynomial `monicOf c` with a
root in `U`. -/
theorem eventually_exists_root {n : ℕ} (a : Fin n → 𝕜) {α : L} (hα : aeval α (monicOf a) = 0)
    (hα' : aeval α (derivative (monicOf a)) ≠ 0) {U : Set L} (hU : U ∈ 𝓝 α) :
    ∀ᶠ c in 𝓝 a, ∃ y ∈ U, aeval y (monicOf c) = 0 := by
  set P : (Fin n → 𝕜) × L → L := fun x ↦ x.2 ^ n + ∑ i, x.1 i • x.2 ^ (i : ℕ) with hPdef
  have hP : ∀ c y, P (c, y) = aeval y (monicOf c) := fun c y ↦ (aeval_monicOf c y).symm
  have hPa : AnalyticAt 𝕜 P (a, α) := by
    refine (analyticAt_snd.pow n).add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
    exact (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst 𝕜 (Fin n → 𝕜) L)).analyticAt _).smul (analyticAt_snd.pow _)
  set D := fderiv 𝕜 P (a, α)
  have hD : HasStrictFDerivAt P D (a, α) := hPa.hasStrictFDerivAt
  set u := aeval α (derivative (monicOf a)) with hu
  have hDy : ∀ dy : L, D (0, dy) = dy * u := by
    have h1 : HasFDerivAt (fun y : L ↦ P (a, y))
        (D.comp (ContinuousLinearMap.inr 𝕜 (Fin n → 𝕜) L)) α :=
      hD.hasFDerivAt.comp α (hasFDerivAt_prodMk_right a α)
    have h2 : HasFDerivAt (fun y : L ↦ P (a, y))
        ((ContinuousLinearMap.toSpanSingleton L u).restrictScalars 𝕜) α := by
      have := ((Polynomial.hasStrictDerivAt_aeval (monicOf a) α).hasDerivAt.hasFDerivAt
        ).restrictScalars 𝕜
      simpa only [hP] using this
    intro dy
    simpa using congrArg (fun T ↦ T dy) (h1.unique h2)
  set Ψ : (Fin n → 𝕜) × L → (Fin n → 𝕜) × L := fun x ↦ (x.1, P x)
  have hΨ : HasStrictFDerivAt Ψ ((ContinuousLinearMap.fst 𝕜 _ _).prod D) (a, α) :=
    hasStrictFDerivAt_fst.prodMk hD
  have hsurj : ((ContinuousLinearMap.fst 𝕜 (Fin n → 𝕜) L).prod D).range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun z ↦ ⟨(z.1, (z.2 - D (z.1, 0)) / u), ?_⟩
    have hsplit : ((z.1, (z.2 - D (z.1, 0)) / u) : (Fin n → 𝕜) × L) =
        (z.1, 0) + (0, (z.2 - D (z.1, 0)) / u) := by simp
    ext1
    · simp
    · change D _ = z.2
      rw [hsplit, map_add, hDy, div_mul_cancel₀ _ hα']
      ring
  have hmap := hΨ.map_nhds_eq_of_surj hsurj
  have himg : Ψ '' (Set.univ ×ˢ U) ∈ 𝓝 (a, (0 : L)) := by
    have h := Filter.image_mem_map (m := Ψ)
      (prod_mem_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 a) hU)
    rw [hmap] at h
    simpa [Ψ, hP, hα] using h
  have hc : Tendsto (fun c : Fin n → 𝕜 ↦ (c, (0 : L))) (𝓝 a) (𝓝 (a, 0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hc himg] with c hc'
  obtain ⟨⟨c', y⟩, ⟨-, hy⟩, he⟩ := hc'
  simp only [Ψ, Prod.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  exact ⟨y, hy, (hP c' y) ▸ he⟩

end CmGlobalization
