module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.FieldSimp

/-!
# Logarithmic derivatives of genuine analytic models

On a regular open domain, actual analytic models of Phi and Phi'/Phi
determine the pointwise logarithmic-derivative identity used by the cluster
Wronskian estimate. The raw representatives need only agree codiscretely;
their derivatives at isolated junk points are never substituted.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

/-- The exact logarithmic derivative of an exponential divisor model at a
regular point. This is the H'-identity used on a separated control circle. -/
theorem logDeriv_exp_divisor_product (S : Finset ℂ) {d : ℂ → ℤ}
    {H : ℂ → ℂ} {z : ℂ} (hH : DifferentiableAt ℂ H z)
    (hregular : ∀ α ∈ S, z ≠ α) :
    logDeriv (fun w => Complex.exp (H w) * ∏ α ∈ S, (w - α) ^ d α) z =
      deriv H z + ∑ α ∈ S, (d α : ℂ) / (z - α) := by
  classical
  have hfactor0 : ∀ α ∈ S, (fun w : ℂ => (w - α) ^ d α) z ≠ 0 :=
    fun α hα => zpow_ne_zero _ (sub_ne_zero.mpr (hregular α hα))
  have hfactorD : ∀ α ∈ S, DifferentiableAt ℂ (fun w : ℂ => (w - α) ^ d α) z :=
    fun α hα => (differentiableAt_id.sub_const α).zpow
      (Or.inl (sub_ne_zero.mpr (hregular α hα)))
  have hP0 : (∏ α ∈ S, (z - α) ^ d α) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor0
  have hPD : DifferentiableAt ℂ (fun w => ∏ α ∈ S, (w - α) ^ d α) z :=
    DifferentiableAt.fun_finset_prod hfactorD
  have he : logDeriv (fun w => Complex.exp (H w)) z = deriv H z := by
    rw [logDeriv_apply, hH.hasDerivAt.cexp.deriv]
    field_simp [Complex.exp_ne_zero]
  rw [logDeriv_fun_mul (f := fun w => Complex.exp (H w))
    (g := fun w => ∏ α ∈ S, (w - α) ^ d α) z (Complex.exp_ne_zero (H z)) hP0 hH.cexp hPD, he,
    logDeriv_fun_prod (f := fun α w : ℂ => (w - α) ^ d α) (x := z) hfactor0 hfactorD]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  rw [logDeriv_fun_zpow (f := fun w : ℂ => w - α) (x := z)
    (differentiableAt_id.sub_const α) (d α)]
  simp [logDeriv_apply, div_eq_mul_inv]

private theorem punctured_eq_of_codiscrete {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hfg : f =ᶠ[codiscreteWithin Ω] g) {z : ℂ} (hz : z ∈ Ω) :
    f =ᶠ[𝓝[≠] z] g := by
  have heq := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg z hz
  have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ Ω :=
    (show ∀ᶠ w in 𝓝 z, w ∈ Ω from hΩ.mem_nhds hz).filter_mono nhdsWithin_le_nhds
  filter_upwards [heq, hmem] with w hw hwΩ
  rcases hw with h | h
  · exact h
  · exact (h hwΩ).elim

/-- Codiscrete analytic models of a function and its logarithmic derivative
give the actual pointwise identity on every regular point of the domain. -/
theorem logDeriv_eqOn_of_codiscrete_analytic_models {Ω : Set ℂ}
    {Φ M A : ℂ → ℂ} (hΩ : IsOpen Ω) (hM : AnalyticOnNhd ℂ M Ω)
    (hM0 : ∀ z ∈ Ω, M z ≠ 0) (hA : ContinuousOn A Ω)
    (hΦ : Φ =ᶠ[codiscreteWithin Ω] M)
    (hlogΦ : logDeriv Φ =ᶠ[codiscreteWithin Ω] A) :
    EqOn (fun z => deriv M z / M z) A Ω := by
  have hderiv : deriv Φ =ᶠ[codiscreteWithin Ω] deriv M := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro z hz
    have hd := (punctured_eq_of_codiscrete hΩ hΦ hz).nhdsNE_deriv
    filter_upwards [hd] with w hw
    exact Or.inl hw
  have hmodel : (fun z => deriv M z / M z) =ᶠ[codiscreteWithin Ω] A := by
    filter_upwards [hΦ, hderiv, hlogΦ] with z hz hd hl
    simpa only [logDeriv_apply, hz, hd] using hl
  have hcontinuous : ContinuousOn (fun z => deriv M z / M z) Ω :=
    hM.deriv.continuousOn.div hM.continuousOn hM0
  intro z hz
  have hp := punctured_eq_of_codiscrete hΩ hmodel hz
  exact tendsto_nhds_unique_of_eventuallyEq
    (((hcontinuous.continuousAt (hΩ.mem_nhds hz))).mono_left nhdsWithin_le_nhds)
    (((hA.continuousAt (hΩ.mem_nhds hz))).mono_left nhdsWithin_le_nhds) hp

/-- The same bridge from a cleared identity. The nonzero assumptions apply
only on the regular open domain where the derivative is used, not at a
fiber center which might be a divisor point. -/
theorem logDeriv_quotient_eqOn_of_codiscrete_clear {Ω : Set ℂ}
    {Φ N Q A : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hN : AnalyticOnNhd ℂ N Ω) (hQ : AnalyticOnNhd ℂ Q Ω)
    (hN0 : ∀ z ∈ Ω, N z ≠ 0) (hQ0 : ∀ z ∈ Ω, Q z ≠ 0)
    (hA : ContinuousOn A Ω)
    (hclear : N =ᶠ[codiscreteWithin Ω] (fun z => Φ z * Q z))
    (hlogΦ : logDeriv Φ =ᶠ[codiscreteWithin Ω] A) :
    EqOn (fun z => deriv (fun w => N w / Q w) z / (N z / Q z)) A Ω := by
  have hΦ : Φ =ᶠ[codiscreteWithin Ω] (fun z => N z / Q z) := by
    filter_upwards [hclear, self_mem_codiscreteWithin Ω] with z hz hzΩ
    exact ((div_eq_iff (hQ0 z hzΩ)).mpr hz).symm
  exact logDeriv_eqOn_of_codiscrete_analytic_models hΩ
    (fun z hz => (hN z hz).div (hQ z hz) (hQ0 z hz))
    (fun z hz => div_ne_zero (hN0 z hz) (hQ0 z hz)) hA hΦ hlogΦ

end ThreeIM
