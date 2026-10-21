module

public import RequestProject.ThreeIM.ClusterFactorData
public import RequestProject.ThreeIM.ClusterLogDerivative
public import RequestProject.ThreeIM.ClusterFactorization

/-!
# Regular models from the same extracted divisor data

The raw meromorphic representatives may have junk at isolated points.
All pointwise derivative identities below concern analytic exponential
models on the complement of the actual finite divisor supports.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology
open scoped BigOperators

namespace ThreeIM.DivisorFactorData

/-- The analytic exponential model on the regular part of the extraction
disk. The integer product may have poles only at the finite support. -/
noncomputable def exponentialModel {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ) (z : ℂ) : ℂ :=
  Complex.exp (D.H z) * ∏ α ∈ D.support, (z - α) ^ D.exponent α

theorem exponentialModel_analyticAt {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hne : ∀ α ∈ D.support, z ≠ α) :
    AnalyticAt ℂ D.exponentialModel z := by
  apply (D.H_analytic z hz).cexp.mul
  apply Finset.analyticAt_fun_prod
  intro α hα
  exact (analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr (hne α hα))

theorem exponentialModel_ne_zero {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {z : ℂ} (hne : ∀ α ∈ D.support, z ≠ α) : D.exponentialModel z ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr
    (fun α hα => zpow_ne_zero _ (sub_ne_zero.mpr (hne α hα))))

/-- The same extracted logarithm and divisor data give the actual raw
meromorphic function codiscretely; values at exceptional points are unused. -/
theorem exponentialModel_eq_codiscrete {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {Ω : Set ℂ} (hΩ : Ω ⊆ ball (0 : ℂ) ρ) :
    F =ᶠ[codiscreteWithin Ω] D.exponentialModel := by
  have hfac := codiscreteWithin.mono (hΩ.trans ball_subset_closedBall) D.factor
  filter_upwards [hfac, self_mem_codiscreteWithin Ω] with z hz hzΩ
  simpa only [exponentialModel, D.exp_H z (hΩ hzΩ), mul_comm] using hz

/-- At every point regular for both actual divisors, the derivative of
the Phi logarithm is the A exponential model minus the genuine simple
fractions. This follows from raw A=Phi'/Phi only codiscretely. -/
theorem deriv_H_eq_logDeriv_model_sub_sum {Φ A : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ)
    (hA : A = logDeriv Φ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ)
    (hD : ∀ α ∈ D.support, z ≠ α) (hE : ∀ α ∈ E.support, z ≠ α) :
    deriv D.H z = E.exponentialModel z -
      ∑ α ∈ D.support, (D.exponent α : ℂ) / (z - α) := by
  let Ω := ball (0 : ℂ) ρ \ ((D.support : Set ℂ) ∪ (E.support : Set ℂ))
  have hΩ : IsOpen Ω := isOpen_ball.inter
    (D.support.finite_toSet.isClosed.union E.support.finite_toSet.isClosed).isOpen_compl
  have hΩball : Ω ⊆ ball (0 : ℂ) ρ := fun _ hw => hw.1
  have hDreg : ∀ w ∈ Ω, ∀ α ∈ D.support, w ≠ α := by
    intro w hw α hα heq
    exact hw.2 (Or.inl (heq.symm ▸ hα))
  have hEreg : ∀ w ∈ Ω, ∀ α ∈ E.support, w ≠ α := by
    intro w hw α hα heq
    exact hw.2 (Or.inr (heq.symm ▸ hα))
  have hzΩ : z ∈ Ω := by
    refine ⟨hz, ?_⟩
    rintro (hd | he)
    · exact hD z hd rfl
    · exact hE z he rfl
  have hEA := E.exponentialModel_eq_codiscrete hΩball
  have hEA' : logDeriv Φ =ᶠ[codiscreteWithin Ω] E.exponentialModel := by
    filter_upwards [hEA] with w hw
    exact (congrFun hA.symm w).trans hw
  have hmodel := logDeriv_eqOn_of_codiscrete_analytic_models hΩ
    (fun w hw => D.exponentialModel_analyticAt (hΩball hw) (hDreg w hw))
    (fun w hw => D.exponentialModel_ne_zero (hDreg w hw))
    (show ContinuousOn E.exponentialModel Ω from
      (show AnalyticOnNhd ℂ E.exponentialModel Ω from
        fun w hw => E.exponentialModel_analyticAt (hΩball hw) (hEreg w hw)).continuousOn)
    (D.exponentialModel_eq_codiscrete hΩball) hEA' hzΩ
  have hlog := logDeriv_exp_divisor_product D.support (d := D.exponent)
    (D.H_analytic z hz).differentiableAt hD
  apply eq_sub_iff_add_eq.mpr
  rw [← hlog]
  exact hmodel

/-- Clearing the positive and negative powers uses these same coupled
data, so the H' estimate remains attached to the counted numerator. -/
theorem cleared_factor_eq_codiscrete {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ) :
    clearedDivisorNumerator D.support (fun α => (D.exponent α).toNat) D.H
      =ᶠ[codiscreteWithin (ball (0 : ℂ) ρ)]
        (fun z => F z * divisorPowerProduct D.support (fun α => (-D.exponent α).toNat) z) := by
  classical
  have hfac := D.exponentialModel_eq_codiscrete (show ball (0 : ℂ) ρ ⊆ ball 0 ρ from subset_rfl)
  have havoid : ∀ᶠ z in codiscreteWithin (ball (0 : ℂ) ρ), z ∉ (D.support : Set ℂ) := by
    have hcom : ∀ᶠ z in codiscrete ℂ, z ∉ (D.support : Set ℂ) :=
      D.support.finite_toSet.compl_mem_codiscrete
    exact hcom.filter_mono (Filter.codiscreteWithin.mono (subset_univ _))
  filter_upwards [hfac, havoid] with z hz hzS
  have hregular : ∀ α ∈ D.support, z - α ≠ 0 := by
    intro α hα heq
    exact hzS ((sub_eq_zero.mp heq).symm ▸ hα)
  have hQ0 : divisorPowerProduct D.support (fun α => (-D.exponent α).toNat) z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun α hα => pow_ne_zero _ (hregular α hα))
  have hsplit : (∏ α ∈ D.support, (z - α) ^ D.exponent α) =
      divisorPowerProduct D.support (fun α => (D.exponent α).toNat) z /
        divisorPowerProduct D.support (fun α => (-D.exponent α).toNat) z := by
    change _ = (∏ α ∈ D.support, (z - α) ^ (D.exponent α).toNat) /
      ∏ α ∈ D.support, (z - α) ^ (-D.exponent α).toNat
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro α hα
    rw [← zpow_natCast_sub_natCast₀ (hregular α hα), Int.toNat_sub_toNat_neg]
  change Complex.exp (D.H z) * divisorPowerProduct D.support (fun α => (D.exponent α).toNat) z = _
  rw [hz]
  unfold exponentialModel
  rw [hsplit]
  field_simp [hQ0]

end ThreeIM.DivisorFactorData
