module

public import RequestProject.ThreeIM.ClusterFactorModels
public import RequestProject.ThreeIM.ClusterGerms

/-! # Padding genuine divisor factors to their common support -/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology
open scoped BigOperators

namespace ThreeIM

theorem int_toNat_real_le_abs (n : ℤ) : (n.toNat : ℝ) ≤ |(n : ℝ)| := by
  cases n with
  | ofNat k => simp
  | negSucc k => simp

namespace DivisorFactorData

theorem prod_exponent_on_superset {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    (S : Finset ℂ) (hS : D.support ⊆ S) (z : ℂ) :
    (∏ α ∈ S, (z - α) ^ D.exponent α) = ∏ α ∈ D.support, (z - α) ^ D.exponent α := by
  classical
  symm
  apply Finset.prod_subset hS
  intro α _ hα
  have hzero : D.exponent α = 0 := not_not.mp (mt (D.support_iff α).mpr hα)
  simp only [hzero, zpow_zero]

theorem prod_natural_exponent_on_superset {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    (S : Finset ℂ) (hS : D.support ⊆ S) (k : ℤ → ℕ) (hk : k 0 = 0) (z : ℂ) :
    (∏ α ∈ S, (z - α) ^ k (D.exponent α)) = ∏ α ∈ D.support, (z - α) ^ k (D.exponent α) := by
  classical
  symm
  apply Finset.prod_subset hS
  intro α _ hα
  have hzero : D.exponent α = 0 := not_not.mp (mt (D.support_iff α).mpr hα)
  simp only [hzero, hk, pow_zero]

theorem cleared_factor_on_superset {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    (S : Finset ℂ) (hS : D.support ⊆ S) {Ω : Set ℂ} (hΩ : Ω ⊆ ball (0 : ℂ) ρ) :
    clearedDivisorNumerator S (fun α => (D.exponent α).toNat) D.H
      =ᶠ[codiscreteWithin Ω]
        (fun z => F z * divisorPowerProduct S (fun α => (-D.exponent α).toNat) z) := by
  have hN : clearedDivisorNumerator S (fun α => (D.exponent α).toNat) D.H =
      clearedDivisorNumerator D.support (fun α => (D.exponent α).toNat) D.H := by
    ext z
    unfold clearedDivisorNumerator divisorPowerProduct
    rw [D.prod_natural_exponent_on_superset S hS Int.toNat (by rfl)]
  have hQ : divisorPowerProduct S (fun α => (-D.exponent α).toNat) =
      divisorPowerProduct D.support (fun α => (-D.exponent α).toNat) := by
    ext z
    unfold divisorPowerProduct
    exact D.prod_natural_exponent_on_superset S hS (fun n => (-n).toNat) (by rfl) z
  rw [hN, hQ]
  exact codiscreteWithin.mono hΩ D.cleared_factor_eq_codiscrete

/-- The exact logarithmic derivative of the cleared quotient is the
canonical A-model at every regular point, on the common padded support. -/
theorem quotient_logDeriv_on_superset {Φ A : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ)
    (hA : A = logDeriv Φ) (S : Finset ℂ) (hDS : D.support ⊆ S) (hES : E.support ⊆ S)
    {U : Set ℂ} (hU : IsOpen U) (hUρ : U ⊆ ball (0 : ℂ) ρ) :
    ∀ w ∈ U, (∀ α ∈ S, w ≠ α) →
      deriv (fun u => clearedDivisorNumerator S (fun α => (D.exponent α).toNat) D.H u /
          divisorPowerProduct S (fun α => (-D.exponent α).toNat) u) w /
        (clearedDivisorNumerator S (fun α => (D.exponent α).toNat) D.H w /
          divisorPowerProduct S (fun α => (-D.exponent α).toNat) w) =
        Complex.exp (E.H w) * ∏ α ∈ S, (w - α) ^ E.exponent α := by
  classical
  let Ω := U \ (S : Set ℂ)
  let N := clearedDivisorNumerator S (fun α => (D.exponent α).toNat) D.H
  let Q := divisorPowerProduct S (fun α => (-D.exponent α).toNat)
  have hΩ : IsOpen Ω := hU.inter S.finite_toSet.isClosed.isOpen_compl
  have hΩρ : Ω ⊆ ball (0 : ℂ) ρ := fun _ hw => hUρ hw.1
  have hreg : ∀ w ∈ Ω, ∀ α ∈ S, w ≠ α := by
    intro w hw α hα heq
    exact hw.2 (heq.symm ▸ hα)
  have hN : AnalyticOnNhd ℂ N Ω := by
    intro w hw
    apply (D.H_analytic w (hΩρ hw)).cexp.mul
    apply Finset.analyticAt_fun_prod
    intro α _
    exact (analyticAt_id.sub analyticAt_const).pow _
  have hQ : AnalyticOnNhd ℂ Q Ω := by
    intro w _
    apply Finset.analyticAt_fun_prod
    intro α _
    exact (analyticAt_id.sub analyticAt_const).pow _
  have hN0 : ∀ w ∈ Ω, N w ≠ 0 := by
    intro w hw
    exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr
      (fun α hα => pow_ne_zero _ (sub_ne_zero.mpr (hreg w hw α hα))))
  have hQ0 : ∀ w ∈ Ω, Q w ≠ 0 := by
    intro w hw
    exact Finset.prod_ne_zero_iff.mpr (fun α hα => pow_ne_zero _ (sub_ne_zero.mpr (hreg w hw α hα)))
  have hEmodel : AnalyticOnNhd ℂ E.exponentialModel Ω := fun w hw =>
    E.exponentialModel_analyticAt (hΩρ hw) (fun α hα => hreg w hw α (hES hα))
  have hraw := E.exponentialModel_eq_codiscrete hΩρ
  have hraw' : logDeriv Φ =ᶠ[codiscreteWithin Ω] E.exponentialModel := by
    filter_upwards [hraw] with w hw
    exact (congrFun hA.symm w).trans hw
  have hmodel := logDeriv_quotient_eqOn_of_codiscrete_clear hΩ hN hQ hN0 hQ0
    hEmodel.continuousOn (D.cleared_factor_on_superset S hDS hΩρ) hraw'
  intro w hw hregular
  have hwΩ : w ∈ Ω := ⟨hw, by intro h; exact hregular w h rfl⟩
  have hp := hmodel hwΩ
  change _ = Complex.exp (E.H w) * ∏ α ∈ E.support, (w - α) ^ E.exponent α at hp
  rw [E.prod_exponent_on_superset S hES w]
  exact hp

end DivisorFactorData
end ThreeIM
