module

public import RequestProject.ThreeIM.ClusterControlCircle
public import RequestProject.ThreeIM.BadPointLayers
public import RequestProject.ThreeIM.ClusterBudgetConstants

/-! # Honest analytic models and divisor geometry on the regular disks -/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- The source budget also dominates the radius, inverse gap, and actual
single-radius multiplicity bound. -/
theorem finiteDiskBudget_basic_controls {R Δ M : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M) :
    let B := finiteDiskBudget R Δ M
    4 ≤ B ∧ R ≤ B ∧ Δ⁻¹ ≤ B ∧ 8 * R * M * Δ⁻¹ ≤ B := by
  let X := R ^ 3 * M * (Δ⁻¹) ^ 2
  let B := finiteDiskBudget R Δ M
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have ht2 : Δ⁻¹ ≤ (Δ⁻¹) ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 2)
  have hR3 : R ≤ R ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (by decide : 1 ≤ 3)
  have hX1 : 1 ≤ X := by
    dsimp [X]
    calc
      (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR
      _ ≤ R ^ 3 * M := le_mul_of_one_le_right (by positivity) hM
      _ ≤ R ^ 3 * M * (Δ⁻¹) ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht)
  have hRX : R ≤ X := by
    calc
      R ≤ R ^ 3 := hR3
      _ ≤ R ^ 3 * M := le_mul_of_one_le_right (by positivity) hM
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht)
  have htX : Δ⁻¹ ≤ X := by
    calc
      Δ⁻¹ ≤ (Δ⁻¹) ^ 2 := ht2
      _ ≤ (R ^ 3 * M) * (Δ⁻¹) ^ 2 := le_mul_of_one_le_left (by positivity)
        (by nlinarith [one_le_pow₀ hR (n := 3)])
  have hmassX : 8 * R * M * Δ⁻¹ ≤ 784 * X := by
    dsimp [X]
    calc
      8 * R * M * Δ⁻¹ ≤ 784 * R ^ 3 * M * (Δ⁻¹) ^ 2 := by gcongr; norm_num
      _ = _ := by ring
  have hmargin : 784 * X ≤ B / 1000 := by
    simpa only [X, B, mul_assoc] using finiteDiskBudget_re_margin hR hΔ hΔ1 hM
  have hB : 4 ≤ B := by
    have hlarge := finiteDiskBudget_ge_million (by linarith : 0 ≤ R) hΔ (by linarith : 0 ≤ M)
    dsimp [B]
    linarith
  have hsmall : B / 1000 ≤ B := by linarith
  exact ⟨hB, (hRX.trans (by nlinarith)).trans (hmargin.trans hsmall),
    (htX.trans (by nlinarith)).trans (hmargin.trans hsmall), hmassX.trans (hmargin.trans hsmall)⟩

theorem truncatedDivisorDistance_le_norm_sub {S : Finset ℂ} {z α : ℂ} (hα : α ∈ S) :
    truncatedDivisorDistance S z ≤ ‖z - α‖ := by
  rw [truncatedDivisorDistance_of_nonempty ⟨α, hα⟩]
  exact (min_le_right _ _).trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem hα)

theorem truncatedDivisorDistance_pos_of_not_mem {S : Finset ℂ} {z : ℂ} (hz : z ∉ S) :
    0 < truncatedDivisorDistance S z := by
  classical
  by_cases hS : S = ∅
  · simp only [hS, truncatedDivisorDistance_empty, zero_lt_one]
  · have hne : (S : Set ℂ).Nonempty := by simpa only [Finset.coe_nonempty] using Finset.nonempty_iff_ne_empty.mpr hS
    rw [truncatedDivisorDistance_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS)]
    exact lt_min zero_lt_one ((S.finite_toSet.isClosed.notMem_iff_infDist_pos hne).mp hz)

/-- The physical disk stays in the inner analytic region and at least
half the center's truncated distance from every actual divisor. -/
theorem regular_disk_geometry (S : Finset ℂ) {z : ℂ} {r B Δ : ℝ}
    (hB : 4 ≤ B) (hΔ : B⁻¹ ≤ Δ) (hz : ‖z‖ ≤ r)
    (hd : 0 < truncatedDivisorDistance S z) :
    ball z (truncatedDivisorDistance S z / B ^ 4) ⊆ ball 0 (r + Δ / 2) ∧
      ∀ w ∈ ball z (truncatedDivisorDistance S z / B ^ 4), ∀ α ∈ S,
        truncatedDivisorDistance S z / 2 ≤ ‖w - α‖ := by
  let d := truncatedDivisorDistance S z
  have hd1 : d ≤ 1 := truncatedDivisorDistance_le_one S z
  have hBpos : 0 < B := by linarith
  have hBone : 1 ≤ B := by linarith
  have hB3 : 2 ≤ B ^ 3 := by
    have hp : B ≤ B ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hBone (by decide : 1 ≤ 3)
    linarith
  have hden : 2 * B ≤ B ^ 4 := by
    calc
      2 * B ≤ B * B ^ 3 := by nlinarith
      _ = B ^ 4 := by ring
  have hrad : d / B ^ 4 ≤ Δ / 2 := by
    calc
      d / B ^ 4 ≤ d / (2 * B) := div_le_div_of_nonneg_left hd.le (by positivity) hden
      _ ≤ 1 / (2 * B) := div_le_div_of_nonneg_right hd1 (by positivity)
      _ = B⁻¹ / 2 := by ring
      _ ≤ Δ / 2 := div_le_div_of_nonneg_right hΔ (by norm_num)
  have hhalf : d / B ^ 4 ≤ d / 2 :=
    div_le_div_of_nonneg_left hd.le (by norm_num) (by nlinarith [hden])
  refine ⟨?_, ?_⟩
  · intro w hw
    have hn := norm_le_norm_add_norm_sub' w z
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    linarith
  · intro w hw α hα
    have hcenter := truncatedDivisorDistance_le_norm_sub hα (z := z)
    have hn : ‖z - α‖ ≤ ‖z - w‖ + ‖w - α‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (z - w) (w - α)
    have hw' : ‖z - w‖ < d / B ^ 4 := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
    change d / 2 ≤ ‖w - α‖
    change d ≤ ‖z - α‖ at hcenter
    linarith

namespace DivisorFactorData

/-- Exact logarithmic derivative of an honest regular exponential model. -/
theorem logDeriv_exponentialModel {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hne : ∀ α ∈ D.support, z ≠ α) :
    deriv D.exponentialModel z / D.exponentialModel z =
      deriv D.H z + ∑ α ∈ D.support, (D.exponent α : ℂ) / (z - α) := by
  exact logDeriv_exp_divisor_product D.support (d := D.exponent)
    (D.H_analytic z hz).differentiableAt hne

/-- A two-sided linear-factor band bounds the center log norm of the
actual analytic model, without evaluating the raw meromorphic function. -/
theorem abs_log_norm_exponentialModel_le {F : ℂ → ℂ} {ρ C L N : ℝ}
    (D : DivisorFactorData F ρ) {z : ℂ}
    (hC : 0 ≤ C) (hL : |(D.H z).re| ≤ L)
    (hband : ∀ α ∈ D.support, Real.exp (-C) ≤ ‖z - α‖ ∧ ‖z - α‖ ≤ Real.exp C)
    (hdegree : (∑ α ∈ D.support, |(D.exponent α : ℝ)|) ≤ N) :
    |Real.log ‖D.exponentialModel z‖| ≤ L + C * N := by
  have hne : ∀ α ∈ D.support, z ≠ α := by
    intro α hα heq
    have hn := (hband α hα).1
    rw [heq, sub_self, norm_zero] at hn
    exact (not_le_of_gt (Real.exp_pos (-C))) hn
  have hprodpos : 0 < ‖∏ α ∈ D.support, (z - α) ^ D.exponent α‖ := norm_pos_iff.mpr
    (Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ (sub_ne_zero.mpr (hne α hα))))
  have hupper := norm_prod_zpow_le_exp D.support hC hband hdegree
  have hlower := norm_prod_zpow_ge_exp D.support hC hband hdegree
  have hloghi := Real.log_le_log hprodpos hupper
  have hloglo := Real.log_le_log (Real.exp_pos (-C * N)) hlower
  rw [Real.log_exp] at hloghi hloglo
  have hidentity : Real.log ‖D.exponentialModel z‖ = (D.H z).re +
      Real.log ‖∏ α ∈ D.support, (z - α) ^ D.exponent α‖ := by
    rw [exponentialModel, norm_mul, Complex.norm_exp,
      Real.log_mul (Real.exp_ne_zero _) hprodpos.ne', Real.log_exp]
  rw [hidentity, abs_le]
  have hre := abs_le.mp hL
  constructor <;> linarith

end DivisorFactorData
end ThreeIM
