module

public import RequestProject.ThreeIM.ClusterFactorControl
public import RequestProject.ThreeIM.ClusterDivisorData
public import RequestProject.ThreeIM.ClusterBudgetConstants

/-!
# Pairwise control from the original single-radius coefficient budget

The coefficient budget is the exact expression in the finite-disk lemma.
The real-part estimates below are derived for the actually extracted
factors of A and Psi, with no independently supplied degree bounds.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- The source's M, including the leading one. -/
noncomputable def finiteDiskCoefficientMass (Φ A Ψ : ℂ → ℂ) (R : ℝ) : ℝ :=
  1 + ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
    ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
    ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R

theorem finiteDiskCoefficientMass_ge_one (Φ A Ψ : ℂ → ℂ) {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ finiteDiskCoefficientMass Φ A Ψ R := by
  unfold finiteDiskCoefficientMass
  linarith [ValueDistribution.characteristic_nonneg (f := A) (a := ⊤) hR,
    ValueDistribution.characteristic_nonneg (f := A⁻¹) (a := ⊤) hR,
    ValueDistribution.characteristic_nonneg (f := Ψ) (a := ⊤) hR,
    ValueDistribution.characteristic_nonneg (f := Ψ⁻¹) (a := ⊤) hR,
    ValueDistribution.logCounting_nonneg (f := Φ) (e := ⊤) hR,
    ValueDistribution.logCounting_nonneg (f := Φ⁻¹) (e := ⊤) hR]

/-- This is the boundary budget of the same zero-free factor used by the
Poisson estimate. -/
noncomputable def factorBoundaryBudget {F : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData F ρ) (R : ℝ) : ℝ :=
  ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R +
    2 * (∑ α ∈ D.support, |(D.exponent α : ℝ)|) * (Real.log ρ + 2)

theorem factorBoundaryBudget_nonneg {F : ℂ → ℂ} {ρ R : ℝ}
    (D : DivisorFactorData F ρ) (hρ : 1 ≤ ρ) (hR : 1 ≤ R) :
    0 ≤ factorBoundaryBudget D R := by
  unfold factorBoundaryBudget
  have hn : 0 ≤ ∑ α ∈ D.support, |(D.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hl : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hT := ValueDistribution.characteristic_nonneg (f := F) (a := ⊤) hR
  have hTi := ValueDistribution.characteristic_nonneg (f := F⁻¹) (a := ⊤) hR
  positivity

/-- The pair of actual boundary factor budgets is polynomially controlled
by the original M and the actual inner-window divisor mass. -/
theorem factorBoundaryBudget_pair_le {Φ A Ψ : ℂ → ℂ} {ρ R Δ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ)
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hwindow : ρ ≤ R - Δ / 8) :
    factorBoundaryBudget E R + factorBoundaryBudget P R ≤
      49 * R ^ 2 * finiteDiskCoefficientMass Φ A Ψ R * Δ⁻¹ := by
  let M := finiteDiskCoefficientMass Φ A Ψ R
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have hρR : ρ ≤ R := by linarith
  have hl0 : 0 ≤ Real.log ρ + 2 := by have := Real.log_nonneg hρ; linarith
  have hl : Real.log ρ + 2 ≤ 3 * R := by
    have hlog := Real.log_le_self (by linarith : 0 ≤ ρ)
    linarith
  have hchars : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
      ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R ≤ M := by
    dsimp [M, finiteDiskCoefficientMass]
    linarith [ValueDistribution.logCounting_nonneg (f := Φ) (e := ⊤) hR,
      ValueDistribution.logCounting_nonneg (f := Φ⁻¹) (e := ⊤) hR]
  have hmass := jointDivisorMass_le_window D E P hΦ hA hΨ hρ hΔ hwindow
  have hmass' : jointDivisorMass D E P ≤ 8 * R * M * Δ⁻¹ := by
    have hcoef : 0 ≤ 8 * R / Δ := by positivity
    have houter : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R ≤ M := by
      dsimp [M, finiteDiskCoefficientMass]
      linarith
    exact hmass.trans ((mul_le_mul_of_nonneg_left houter hcoef).trans_eq (by ring))
  have hdegrees : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) +
      (∑ α ∈ P.support, |(P.exponent α : ℝ)|) ≤ jointDivisorMass D E P := by
    rw [jointDivisorMass_eq_sum_degrees]
    have hn : 0 ≤ ∑ α ∈ D.support, |(D.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hm0 : 0 ≤ jointDivisorMass D E P :=
    (show 0 ≤ ((jointDivisorSupport D E P).card : ℝ) by positivity).trans
      (jointDivisorSupport_card_le_mass D E P)
  have hMsmall : M ≤ R ^ 2 * M * Δ⁻¹ := by
    calc
      M ≤ R ^ 2 * M := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hR)
      _ ≤ R ^ 2 * M * Δ⁻¹ := le_mul_of_one_le_right (by positivity) ht
  calc
    factorBoundaryBudget E R + factorBoundaryBudget P R ≤
        M + 2 * jointDivisorMass D E P * (Real.log ρ + 2) := by
      unfold factorBoundaryBudget
      have hd := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdegrees (show (0 : ℝ) ≤ 2 by norm_num)) hl0
      nlinarith
    _ ≤ M + 6 * R * jointDivisorMass D E P := by
      have hd := mul_le_mul_of_nonneg_left hl
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hm0)
      nlinarith
    _ ≤ M + 48 * R ^ 2 * M * Δ⁻¹ := by
      have hd := mul_le_mul_of_nonneg_left hmass' (show 0 ≤ 6 * R by positivity)
      nlinarith
    _ ≤ 49 * R ^ 2 * M * Δ⁻¹ := by nlinarith

private theorem factorBoundaryBudget_scaled_pair_le {Φ A Ψ : ℂ → ℂ} {ρ R Δ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ)
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hwindow : ρ ≤ R - Δ / 8) :
    2 * ρ / (Δ / 8) * (factorBoundaryBudget E R + factorBoundaryBudget P R) ≤
      784 * (R ^ 3 * finiteDiskCoefficientMass Φ A Ψ R) * (Δ⁻¹) ^ 2 := by
  have hρR : ρ ≤ R := by linarith
  have hscale : 2 * ρ / (Δ / 8) ≤ 16 * R * Δ⁻¹ := by
    rw [div_div_eq_mul_div, div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_right hρR (inv_nonneg.mpr hΔ.le)]
  have hsum0 : 0 ≤ factorBoundaryBudget E R + factorBoundaryBudget P R :=
    add_nonneg (factorBoundaryBudget_nonneg E hρ hR) (factorBoundaryBudget_nonneg P hρ hR)
  calc
    _ ≤ (16 * R * Δ⁻¹) *
        (49 * R ^ 2 * finiteDiskCoefficientMass Φ A Ψ R * Δ⁻¹) :=
      mul_le_mul hscale (factorBoundaryBudget_pair_le D E P hΦ hA hΨ hR hρ hΔ hΔ1 hwindow)
        hsum0 (by positivity)
    _ = _ := by ring

/-- Both actual logarithms have the source's B/1000 real-part margin on
the inner gap disk. Every input is the original meromorphic data or its
already proved extraction, not a synthetic bounded-factor hypothesis. -/
theorem factor_pair_abs_re_le_budget {Φ A Ψ : ℂ → ℂ} {ρ R Δ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ)
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hwindow : ρ ≤ R - Δ / 8)
    {z : ℂ} (hz : ‖z‖ ≤ ρ - Δ / 8) :
    |(E.H z).re| + |(P.H z).re| ≤
      finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R) / 1000 := by
  have hρR : ρ ≤ R := by linarith
  have hE := E.abs_re_H_le_characteristic_gap hA hρ hρR (by positivity : 0 < Δ / 8) hz
  have hP := P.abs_re_H_le_characteristic_gap hΨ hρ hρR (by positivity : 0 < Δ / 8) hz
  have hsum : |(E.H z).re| + |(P.H z).re| ≤
      2 * ρ / (Δ / 8) * (factorBoundaryBudget E R + factorBoundaryBudget P R) := by
    unfold factorBoundaryBudget
    nlinarith
  exact hsum.trans ((factorBoundaryBudget_scaled_pair_le D E P hΦ hA hΨ hR hρ hΔ hΔ1 hwindow).trans
    (finiteDiskBudget_re_margin hR hΔ hΔ1 (finiteDiskCoefficientMass_ge_one Φ A Ψ hR)))

/-- On the next inner gap disk the actual logarithmic derivatives have
sum at most B/2. The constant terms from both logarithms are retained. -/
theorem factor_pair_norm_deriv_le_budget {Φ A Ψ : ℂ → ℂ} {ρ R Δ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ)
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hR : 1 ≤ R) (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hwindow : ρ ≤ R - Δ / 8)
    {z : ℂ} (hz : ‖z‖ ≤ ρ - Δ / 4) :
    ‖deriv E.H z‖ + ‖deriv P.H z‖ ≤
      finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R) / 2 := by
  let M := finiteDiskCoefficientMass Φ A Ψ R
  let K := 2 * ρ / (Δ / 8) * (factorBoundaryBudget E R + factorBoundaryBudget P R)
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have hρR : ρ ≤ R := by linarith
  have hz' : ‖z‖ ≤ ρ - 2 * (Δ / 8) := by linarith
  have hE := E.norm_deriv_H_le_characteristic_gap hA hρ hρR (by positivity : 0 < Δ / 8) hz'
  have hP := P.norm_deriv_H_le_characteristic_gap hΨ hρ hρR (by positivity : 0 < Δ / 8) hz'
  change ‖deriv E.H z‖ ≤ 8 * (2 * (2 * ρ / (Δ / 8) * factorBoundaryBudget E R) + 5) / (Δ / 8) at hE
  change ‖deriv P.H z‖ ≤ 8 * (2 * (2 * ρ / (Δ / 8) * factorBoundaryBudget P R) + 5) / (Δ / 8) at hP
  have hsum : ‖deriv E.H z‖ + ‖deriv P.H z‖ ≤ 64 * Δ⁻¹ * (2 * K + 10) := by
    exact (add_le_add hE hP).trans_eq (by
      dsimp [K]
      simp only [div_eq_mul_inv]
      ring)
  have hK : K ≤ 784 * (R ^ 3 * M) * (Δ⁻¹) ^ 2 :=
    factorBoundaryBudget_scaled_pair_le D E P hΦ hA hΨ hR hρ hΔ hΔ1 hwindow
  have hX : 1 ≤ R ^ 3 * M := by
    calc
      (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR
      _ ≤ R ^ 3 * M := le_mul_of_one_le_right (by positivity) hM
  have hXt : 1 ≤ R ^ 3 * M * (Δ⁻¹) ^ 2 :=
    hX.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht))
  have hmain := mul_le_mul_of_nonneg_left hK (show 0 ≤ 128 * Δ⁻¹ by positivity)
  have hconstant := mul_le_mul_of_nonneg_left hXt (show 0 ≤ 640 * Δ⁻¹ by positivity)
  have hpoly : 64 * Δ⁻¹ * (2 * K + 10) ≤ 100992 * (R ^ 3 * M) * (Δ⁻¹) ^ 3 := by
    nlinarith
  have hmargin := finiteDiskBudget_derivative_margin hR hΔ hΔ1 hM
  calc
    _ ≤ 100992 * (R ^ 3 * M) * (Δ⁻¹) ^ 3 := hsum.trans hpoly
    _ ≤ 2 * (100672 * (R ^ 3 * M) * (Δ⁻¹) ^ 3) := by
      have hp : 0 ≤ R ^ 3 * M * (Δ⁻¹) ^ 3 := by positivity
      nlinarith
    _ ≤ 2 * (finiteDiskBudget R Δ M / 4) :=
      mul_le_mul_of_nonneg_left hmargin (by norm_num)
    _ = finiteDiskBudget R Δ M / 2 := by ring

end ThreeIM
