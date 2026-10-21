module

public import RequestProject.ThreeIM.ClusterFactorModels
public import RequestProject.ThreeIM.ClusterFactorBounds
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extending the actual logarithm's derivative bound from a control circle

The identity is evaluated only for analytic exponential models at regular
circle points. The maximum modulus principle then controls H' throughout
the disk, including the original meromorphic divisor points.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- The corresponding upper estimate for integer-power divisor products. -/
theorem norm_prod_zpow_le_exp (s : Finset ℂ) {f : ℂ → ℂ} {d : ℂ → ℤ} {C M : ℝ}
    (hC : 0 ≤ C)
    (hband : ∀ α ∈ s, Real.exp (-C) ≤ ‖f α‖ ∧ ‖f α‖ ≤ Real.exp C)
    (hdegree : (∑ α ∈ s, |(d α : ℝ)|) ≤ M) :
    ‖∏ α ∈ s, f α ^ d α‖ ≤ Real.exp (C * M) := by
  have hne : ∀ α ∈ s, f α ≠ 0 := by
    intro α hα
    exact norm_pos_iff.mp ((Real.exp_pos (-C)).trans_le (hband α hα).1)
  have hp : 0 < ‖∏ α ∈ s, f α ^ d α‖ := norm_pos_iff.mpr
    (Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ (hne α hα)))
  have hlower := norm_prod_zpow_ge_exp s (d := fun α => -d α) hC hband
    (by simpa only [Int.cast_neg, abs_neg] using hdegree)
  have heq : (∏ α ∈ s, f α ^ (-d α)) = (∏ α ∈ s, f α ^ d α)⁻¹ := by
    simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [heq, norm_inv] at hlower
  have hinv := (inv_le_inv₀ (inv_pos.mpr hp) (Real.exp_pos (-C * M))).mpr hlower
  simpa only [inv_inv, show -C * M = -(C * M) by ring, Real.exp_neg] using hinv

/-- The simple fractions are bounded by genuine total multiplicity over
the distance to the divisor set. -/
theorem norm_sum_divisor_fractions_le (s : Finset ℂ) {d : ℂ → ℤ} {z : ℂ} {δ N : ℝ}
    (hδ : 0 < δ) (hsep : ∀ α ∈ s, δ ≤ ‖z - α‖)
    (hdegree : (∑ α ∈ s, |(d α : ℝ)|) ≤ N) :
    ‖∑ α ∈ s, (d α : ℂ) / (z - α)‖ ≤ N / δ := by
  calc
    ‖∑ α ∈ s, (d α : ℂ) / (z - α)‖ ≤ ∑ α ∈ s, ‖(d α : ℂ) / (z - α)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ α ∈ s, |(d α : ℝ)| / δ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_div]
      have hn : ‖(d α : ℂ)‖ = |(d α : ℝ)| := by simp
      rw [hn]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hδ (hsep α hα)
    _ = (∑ α ∈ s, |(d α : ℝ)|) / δ := by rw [Finset.sum_div]
    _ ≤ N / δ := div_le_div_of_nonneg_right hdegree hδ.le

/-- The exact regular-circle identity bounds H' on its whole interior by
the maximum modulus principle. All hypotheses here are local estimates
of already constructed divisor factors, not a new selection assumption. -/
theorem norm_deriv_H_le_of_control_circle {Φ A : ℂ → ℂ} {ρ σ δ C K N : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ)
    (hA : A = logDeriv Φ) (hσ : 0 < σ) (hσρ : σ < ρ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdegreeD : (∑ α ∈ D.support, |(D.exponent α : ℝ)|) ≤ N)
    (hdegreeE : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) ≤ N)
    (hsepD : ∀ w ∈ sphere (0 : ℂ) σ, ∀ α ∈ D.support, δ ≤ ‖w - α‖)
    (hbandE : ∀ w ∈ sphere (0 : ℂ) σ, ∀ α ∈ E.support,
      Real.exp (-C) ≤ ‖w - α‖ ∧ ‖w - α‖ ≤ Real.exp C)
    (hre : ∀ w ∈ sphere (0 : ℂ) σ, (E.H w).re ≤ K) :
    ∀ z ∈ closedBall (0 : ℂ) σ,
      ‖deriv D.H z‖ ≤ Real.exp (K + C * N) + N / δ := by
  have hsub : closedBall (0 : ℂ) σ ⊆ ball (0 : ℂ) ρ := closedBall_subset_ball hσρ
  have hboundary : ∀ w ∈ sphere (0 : ℂ) σ,
      ‖deriv D.H w‖ ≤ Real.exp (K + C * N) + N / δ := by
    intro w hw
    have hwρ := hsub (sphere_subset_closedBall hw)
    have hDreg : ∀ α ∈ D.support, w ≠ α := by
      intro α hα heq
      have hn := hsepD w hw α hα
      rw [heq, sub_self, norm_zero] at hn
      linarith
    have hEreg : ∀ α ∈ E.support, w ≠ α := by
      intro α hα heq
      have hn := (hbandE w hw α hα).1
      rw [heq, sub_self, norm_zero] at hn
      exact (not_le_of_gt (Real.exp_pos (-C))) hn
    have hmodel : ‖E.exponentialModel w‖ ≤ Real.exp (K + C * N) := by
      unfold DivisorFactorData.exponentialModel
      rw [norm_mul, Complex.norm_exp, Real.exp_add]
      exact mul_le_mul (Real.exp_le_exp.mpr (hre w hw))
        (norm_prod_zpow_le_exp E.support hC (hbandE w hw) hdegreeE)
        (norm_nonneg _) (Real.exp_pos _).le
    rw [D.deriv_H_eq_logDeriv_model_sub_sum E hA hwρ hDreg hEreg]
    exact (norm_sub_le _ _).trans (add_le_add hmodel
      (norm_sum_divisor_fractions_le D.support hδ (hsepD w hw) hdegreeD))
  have hderiv : AnalyticOnNhd ℂ (deriv D.H) (ball (0 : ℂ) ρ) := D.H_analytic.deriv
  have hdiff : DiffContOnCl ℂ (deriv D.H) (ball (0 : ℂ) σ) := by
    refine ⟨hderiv.differentiableOn.mono (ball_subset_ball hσρ.le), ?_⟩
    rw [closure_ball (0 : ℂ) hσ.ne']
    exact hderiv.continuousOn.mono hsub
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
  · intro w hw
    exact hboundary w (by simpa only [frontier_ball (0 : ℂ) hσ.ne'] using hw)
  · simpa only [closure_ball (0 : ℂ) hσ.ne'] using hz

end ThreeIM
