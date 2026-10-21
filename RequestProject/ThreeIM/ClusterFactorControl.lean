module

public import RequestProject.ThreeIM.ClusterFactorData
public import RequestProject.ThreeIM.LogDerivFactor

/-!
# Interior control of the actual zero-free divisor factors

The boundary proximity and interior logarithm refer to the same extracted
factor. The estimates below derive from the characteristic of the original
meromorphic function, rather than assuming a separate bounded factor.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real MeasureTheory
open scoped BigOperators

namespace ThreeIM

/-- The logarithmic derivative estimate on a disk centered at an arbitrary
point. Translation avoids the extra global-radius factor in its use. -/
theorem norm_logDeriv_le_of_abs_log_le_centered {g : ℂ → ℂ} {c : ℂ} {s K : ℝ}
    (hs : 0 < s) (hg : DifferentiableOn ℂ g (ball c s))
    (hg0 : ∀ z ∈ ball c s, g z ≠ 0)
    (hK : ∀ z ∈ ball c s, |log ‖g z‖| ≤ K) :
    ‖deriv g c / g c‖ ≤ 8 * (2 * K + 5) / s := by
  let G : ℂ → ℂ := fun w => g (c + w)
  have hmem (w : ℂ) (hw : w ∈ ball (0 : ℂ) s) : c + w ∈ ball c s := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hG : DifferentiableOn ℂ G (ball 0 s) := by
    intro w hw
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds (hmem w hw))).comp w
      ((differentiableAt_id).const_add c)).differentiableWithinAt
  have hG0 : ∀ w ∈ ball (0 : ℂ) s, G w ≠ 0 := fun w hw => hg0 _ (hmem w hw)
  have hGK : ∀ w ∈ ball (0 : ℂ) s, |log ‖G w‖| ≤ K := fun w hw => hK _ (hmem w hw)
  have hbound := norm_logDeriv_le_of_abs_log_le hG hG0 hGK
    (show (0 : ℝ) ≤ 0 from le_rfl) hs (z := 0) (by simp)
  have hderiv : deriv G 0 = deriv g c := by
    have hgc := (hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hs))).hasDerivAt
    have hgc' : HasDerivAt g (deriv g c) (c + (0 : ℂ)) := by simpa using hgc
    have hd := hgc'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add c)
    simpa only [G, Function.comp_def, add_zero, mul_one] using hd.deriv
  rw [hderiv] at hbound
  simp only [G, add_zero, sub_zero] at hbound
  refine hbound.trans_eq ?_
  field_simp [hs.ne']

namespace DivisorFactorData

/-- The selected logarithm has exactly the log norm of its own zero-free
factor as real part, throughout the open extraction disk. -/
theorem re_H_eq_log_norm {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) : (D.H z).re = log ‖D.g z‖ := by
  rw [← D.exp_H z hz, Complex.norm_exp, Real.log_exp]

/-- The same logarithm differentiates to its own factor's genuine
logarithmic derivative. No raw singular values of F are evaluated. -/
theorem deriv_H_eq_logDeriv_g {F : ℂ → ℂ} {ρ : ℝ} (D : DivisorFactorData F ρ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) : deriv D.H z = deriv D.g z / D.g z := by
  have heq : D.g =ᶠ[𝓝 z] fun w => Complex.exp (D.H w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using (D.exp_H w hw).symm
  have hH := (D.H_analytic z hz).differentiableAt.hasDerivAt
  rw [heq.deriv_eq, hH.cexp.deriv, ← D.exp_H z hz]
  field_simp [Complex.exp_ne_zero]

/-- The actual boundary proximity of the extracted factor is bounded by
the two original characteristics at a single outer radius. -/
theorem proximity_pair_le_characteristics {F : ℂ → ℂ} {ρ R : ℝ}
    (D : DivisorFactorData F ρ) (hF : MeromorphicOn F univ)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) :
    circleAverage (fun z => log⁺ ‖D.g z‖) 0 ρ +
      circleAverage (fun z => log⁺ ‖(D.g z)⁻¹‖) 0 ρ ≤
      ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R +
        2 * (∑ α ∈ D.support, |(D.exponent α : ℝ)|) * (log ρ + 2) := by
  have hbase := proximity_factor_le (fun z => hF z (mem_univ z)) hρ D.roots
    D.g_analytic D.log_norm
  have hρpos : 0 < ρ := by linarith
  have hFmono := characteristic_top_mono (fun z => hF z (mem_univ z)) hρpos hρR
  have hFimono := characteristic_top_mono (fun z => (hF z (mem_univ z)).inv) hρpos hρR
  have hpF : circleAverage (fun z => log⁺ ‖F z‖) 0 ρ ≤
      ValueDistribution.characteristic F ⊤ ρ := by
    simp only [ValueDistribution.characteristic, Pi.add_apply, ValueDistribution.proximity_top]
    linarith [ValueDistribution.logCounting_nonneg (f := F) (e := ⊤) hρ]
  have hpFi : circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ ≤
      ValueDistribution.characteristic F⁻¹ ⊤ ρ := by
    simpa only [Pi.inv_apply, norm_inv] using
      (show circleAverage (fun z => log⁺ ‖F⁻¹ z‖) 0 ρ ≤
        ValueDistribution.characteristic F⁻¹ ⊤ ρ by
          simp only [ValueDistribution.characteristic, Pi.add_apply, ValueDistribution.proximity_top]
          linarith [ValueDistribution.logCounting_nonneg (f := F⁻¹) (e := ⊤) hρ])
  linarith

/-- Uniform real-part control at distance epsilon from the extraction
boundary, derived from the original characteristic and integer divisors. -/
theorem abs_re_H_le_characteristic_gap {F : ℂ → ℂ} {ρ R ε : ℝ}
    (D : DivisorFactorData F ρ) (hF : MeromorphicOn F univ)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ ρ - ε) :
    |(D.H z).re| ≤ 2 * ρ / ε *
      (ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R +
        2 * (∑ α ∈ D.support, |(D.exponent α : ℝ)|) * (log ρ + 2)) := by
  have hρpos : 0 < ρ := by linarith
  have hzρ : ‖z‖ < ρ := by linarith
  have hzb : z ∈ ball (0 : ℂ) ρ := by simpa only [mem_ball, dist_zero_right] using hzρ
  rw [D.re_H_eq_log_norm hzb]
  have hpoisson := abs_log_norm_le_poisson hρpos D.g_analytic D.g_ne_zero hzρ
  have hbudget := D.proximity_pair_le_characteristics hF hρ hρR
  have hratio : (ρ + ‖z‖) / (ρ - ‖z‖) ≤ 2 * ρ / ε := by
    apply (div_le_div_iff₀ (by linarith : 0 < ρ - ‖z‖) hε).mpr
    nlinarith [norm_nonneg z]
  have havg : 0 ≤ circleAverage (fun z => log⁺ ‖D.g z‖) 0 ρ +
      circleAverage (fun z => log⁺ ‖(D.g z)⁻¹‖) 0 ρ :=
    add_nonneg (circleAverage_nonneg_of_nonneg (fun _ _ => posLog_nonneg))
      (circleAverage_nonneg_of_nonneg (fun _ _ => posLog_nonneg))
  exact hpoisson.trans ((mul_le_mul_of_nonneg_right hratio havg).trans
    (mul_le_mul_of_nonneg_left hbudget (by positivity)))

/-- A local derivative bound for the same extracted logarithm. Its
dependence on the gap is quadratic after substituting the real-part bound. -/
theorem norm_deriv_H_le_characteristic_gap {F : ℂ → ℂ} {ρ R ε : ℝ}
    (D : DivisorFactorData F ρ) (hF : MeromorphicOn F univ)
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ ρ - 2 * ε) :
    ‖deriv D.H z‖ ≤ 8 * (2 * (2 * ρ / ε *
      (ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R +
        2 * (∑ α ∈ D.support, |(D.exponent α : ℝ)|) * (log ρ + 2))) + 5) / ε := by
  have hsub : ball z ε ⊆ ball (0 : ℂ) ρ := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have hn := norm_le_norm_add_norm_sub' w z
    linarith
  have hK : ∀ w ∈ ball z ε, |log ‖D.g w‖| ≤ 2 * ρ / ε *
      (ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R +
        2 * (∑ α ∈ D.support, |(D.exponent α : ℝ)|) * (log ρ + 2)) := by
    intro w hw
    rw [← D.re_H_eq_log_norm (hsub hw)]
    apply D.abs_re_H_le_characteristic_gap hF hρ hρR hε
    have hn := norm_le_norm_add_norm_sub' w z
    rw [mem_ball, dist_eq_norm] at hw
    linarith
  have hg : DifferentiableOn ℂ D.g (ball z ε) := by
    intro w hw
    exact (D.g_analytic w (ball_subset_closedBall (hsub hw))).differentiableAt.differentiableWithinAt
  have hzero : ∀ w ∈ ball z ε, D.g w ≠ 0 :=
    fun w hw => D.g_ne_zero w (ball_subset_closedBall (hsub hw))
  have hzb : z ∈ ball (0 : ℂ) ρ := hsub (mem_ball_self hε)
  rw [D.deriv_H_eq_logDeriv_g hzb]
  exact norm_logDeriv_le_of_abs_log_le_centered hε hg hzero hK

end DivisorFactorData
end ThreeIM
