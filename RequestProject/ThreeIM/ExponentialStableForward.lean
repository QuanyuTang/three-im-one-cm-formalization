module

public import RequestProject.ThreeIM.ExponentialStableTailWeights
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Forward exponential convolution on bounded trajectories

The integration variable is real. A trajectory is defined on the nonnegative real
axis, and its continuous extension in the integral is obtained by `Real.toNNReal`.
No continuity of the translation action on the space of bounded continuous
functions is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology NNReal BoundedContinuousFunction

namespace ThreeIM

theorem norm_expDecay_le_one {rate : ℝ} (hRate : 0 ≤ rate) (t : ℝ≥0) :
    ‖(Real.exp (-rate * (t : ℝ)) : ℂ)‖ ≤ 1 :=
  stableTailDecay_value_norm_le rate hRate t

/-- The same verified bounded weight used by the tail convolution. -/
noncomputable def expDecayBCF (rate : ℝ) (hRate : 0 ≤ rate) : ℝ≥0 →ᵇ ℂ :=
  stableTailDecay rate hRate

theorem expDecayBCF_apply (rate : ℝ) (hRate : 0 ≤ rate) (t : ℝ≥0) :
    expDecayBCF rate hRate t = (Real.exp (-rate * (t : ℝ)) : ℂ) := rfl

theorem norm_expDecayBCF_le (rate : ℝ) (hRate : 0 ≤ rate) :
    ‖expDecayBCF rate hRate‖ ≤ 1 := norm_stableTailDecay_le rate hRate

theorem expDecayBCF_zero (rate : ℝ) (hRate : 0 ≤ rate) :
    expDecayBCF rate hRate 0 = 1 := by simp [expDecayBCF_apply]

theorem expDecayBCF_add (rate weight : ℝ) (hRate : 0 ≤ rate) (hWeight : 0 ≤ weight) :
    expDecayBCF (rate + weight) (add_nonneg hRate hWeight) =
      expDecayBCF rate hRate * expDecayBCF weight hWeight := by
  ext t
  simp only [BoundedContinuousFunction.mul_apply, expDecayBCF_apply]
  rw [show -(rate + weight) * (t : ℝ) = -rate * (t : ℝ) + -weight * (t : ℝ) by ring,
    Real.exp_add, Complex.ofReal_mul]

noncomputable def forwardExpIntegral (μ : ℝ) (h : ℝ≥0 →ᵇ ℂ) (t : ℝ≥0) : ℂ :=
  (Real.exp (-μ * (t : ℝ)) : ℂ) *
    ∫ s : ℝ in 0..(t : ℝ), (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)

theorem continuous_forward_integrand (μ : ℝ) (h : ℝ≥0 →ᵇ ℂ) :
    Continuous (fun s : ℝ => (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).mul
    (h.continuous.comp continuous_real_toNNReal)

theorem continuous_forwardExpIntegral (μ : ℝ) (h : ℝ≥0 →ᵇ ℂ) :
    Continuous (forwardExpIntegral μ h) := by
  have hp : Continuous (fun r : ℝ =>
      ∫ s : ℝ in 0..r, (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact (HasStrictDerivAt.hasDerivAt
      ((continuous_forward_integrand μ h).integral_hasStrictDerivAt 0 r)).continuousAt
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_subtype_val))).mul (hp.comp continuous_subtype_val)

theorem real_exp_interval_integral {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    (∫ s : ℝ in 0..t, Real.exp (μ * s)) = (Real.exp (μ * t) - 1) / μ := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hμ.ne', mul_zero,
    _root_.integral_exp, Real.exp_zero]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem norm_forwardExpIntegral_le {μ : ℝ} (hμ : 0 < μ) (h : ℝ≥0 →ᵇ ℂ)
    (t : ℝ≥0) : ‖forwardExpIntegral μ h t‖ ≤ μ⁻¹ * ‖h‖ := by
  have hcont := continuous_forward_integrand μ h
  have hreal : Continuous (fun s : ℝ => Real.exp (μ * s) * ‖h‖) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const
  have hint :
      (∫ s : ℝ in 0..(t : ℝ),
        ‖(Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)‖) ≤
      (∫ s : ℝ in 0..(t : ℝ), Real.exp (μ * s) * ‖h‖) := by
    apply intervalIntegral.integral_mono_on t.coe_nonneg
      (hcont.norm.intervalIntegrable _ _) (hreal.intervalIntegrable _ _)
    intro s _
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm _) (Real.exp_pos _).le
  have he : Real.exp (-μ * (t : ℝ)) * Real.exp (μ * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hcoeff : Real.exp (-μ * (t : ℝ)) *
      ((Real.exp (μ * (t : ℝ)) - 1) / μ) ≤ μ⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_sub, he, mul_one]
    exact mul_le_of_le_one_left (inv_nonneg.mpr hμ.le)
      (sub_le_self _ (Real.exp_pos _).le)
  calc
    ‖forwardExpIntegral μ h t‖ = Real.exp (-μ * (t : ℝ)) *
        ‖∫ s : ℝ in 0..(t : ℝ),
          (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)‖ := by
      simp only [forwardExpIntegral, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (-μ * (t : ℝ)) *
        (∫ s : ℝ in 0..(t : ℝ), Real.exp (μ * s) * ‖h‖) :=
      mul_le_mul_of_nonneg_left
        ((intervalIntegral.norm_integral_le_integral_norm t.coe_nonneg).trans hint)
        (Real.exp_pos _).le
    _ = (Real.exp (-μ * (t : ℝ)) *
        ((Real.exp (μ * (t : ℝ)) - 1) / μ)) * ‖h‖ := by
      rw [intervalIntegral.integral_mul_const, real_exp_interval_integral hμ, mul_assoc]
    _ ≤ μ⁻¹ * ‖h‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)

/-- The stable forward convolution, as a complex continuous linear map. -/
noncomputable def forwardExpCLM (μ : ℝ) (hμ : 0 < μ) :
    (ℝ≥0 →ᵇ ℂ) →L[ℂ] (ℝ≥0 →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun h => BoundedContinuousFunction.ofNormedAddCommGroup
        (forwardExpIntegral μ h) (continuous_forwardExpIntegral μ h)
        (μ⁻¹ * ‖h‖) (norm_forwardExpIntegral_le hμ h)
      map_add' := fun h k => by
        ext t
        change forwardExpIntegral μ (h + k) t =
          forwardExpIntegral μ h t + forwardExpIntegral μ k t
        simp only [forwardExpIntegral, BoundedContinuousFunction.add_apply, mul_add]
        rw [intervalIntegral.integral_add
          ((continuous_forward_integrand μ h).intervalIntegrable _ _)
          ((continuous_forward_integrand μ k).intervalIntegrable _ _), mul_add]
      map_smul' := fun c h => by
        ext t
        change forwardExpIntegral μ (c • h) t = c * forwardExpIntegral μ h t
        simp only [forwardExpIntegral, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        have heq : (fun s : ℝ =>
            (Real.exp (μ * s) : ℂ) * (c * h (Real.toNNReal s))) =
            (fun s : ℝ => c * ((Real.exp (μ * s) : ℂ) * h (Real.toNNReal s))) := by
          funext s
          ring
        rw [heq]
        rw [intervalIntegral.integral_const_mul]
        ring }
    μ⁻¹ fun h => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _))
      (norm_forwardExpIntegral_le hμ h)

theorem forwardExpCLM_apply (μ : ℝ) (hμ : 0 < μ) (h : ℝ≥0 →ᵇ ℂ) (t : ℝ≥0) :
    forwardExpCLM μ hμ h t = (Real.exp (-μ * (t : ℝ)) : ℂ) *
      ∫ s : ℝ in 0..(t : ℝ), (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s) := rfl

theorem norm_forwardExpCLM_le (μ : ℝ) (hμ : 0 < μ) :
    ‖forwardExpCLM μ hμ‖ ≤ μ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro h
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _))
    (norm_forwardExpIntegral_le hμ h)

theorem forwardExpCLM_zero (μ : ℝ) (hμ : 0 < μ) (h : ℝ≥0 →ᵇ ℂ) :
    forwardExpCLM μ hμ h 0 = 0 := by
  simp [forwardExpCLM_apply]

end ThreeIM
