module

public import RequestProject.ThreeIM.ExponentialStableTail

/-! # Exponential weights for the bounded tail convolution

The identity below changes the convolution rate rather than assuming decay
of a bounded solution. It is useful when the forcing is an actual decaying
exponential times a bounded nonlinear remainder.
-/

@[expose] public section

open Filter Set MeasureTheory Topology
open scoped Topology NNReal BoundedContinuousFunction

namespace ThreeIM

set_option autoImplicit false

theorem stableTailDecay_continuous (weight : ℝ) :
    Continuous (fun t : ℝ≥0 => (Real.exp (-weight * (t : ℝ)) : ℂ)) := by
  fun_prop

theorem stableTailDecay_value_norm_le (weight : ℝ) (hWeight : 0 ≤ weight) (t : ℝ≥0) :
    ‖(Real.exp (-weight * (t : ℝ)) : ℂ)‖ ≤ 1 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hWeight) t.coe_nonneg

noncomputable def stableTailDecay (weight : ℝ) (hWeight : 0 ≤ weight) : ℝ≥0 →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ≥0 => (Real.exp (-weight * (t : ℝ)) : ℂ))
    (stableTailDecay_continuous weight) 1 (stableTailDecay_value_norm_le weight hWeight)

theorem stableTailDecay_apply (weight : ℝ) (hWeight : 0 ≤ weight) (t : ℝ≥0) :
    stableTailDecay weight hWeight t = (Real.exp (-weight * (t : ℝ)) : ℂ) := rfl

theorem norm_stableTailDecay_le (weight : ℝ) (hWeight : 0 ≤ weight) :
    ‖stableTailDecay weight hWeight‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (stableTailDecay_continuous weight) zero_le_one
    (stableTailDecay_value_norm_le weight hWeight)

/-- Multiplying the forcing by a decaying exponential changes the tail rate
and leaves precisely the same exponential at the evaluation point. -/
theorem stableTail_weight_mul (rate weight : ℝ) (hRate : 0 < rate) (hWeight : 0 ≤ weight)
    (h : ℝ≥0 →ᵇ ℂ) (t : ℝ≥0) :
    stableTail rate hRate (stableTailDecay weight hWeight * h) t =
      (Real.exp (-weight * (t : ℝ)) : ℂ) *
        stableTail (rate + weight) (add_pos_of_pos_of_nonneg hRate hWeight) h t := by
  rw [stableTail_apply, stableTail_apply, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro s hs
  simp only [BoundedContinuousFunction.mul_apply, stableTailDecay_apply]
  have hsum : ((t + Real.toNNReal s : ℝ≥0) : ℝ) = (t : ℝ) + s := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs]
  rw [hsum,
    show -weight * ((t : ℝ) + s) = -weight * (t : ℝ) + -weight * s by ring,
    Real.exp_add, Complex.ofReal_mul,
    show -(rate + weight) * s = -rate * s + -weight * s by ring,
    Real.exp_add, Complex.ofReal_mul]
  ring

end ThreeIM
