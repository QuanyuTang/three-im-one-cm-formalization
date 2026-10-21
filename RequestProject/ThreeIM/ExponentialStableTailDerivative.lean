module

public import RequestProject.ThreeIM.ExponentialStableTail
public import Mathlib.MeasureTheory.Group.Integral

/-! # Differentiating the bounded tail convolution

The variable is moved into the lower integration endpoint before applying
the fundamental theorem of calculus. The input is only continuous; its
derivative and strong continuity of translations in the BCF norm are unused.
-/

@[expose] public section

open Filter Set MeasureTheory Topology
open scoped Topology NNReal BoundedContinuousFunction

namespace ThreeIM

set_option autoImplicit false

theorem stableTail_weighted_integrable {rate : ℝ} (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) (t : ℝ) :
    IntegrableOn (fun s : ℝ => (Real.exp (-rate * s) : ℂ) * h s) (Ioi t) := by
  have hc : Continuous (fun s : ℝ => (Real.exp (-rate * s) : ℂ) * h s) := by
    have hh : Continuous h := h.continuous
    fun_prop
  refine ((integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hRate) t).mul_const ‖h‖).mono'
    hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s => by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm s) (Real.exp_pos _).le

theorem stableTailReal_eq_exp_mul_integral (rate : ℝ) (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) (t : ℝ) :
    stableTailReal rate hRate h t = (Real.exp (rate * t) : ℂ) *
      ∫ s : ℝ in Ioi t, (Real.exp (-rate * s) : ℂ) * h s := by
  let k : ℝ → ℂ := fun s => (Real.exp (-rate * s) : ℂ) * h s
  have hp : (fun s : ℝ => t + s) ⁻¹' Ioi t = Ioi 0 := by
    ext s
    simp only [mem_preimage, mem_Ioi, lt_add_iff_pos_right]
  have hshift := (measurePreserving_add_left volume t).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding k (Ioi t)
  rw [hp] at hshift
  have hfactor : (∫ s : ℝ in Ioi 0, k (t + s)) =
      (Real.exp (-rate * t) : ℂ) * stableTailReal rate hRate h t := by
    rw [stableTailReal_apply, integral_Ici_eq_integral_Ioi, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    dsimp only [k]
    rw [show -rate * (t + s) = -rate * t + -rate * s by ring,
      Real.exp_add, Complex.ofReal_mul]
    ring
  have hexp : (Real.exp (rate * t) : ℂ) * (Real.exp (-rate * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  calc
    stableTailReal rate hRate h t = (Real.exp (rate * t) : ℂ) *
        ((Real.exp (-rate * t) : ℂ) * stableTailReal rate hRate h t) := by
      rw [← mul_assoc, hexp, one_mul]
    _ = _ := by rw [← hfactor, hshift]

/-- The full-line bounded tail solves its differential equation for every
real time, even when its input is merely continuous. -/
theorem stableTailReal_hasDerivAt (rate : ℝ) (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stableTailReal rate hRate h s)
      ((rate : ℂ) * stableTailReal rate hRate h t - h t) t := by
  let k : ℝ → ℂ := fun s => (Real.exp (-rate * s) : ℂ) * h s
  let C : ℂ := ∫ s : ℝ in Ioi 0, k s
  have hc : Continuous k := by
    have hh : Continuous h := h.continuous
    dsimp only [k]
    fun_prop
  have hrepr : ∀ x : ℝ, stableTailReal rate hRate h x =
      (Real.exp (rate * x) : ℂ) * (C - ∫ s : ℝ in 0..x, k s) := by
    intro x
    rw [stableTailReal_eq_exp_mul_integral]
    congr 1
    have hi := intervalIntegral.integral_interval_add_Ioi
      (stableTail_weighted_integrable hRate h 0) (stableTail_weighted_integrable hRate h x)
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hi)
  have he := (((hasDerivAt_id t).const_mul rate).exp).ofReal_comp
  simp only [id_eq, mul_one, Complex.ofReal_mul] at he
  have hi := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd := (he.mul ((hasDerivAt_const t C).sub hi)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hrepr)
  have hexp : (Real.exp (rate * t) : ℂ) * (Real.exp (-rate * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  convert hd using 1
  change (rate : ℂ) * stableTailReal rate hRate h t - h t =
    ((Real.exp (rate * t) : ℂ) * (rate : ℂ)) * (C - ∫ s : ℝ in 0..t, k s) +
      (Real.exp (rate * t) : ℂ) * (0 - k t)
  rw [hrepr t, show k t = (Real.exp (-rate * t) : ℂ) * h t from rfl]
  calc
    (rate : ℂ) * ((Real.exp (rate * t) : ℂ) * (C - ∫ s : ℝ in 0..t, k s)) - h t =
        ((rate : ℂ) * (Real.exp (rate * t) : ℂ)) * (C - ∫ s : ℝ in 0..t, k s) -
          ((Real.exp (rate * t) : ℂ) * (Real.exp (-rate * t) : ℂ)) * h t := by
      rw [hexp]
      ring
    _ = _ := by ring

/-- Positive-time derivative of the half-line tail, read as an ordinary
real-variable function. -/
theorem stableTail_hasDerivAt (rate : ℝ) (hRate : 0 < rate)
    (h : ℝ≥0 →ᵇ ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => stableTail rate hRate h (Real.toNNReal s))
      ((rate : ℂ) * stableTail rate hRate h (Real.toNNReal t) - h (Real.toNNReal t)) t := by
  have heq : (fun s : ℝ => stableTail rate hRate h (Real.toNNReal s)) =ᶠ[𝓝 t]
      (fun s : ℝ => stableTailReal rate hRate (stableTailExtend h) s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change stableTailReal rate hRate (stableTailExtend h) (Real.toNNReal s : ℝ) = _
    rw [Real.coe_toNNReal _ hs.le]
  have hd := (stableTailReal_hasDerivAt rate hRate (stableTailExtend h) t).congr_of_eventuallyEq heq
  convert hd using 1
  change (rate : ℂ) * stableTail rate hRate h (Real.toNNReal t) - h (Real.toNNReal t) =
    (rate : ℂ) * stableTailReal rate hRate (stableTailExtend h) t - h (Real.toNNReal t)
  have hcenter : stableTail rate hRate h (Real.toNNReal t) =
      stableTailReal rate hRate (stableTailExtend h) t := heq.self_of_nhds
  rw [hcenter]

end ThreeIM
