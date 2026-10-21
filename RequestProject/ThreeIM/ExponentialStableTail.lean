module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Complex.RealDeriv

/-! # The bounded tail convolution used for the stable graph

The integral is defined pointwise. No strong continuity or measurability
of translations with values in the full bounded-continuous-function space
is assumed. Continuity of the output follows from scalar dominated
convergence with a fixed integrable exponential majorant.
-/

@[expose] public section

open Filter Set MeasureTheory Topology
open scoped Topology NNReal BoundedContinuousFunction

namespace ThreeIM

set_option autoImplicit false

theorem stableTail_exp_integrable {rate : ℝ} (hRate : 0 < rate) :
    IntegrableOn (fun s : ℝ => Real.exp (-rate * s)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hRate) 0

theorem stableTail_exp_integral {rate : ℝ} (hRate : 0 < rate) :
    (∫ s : ℝ in Ici 0, Real.exp (-rate * s)) = 1 / rate := by
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_iff_pos.mpr hRate)]
  simp

noncomputable def stableTailRealValue (rate : ℝ) (h : ℝ →ᵇ ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * h (t + s)

theorem stableTailReal_kernel_bound (rate : ℝ) (h : ℝ →ᵇ ℂ) (t s : ℝ) :
    ‖(Real.exp (-rate * s) : ℂ) * h (t + s)‖ ≤ Real.exp (-rate * s) * ‖h‖ := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm (t + s)) (Real.exp_pos _).le

theorem stableTailReal_kernel_integrable {rate : ℝ} (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) (t : ℝ) :
    IntegrableOn (fun s : ℝ => (Real.exp (-rate * s) : ℂ) * h (t + s)) (Ici 0) := by
  have hc : Continuous (fun s : ℝ => (Real.exp (-rate * s) : ℂ) * h (t + s)) := by
    have hh : Continuous h := h.continuous
    fun_prop
  exact ((stableTail_exp_integrable hRate).mul_const ‖h‖).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (stableTailReal_kernel_bound rate h t))

theorem stableTailReal_continuous {rate : ℝ} (hRate : 0 < rate) (h : ℝ →ᵇ ℂ) :
    Continuous (stableTailRealValue rate h) := by
  apply continuous_of_dominated (μ := volume.restrict (Ici (0 : ℝ)))
    (bound := fun s => Real.exp (-rate * s) * ‖h‖)
  · intro t
    exact (stableTailReal_kernel_integrable hRate h t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (stableTailReal_kernel_bound rate h t)
  · exact (stableTail_exp_integrable hRate).mul_const ‖h‖
  · exact Filter.Eventually.of_forall fun s => continuous_const.mul
      (h.continuous.comp (continuous_id.add continuous_const))

theorem stableTailReal_value_norm_le {rate : ℝ} (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) (t : ℝ) : ‖stableTailRealValue rate h t‖ ≤ ‖h‖ / rate := by
  calc
    ‖stableTailRealValue rate h t‖ ≤
        ∫ s : ℝ in Ici 0, ‖(Real.exp (-rate * s) : ℂ) * h (t + s)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ici 0, Real.exp (-rate * s) * ‖h‖ :=
      integral_mono_ae (stableTailReal_kernel_integrable hRate h t).norm
        ((stableTail_exp_integrable hRate).mul_const ‖h‖)
        (Filter.Eventually.of_forall (stableTailReal_kernel_bound rate h t))
    _ = ‖h‖ / rate := by
      rw [integral_mul_const, stableTail_exp_integral hRate]
      ring

noncomputable def stableTailRealBounded (rate : ℝ) (hRate : 0 < rate)
    (h : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (stableTailRealValue rate h)
    (stableTailReal_continuous hRate h) (‖h‖ / rate) (stableTailReal_value_norm_le hRate h)

theorem stableTailRealBounded_norm_le {rate : ℝ} (hRate : 0 < rate) (h : ℝ →ᵇ ℂ) :
    ‖stableTailRealBounded rate hRate h‖ ≤ ‖h‖ / rate :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (stableTailReal_continuous hRate h) (div_nonneg (norm_nonneg h) hRate.le)
    (stableTailReal_value_norm_le hRate h)

noncomputable def stableTailRealLinear (rate : ℝ) (hRate : 0 < rate) :
    (ℝ →ᵇ ℂ) →ₗ[ℂ] (ℝ →ᵇ ℂ) where
  toFun := stableTailRealBounded rate hRate
  map_add' h k := by
    ext t
    change (∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * (h + k) (t + s)) =
      (∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * h (t + s)) +
        ∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * k (t + s)
    simp_rw [BoundedContinuousFunction.add_apply, mul_add]
    exact integral_add (stableTailReal_kernel_integrable hRate h t)
      (stableTailReal_kernel_integrable hRate k t)
  map_smul' c h := by
    ext t
    change (∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * (c • h) (t + s)) =
      c * ∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * h (t + s)
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
    calc
      (∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * (c * h (t + s))) =
          ∫ s : ℝ in Ici 0, c * ((Real.exp (-rate * s) : ℂ) * h (t + s)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by ring
      _ = _ := integral_const_mul c _

/-- Tail convolution on the full real line, bundled as a complex continuous
linear operator. -/
noncomputable def stableTailReal (rate : ℝ) (hRate : 0 < rate) :
    (ℝ →ᵇ ℂ) →L[ℂ] (ℝ →ᵇ ℂ) :=
  (stableTailRealLinear rate hRate).mkContinuous (1 / rate) (fun h => by
    change ‖stableTailRealBounded rate hRate h‖ ≤ (1 / rate) * ‖h‖
    exact (stableTailRealBounded_norm_le hRate h).trans_eq (by ring))

theorem stableTailReal_apply (rate : ℝ) (hRate : 0 < rate) (h : ℝ →ᵇ ℂ) (t : ℝ) :
    stableTailReal rate hRate h t =
      ∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * h (t + s) := rfl

theorem norm_stableTailReal_le (rate : ℝ) (hRate : 0 < rate) :
    ‖stableTailReal rate hRate‖ ≤ 1 / rate := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  change ‖stableTailRealBounded rate hRate h‖ ≤ (1 / rate) * ‖h‖
  exact (stableTailRealBounded_norm_le hRate h).trans_eq (by ring)

noncomputable def stableTailPrecomp {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (g : C(α, β)) :
    (β →ᵇ ℂ) →L[ℂ] (α →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun h => h.compContinuous g
      map_add' := fun h k => by ext t; rfl
      map_smul' := fun c h => by ext t; rfl }
    1 (fun h => by
      change ‖h.compContinuous g‖ ≤ 1 * ‖h‖
      simpa only [one_mul] using h.norm_compContinuous_le g)

noncomputable def stableTailExtend : (ℝ≥0 →ᵇ ℂ) →L[ℂ] (ℝ →ᵇ ℂ) :=
  stableTailPrecomp ⟨Real.toNNReal, by fun_prop⟩

noncomputable def stableTailRestrict : (ℝ →ᵇ ℂ) →L[ℂ] (ℝ≥0 →ᵇ ℂ) :=
  stableTailPrecomp ⟨fun t : ℝ≥0 => (t : ℝ), by fun_prop⟩

/-- The tail operator on nonnegative time, with the exact domain used by
the weighted stable-graph fixed-point equation. -/
noncomputable def stableTail (rate : ℝ) (hRate : 0 < rate) :
    (ℝ≥0 →ᵇ ℂ) →L[ℂ] (ℝ≥0 →ᵇ ℂ) :=
  stableTailRestrict.comp ((stableTailReal rate hRate).comp stableTailExtend)

theorem stableTail_apply (rate : ℝ) (hRate : 0 < rate) (h : ℝ≥0 →ᵇ ℂ) (t : ℝ≥0) :
    stableTail rate hRate h t =
      ∫ s : ℝ in Ici 0, (Real.exp (-rate * s) : ℂ) * h (t + Real.toNNReal s) := by
  change (∫ s : ℝ in Ici 0,
    (Real.exp (-rate * s) : ℂ) * h (Real.toNNReal ((t : ℝ) + s))) = _
  apply setIntegral_congr_fun measurableSet_Ici
  intro s hs
  have he : Real.toNNReal ((t : ℝ) + s) = t + Real.toNNReal s := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (add_nonneg t.coe_nonneg hs), NNReal.coe_add,
      Real.coe_toNNReal _ hs]
  change (Real.exp (-rate * s) : ℂ) * h (Real.toNNReal ((t : ℝ) + s)) =
    (Real.exp (-rate * s) : ℂ) * h (t + Real.toNNReal s)
  rw [he]

theorem norm_stableTail_le (rate : ℝ) (hRate : 0 < rate) : ‖stableTail rate hRate‖ ≤ 1 / rate := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  have hext : ‖stableTailExtend h‖ ≤ ‖h‖ :=
    h.norm_compContinuous_le ⟨Real.toNNReal, by fun_prop⟩
  have hrest : ‖stableTail rate hRate h‖ ≤ ‖stableTailReal rate hRate (stableTailExtend h)‖ :=
    (stableTailReal rate hRate (stableTailExtend h)).norm_compContinuous_le
      ⟨fun t : ℝ≥0 => (t : ℝ), by fun_prop⟩
  exact hrest.trans (((stableTailReal rate hRate).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_stableTailReal_le rate hRate) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hext (by positivity))))

/-- A bounded solution of the unstable linear equation has the genuine
tail representation. No decay estimate is added as an assumption. -/
theorem stableTailReal_variation_of_constants (rate : ℝ) (hRate : 0 < rate)
    (w q : ℝ →ᵇ ℂ)
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt w ((rate : ℂ) * w t + q t) t)
    (t : ℝ) (ht : 0 ≤ t) : w t = -stableTailReal rate hRate q t := by
  let f : ℝ → ℂ := fun s => (Real.exp (-rate * s) : ℂ) * w (t + s)
  have hc : Continuous f := by
    have hwc : Continuous w := w.continuous
    dsimp only [f]
    fun_prop
  have hd : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt f
      ((Real.exp (-rate * s) : ℂ) * q (t + s)) s := by
    intro s hs
    have he := (((hasDerivAt_id s).const_mul (-rate)).exp).ofReal_comp
    simp only [id_eq, mul_one, Complex.ofReal_mul] at he
    have hshift : HasDerivAt (fun x : ℝ => t + x) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add t
    have hws : HasDerivAt (fun x : ℝ => w (t + x))
        ((rate : ℂ) * w (t + s) + q (t + s)) s := by
      simpa only [Function.comp_def, one_smul] using
        (hw (t + s) (add_pos_of_nonneg_of_pos ht hs)).scomp s hshift
    convert he.mul hws using 1 <;> push_cast <;> ring
  have hexp : Tendsto (fun s : ℝ => Real.exp (-rate * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hRate))
  have hupper : Tendsto (fun s : ℝ => Real.exp (-rate * s) * ‖w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hexp.mul_const ‖w‖
  have hlim : Tendsto f atTop (𝓝 (0 : ℂ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
      (Filter.Eventually.of_forall fun s => norm_nonneg (f s))
      (Filter.Eventually.of_forall (stableTailReal_kernel_bound rate w t)) hupper)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    hc.continuousAt.continuousWithinAt hd
    ((stableTailReal_kernel_integrable hRate q t).mono_set Ioi_subset_Ici_self) hlim
  have htail : stableTailReal rate hRate q t = -w t := by
    rw [stableTailReal_apply, integral_Ici_eq_integral_Ioi]
    simpa only [f, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul, add_zero, zero_sub]
      using hFTC
  simpa only [neg_neg] using (congrArg Neg.neg htail).symm

/-- The same tail formula on nonnegative time. The derivative premise is
the ordinary real reading of the bounded continuous half-line function. -/
theorem stableTail_variation_of_constants (rate : ℝ) (hRate : 0 < rate)
    (w q : ℝ≥0 →ᵇ ℂ)
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
      ((rate : ℂ) * w (Real.toNNReal t) + q (Real.toNNReal t)) t)
    (t : ℝ≥0) : w t = -stableTail rate hRate q t := by
  have h := stableTailReal_variation_of_constants rate hRate
    (stableTailExtend w) (stableTailExtend q) hw (t : ℝ) t.coe_nonneg
  change w (Real.toNNReal (t : ℝ)) =
    -stableTailReal rate hRate (stableTailExtend q) (t : ℝ) at h
  change w t = -stableTailReal rate hRate (stableTailExtend q) (t : ℝ)
  simpa only [Real.toNNReal_coe] using h

end ThreeIM
