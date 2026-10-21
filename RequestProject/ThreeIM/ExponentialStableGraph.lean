module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import RequestProject.ThreeIM.ExponentialStableForward
public import RequestProject.ThreeIM.ExponentialStableTail
public import RequestProject.ThreeIM.ExponentialStableTailWeights
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consolidated stable-expansion foundations

The declarations below retain the exact mathematical bodies of the
unverified draft modules archived in the external audit directory.
This grouping reduces repeated loading of their common imports.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
open Set
open Filter Topology
open scoped Topology
open Filter Topology
open scoped Topology
open Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace ThreeIM

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-! ## Declarations from ExponentialStableForwardDerivative -/


noncomputable def forwardExpRealValue (μ : ℝ) (h : ℝ≥0 →ᵇ ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-μ * t) : ℂ) *
    ∫ s : ℝ in 0..t, (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)

theorem forwardExpRealValue_hasDerivAt (μ : ℝ) (h : ℝ≥0 →ᵇ ℂ) (t : ℝ) :
    HasDerivAt (forwardExpRealValue μ h)
      (-(μ : ℂ) * forwardExpRealValue μ h t + h (Real.toNNReal t)) t := by
  have he : HasDerivAt (fun s : ℝ => (Real.exp (-μ * s) : ℂ))
      (-(μ : ℂ) * (Real.exp (-μ * t) : ℂ)) t := by
    have hd := (((hasDerivAt_id t).const_mul (-μ)).exp).ofReal_comp
    simp only [id_eq, mul_one] at hd
    convert hd using 1 <;>
      push_cast <;> ring
  have hp := ((continuous_forward_integrand μ h).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hcancel : (Real.exp (-μ * t) : ℂ) * (Real.exp (μ * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [show -μ * t + μ * t = 0 by ring]
  convert he.fun_mul hp using 1
  · rfl
  · dsimp only [forwardExpRealValue]
    calc
      _ = -(μ : ℂ) * ((Real.exp (-μ * t) : ℂ) *
          (∫ s : ℝ in 0..t, (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s))) +
          ((Real.exp (-μ * t) : ℂ) * (Real.exp (μ * t) : ℂ)) * h (Real.toNNReal t) := by
        rw [hcancel, one_mul]
      _ = _ := by ring

theorem forwardExpCLM_hasDerivAt (μ : ℝ) (hμ : 0 < μ) (h : ℝ≥0 →ᵇ ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => forwardExpCLM μ hμ h (Real.toNNReal s))
      (-(μ : ℂ) * forwardExpCLM μ hμ h (Real.toNNReal t) + h (Real.toNNReal t)) t := by
  have hev : (fun s : ℝ => forwardExpCLM μ hμ h (Real.toNNReal s)) =ᶠ[𝓝 t]
      forwardExpRealValue μ h := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [forwardExpCLM_apply, Real.coe_toNNReal _ hs.le]
    rfl
  have hd := (forwardExpRealValue_hasDerivAt μ h t).congr_of_eventuallyEq hev
  rw [← hev.self_of_nhds] at hd
  exact hd

theorem forwardExpCLM_variation_of_constants (μ : ℝ) (hμ : 0 < μ)
    (w : ℝ≥0 → ℂ) (hwc : Continuous w) (h : ℝ≥0 →ᵇ ℂ)
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
      (-(μ : ℂ) * w (Real.toNNReal t) + h (Real.toNNReal t)) t)
    (t : ℝ≥0) :
    w t = (Real.exp (-μ * (t : ℝ)) : ℂ) * w 0 + forwardExpCLM μ hμ h t := by
  let z : ℝ → ℂ := fun s => (Real.exp (μ * s) : ℂ) * w (Real.toNNReal s)
  have hzc : Continuous z := by
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul (hwc.comp continuous_real_toNNReal)
  have hzd : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ), HasDerivAt z
      ((Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)) s := by
    intro s hs
    have he := (((hasDerivAt_id s).const_mul μ).exp).ofReal_comp
    simp only [id_eq, mul_one] at he
    convert he.mul (hw s hs.1) using 1 <;> push_cast <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    hzc.continuousOn hzd ((continuous_forward_integrand μ h).intervalIntegrable _ _)
  have hcancel : (Real.exp (-μ * (t : ℝ)) : ℂ) * (Real.exp (μ * (t : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [show -μ * (t : ℝ) + μ * (t : ℝ) = 0 by ring]
  have hFTC' : (∫ s : ℝ in 0..(t : ℝ),
      (Real.exp (μ * s) : ℂ) * h (Real.toNNReal s)) =
      (Real.exp (μ * (t : ℝ)) : ℂ) * w t - w 0 := by
    simpa only [z, Real.toNNReal_coe, mul_zero, Real.exp_zero, Complex.ofReal_one,
      Real.toNNReal_zero, one_mul] using hFTC
  rw [forwardExpCLM_apply, hFTC']
  calc
    w t = ((Real.exp (-μ * (t : ℝ)) : ℂ) * (Real.exp (μ * (t : ℝ)) : ℂ)) * w t := by
      rw [hcancel, one_mul]
    _ = _ := by ring


/-! ## Declarations from ExponentialStableShift -/


noncomputable def stableTimeShift (τ : ℝ≥0) :
    (ℝ≥0 →ᵇ ℂ) →L[ℂ] (ℝ≥0 →ᵇ ℂ) :=
  stableTailPrecomp ⟨fun s : ℝ≥0 => τ + s, by fun_prop⟩

theorem stableTimeShift_apply (τ : ℝ≥0) (h : ℝ≥0 →ᵇ ℂ) (s : ℝ≥0) :
    stableTimeShift τ h s = h (τ + s) := rfl

theorem norm_stableTimeShift_le (τ : ℝ≥0) : ‖stableTimeShift τ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  change ‖h.compContinuous ⟨fun s : ℝ≥0 => τ + s, by fun_prop⟩‖ ≤ 1 * ‖h‖
  simpa only [one_mul] using
    h.norm_compContinuous_le ⟨fun s : ℝ≥0 => τ + s, by fun_prop⟩

noncomputable def stableWeightedTimeShift (weight : ℝ) (hWeight : 0 ≤ weight)
    (τ : ℝ≥0) : (ℝ≥0 →ᵇ ℂ) →L[ℂ] (ℝ≥0 →ᵇ ℂ) :=
  (Real.exp (-weight * (τ : ℝ)) : ℂ) • stableTimeShift τ

theorem stableWeightedTimeShift_apply (weight : ℝ) (hWeight : 0 ≤ weight)
    (τ : ℝ≥0) (h : ℝ≥0 →ᵇ ℂ) (s : ℝ≥0) :
    stableWeightedTimeShift weight hWeight τ h s =
      (Real.exp (-weight * (τ : ℝ)) : ℂ) * h (τ + s) := by
  simp [stableWeightedTimeShift, stableTimeShift_apply, smul_eq_mul]

theorem norm_stableWeightedTimeShift_le (weight : ℝ) (hWeight : 0 ≤ weight)
    (τ : ℝ≥0) : ‖stableWeightedTimeShift weight hWeight τ‖ ≤
      Real.exp (-weight * (τ : ℝ)) := by
  rw [stableWeightedTimeShift, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (norm_stableTimeShift_le τ)
    (Real.exp_pos _).le).trans_eq (mul_one _)

theorem norm_stableWeightedTimeShift_le_one (weight : ℝ) (hWeight : 0 ≤ weight)
    (τ : ℝ≥0) : ‖stableWeightedTimeShift weight hWeight τ‖ ≤ 1 := by
  exact (norm_stableWeightedTimeShift_le weight hWeight τ).trans
    (Real.exp_le_one_iff.mpr (by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hWeight τ.coe_nonneg)))

theorem stableWeightedTimeShift_decay_mul (weight : ℝ) (hWeight : 0 ≤ weight)
    (τ : ℝ≥0) (h : ℝ≥0 →ᵇ ℂ) :
    stableTailDecay weight hWeight * stableWeightedTimeShift weight hWeight τ h =
      stableTimeShift τ (stableTailDecay weight hWeight * h) := by
  ext s
  simp only [BoundedContinuousFunction.mul_apply, stableWeightedTimeShift_apply,
    stableTimeShift_apply, stableTailDecay_apply, NNReal.coe_add]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -weight * (s : ℝ) + -weight * (τ : ℝ) =
    -weight * ((τ : ℝ) + (s : ℝ)) by ring]

theorem stableTail_timeShift (rate : ℝ) (hRate : 0 < rate)
    (τ : ℝ≥0) (h : ℝ≥0 →ᵇ ℂ) :
    stableTail rate hRate (stableTimeShift τ h) =
      stableTimeShift τ (stableTail rate hRate h) := by
  ext t
  simp only [stableTail_apply, stableTimeShift_apply, add_assoc]

theorem stableTail_timeShift_zero (rate : ℝ) (hRate : 0 < rate)
    (τ : ℝ≥0) (h : ℝ≥0 →ᵇ ℂ) :
    stableTail rate hRate (stableTimeShift τ h) 0 = stableTail rate hRate h τ := by
  rw [stableTail_timeShift, stableTimeShift_apply, add_zero]


/-! ## Declarations from ExponentialStableDecay -/


theorem norm_le_exp_of_logDeriv_re_le {u du : ℝ → ℂ} {R rate : ℝ}
    (hd : ∀ t, R ≤ t → HasDerivAt u (du t) t)
    (hu : ∀ t, R ≤ t → u t ≠ 0)
    (hlog : ∀ t, R ≤ t → (du t / u t).re ≤ -rate)
    {s t : ℝ} (hs : R ≤ s) (hst : s ≤ t) :
    ‖u t‖ ≤ ‖u s‖ * Real.exp (-rate * (t - s)) := by
  have hn (x : ℝ) (hx : R ≤ x) :
      HasDerivAt (fun y => ‖u y‖ ^ 2)
        (2 * (‖u x‖ ^ 2 * (du x / u x).re)) x := by
    have h₂ := (hd x hx).norm_sq
    convert h₂ using 2
    rw [Complex.inner]
    have hnorm : ((‖u x‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (u x) * u x := by
      push_cast
      rw [Complex.conj_mul']
    have he : du x * (starRingEnd ℂ) (u x) =
        ((‖u x‖ ^ 2 : ℝ) : ℂ) * (du x / u x) := by
      rw [hnorm]
      field_simp [hu x hx] <;> ring
    rw [he, Complex.re_ofReal_mul]
  let φ : ℝ → ℝ := fun x => Real.exp (2 * rate * x) * ‖u x‖ ^ 2
  have hφ (x : ℝ) (hx : R ≤ x) : HasDerivAt φ
      (2 * Real.exp (2 * rate * x) * ‖u x‖ ^ 2 * (rate + (du x / u x).re)) x := by
    have he := ((hasDerivAt_id x).const_mul (2 * rate)).exp
    simp only [id_eq, mul_one] at he
    convert he.mul (hn x hx) using 1 <;> ring
  have hm : AntitoneOn φ (Ici R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici R)
    · intro x hx
      exact (hφ x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hφ x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hφ x (le_of_lt hx)).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · linarith [hlog x (le_of_lt hx)]
  have hmono : φ t ≤ φ s := hm hs (hs.trans hst) hst
  have heₜ : Real.exp (-(2 * rate * t)) * Real.exp (2 * rate * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have heₛ : Real.exp (-(2 * rate * t)) * Real.exp (2 * rate * s) =
      Real.exp (-rate * (t - s)) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsq : ‖u t‖ ^ 2 ≤ (‖u s‖ * Real.exp (-rate * (t - s))) ^ 2 := by
    calc
      ‖u t‖ ^ 2 = Real.exp (-(2 * rate * t)) *
          (Real.exp (2 * rate * t) * ‖u t‖ ^ 2) := by
        rw [← mul_assoc, heₜ, one_mul]
      _ ≤ Real.exp (-(2 * rate * t)) *
          (Real.exp (2 * rate * s) * ‖u s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
      _ = (‖u s‖ * Real.exp (-rate * (t - s))) ^ 2 := by
        rw [← mul_assoc, heₛ, mul_pow]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).mp hsq


/-! ## Declarations from ExponentialStableImplicit -/


theorem exists_analytic_implicit_graph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E × F → F} {f' : E × F →L[ℂ] F} {a : E} {b : F}
    (hf : AnalyticAt ℂ f (a, b)) (hd : HasFDerivAt f f' (a, b))
    (hbij : Function.Bijective (f'.comp (ContinuousLinearMap.inr ℂ E F))) :
    ∃ φ : E → F, AnalyticAt ℂ φ a ∧ φ a = b ∧
      (∀ᶠ x in 𝓝 a, f (x, φ x) = f (a, b)) ∧
      (∀ᶠ p in 𝓝 (a, b), f p = f (a, b) → φ p.1 = p.2) := by
  have hc : ContDiffAt ℂ ω f (a, b) := hf.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f (a, b) ∘L ContinuousLinearMap.inr ℂ E F).IsInvertible := by
    rw [hd.fderiv]
    exact ⟨ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, hc.eventually_apply_implicitFunction hn hi, ?_⟩
  exact (hc.eventually_apply_eq_iff_implicitFunction hn hi).mono fun p hp h => hp.mp h


/-! ## Declarations from ExponentialStableNonlinear -/


section Algebra

variable {A : Type*} [CommRing A]

def stableDenominator (a κ : A) (p : A × A × A) : A :=
  1 - p.1 * (p.2.2 - κ) * (a + p.2.1)

noncomputable def stableRu (a κ d₀ d₁ μ : A) (p : A × A × A) : A :=
  (-κ * (p.2.2 - κ) * (d₀ + d₁ * p.2.1 + p.2.1 ^ 2) +
    μ * stableDenominator a κ p) * Ring.inverse (stableDenominator a κ p)

noncomputable def stableRw (a κ e₁ e₂ e₃ : A) (p : A × A × A) : A :=
  κ * (p.2.2 - κ) *
    (a + p.2.1 - e₁ + e₂ * p.1 * (p.2.2 - κ) -
      e₃ * p.1 ^ 2 * (p.2.2 - κ) ^ 2) * Ring.inverse (stableDenominator a κ p)

def stableInverseProduct (e₁ e₂ e₃ X v : A) : A :=
  1 - e₁ * X * v + e₂ * X ^ 2 * v ^ 2 - e₃ * X ^ 3 * v ^ 3

theorem stableRu_numerator_decomposition (a κ d₀ d₁ μ : A)
    (hμ : μ = -(κ ^ 2 * d₀)) (X u w : A) :
    -κ * (w - κ) * (d₀ + d₁ * u + u ^ 2) +
      μ * stableDenominator a κ (X, u, w) =
    X * (-μ * (w - κ) * (a + u)) +
      u * (-κ * (w - κ) * (d₁ + u)) + w * (-κ * d₀) := by
  rw [hμ]
  simp only [stableDenominator]
  ring

/-- The common decaying weight is factored algebraically; its inverse is never used. -/
noncomputable def stableRuWeightedFactor (a κ d₀ d₁ μ E : A) (p : A × A × A) : A :=
  (p.1 * (-μ * (E * p.2.2 - κ) * (a + E * p.2.1)) +
    p.2.1 * (-κ * (E * p.2.2 - κ) * (d₁ + E * p.2.1)) +
    p.2.2 * (-κ * d₀)) *
      Ring.inverse (stableDenominator a κ (E * p.1, E * p.2.1, E * p.2.2))

theorem stableRu_weight_factor (a κ d₀ d₁ μ E Xc U W : A)
    (hμ : μ = -(κ ^ 2 * d₀)) :
    stableRu a κ d₀ d₁ μ (E * Xc, E * U, E * W) =
      E * stableRuWeightedFactor a κ d₀ d₁ μ E (Xc, U, W) := by
  unfold stableRu
  rw [stableRu_numerator_decomposition a κ d₀ d₁ μ hμ]
  simp only [stableRuWeightedFactor]
  ring

/-- Scaling the weighted inputs commutes with extracting their common
weight. No inverse of the scale or of a decaying trajectory is required. -/
theorem stableRuWeightedFactor_scale (a κ d₀ d₁ μ E c Xc U W : A) :
    stableRuWeightedFactor a κ d₀ d₁ μ E (c * Xc, c * U, c * W) =
      c * stableRuWeightedFactor a κ d₀ d₁ μ (c * E) (Xc, U, W) := by
  have hX : E * (c * Xc) = (c * E) * Xc := by ring
  have hU : E * (c * U) = (c * E) * U := by ring
  have hW : E * (c * W) = (c * E) * W := by ring
  unfold stableRuWeightedFactor
  rw [hX, hU, hW]
  ring

theorem stableInverseProduct_sub_denominator (a κ e₁ e₂ e₃ X u w : A) :
    stableInverseProduct e₁ e₂ e₃ X (w - κ) - stableDenominator a κ (X, u, w) =
      X * (w - κ) * (a + u - e₁ + e₂ * X * (w - κ) -
        e₃ * X ^ 2 * (w - κ) ^ 2) := by
  simp only [stableInverseProduct, stableDenominator]
  ring

theorem stableRu_zero (a κ d₀ d₁ μ : A) (hμ : μ = -(κ ^ 2 * d₀)) :
    stableRu a κ d₀ d₁ μ (0, 0, 0) = 0 := by
  unfold stableRu
  rw [stableRu_numerator_decomposition a κ d₀ d₁ μ hμ 0 0 0]
  simp

theorem stable_u_equation (a κ d₀ d₁ μ X u w : A)
    (hD : IsUnit (stableDenominator a κ (X, u, w))) :
    -κ * (w - κ) * (u * (d₀ + d₁ * u + u ^ 2)) *
        Ring.inverse (stableDenominator a κ (X, u, w)) =
      -μ * u + u * stableRu a κ d₀ d₁ μ (X, u, w) := by
  have hcancel := Ring.mul_inverse_cancel (stableDenominator a κ (X, u, w)) hD
  calc
    _ = -κ * (w - κ) * (u * (d₀ + d₁ * u + u ^ 2)) *
        Ring.inverse (stableDenominator a κ (X, u, w)) +
        μ * u * (stableDenominator a κ (X, u, w) *
          Ring.inverse (stableDenominator a κ (X, u, w))) - μ * u := by
      rw [hcancel, mul_one]
      ring
    _ = _ := by simp only [stableRu]; ring

theorem stable_w_equation (a κ e₁ e₂ e₃ X u w : A)
    (hD : IsUnit (stableDenominator a κ (X, u, w))) :
    (w - κ) + κ * stableInverseProduct e₁ e₂ e₃ X (w - κ) *
        Ring.inverse (stableDenominator a κ (X, u, w)) =
      w + X * stableRw a κ e₁ e₂ e₃ (X, u, w) := by
  have hcancel := Ring.mul_inverse_cancel (stableDenominator a κ (X, u, w)) hD
  calc
    _ = w + κ * (stableInverseProduct e₁ e₂ e₃ X (w - κ) -
        stableDenominator a κ (X, u, w)) *
        Ring.inverse (stableDenominator a κ (X, u, w)) := by
      calc
        _ = w + κ * stableInverseProduct e₁ e₂ e₃ X (w - κ) *
            Ring.inverse (stableDenominator a κ (X, u, w)) -
            κ * (stableDenominator a κ (X, u, w) *
              Ring.inverse (stableDenominator a κ (X, u, w))) := by rw [hcancel]; ring
        _ = _ := by ring
    _ = _ := by rw [stableInverseProduct_sub_denominator]; simp only [stableRw]; ring

end Algebra

section Analytic

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem stableDenominator_isUnit_of_norm_lt (a κ X u w : A)
    (hsmall : ‖X * (w - κ) * (a + u)‖ < 1) :
    IsUnit (stableDenominator a κ (X, u, w)) := by
  simpa only [stableDenominator, Units.val_oneSub] using
    (Units.oneSub (X * (w - κ) * (a + u)) hsmall).isUnit

private theorem analyticAt_stableInverseDenominator (a κ : A) :
    AnalyticAt ℂ (fun p : A × A × A => Ring.inverse (stableDenominator a κ p))
      (0, 0, 0) := by
  have hx : AnalyticAt ℂ (fun p : A × A × A =>
      p.1 * (p.2.2 - κ) * (a + p.2.1)) (0, 0, 0) := by fun_prop
  simpa only [stableDenominator] using
    (analyticAt_inverse_one_sub ℂ A).comp_of_eq' hx (by simp)

theorem analyticAt_stableRu (a κ d₀ d₁ μ : A) :
    AnalyticAt ℂ (stableRu a κ d₀ d₁ μ) (0, 0, 0) := by
  have hn : AnalyticAt ℂ (fun p : A × A × A =>
      -κ * (p.2.2 - κ) * (d₀ + d₁ * p.2.1 + p.2.1 ^ 2) +
        μ * stableDenominator a κ p) (0, 0, 0) := by
    unfold stableDenominator
    fun_prop
  exact hn.mul (analyticAt_stableInverseDenominator a κ)

theorem analyticAt_stableRw (a κ e₁ e₂ e₃ : A) :
    AnalyticAt ℂ (stableRw a κ e₁ e₂ e₃) (0, 0, 0) := by
  have hn : AnalyticAt ℂ (fun p : A × A × A =>
      κ * (p.2.2 - κ) *
        (a + p.2.1 - e₁ + e₂ * p.1 * (p.2.2 - κ) -
          e₃ * p.1 ^ 2 * (p.2.2 - κ) ^ 2)) (0, 0, 0) := by fun_prop
  exact hn.mul (analyticAt_stableInverseDenominator a κ)

theorem stableRuWeightedFactor_zero (a κ d₀ d₁ μ E : A) :
    stableRuWeightedFactor a κ d₀ d₁ μ E (0, 0, 0) = 0 := by
  simp [stableRuWeightedFactor]

theorem analyticAt_stableRuWeightedFactor (a κ d₀ d₁ μ E : A) :
    AnalyticAt ℂ (stableRuWeightedFactor a κ d₀ d₁ μ E) (0, 0, 0) := by
  have hn : AnalyticAt ℂ (fun p : A × A × A =>
      p.1 * (-μ * (E * p.2.2 - κ) * (a + E * p.2.1)) +
        p.2.1 * (-κ * (E * p.2.2 - κ) * (d₁ + E * p.2.1)) +
        p.2.2 * (-κ * d₀)) (0, 0, 0) := by fun_prop
  have hp : AnalyticAt ℂ (fun p : A × A × A =>
      (E * p.1, E * p.2.1, E * p.2.2)) (0, 0, 0) := by fun_prop
  exact hn.mul ((analyticAt_stableInverseDenominator a κ).comp_of_eq' hp (by simp))

theorem hasFDerivAt_mul_stableRu_zero
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (a κ d₀ d₁ μ : A) (hμ : μ = -(κ ^ 2 * d₀))
    (M Lᵤ Lw : B →L[ℂ] A) :
    HasFDerivAt (fun z : B => M z * stableRu a κ d₀ d₁ μ (0, Lᵤ z, Lw z))
      (0 : B →L[ℂ] A) (0 : B) := by
  have hp : AnalyticAt ℂ (fun z : B => ((0 : A), Lᵤ z, Lw z)) 0 :=
    analyticAt_const.prod ((Lᵤ.analyticAt 0).prod (Lw.analyticAt 0))
  have hr : AnalyticAt ℂ (fun z : B => stableRu a κ d₀ d₁ μ (0, Lᵤ z, Lw z)) 0 :=
    (analyticAt_stableRu a κ d₀ d₁ μ).comp_of_eq' hp (by simp)
  have hd := M.hasFDerivAt.mul hr.differentiableAt.hasFDerivAt
  refine hd.congr_fderiv ?_
  ext z
  simp [ContinuousLinearMap.smul_apply, stableRu_zero a κ d₀ d₁ μ hμ, smul_eq_mul]

end Analytic


/-! ## Declarations from ExponentialStableGraph -/


variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

noncomputable def stableGraphResidual
    (a κ d₀ d₁ μ e₁ e₂ e₃ : A) (X Xc I : ℂ →L[ℂ] A)
    (E G T : A →L[ℂ] A) (p : (ℂ × ℂ) × (A × A)) : A × A :=
  (p.2.1 - I p.1.2 -
      G (p.2.1 * stableRu a κ d₀ d₁ μ (X p.1.1, E p.2.1, E p.2.2)),
    p.2.2 + T (Xc p.1.1 * stableRw a κ e₁ e₂ e₃ (X p.1.1, E p.2.1, E p.2.2)))

theorem stableGraphResidual_zero
    (a κ d₀ d₁ μ e₁ e₂ e₃ : A) (X Xc I : ℂ →L[ℂ] A) (E G T : A →L[ℂ] A) :
    stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T 0 = 0 := by
  simp [stableGraphResidual]

theorem analyticAt_stableGraphResidual
    (a κ d₀ d₁ μ e₁ e₂ e₃ : A) (X Xc I : ℂ →L[ℂ] A) (E G T : A →L[ℂ] A) :
    AnalyticAt ℂ (stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T) 0 := by
  have hp : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) =>
      (X p.1.1, E p.2.1, E p.2.2)) 0 :=
    ((X.analyticAt _).comp (analyticAt_fst.comp analyticAt_fst)).prod
      (((E.analyticAt _).comp (analyticAt_fst.comp analyticAt_snd)).prod
        ((E.analyticAt _).comp (analyticAt_snd.comp analyticAt_snd)))
  have hRu : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) =>
      stableRu a κ d₀ d₁ μ (X p.1.1, E p.2.1, E p.2.2)) 0 :=
    (analyticAt_stableRu a κ d₀ d₁ μ).comp_of_eq' hp (by simp)
  have hRw : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) =>
      stableRw a κ e₁ e₂ e₃ (X p.1.1, E p.2.1, E p.2.2)) 0 :=
    (analyticAt_stableRw a κ e₁ e₂ e₃).comp_of_eq' hp (by simp)
  have hu : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) => p.2.1) 0 :=
    analyticAt_fst.comp analyticAt_snd
  have hw : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) => p.2.2) 0 :=
    analyticAt_snd.comp analyticAt_snd
  have hI : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) => I p.1.2) 0 :=
    (I.analyticAt _).comp (analyticAt_snd.comp analyticAt_fst)
  have hXc : AnalyticAt ℂ (fun p : (ℂ × ℂ) × (A × A) => Xc p.1.1) 0 :=
    (Xc.analyticAt _).comp (analyticAt_fst.comp analyticAt_fst)
  exact ((hu.sub hI).sub ((G.analyticAt _).comp (hu.mul hRu))).prod
    (hw.add ((T.analyticAt _).comp (hXc.mul hRw)))

theorem hasFDerivAt_stableGraphResidual_trajectory
    (a κ d₀ d₁ μ e₁ e₂ e₃ : A) (hμ : μ = -(κ ^ 2 * d₀))
    (X Xc I : ℂ →L[ℂ] A) (E G T : A →L[ℂ] A) :
    HasFDerivAt
      (fun s : A × A => stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T (0, s))
      (ContinuousLinearMap.id ℂ (A × A)) 0 := by
  let M₁ : (A × A) →L[ℂ] A := ContinuousLinearMap.fst ℂ A A
  let M₂ : (A × A) →L[ℂ] A := ContinuousLinearMap.snd ℂ A A
  have hn := hasFDerivAt_mul_stableRu_zero a κ d₀ d₁ μ hμ M₁ (E.comp M₁) (E.comp M₂)
  have hGn := G.hasFDerivAt.comp 0 hn
  have h₁ : HasFDerivAt
      (fun s : A × A =>
        (stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T (0, s)).1)
      M₁ 0 := by
    simpa only [stableGraphResidual, Prod.fst_zero, Prod.snd_zero, map_zero, sub_zero,
      ContinuousLinearMap.comp_zero,
      M₁, M₂, ContinuousLinearMap.comp_apply, Function.comp_def, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd'] using! M₁.hasFDerivAt.fun_sub hGn
  have h₂ : HasFDerivAt
      (fun s : A × A =>
        (stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T (0, s)).2)
      M₂ 0 := by
    simpa only [stableGraphResidual, Prod.fst_zero, Prod.snd_zero,
      map_zero, zero_mul, add_zero, M₂,
      ContinuousLinearMap.coe_snd'] using M₂.hasFDerivAt
  convert h₁.prodMk h₂ using 1 <;> ext s <;> rfl

theorem exists_analytic_stable_graph
    (a κ d₀ d₁ μ e₁ e₂ e₃ : A) (hμ : μ = -(κ ^ 2 * d₀))
    (X Xc I : ℂ →L[ℂ] A) (E G T : A →L[ℂ] A) :
    ∃ φ : (ℂ × ℂ) → A × A, AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧
      (∀ᶠ p in 𝓝 0,
        stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T (p, φ p) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : (ℂ × ℂ) × (A × A)),
        stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T p = 0 →
          φ p.1 = p.2) := by
  let R := stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T
  have hR : AnalyticAt ℂ R 0 := analyticAt_stableGraphResidual a κ d₀ d₁ μ e₁ e₂ e₃ X Xc I E G T
  have hd : HasFDerivAt R (fderiv ℂ R 0) 0 := hR.differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun s : A × A => R (0, s))
      ((fderiv ℂ R 0).comp (ContinuousLinearMap.inr ℂ (ℂ × ℂ) (A × A))) 0 := by
    exact hd.comp 0 (ContinuousLinearMap.inr ℂ (ℂ × ℂ) (A × A)).hasFDerivAt
  have he := (hasFDerivAt_stableGraphResidual_trajectory
    a κ d₀ d₁ μ e₁ e₂ e₃ hμ X Xc I E G T).unique hc
  have hb : Function.Bijective
      ((fderiv ℂ R 0).comp (ContinuousLinearMap.inr ℂ (ℂ × ℂ) (A × A))) := by
    rw [← he]
    exact Function.bijective_id
  obtain ⟨φ, hφa, hφ0, hφr, hφu⟩ := exists_analytic_implicit_graph hR hd hb
  have hR0 : R (0, 0) = 0 := by simp [R, stableGraphResidual]
  refine ⟨φ, hφa, hφ0, ?_, ?_⟩
  · change ∀ᶠ p in 𝓝 0, R (p, φ p) = 0
    simpa only [hR0] using hφr
  · change ∀ᶠ p in 𝓝 (0, 0), R p = 0 → φ p.1 = p.2
    simpa only [hR0] using hφu


/-! ## Declarations from ExponentialStableTrajectory -/


abbrev StableTrajectory := ℝ≥0 →ᵇ ℂ

theorem norm_weighted_decay_value_le (weight rate M : ℝ)
    (hWeight : weight ≤ rate) (hM : 0 ≤ M) (u : ℝ≥0 → ℂ)
    (hu : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ))) (t : ℝ≥0) :
    ‖(Real.exp (weight * (t : ℝ)) : ℂ) * u t‖ ≤ M := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (weight * (t : ℝ)) * ‖u t‖ ≤
        Real.exp (weight * (t : ℝ)) * (M * Real.exp (-rate * (t : ℝ))) :=
      mul_le_mul_of_nonneg_left (hu t) (Real.exp_pos _).le
    _ = M * Real.exp ((weight - rate) * (t : ℝ)) := by
      rw [show Real.exp (weight * (t : ℝ)) *
          (M * Real.exp (-rate * (t : ℝ))) =
          M * (Real.exp (weight * (t : ℝ)) * Real.exp (-rate * (t : ℝ))) by ring,
        ← Real.exp_add]
      rw [show weight * (t : ℝ) + -rate * (t : ℝ) =
        (weight - rate) * (t : ℝ) by ring]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hWeight) t.coe_nonneg)) hM
    _ = M := mul_one M

/-- This bundle is constructed from an actual scalar decay estimate. -/
noncomputable def weightedDecayTrajectory (weight rate M : ℝ)
    (hWeight : weight ≤ rate) (hM : 0 ≤ M) (u : ℝ≥0 → ℂ) (huc : Continuous u)
    (hu : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ))) : StableTrajectory :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (Real.exp (weight * (t : ℝ)) : ℂ) * u t)
    (by fun_prop) M (norm_weighted_decay_value_le weight rate M hWeight hM u hu)

theorem weightedDecayTrajectory_apply (weight rate M : ℝ)
    (hWeight : weight ≤ rate) (hM : 0 ≤ M) (u : ℝ≥0 → ℂ) (huc : Continuous u)
    (hu : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ))) (t : ℝ≥0) :
    weightedDecayTrajectory weight rate M hWeight hM u huc hu t =
      (Real.exp (weight * (t : ℝ)) : ℂ) * u t := rfl

theorem norm_weightedDecayTrajectory_le (weight rate M : ℝ)
    (hWeight : weight ≤ rate) (hM : 0 ≤ M) (u : ℝ≥0 → ℂ) (huc : Continuous u)
    (hu : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ))) :
    ‖weightedDecayTrajectory weight rate M hWeight hM u huc hu‖ ≤ M :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM
    (norm_weighted_decay_value_le weight rate M hWeight hM u hu)

theorem stableTrajectory_unit_ne_zero (D : StableTrajectory) (hD : IsUnit D)
    (t : ℝ≥0) : D t ≠ 0 := by
  have hmul : D t * (Ring.inverse D) t = 1 := by
    simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.coe_one,
      Pi.one_apply] using
      congrArg (fun q : StableTrajectory => q t) (Ring.mul_inverse_cancel D hD)
  intro hz
  simp [hz] at hmul

theorem stableTrajectory_inverse_apply (D : StableTrajectory) (hD : IsUnit D)
    (t : ℝ≥0) : (Ring.inverse D) t = (D t)⁻¹ := by
  have hmul : D t * (Ring.inverse D) t = 1 := by
    simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.coe_one,
      Pi.one_apply] using
      congrArg (fun q : StableTrajectory => q t) (Ring.mul_inverse_cancel D hD)
  have hne := stableTrajectory_unit_ne_zero D hD t
  apply mul_left_cancel₀ hne
  rw [hmul, mul_inv_cancel₀ hne]

theorem stableTrajectory_denominator_isUnit_of_pointwise_le_half
    (a κ : ℂ) (X u w : StableTrajectory)
    (hsmall : ∀ t, ‖X t * (w t - κ) * (a + u t)‖ ≤ (1 / 2 : ℝ)) :
    IsUnit (stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, u, w)) := by
  have hnorm : ‖X * (w - algebraMap ℂ StableTrajectory κ) *
      (algebraMap ℂ StableTrajectory a + u)‖ ≤ (1 / 2 : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    intro t
    simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.algebraMap_apply,
      smul_eq_mul, mul_one] using hsmall t
  exact stableDenominator_isUnit_of_norm_lt _ _ _ _ _
    (hnorm.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))

noncomputable def stableTrajectorySeed (rate : ℝ) (hRate : 0 ≤ rate) :
    ℂ →L[ℂ] StableTrajectory :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (expDecayBCF rate hRate)

theorem stableTrajectorySeed_apply (rate : ℝ) (hRate : 0 ≤ rate)
    (c : ℂ) (t : ℝ≥0) :
    stableTrajectorySeed rate hRate c t = c * (Real.exp (-rate * (t : ℝ)) : ℂ) := by
  simp [stableTrajectorySeed, expDecayBCF_apply, smul_eq_mul]

/-- The weighted unstable component is a bounded function by construction,
before any bound on the weighted original orbit is assumed. -/
noncomputable def stableWeightedTailTrajectory (σ : ℝ) (hσ1 : σ < 1)
    (X₀ : ℂ) (r : StableTrajectory) : StableTrajectory :=
  -(X₀ • (expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le) *
    stableTail 2 (by norm_num) r))

theorem stableWeightedTailTrajectory_apply (σ : ℝ) (hσ1 : σ < 1)
    (X₀ : ℂ) (r : StableTrajectory) (t : ℝ≥0) :
    stableWeightedTailTrajectory σ hσ1 X₀ r t =
      -X₀ * (Real.exp (-(1 - σ) * (t : ℝ)) : ℂ) *
        stableTail 2 (by norm_num) r t := by
  simp [stableWeightedTailTrajectory, expDecayBCF_apply, smul_eq_mul, mul_assoc]

theorem norm_stableWeightedTailTrajectory_le (σ : ℝ) (hσ1 : σ < 1)
    (X₀ : ℂ) (r : StableTrajectory) :
    ‖stableWeightedTailTrajectory σ hσ1 X₀ r‖ ≤ ‖X₀‖ * ‖r‖ / 2 := by
  have ht : ‖stableTail 2 (by norm_num) r‖ ≤ (1 / 2 : ℝ) * ‖r‖ :=
    ((stableTail 2 (by norm_num)).le_opNorm r).trans
      (mul_le_mul_of_nonneg_right (norm_stableTail_le 2 (by norm_num)) (norm_nonneg r))
  have hprod := mul_le_mul
    (norm_expDecayBCF_le (1 - σ) (sub_nonneg.mpr hσ1.le)) ht
    (norm_nonneg (stableTail 2 (by norm_num) r)) zero_le_one
  calc
    ‖stableWeightedTailTrajectory σ hσ1 X₀ r‖ =
        ‖X₀‖ * ‖expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le) *
          stableTail 2 (by norm_num) r‖ := by
      rw [stableWeightedTailTrajectory, norm_neg, norm_smul]
    _ ≤ ‖X₀‖ * (‖expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le)‖ *
        ‖stableTail 2 (by norm_num) r‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖X₀‖ * (1 * ((1 / 2 : ℝ) * ‖r‖)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖X₀‖ * ‖r‖ / 2 := by ring

theorem stableWeightedTailTrajectory_residual (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (X₀ : ℂ) (r : StableTrajectory) :
    stableWeightedTailTrajectory σ hσ1 X₀ r +
      stableTail (1 + σ) (by linarith)
        (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) X₀ * r) = 0 := by
  have hseed : stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) X₀ * r =
      X₀ • (stableTailDecay (1 - σ) (sub_nonneg.mpr hσ1.le) * r) := by
    ext t
    simp only [BoundedContinuousFunction.mul_apply, stableTrajectorySeed_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, stableTailDecay_apply]
    ring
  rw [hseed, map_smul]
  ext t
  simp only [BoundedContinuousFunction.add_apply, stableWeightedTailTrajectory_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply]
  have hweight : stableTail (1 + σ) (by linarith)
      (stableTailDecay (1 - σ) (sub_nonneg.mpr hσ1.le) * r) t =
      (Real.exp (-(1 - σ) * (t : ℝ)) : ℂ) * stableTail 2 (by norm_num) r t := by
    simpa only [show (1 + σ) + (1 - σ) = (2 : ℝ) by ring] using
      stableTail_weight_mul (1 + σ) (1 - σ) (by linarith)
        (sub_nonneg.mpr hσ1.le) r t
  rw [hweight]
  ring

theorem stableTrajectory_w_eq_tail_of_ode (X₀ : ℂ) (w r : StableTrajectory)
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
      (w (Real.toNNReal t) + X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) *
        r (Real.toNNReal t)) t) (t : ℝ≥0) :
    w t = -X₀ * (Real.exp (-(t : ℝ)) : ℂ) * stableTail 2 (by norm_num) r t := by
  have hseed : stableTrajectorySeed 1 zero_le_one X₀ * r =
      X₀ • (stableTailDecay 1 zero_le_one * r) := by
    ext s
    simp only [BoundedContinuousFunction.mul_apply, stableTrajectorySeed_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, stableTailDecay_apply]
    ring
  have hODE : ∀ s : ℝ, 0 < s → HasDerivAt (fun v : ℝ => w (Real.toNNReal v))
      ((1 : ℂ) * w (Real.toNNReal s) +
        (stableTrajectorySeed 1 zero_le_one X₀ * r) (Real.toNNReal s)) s := by
    intro s hs
    simpa only [one_mul, BoundedContinuousFunction.mul_apply,
      stableTrajectorySeed_apply, neg_one_mul] using hw s hs
  have htail := stableTail_variation_of_constants 1 zero_lt_one w
    (stableTrajectorySeed 1 zero_le_one X₀ * r) hODE t
  rw [hseed, map_smul] at htail
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul] at htail
  rw [stableTail_weight_mul] at htail
  simpa only [one_add_one_eq_two, neg_one_mul, neg_mul, one_mul, mul_assoc] using htail

theorem stableWeightedTailTrajectory_matches_ode (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (X₀ : ℂ) (w r : StableTrajectory)
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
      (w (Real.toNNReal t) + X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) *
        r (Real.toNNReal t)) t) (t : ℝ≥0) :
    expDecayBCF σ hσ t * stableWeightedTailTrajectory σ hσ1 X₀ r t = w t := by
  have hweights : (Real.exp (-σ * (t : ℝ)) : ℂ) *
      (Real.exp (-(1 - σ) * (t : ℝ)) : ℂ) = (Real.exp (-(t : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show -σ * (t : ℝ) + -(1 - σ) * (t : ℝ) = -(t : ℝ) by ring]
  rw [expDecayBCF_apply, stableWeightedTailTrajectory_apply,
    stableTrajectory_w_eq_tail_of_ode X₀ w r hw t]
  calc
    _ = -X₀ * ((Real.exp (-σ * (t : ℝ)) : ℂ) *
        (Real.exp (-(1 - σ) * (t : ℝ)) : ℂ)) * stableTail 2 (by norm_num) r t := by ring
    _ = _ := by rw [hweights]

theorem stableTrajectory_forward_residual_of_ode (rate : ℝ) (hRate : 0 < rate)
    (U q : StableTrajectory)
    (hU : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => U (Real.toNNReal s))
      (-(rate : ℂ) * U (Real.toNNReal t) +
        U (Real.toNNReal t) * q (Real.toNNReal t)) t) :
    U - stableTrajectorySeed rate hRate.le (U 0) - forwardExpCLM rate hRate (U * q) = 0 := by
  have heq (t : ℝ≥0) := forwardExpCLM_variation_of_constants rate hRate
    (fun s => U s) U.continuous (U * q) hU t
  ext t
  simp only [BoundedContinuousFunction.sub_apply, stableTrajectorySeed_apply,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  rw [heq t]
  ring

noncomputable def stableTrajectoryWeight (σ : ℝ) (hσ : 0 ≤ σ) :
    StableTrajectory →L[ℂ] StableTrajectory :=
  ContinuousLinearMap.mul ℂ StableTrajectory (expDecayBCF σ hσ)

noncomputable def stableTrajectoryResidual
    (a κ d₀ d₁ e₁ e₂ e₃ : ℂ) (μ σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hσμ : σ < μ)
    (p : (ℂ × ℂ) × (StableTrajectory × StableTrajectory)) :
    StableTrajectory × StableTrajectory :=
  stableGraphResidual
    (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
    (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
    (algebraMap ℂ StableTrajectory (μ : ℂ))
    (algebraMap ℂ StableTrajectory e₁) (algebraMap ℂ StableTrajectory e₂)
    (algebraMap ℂ StableTrajectory e₃)
    (stableTrajectorySeed 1 zero_le_one)
    (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le))
    (stableTrajectorySeed (μ - σ) (sub_nonneg.mpr hσμ.le))
    (stableTrajectoryWeight σ hσ.le)
    (forwardExpCLM (μ - σ) (sub_pos.mpr hσμ))
    (stableTail (1 + σ) (by linarith)) p

theorem exists_analytic_weighted_trajectory_graph
    (a κ d₀ d₁ e₁ e₂ e₃ : ℂ) (μ σ : ℝ)
    (hμ : (μ : ℂ) = -(κ ^ 2 * d₀))
    (hσ : 0 < σ) (hσ1 : σ < 1) (hσμ : σ < μ) :
    ∃ φ : (ℂ × ℂ) → StableTrajectory × StableTrajectory,
      AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧
      (∀ᶠ p in 𝓝 0,
        stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ (p, φ p) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : (ℂ × ℂ) × (StableTrajectory × StableTrajectory)),
        stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ p = 0 →
          φ p.1 = p.2) := by
  have hμA : algebraMap ℂ StableTrajectory (μ : ℂ) =
      -((algebraMap ℂ StableTrajectory κ) ^ 2 * algebraMap ℂ StableTrajectory d₀) := by
    simpa only [map_neg, map_mul, map_pow] using
      congrArg (algebraMap ℂ StableTrajectory) hμ
  simpa only [stableTrajectoryResidual] using
    exists_analytic_stable_graph
      (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
      (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
      (algebraMap ℂ StableTrajectory (μ : ℂ))
      (algebraMap ℂ StableTrajectory e₁) (algebraMap ℂ StableTrajectory e₂)
      (algebraMap ℂ StableTrajectory e₃) hμA
      (stableTrajectorySeed 1 zero_le_one)
      (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le))
      (stableTrajectorySeed (μ - σ) (sub_nonneg.mpr hσμ.le))
      (stableTrajectoryWeight σ hσ.le)
      (forwardExpCLM (μ - σ) (sub_pos.mpr hσμ))
      (stableTail (1 + σ) (by linarith))


/-! ## Declarations from ExponentialStableCorrection -/


noncomputable def stableTrajectoryCorrection
    (a κ d₀ d₁ μ : ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory) (p : ℂ × ℂ) : ℂ :=
  ((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ≥0)).comp (stableTail σ hσ))
    (stableRuWeightedFactor
      (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
      (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
      (algebraMap ℂ StableTrajectory μ) (expDecayBCF σ hσ.le)
      (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) p.1,
        (φ p).1, (φ p).2))

theorem stableTrajectoryCorrection_zero
    (a κ d₀ d₁ μ : ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory) (hφ0 : φ 0 = 0) :
    stableTrajectoryCorrection a κ d₀ d₁ μ σ hσ hσ1 φ 0 = 0 := by
  simp [stableTrajectoryCorrection, hφ0, stableRuWeightedFactor_zero]

theorem analyticAt_stableTrajectoryCorrection
    (a κ d₀ d₁ μ : ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory)
    (hφ : AnalyticAt ℂ φ 0) (hφ0 : φ 0 = 0) :
    AnalyticAt ℂ (stableTrajectoryCorrection a κ d₀ d₁ μ σ hσ hσ1 φ) 0 := by
  have hp : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) p.1,
        (φ p).1, (φ p).2)) 0 :=
    (((stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le)).analyticAt _).comp
      analyticAt_fst).prod ((analyticAt_fst.comp hφ).prod (analyticAt_snd.comp hφ))
  have hf := (analyticAt_stableRuWeightedFactor
    (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
    (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
    (algebraMap ℂ StableTrajectory μ) (expDecayBCF σ hσ.le)).comp_of_eq' hp
      (by simp [hφ0])
  exact (((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ≥0)).comp
    (stableTail σ hσ)).analyticAt _).comp hf


/-! ## Declarations from ExponentialStableCoordinate -/


theorem stable_coordinate_inverse_factor {u Q v : ℂ}
    (h : u * Complex.exp v = Q) : u = Q * Complex.exp (-v) := by
  rw [← h, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

theorem analytic_stable_coordinate_factor
    {H J : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hJ : AnalyticAt ℂ J 0) (hJ0 : J 0 = 0)
    (hInv : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      H p * Complex.exp (J (p.1, H p)) = p.2) :
    ∃ E : ℂ × ℂ → ℂ, AnalyticAt ℂ E 0 ∧ E 0 = 1 ∧
      (∀ p, E p ≠ 0) ∧ (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), H p = p.2 * E p) := by
  let E : ℂ × ℂ → ℂ := fun p => Complex.exp (-J (p.1, H p))
  have hJ00 : J (0, 0) = 0 := hJ0
  have hJh : AnalyticAt ℂ (fun p : ℂ × ℂ => J (p.1, H p)) 0 :=
    hJ.comp_of_eq' (analyticAt_fst.prod hH) (by simp [hH0])
  refine ⟨E, hJh.neg.cexp', ?_, fun p => Complex.exp_ne_zero _, ?_⟩
  · simp [E, hH0, hJ00]
  · exact hInv.mono fun p hp => stable_coordinate_inverse_factor hp

theorem exists_analytic_stable_coordinate_inverse
    {J : ℂ × ℂ → ℂ} (hJ : AnalyticAt ℂ J 0) (hJ0 : J 0 = 0) :
    ∃ H : ℂ × ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 0 ∧
      (∀ᶠ X : ℂ in 𝓝 0, H (X, 0) = 0) ∧
      fderiv ℂ H 0 (0, 1) = 1 ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        H p * Complex.exp (J (p.1, H p)) = p.2) ∧
      (∀ᶠ z in 𝓝 (0 : (ℂ × ℂ) × ℂ),
        z.2 * Complex.exp (J (z.1.1, z.2)) = z.1.2 → H z.1 = z.2) := by
  let R : (ℂ × ℂ) × ℂ → ℂ := fun z =>
    z.2 * Complex.exp (J (z.1.1, z.2)) - z.1.2
  have hJ00 : J (0, 0) = 0 := hJ0
  have hR0 : R (0, 0) = 0 := by simp [R]
  have hp : AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => (z.1.1, z.2)) 0 :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hRJ : AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => J (z.1.1, z.2)) 0 :=
    hJ.comp_of_eq' hp rfl
  have hR : AnalyticAt ℂ R 0 := by
    unfold R
    fun_prop
  have hJline : AnalyticAt ℂ (fun u : ℂ => J (0, u)) 0 := by
    exact hJ.comp_of_eq' (by fun_prop) rfl
  have hscalar : HasDerivAt (fun u : ℂ => R (0, u)) 1 0 := by
    simpa [R, hJ00] using!
      (hasDerivAt_id (0 : ℂ)).fun_mul hJline.differentiableAt.hasDerivAt.cexp
  have htrajectory : HasFDerivAt (fun u : ℂ => R (0, u))
      (ContinuousLinearMap.id ℂ ℂ) 0 := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa using hscalar
  have hd := hR.differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun u : ℂ => R (0, u))
      ((fderiv ℂ R 0).comp (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ)) 0 :=
    hd.comp 0 (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).hasFDerivAt
  have he := htrajectory.unique hc
  have hbij : Function.Bijective
      ((fderiv ℂ R 0).comp (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ)) := by
    rw [← he]
    exact Function.bijective_id
  obtain ⟨H, hH, hH0, hHr, hHu⟩ := exists_analytic_implicit_graph hR hd hbij
  have hidentity : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      H p * Complex.exp (J (p.1, H p)) = p.2 := by
    filter_upwards [hHr] with p hp
    have hp0 : R (p, H p) = 0 := hp.trans hR0
    exact sub_eq_zero.mp hp0
  have hHZ : ∀ᶠ X : ℂ in 𝓝 0, H (X, 0) = 0 := by
    have ht : Tendsto (fun X : ℂ => (X, (0 : ℂ))) (𝓝 0) (𝓝 0) :=
      tendsto_id.prodMk_nhds tendsto_const_nhds
    filter_upwards [ht.eventually hidentity] with X hX
    exact (mul_eq_zero.mp hX).resolve_right (Complex.exp_ne_zero _)
  obtain ⟨E, hE, hE0, -, hfactor⟩ :=
    analytic_stable_coordinate_factor hH hH0 hJ hJ0 hidentity
  have hprod : HasFDerivAt (fun p : ℂ × ℂ => p.2 * E p)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
    have hd := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.mul
      hE.differentiableAt.hasFDerivAt
    refine hd.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_snd', hE0, smul_eq_mul]
  have hHd : HasFDerivAt H (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 :=
    hprod.congr_of_eventuallyEq hfactor
  have hnorm : fderiv ℂ H 0 (0, 1) = 1 := by
    rw [hHd.fderiv]
    rfl
  refine ⟨H, hH, hH0, hHZ, hnorm, hidentity, ?_⟩
  filter_upwards [hHu] with z hz
  intro heq
  apply hz
  rw [hR0]
  exact sub_eq_zero.mpr heq


end ThreeIM
