module

public import RequestProject.ThreeIM.ExponentialRealStableContinuation
public import RequestProject.ThreeIM.ExponentialStableTailDerivative
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Construction of actual real stable data

This candidate assembles scalar orbit construction, actual weighted-tail
capture, and the analytic coordinate change. It is awaiting formal
compilation; existence of stable data is a conclusion from ExponentialPair.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set NoWanderingDomains
open scoped Topology NNReal BoundedContinuousFunction ContDiff

namespace ThreeIM

/-! ## ExponentialStableCapture -/

theorem stableDenominator_trajectory_apply (a κ : ℂ)
    (X u w : StableTrajectory) (t : ℝ≥0) :
    stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, u, w) t =
        stableDenominator a κ (X t, u t, w t) := by
  simp [stableDenominator, smul_eq_mul]

theorem stableRu_trajectory_apply (a κ d₀ d₁ μ : ℂ)
    (X u w : StableTrajectory)
    (hD : IsUnit (stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, u, w))) (t : ℝ≥0) :
    stableRu (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
      (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
      (algebraMap ℂ StableTrajectory μ) (X, u, w) t =
        stableRu a κ d₀ d₁ μ (X t, u t, w t) := by
  simp only [stableRu, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.neg_apply, BoundedContinuousFunction.pow_apply,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one,
    stableTrajectory_inverse_apply _ hD, stableDenominator_trajectory_apply,
    Ring.inverse_eq_inv]

theorem stableRw_trajectory_apply (a κ e₁ e₂ e₃ : ℂ)
    (X u w : StableTrajectory)
    (hD : IsUnit (stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, u, w))) (t : ℝ≥0) :
    stableRw (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
      (algebraMap ℂ StableTrajectory e₁) (algebraMap ℂ StableTrajectory e₂)
      (algebraMap ℂ StableTrajectory e₃) (X, u, w) t =
        stableRw a κ e₁ e₂ e₃ (X t, u t, w t) := by
  simp only [stableRw, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.neg_apply, BoundedContinuousFunction.pow_apply,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one,
    stableTrajectory_inverse_apply _ hD, stableDenominator_trajectory_apply,
    Ring.inverse_eq_inv]

/-- Weighting a genuinely decaying scalar trajectory changes its linear
rate from μ to μ−σ. All derivatives are ordinary derivatives at positive
time; no derivative of the clamp map at zero is used. -/
theorem weightedDecayTrajectory_hasDerivAt
    (σ rate M μ : ℝ) (hσrate : σ ≤ rate) (hM : 0 ≤ M)
    (u : ℝ≥0 → ℂ) (huc : Continuous u)
    (hub : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ)))
    (q : ℝ≥0 → ℂ) {t : ℝ} (ht : 0 < t)
    (hud : HasDerivAt (fun s : ℝ => u (Real.toNNReal s))
      (-(μ : ℂ) * u (Real.toNNReal t) +
        u (Real.toNNReal t) * q (Real.toNNReal t)) t) :
    HasDerivAt (fun s : ℝ =>
      weightedDecayTrajectory σ rate M hσrate hM u huc hub (Real.toNNReal s))
      (-((μ - σ : ℝ) : ℂ) *
          weightedDecayTrajectory σ rate M hσrate hM u huc hub (Real.toNNReal t) +
        weightedDecayTrajectory σ rate M hσrate hM u huc hub (Real.toNNReal t) *
          q (Real.toNNReal t)) t := by
  have he := (((hasDerivAt_id t).const_mul σ).exp).ofReal_comp
  simp only [id_eq, mul_one] at he
  have hd := he.mul hud
  have hev : (fun s : ℝ =>
      weightedDecayTrajectory σ rate M hσrate hM u huc hub (Real.toNNReal s))
      =ᶠ[𝓝 t] (fun s : ℝ => (Real.exp (σ * s) : ℂ) * u (Real.toNNReal s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp only [weightedDecayTrajectory_apply, Real.coe_toNNReal _ hs.le]
  convert hd.congr_of_eventuallyEq hev using 1
  simp only [weightedDecayTrajectory_apply, Real.coe_toNNReal _ ht.le]
  push_cast
  ring

/-- This bridge constructs the weighted unstable component by its tail
integral and proves the actual Banach residual vanishes. It does not assume
the original weighted unstable component was already bounded. -/
theorem stableTrajectoryResidual_eq_zero_of_scalar_ode
    (a κ d₀ d₁ e₁ e₂ e₃ : ℂ) (μ σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hσμ : σ < μ)
    (X₀ : ℂ) (U w r : StableTrajectory)
    (hr : ∀ t : ℝ≥0, r t = stableRw a κ e₁ e₂ e₃
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ),
        expDecayBCF σ hσ.le t * U t, w t))
    (hsmall : ∀ t : ℝ≥0,
      ‖(X₀ * (Real.exp (-(t : ℝ)) : ℂ)) * (w t - κ) *
        (a + expDecayBCF σ hσ.le t * U t)‖ ≤ (1 / 2 : ℝ))
    (hU : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => U (Real.toNNReal s))
        (-((μ - σ : ℝ) : ℂ) * U (Real.toNNReal t) +
          U (Real.toNNReal t) * stableRu a κ d₀ d₁ (μ : ℂ)
            (X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              expDecayBCF σ hσ.le (Real.toNNReal t) * U (Real.toNNReal t),
              w (Real.toNNReal t))) t)
    (hw : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
        (w (Real.toNNReal t) + X₀ *
          (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) * r (Real.toNNReal t)) t) :
    stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ
      ((X₀, U 0), (U, stableWeightedTailTrajectory σ hσ1 X₀ r)) = 0 := by
  let X := stableTrajectorySeed 1 zero_le_one X₀
  let E := expDecayBCF σ hσ.le
  let W := stableWeightedTailTrajectory σ hσ1 X₀ r
  have hW (t : ℝ≥0) : E t * W t = w t :=
    stableWeightedTailTrajectory_matches_ode σ hσ.le hσ1 X₀ w r hw t
  have hD : IsUnit (stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, E * U, E * W)) := by
    apply stableTrajectory_denominator_isUnit_of_pointwise_le_half
    intro t
    simpa only [X, stableTrajectorySeed_apply, neg_one_mul,
      BoundedContinuousFunction.mul_apply, hW t] using hsmall t
  let q := stableRu (algebraMap ℂ StableTrajectory a)
    (algebraMap ℂ StableTrajectory κ) (algebraMap ℂ StableTrajectory d₀)
    (algebraMap ℂ StableTrajectory d₁) (algebraMap ℂ StableTrajectory (μ : ℂ))
    (X, E * U, E * W)
  let Rw := stableRw (algebraMap ℂ StableTrajectory a)
    (algebraMap ℂ StableTrajectory κ) (algebraMap ℂ StableTrajectory e₁)
    (algebraMap ℂ StableTrajectory e₂) (algebraMap ℂ StableTrajectory e₃)
    (X, E * U, E * W)
  have hq (t : ℝ≥0) : q t = stableRu a κ d₀ d₁ (μ : ℂ)
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ), E t * U t, w t) := by
    dsimp only [q]
    rw [stableRu_trajectory_apply _ _ _ _ _ _ _ _ hD]
    simp only [X, stableTrajectorySeed_apply, neg_one_mul,
      BoundedContinuousFunction.mul_apply, hW t]
  have hrw : Rw = r := by
    ext t
    dsimp only [Rw]
    rw [stableRw_trajectory_apply _ _ _ _ _ _ _ _ hD]
    simpa only [X, stableTrajectorySeed_apply, neg_one_mul,
      BoundedContinuousFunction.mul_apply, hW t] using (hr t).symm
  have hU' : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => U (Real.toNNReal s))
        (-((μ - σ : ℝ) : ℂ) * U (Real.toNNReal t) +
          U (Real.toNNReal t) * q (Real.toNNReal t)) t := by
    intro t ht
    rw [hq]
    exact hU t ht
  have hfirst := stableTrajectory_forward_residual_of_ode
    (μ - σ) (sub_pos.mpr hσμ) U q hU'
  have hsecond := stableWeightedTailTrajectory_residual σ hσ hσ1 X₀ r
  change
    (U - stableTrajectorySeed (μ - σ) (sub_nonneg.mpr hσμ.le) (U 0) -
      forwardExpCLM (μ - σ) (sub_pos.mpr hσμ) (U * q),
      W + stableTail (1 + σ) (by linarith)
        (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) X₀ * Rw)) = 0
  rw [hrw, hfirst]
  exact Prod.ext rfl hsecond

/-- Construct both weighted BCFs from a scalar tail. The unstable
component is obtained from its unweighted bounded orbit and the exact
tail formula; its weighted boundedness is a conclusion. -/
theorem exists_weighted_trajectory_residual_of_scalar_tail
    (a κ d₀ d₁ e₁ e₂ e₃ X₀ : ℂ) (μ σ rate M Mw Mr : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hσμ : σ < μ)
    (hσrate : σ ≤ rate) (hM : 0 ≤ M) (hMr : 0 ≤ Mr)
    (u w : ℝ≥0 → ℂ) (huc : Continuous u) (hwc : Continuous w)
    (hub : ∀ t, ‖u t‖ ≤ M * Real.exp (-rate * (t : ℝ)))
    (hwb : ∀ t, ‖w t‖ ≤ Mw)
    (hrc : Continuous (fun t : ℝ≥0 => stableRw a κ e₁ e₂ e₃
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ), u t, w t)))
    (hrb : ∀ t : ℝ≥0, ‖stableRw a κ e₁ e₂ e₃
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ), u t, w t)‖ ≤ Mr)
    (hsmall : ∀ t : ℝ≥0,
      ‖(X₀ * (Real.exp (-(t : ℝ)) : ℂ)) * (w t - κ) * (a + u t)‖ ≤ (1 / 2 : ℝ))
    (hu : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => u (Real.toNNReal s))
        (-(μ : ℂ) * u (Real.toNNReal t) + u (Real.toNNReal t) *
          stableRu a κ d₀ d₁ (μ : ℂ)
            (X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              u (Real.toNNReal t), w (Real.toNNReal t))) t)
    (hw : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => w (Real.toNNReal s))
        (w (Real.toNNReal t) + X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) *
          stableRw a κ e₁ e₂ e₃
            (X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              u (Real.toNNReal t), w (Real.toNNReal t))) t) :
    ∃ U W : StableTrajectory,
      ‖U‖ ≤ M ∧ ‖W‖ ≤ ‖X₀‖ * Mr / 2 ∧
      (∀ t, expDecayBCF σ hσ.le t * U t = u t) ∧
      (∀ t, expDecayBCF σ hσ.le t * W t = w t) ∧
      stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ
        ((X₀, u 0), (U, W)) = 0 := by
  let U := weightedDecayTrajectory σ rate M hσrate hM u huc hub
  let wB : StableTrajectory :=
    BoundedContinuousFunction.ofNormedAddCommGroup w hwc Mw hwb
  let rB : StableTrajectory := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ≥0 => stableRw a κ e₁ e₂ e₃
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ), u t, w t)) hrc Mr hrb
  let W := stableWeightedTailTrajectory σ hσ1 X₀ rB
  have hU (t : ℝ≥0) : expDecayBCF σ hσ.le t * U t = u t := by
    rw [expDecayBCF_apply, weightedDecayTrajectory_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show -σ * (t : ℝ) + σ * (t : ℝ) = 0 by ring]
    simp
  have hU0 : U 0 = u 0 := by
    simpa only [expDecayBCF_apply, NNReal.coe_zero, mul_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul] using hU 0
  have hUODE : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => U (Real.toNNReal s))
        (-((μ - σ : ℝ) : ℂ) * U (Real.toNNReal t) + U (Real.toNNReal t) *
          stableRu a κ d₀ d₁ (μ : ℂ)
            (X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              expDecayBCF σ hσ.le (Real.toNNReal t) * U (Real.toNNReal t),
              wB (Real.toNNReal t))) t := by
    intro t ht
    rw [hU]
    exact weightedDecayTrajectory_hasDerivAt σ rate M μ hσrate hM u huc hub
      (fun s => stableRu a κ d₀ d₁ (μ : ℂ)
        (X₀ * (Real.exp (-(s : ℝ)) : ℂ), u s, w s)) ht (hu t ht)
  have hwB : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => wB (Real.toNNReal s))
        (wB (Real.toNNReal t) + X₀ * (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) *
          rB (Real.toNNReal t)) t := hw
  have hr : ∀ t : ℝ≥0, rB t = stableRw a κ e₁ e₂ e₃
      (X₀ * (Real.exp (-(t : ℝ)) : ℂ),
        expDecayBCF σ hσ.le t * U t, wB t) := by
    intro t
    rw [hU]
    rfl
  have hsmall' : ∀ t : ℝ≥0,
      ‖(X₀ * (Real.exp (-(t : ℝ)) : ℂ)) * (wB t - κ) *
        (a + expDecayBCF σ hσ.le t * U t)‖ ≤ (1 / 2 : ℝ) := by
    intro t
    rw [hU]
    exact hsmall t
  have hR := stableTrajectoryResidual_eq_zero_of_scalar_ode
    a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ X₀ U wB rB hr hsmall' hUODE hwB
  have hrnorm : ‖rB‖ ≤ Mr :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hMr hrb
  refine ⟨U, W, norm_weightedDecayTrajectory_le σ rate M hσrate hM u huc hub,
    (norm_stableWeightedTailTrajectory_le σ hσ1 X₀ rB).trans ?_, hU, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrnorm (norm_nonneg X₀)) (by norm_num)
  · exact stableWeightedTailTrajectory_matches_ode σ hσ.le hσ1 X₀ wB rB hwB
  · simpa only [hU0] using hR

/-- Small scalar parameters and norm bounds suffice to enter the single
IFT uniqueness neighborhood, even when the solution BCFs are chosen
separately at each parameter. No continuous family of translations is
postulated. -/
theorem eventually_stable_graph_eq_of_small_solutions
    {ι : Type*} {l : Filter ι}
    (R : (ℂ × ℂ) × (StableTrajectory × StableTrajectory) →
      StableTrajectory × StableTrajectory)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory)
    (hunique : ∀ᶠ z in 𝓝 (0 : (ℂ × ℂ) × (StableTrajectory × StableTrajectory)),
      R z = 0 → φ z.1 = z.2)
    (x u : ι → ℂ) (B : ι → ℝ)
    (hx : Tendsto x l (𝓝 0)) (hu : Tendsto u l (𝓝 0))
    (hB : Tendsto B l (𝓝 0)) :
    ∀ᶠ i in l, ∀ U W : StableTrajectory,
      ‖U‖ ≤ ‖u i‖ → ‖W‖ ≤ B i → R ((x i, u i), (U, W)) = 0 →
        φ (x i, u i) = (U, W) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hunique
  have hxs : ∀ᶠ i in l, ‖x i‖ < ε :=
    hx.norm.eventually (eventually_lt_nhds (by simpa using hε))
  have hus : ∀ᶠ i in l, ‖u i‖ < ε :=
    hu.norm.eventually (eventually_lt_nhds (by simpa using hε))
  have hBs : ∀ᶠ i in l, B i < ε :=
    hB.eventually (eventually_lt_nhds hε)
  filter_upwards [hxs, hus, hBs] with i hxi hui hBi
  intro U W hU hW hR
  apply hball (y := ((x i, u i), (U, W))) ?_ hR
  simpa only [dist_zero_right, Prod.norm_def, max_lt_iff] using
    And.intro (And.intro hxi hui) (And.intro (hU.trans_lt hui) (hW.trans_lt hBi))

theorem expDecayBCF_add_apply (σ : ℝ) (hσ : 0 ≤ σ) (s t : ℝ≥0) :
    expDecayBCF σ hσ (s + t) =
      expDecayBCF σ hσ s * expDecayBCF σ hσ t := by
  simp only [expDecayBCF_apply, NNReal.coe_add]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem expDecayBCF_apply_ne_zero (σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    expDecayBCF σ hσ t ≠ 0 := by
  rw [expDecayBCF_apply]
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

/-- The common scalar Ru values determine the shift of the weighted
factors. This uses cancellation only at scalar nonzero exponential
values; no inverse of a BCF decay weight is formed. -/
theorem stable_weighted_factor_shift
    (σ : ℝ) (hσ : 0 ≤ σ) (τ : ℝ≥0) (r₀ rτ : StableTrajectory)
    (hfactor : ∀ s : ℝ≥0,
      expDecayBCF σ hσ s * rτ s = expDecayBCF σ hσ (τ + s) * r₀ (τ + s)) :
    rτ = (expDecayBCF σ hσ τ) • stableTimeShift τ r₀ := by
  ext s
  apply mul_left_cancel₀ (expDecayBCF_apply_ne_zero σ hσ s)
  rw [hfactor s, expDecayBCF_add_apply]
  simp only [BoundedContinuousFunction.smul_apply, stableTimeShift_apply, smul_eq_mul]
  ring

theorem stable_correction_shift_value
    (σ : ℝ) (hσ : 0 < σ) (τ : ℝ≥0) (r₀ rτ : StableTrajectory)
    (hfactor : ∀ s : ℝ≥0,
      expDecayBCF σ hσ.le s * rτ s =
        expDecayBCF σ hσ.le (τ + s) * r₀ (τ + s)) :
    stableTail σ hσ rτ 0 =
      expDecayBCF σ hσ.le τ * stableTail σ hσ r₀ τ := by
  rw [stable_weighted_factor_shift σ hσ.le τ r₀ rτ hfactor, map_smul]
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul,
    stableTail_timeShift_zero]

/-- Once the shift identity has been established by actual trajectory
uniqueness, only the scalar tail FTC is needed to differentiate J. -/
theorem stable_correction_hasDerivAt_of_tail_identity
    (σ : ℝ) (hσ : 0 < σ) (r : StableTrajectory)
    (j : ℝ≥0 → ℂ)
    (hj : ∀ t : ℝ≥0,
      j t = expDecayBCF σ hσ.le t * stableTail σ hσ r t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => j (Real.toNNReal s))
      (-expDecayBCF σ hσ.le (Real.toNNReal t) * r (Real.toNNReal t)) t := by
  have he := (((hasDerivAt_id t).const_mul (-σ)).exp).ofReal_comp
  simp only [id_eq, mul_one] at he
  have hd := he.mul (stableTail_hasDerivAt σ hσ r t ht)
  have hev : (fun s : ℝ => j (Real.toNNReal s)) =ᶠ[𝓝 t]
      (fun s : ℝ => (Real.exp (-σ * s) : ℂ) *
        stableTail σ hσ r (Real.toNNReal s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [hj, expDecayBCF_apply, Real.coe_toNNReal _ hs.le]
  convert hd.congr_of_eventuallyEq hev using 1
  simp only [expDecayBCF_apply, Real.coe_toNNReal _ ht.le]
  push_cast
  ring

/-- The correction has the positive sign Q=u·exp(J). The cancellation
uses exactly J′=−Ru; no expansion or estimate is substituted for it. -/
theorem stable_linearized_hasDerivAt
    (μ : ℝ) (u j r : ℝ≥0 → ℂ) {t : ℝ}
    (hu : HasDerivAt (fun s : ℝ => u (Real.toNNReal s))
      (-(μ : ℂ) * u (Real.toNNReal t) +
        u (Real.toNNReal t) * r (Real.toNNReal t)) t)
    (hj : HasDerivAt (fun s : ℝ => j (Real.toNNReal s))
      (-r (Real.toNNReal t)) t) :
    HasDerivAt (fun s : ℝ => u (Real.toNNReal s) *
      Complex.exp (j (Real.toNNReal s)))
      (-(μ : ℂ) * (u (Real.toNNReal t) *
        Complex.exp (j (Real.toNNReal t)))) t := by
  convert hu.mul hj.cexp using 1
  ring

/-- A continuous corrected orbit satisfying its actual ODE has the exact
exponential formula on the full nonnegative real tail. -/
theorem stable_linearized_exponential_formula
    (μ : ℝ) (hμ : 0 < μ) (u j r : ℝ≥0 → ℂ)
    (huc : Continuous u) (hjc : Continuous j)
    (hu : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => u (Real.toNNReal s))
        (-(μ : ℂ) * u (Real.toNNReal t) +
          u (Real.toNNReal t) * r (Real.toNNReal t)) t)
    (hj : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => j (Real.toNNReal s))
        (-r (Real.toNNReal t)) t) (t : ℝ≥0) :
    u t * Complex.exp (j t) =
      (Real.exp (-μ * (t : ℝ)) : ℂ) *
        (u 0 * Complex.exp (j 0)) := by
  let Q : ℝ≥0 → ℂ := fun s => u s * Complex.exp (j s)
  have hQc : Continuous Q := by
    exact huc.mul (Complex.continuous_exp.comp hjc)
  have hQd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => Q (Real.toNNReal s))
        (-(μ : ℂ) * Q (Real.toNNReal t) +
          (0 : StableTrajectory) (Real.toNNReal t)) t := by
    intro s hs
    simpa only [Q, BoundedContinuousFunction.coe_zero, Pi.zero_apply, add_zero] using
      stable_linearized_hasDerivAt μ u j r (hu s hs) (hj s hs)
  simpa only [Q, map_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply, add_zero] using
    forwardExpCLM_variation_of_constants μ hμ Q hQc 0 hQd t


/-! ## ExponentialStableActualState -/

/-- Intermediate scalar ODE data. An actual ExponentialPair constructs
this record below, including its decay and nonvanishing fields. -/
structure StableRealScalarOrbit (a κ d₀ d₁ e₁ e₂ e₃ : ℂ) (μ : ℝ) where
  u : ℝ → ℂ
  w : ℝ → ℂ
  u_tendsto : Tendsto u atTop (𝓝 0)
  w_tendsto : Tendsto w atTop (𝓝 0)
  lower : ℝ
  u_ne_zero : ∀ t : ℝ, lower ≤ t → u t ≠ 0
  u_hasDerivAt : ∀ t : ℝ, lower ≤ t → HasDerivAt u
    (-(μ : ℂ) * u t + u t * stableRu a κ d₀ d₁ (μ : ℂ)
      (Complex.exp (-(t : ℂ)), u t, w t)) t
  w_hasDerivAt : ∀ t : ℝ, lower ≤ t → HasDerivAt w
    (w t + Complex.exp (-(t : ℂ)) * stableRw a κ e₁ e₂ e₃
      (Complex.exp (-(t : ℂ)), u t, w t)) t
  u_decay : ∀ s t : ℝ, lower ≤ s → s ≤ t →
    ‖u t‖ ≤ ‖u s‖ * Real.exp (-(μ / 2) * (t - s))

theorem ExponentialPair.canonical_real_stable_state_tendsto
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    (j : Fin 3)
    (hj : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun z => chartFiniteMap (sphereGermValue f z))
      (rightSectorAtTop δ) (𝓝 (a j))) :
    Tendsto (fun r : ℝ =>
      (Complex.exp (-(r : ℂ)),
        chartFiniteMap (sphereGermValue f (r : ℂ)) - a j,
        Complex.exp (r : ℂ) /
          chartFiniteMap (sphereGermValue g (r : ℂ)) + κ))
      atTop (𝓝 (0, 0, 0)) := by
  have hray : Tendsto (fun r : ℝ => (r : ℂ)) atTop (rightSectorAtTop 1) := by
    simpa using tendsto_ray_rightSector 0
  have hx : Tendsto (fun r : ℝ => Complex.exp (-(r : ℂ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using
      (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
  have hu : Tendsto (fun r : ℝ =>
      chartFiniteMap (sphereGermValue f (r : ℂ)) - a j) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using ((hj 1 (by norm_num)).comp hray).sub_const (a j)
  have hw : Tendsto (fun r : ℝ => Complex.exp (r : ℂ) /
      chartFiniteMap (sphereGermValue g (r : ℂ)) + κ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_comm, neg_add_cancel] using
      ((h.canonical_inverse_g_mul_exp_tendsto_rightSector (by norm_num : (0 : ℝ) < 1)).comp
        hray).add_const κ
  exact hx.prodMk_nhds (hu.prodMk_nhds hw)

/-- All scalar-tail inputs are produced from the original pair and the
same marked value and positive exponent as the verified sector theorem.
No exponential-decay or graph-membership premise is added to the pair. -/
theorem ExponentialPair.exists_canonical_real_scalar_orbit
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∃ j : Fin 3, ∃ μ : ℝ, 0 < μ ∧
      (μ : ℂ) = -(κ ^ 2 * deriv (cubicP a) (a j)) ∧
      ∃ O : StableRealScalarOrbit (a j) κ (deriv (cubicP a) (a j))
          (3 * a j - stableCubicE1 a) (stableCubicE1 a)
          (stableCubicE2 a) (stableCubicE3 a) μ,
        (∀ r : ℝ, O.u r = chartFiniteMap (sphereGermValue f (r : ℂ)) - a j) ∧
        (∀ r : ℝ, O.w r = Complex.exp (r : ℂ) /
          chartFiniteMap (sphereGermValue g (r : ℂ)) + κ) := by
  obtain ⟨j, μ, hj, hμ, hμc, Rd, hRd, hdecay⟩ :=
    h.exists_canonical_real_exponential_decay
  let u : ℝ → ℂ := fun r => chartFiniteMap (sphereGermValue f (r : ℂ)) - a j
  let w : ℝ → ℂ := fun r => Complex.exp (r : ℂ) /
    chartFiniteMap (sphereGermValue g (r : ℂ)) + κ
  have hstate := h.canonical_real_stable_state_tendsto j hj
  have hul : Tendsto u atTop (𝓝 0) := hstate.snd_nhds.fst_nhds
  have hwl : Tendsto w atTop (𝓝 0) := hstate.snd_nhds.snd_nhds
  obtain ⟨Rs, hRs⟩ := eventually_atTop.mp
    ((h.canonical_real_stable_system_eventually j (μ : ℂ)).and
      h.canonical_real_good_eventually)
  let R : ℝ := max Rd Rs
  let O : StableRealScalarOrbit (a j) κ (deriv (cubicP a) (a j))
      (3 * a j - stableCubicE1 a) (stableCubicE1 a)
      (stableCubicE2 a) (stableCubicE3 a) μ := {
    u := u
    w := w
    u_tendsto := hul
    w_tendsto := hwl
    lower := R
    u_ne_zero := by
      intro r hr
      exact sub_ne_zero.mpr ((hRs r ((le_max_right Rd Rs).trans hr)).2.2 j)
    u_hasDerivAt := by
      intro r hr
      exact (hRs r ((le_max_right Rd Rs).trans hr)).1.1
    w_hasDerivAt := by
      intro r hr
      exact (hRs r ((le_max_right Rd Rs).trans hr)).1.2
    u_decay := by
      intro s t hs hst
      exact hdecay s t ((le_max_left Rd Rs).trans hs) hst }
  exact ⟨j, μ, hμ, hμc, O, fun _ => rfl, fun _ => rfl⟩

theorem continuous_stableRw_of_small_state
    {A : Type*} [TopologicalSpace A]
    (a κ e₁ e₂ e₃ : ℂ) (X u w : A → ℂ)
    (hX : Continuous X) (hu : Continuous u) (hw : Continuous w)
    (hsmall : ∀ t : A, ‖X t * (w t - κ) * (a + u t)‖ ≤ (1 / 2 : ℝ)) :
    Continuous (fun t => stableRw a κ e₁ e₂ e₃ (X t, u t, w t)) := by
  have hD : ∀ t : A, stableDenominator a κ (X t, u t, w t) ≠ 0 := by
    intro t
    exact isUnit_iff_ne_zero.mp (stableDenominator_isUnit_of_norm_lt a κ (X t) (u t) (w t)
      ((hsmall t).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)))
  have hDc : Continuous (fun t => stableDenominator a κ (X t, u t, w t)) := by
    unfold stableDenominator
    fun_prop
  have hN : Continuous (fun t : A => κ * (w t - κ) *
      (a + u t - e₁ + e₂ * X t * (w t - κ) - e₃ * X t ^ 2 * (w t - κ) ^ 2)) := by
    fun_prop
  simpa only [stableRw, Ring.inverse_eq_inv] using hN.fun_mul (hDc.fun_inv₀ hD)

/-- One fixed small state neighborhood supplies bounds for every real
tail at once. The Rw bound need not tend to zero. -/
theorem exists_uniform_scalar_stable_tail_bounds
    (a κ e₁ e₂ e₃ : ℂ) (X u w : ℝ → ℂ)
    (hx : Tendsto X atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 0))
    (hw : Tendsto w atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ t : ℝ, R ≤ t →
      ‖w t‖ ≤ 1 ∧ ‖stableRw a κ e₁ e₂ e₃ (X t, u t, w t)‖ ≤ C ∧
        ‖X t * (w t - κ) * (a + u t)‖ ≤ (1 / 2 : ℝ) := by
  let q₀ := stableRw a κ e₁ e₂ e₃ (0, 0, 0)
  have hstate := hx.prodMk_nhds (hu.prodMk_nhds hw)
  have hq : Tendsto (fun t => stableRw a κ e₁ e₂ e₃ (X t, u t, w t))
      atTop (𝓝 q₀) := (analyticAt_stableRw a κ e₁ e₂ e₃).continuousAt.tendsto.comp hstate
  have hprod : Tendsto (fun t => X t * (w t - κ) * (a + u t)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hx.mul (hw.sub_const κ)).mul (hu.const_add a)
  have hwb : ∀ᶠ t : ℝ in atTop, ‖w t‖ ≤ 1 :=
    (hw.norm.eventually (eventually_lt_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 : ℝ)))).mono
      fun _ ht => ht.le
  have hqb : ∀ᶠ t : ℝ in atTop,
      ‖stableRw a κ e₁ e₂ e₃ (X t, u t, w t)‖ ≤ ‖q₀‖ + 1 :=
    (hq.norm.eventually (eventually_lt_nhds (by linarith : ‖q₀‖ < ‖q₀‖ + 1))).mono
      fun _ ht => ht.le
  have hpb : ∀ᶠ t : ℝ in atTop,
      ‖X t * (w t - κ) * (a + u t)‖ ≤ (1 / 2 : ℝ) :=
    (hprod.norm.eventually (eventually_lt_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 / 2 : ℝ)))).mono
      fun _ ht => ht.le
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hwb.and (hqb.and hpb))
  exact ⟨‖q₀‖ + 1, by linarith [norm_nonneg q₀], R, hR⟩


/-! ## ExponentialStableTailCapture -/

theorem stable_exp_neg_real_add (R s : ℝ) :
    Complex.exp (-((R + s : ℝ) : ℂ)) =
      Complex.exp (-(R : ℂ)) * (Real.exp (-s) : ℂ) := by
  rw [show -((R + s : ℝ) : ℂ) = -(R : ℂ) + (-s : ℝ) by push_cast; ring,
    Complex.exp_add, Complex.ofReal_exp]

/-- Positive real time is used for derivatives. The initial endpoint is
handled by continuity of the original scalar orbit on its closed tail. -/
theorem StableRealScalarOrbit.continuous_shifted_u
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    {R : ℝ} (hR : O.lower ≤ R) :
    Continuous (fun s : ℝ≥0 => O.u (R + (s : ℝ))) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hs : ContinuousAt (fun t : ℝ≥0 => R + (t : ℝ)) s :=
    (continuous_const.add NNReal.continuous_coe).continuousAt
  exact ContinuousAt.comp' (f := fun t : ℝ≥0 => R + (t : ℝ)) (g := O.u) (x := s)
    ((O.u_hasDerivAt (R + (s : ℝ))
      (hR.trans (le_add_of_nonneg_right s.coe_nonneg))).continuousAt) hs

theorem StableRealScalarOrbit.continuous_shifted_w
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    {R : ℝ} (hR : O.lower ≤ R) :
    Continuous (fun s : ℝ≥0 => O.w (R + (s : ℝ))) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hs : ContinuousAt (fun t : ℝ≥0 => R + (t : ℝ)) s :=
    (continuous_const.add NNReal.continuous_coe).continuousAt
  exact ContinuousAt.comp' (f := fun t : ℝ≥0 => R + (t : ℝ)) (g := O.w) (x := s)
    ((O.w_hasDerivAt (R + (s : ℝ))
      (hR.trans (le_add_of_nonneg_right s.coe_nonneg))).continuousAt) hs

/-- The shifted scalar orbit has the exact small initial coefficient
exp(-R); all nonlinear terms keep the same parameters. -/
theorem StableRealScalarOrbit.shifted_u_hasDerivAt
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    {R t : ℝ} (hR : O.lower ≤ R) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => O.u (R + (Real.toNNReal s : ℝ)))
      (-(μ : ℂ) * O.u (R + (Real.toNNReal t : ℝ)) +
        O.u (R + (Real.toNNReal t : ℝ)) *
          stableRu a κ d₀ d₁ (μ : ℂ)
            (Complex.exp (-(R : ℂ)) *
              (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              O.u (R + (Real.toNNReal t : ℝ)),
              O.w (R + (Real.toNNReal t : ℝ)))) t := by
  have hRt : O.lower ≤ R + t := hR.trans (le_add_of_nonneg_right ht.le)
  have hd := (O.u_hasDerivAt (R + t) hRt).scomp t ((hasDerivAt_id t).const_add R)
  have heq : (fun s : ℝ => O.u (R + (Real.toNNReal s : ℝ)))
      =ᶠ[𝓝 t] (fun s : ℝ => O.u (R + s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [Real.coe_toNNReal _ hs.le]
  simpa only [Real.coe_toNNReal _ ht.le, one_smul, stable_exp_neg_real_add] using
    hd.congr_of_eventuallyEq heq

theorem StableRealScalarOrbit.shifted_w_hasDerivAt
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    {R t : ℝ} (hR : O.lower ≤ R) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => O.w (R + (Real.toNNReal s : ℝ)))
      (O.w (R + (Real.toNNReal t : ℝ)) +
        Complex.exp (-(R : ℂ)) *
          (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ) *
          stableRw a κ e₁ e₂ e₃
            (Complex.exp (-(R : ℂ)) *
              (Real.exp (-(Real.toNNReal t : ℝ)) : ℂ),
              O.u (R + (Real.toNNReal t : ℝ)),
              O.w (R + (Real.toNNReal t : ℝ)))) t := by
  have hRt : O.lower ≤ R + t := hR.trans (le_add_of_nonneg_right ht.le)
  have hd := (O.w_hasDerivAt (R + t) hRt).scomp t ((hasDerivAt_id t).const_add R)
  have heq : (fun s : ℝ => O.w (R + (Real.toNNReal s : ℝ)))
      =ᶠ[𝓝 t] (fun s : ℝ => O.w (R + s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [Real.coe_toNNReal _ hs.le]
  simpa only [Real.coe_toNNReal _ ht.le, one_smul, stable_exp_neg_real_add] using
    hd.congr_of_eventuallyEq heq

/-- Every sufficiently late actual tail enters the same implicit graph's
uniqueness neighborhood. The BCF choices need not be continuous in R.
Their norm bounds follow from the scalar decay and the tail integral;
neither bounded weighted unstable coordinates nor graph membership is an
extra hypothesis. -/
theorem StableRealScalarOrbit.eventually_weighted_graph_capture
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ σ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    (hμ : 0 < μ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hσμ : σ < μ) (hσhalf : σ ≤ μ / 2)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory)
    (hunique : ∀ᶠ z in 𝓝 (0 : (ℂ × ℂ) × (StableTrajectory × StableTrajectory)),
      stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ z = 0 →
        φ z.1 = z.2) :
    ∀ᶠ R : ℝ in atTop, ∀ s : ℝ≥0,
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).1 s =
        O.u (R + (s : ℝ)) ∧
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).2 s =
        O.w (R + (s : ℝ)) := by
  let X : ℝ → ℂ := fun R => Complex.exp (-(R : ℂ))
  have hx : Tendsto X atTop (𝓝 0) := by
    simpa only [X, Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using
      (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
  obtain ⟨C, hC, Rb, hb⟩ := exists_uniform_scalar_stable_tail_bounds
    a κ e₁ e₂ e₃ X O.u O.w hx O.u_tendsto O.w_tendsto
  let B : ℝ → ℝ := fun R => ‖X R‖ * C / 2
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B, norm_zero, zero_mul, zero_div] using
      (hx.norm.mul_const C).div_const 2
  have htrap := eventually_stable_graph_eq_of_small_solutions
    (stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ)
    φ hunique X O.u B hx O.u_tendsto hB
  filter_upwards [htrap, eventually_ge_atTop (max O.lower Rb)] with R hgraph hR
  have hRl : O.lower ≤ R := (le_max_left _ _).trans hR
  have hRb : Rb ≤ R := (le_max_right _ _).trans hR
  let u : ℝ≥0 → ℂ := fun s => O.u (R + (s : ℝ))
  let w : ℝ≥0 → ℂ := fun s => O.w (R + (s : ℝ))
  have huc : Continuous u := O.continuous_shifted_u hRl
  have hwc : Continuous w := O.continuous_shifted_w hRl
  have hu0 : u 0 = O.u R := by simp only [u, NNReal.coe_zero, add_zero]
  have hfuture (s : ℝ≥0) : Rb ≤ R + (s : ℝ) :=
    hRb.trans (le_add_of_nonneg_right s.coe_nonneg)
  have hub (s : ℝ≥0) : ‖u s‖ ≤ ‖O.u R‖ * Real.exp (-(μ / 2) * (s : ℝ)) := by
    simpa only [u, add_sub_cancel_left] using
      O.u_decay R (R + (s : ℝ)) hRl (le_add_of_nonneg_right s.coe_nonneg)
  have hwb (s : ℝ≥0) : ‖w s‖ ≤ 1 := (hb _ (hfuture s)).1
  have hrb (s : ℝ≥0) :
      ‖stableRw a κ e₁ e₂ e₃
        (X R * (Real.exp (-(s : ℝ)) : ℂ), u s, w s)‖ ≤ C := by
    simpa only [X, u, w, ← stable_exp_neg_real_add] using (hb _ (hfuture s)).2.1
  have hsmall (s : ℝ≥0) :
      ‖(X R * (Real.exp (-(s : ℝ)) : ℂ)) * (w s - κ) * (a + u s)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [X, u, w, ← stable_exp_neg_real_add] using (hb _ (hfuture s)).2.2
  have hxc : Continuous (fun s : ℝ≥0 => X R * (Real.exp (-(s : ℝ)) : ℂ)) := by
    fun_prop
  have hrc := continuous_stableRw_of_small_state a κ e₁ e₂ e₃
    (fun s : ℝ≥0 => X R * (Real.exp (-(s : ℝ)) : ℂ)) u w hxc huc hwc hsmall
  obtain ⟨U, W, hU, hW, hu, hw, hres⟩ :=
    exists_weighted_trajectory_residual_of_scalar_tail
      a κ d₀ d₁ e₁ e₂ e₃ (X R) μ σ (μ / 2) ‖O.u R‖ 1 C
      hσ hσ1 hσμ hσhalf (norm_nonneg _) hC.le u w huc hwc hub hwb hrc hrb hsmall
      (fun t ht => O.shifted_u_hasDerivAt hRl ht)
      (fun t ht => O.shifted_w_hasDerivAt hRl ht)
  have hres' : stableTrajectoryResidual a κ d₀ d₁ e₁ e₂ e₃ μ σ hσ hσ1 hσμ
      ((X R, O.u R), (U, W)) = 0 := by simpa only [hu0] using hres
  have heq : φ (X R, O.u R) = (U, W) := hgraph U W hU hW hres'
  intro s
  rw [show Complex.exp (-(R : ℂ)) = X R from rfl, heq]
  exact ⟨hu s, hw s⟩


/-! ## ExponentialStableCoordinateFlow -/

noncomputable def stableTrajectoryCorrectionFactor
    (a κ d₀ d₁ μ : ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory) (p : ℂ × ℂ) :
    StableTrajectory :=
  stableRuWeightedFactor
    (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
    (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
    (algebraMap ℂ StableTrajectory μ) (expDecayBCF σ hσ.le)
    (stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) p.1,
      (φ p).1, (φ p).2)

theorem stableTrajectoryCorrection_eq_tail_factor
    (a κ d₀ d₁ μ : ℂ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory) (p : ℂ × ℂ) :
    stableTrajectoryCorrection a κ d₀ d₁ μ σ hσ hσ1 φ p =
      stableTail σ hσ
        (stableTrajectoryCorrectionFactor a κ d₀ d₁ μ σ hσ hσ1 φ p) 0 := rfl

theorem stable_real_exp_shift (R : ℝ) (s : ℝ≥0) :
    Complex.exp (-((R + (s : ℝ) : ℝ) : ℂ)) =
      Complex.exp (-(R : ℂ)) * (Real.exp (-(s : ℝ)) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Evaluation of the extracted factor is justified using a genuine
Banach unit denominator. The equality never inverts a decaying BCF. -/
theorem stableTrajectoryCorrectionFactor_mul_decay
    (a κ d₀ d₁ μ : ℂ) (hμ : μ = -(κ ^ 2 * d₀))
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory) (p : ℂ × ℂ)
    (u w : ℝ≥0 → ℂ)
    (hU : ∀ s, expDecayBCF σ hσ.le s * (φ p).1 s = u s)
    (hW : ∀ s, expDecayBCF σ hσ.le s * (φ p).2 s = w s)
    (hsmall : ∀ s : ℝ≥0,
      ‖(p.1 * (Real.exp (-(s : ℝ)) : ℂ)) * (w s - κ) * (a + u s)‖ ≤ (1 / 2 : ℝ))
    (s : ℝ≥0) :
    expDecayBCF σ hσ.le s *
        stableTrajectoryCorrectionFactor a κ d₀ d₁ μ σ hσ hσ1 φ p s =
      stableRu a κ d₀ d₁ μ
        (p.1 * (Real.exp (-(s : ℝ)) : ℂ), u s, w s) := by
  let E := expDecayBCF σ hσ.le
  let Xc := stableTrajectorySeed (1 - σ) (sub_nonneg.mpr hσ1.le) p.1
  let X := stableTrajectorySeed 1 zero_le_one p.1
  let U := (φ p).1
  let W := (φ p).2
  have hU' (t : ℝ≥0) : E t * U t = u t := hU t
  have hW' (t : ℝ≥0) : E t * W t = w t := hW t
  have hseed : E * Xc = X := by
    ext t
    have he : expDecayBCF σ hσ.le t *
        expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le) t = expDecayBCF 1 zero_le_one t := by
      simpa only [show σ + (1 - σ) = (1 : ℝ) by ring,
        BoundedContinuousFunction.mul_apply] using
        (congrArg (fun q : StableTrajectory => q t)
          (expDecayBCF_add σ (1 - σ) hσ.le (sub_nonneg.mpr hσ1.le))).symm
    simp only [E, Xc, X, BoundedContinuousFunction.mul_apply,
      stableTrajectorySeed_apply]
    change expDecayBCF σ hσ.le t *
      (p.1 * expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le) t) =
        p.1 * expDecayBCF 1 zero_le_one t
    calc
      _ = p.1 * (expDecayBCF σ hσ.le t *
        expDecayBCF (1 - σ) (sub_nonneg.mpr hσ1.le) t) := by ring
      _ = _ := by rw [he]
  have hD : IsUnit (stableDenominator (algebraMap ℂ StableTrajectory a)
      (algebraMap ℂ StableTrajectory κ) (X, E * U, E * W)) := by
    apply stableTrajectory_denominator_isUnit_of_pointwise_le_half
    intro t
    simpa only [X, stableTrajectorySeed_apply, neg_one_mul,
      BoundedContinuousFunction.mul_apply, hU' t, hW' t] using hsmall t
  have hμA : algebraMap ℂ StableTrajectory μ =
      -((algebraMap ℂ StableTrajectory κ) ^ 2 * algebraMap ℂ StableTrajectory d₀) := by
    simpa only [map_neg, map_mul, map_pow] using
      congrArg (algebraMap ℂ StableTrajectory) hμ
  have hfactor := stableRu_weight_factor
    (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
    (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
    (algebraMap ℂ StableTrajectory μ) E Xc U W hμA
  rw [hseed] at hfactor
  have hs := congrArg (fun q : StableTrajectory => q s) hfactor
  calc
    _ = stableRu (algebraMap ℂ StableTrajectory a) (algebraMap ℂ StableTrajectory κ)
        (algebraMap ℂ StableTrajectory d₀) (algebraMap ℂ StableTrajectory d₁)
        (algebraMap ℂ StableTrajectory μ) (X, E * U, E * W) s := by
      exact hs.symm
    _ = _ := by
      rw [stableRu_trajectory_apply _ _ _ _ _ _ _ _ hD]
      simp only [X, stableTrajectorySeed_apply, neg_one_mul,
        BoundedContinuousFunction.mul_apply, hU' s, hW' s]

/-- Every shifted captured orbit has the same scalar Ru values. This
gives the exact scalar tail identity for J without differentiating any
family of BCF translations. -/
theorem stableTrajectoryCorrection_real_tail_identity
    (a κ d₀ d₁ μ : ℂ) (hμ : μ = -(κ ^ 2 * d₀))
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory)
    (u w : ℝ → ℂ) (T : ℝ)
    (hcap : ∀ R : ℝ, T ≤ R → ∀ s : ℝ≥0,
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), u R)).1 s = u (R + s) ∧
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), u R)).2 s = w (R + s))
    (hsmall : ∀ R : ℝ, T ≤ R →
      ‖Complex.exp (-(R : ℂ)) * (w R - κ) * (a + u R)‖ ≤ (1 / 2 : ℝ))
    (τ : ℝ≥0) :
    stableTrajectoryCorrection a κ d₀ d₁ μ σ hσ hσ1 φ
        (Complex.exp (-((T + (τ : ℝ) : ℝ) : ℂ)), u (T + τ)) =
      expDecayBCF σ hσ.le τ * stableTail σ hσ
        (stableTrajectoryCorrectionFactor a κ d₀ d₁ μ σ hσ hσ1 φ
          (Complex.exp (-(T : ℂ)), u T)) τ := by
  let p : ℝ → ℂ × ℂ := fun R => (Complex.exp (-(R : ℂ)), u R)
  let r : ℝ → StableTrajectory := fun R =>
    stableTrajectoryCorrectionFactor a κ d₀ d₁ μ σ hσ hσ1 φ (p R)
  have hfactor (R : ℝ) (hR : T ≤ R) (s : ℝ≥0) :
      expDecayBCF σ hσ.le s * r R s =
        stableRu a κ d₀ d₁ μ
          (Complex.exp (-((R + (s : ℝ) : ℝ) : ℂ)), u (R + s), w (R + s)) := by
    have hh := stableTrajectoryCorrectionFactor_mul_decay a κ d₀ d₁ μ hμ
      σ hσ hσ1 φ (p R) (fun s => u (R + s)) (fun s => w (R + s))
      (fun s => (hcap R hR s).1) (fun s => (hcap R hR s).2) ?_ s
    · simpa only [p, Prod.fst, ← stable_real_exp_shift] using hh
    · intro t
      simpa only [p, Prod.fst, ← stable_real_exp_shift] using
        hsmall (R + t) (hR.trans (le_add_of_nonneg_right t.coe_nonneg))
  have hcompare (s : ℝ≥0) :
      expDecayBCF σ hσ.le s * r (T + τ) s =
        expDecayBCF σ hσ.le (τ + s) * r T (τ + s) := by
    rw [hfactor (T + τ) (le_add_of_nonneg_right τ.coe_nonneg), hfactor T le_rfl]
    simp only [NNReal.coe_add, add_assoc]
  rw [stableTrajectoryCorrection_eq_tail_factor]
  exact stable_correction_shift_value σ hσ τ (r T) (r (T + τ)) hcompare

theorem stable_exponential_rescale (μ T r : ℝ) (q : ℂ) :
    (Real.exp (-μ * (r - T)) : ℂ) * q =
      (Complex.exp ((μ : ℂ) * (T : ℂ)) * q) *
        Complex.exp (-(μ : ℂ) * (r : ℂ)) := by
  rw [Complex.ofReal_exp]
  calc
    _ = q * Complex.exp ((μ : ℂ) * (T : ℂ) + -(μ : ℂ) * (r : ℂ)) := by
      rw [mul_comm]
      congr 2
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add]; ring

/-- Captured actual scalar tails give the exact corrected exponential,
including a nonzero leading constant obtained from the original orbit's
nonvanishing. No nonzero-constant premise is introduced. -/
theorem StableRealScalarOrbit.linearized_formula_of_capture
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ σ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    (hμ : 0 < μ) (hμc : (μ : ℂ) = -(κ ^ 2 * d₀))
    (hσ : 0 < σ) (hσ1 : σ < 1)
    (φ : ℂ × ℂ → StableTrajectory × StableTrajectory)
    (T : ℝ) (hT : O.lower ≤ T)
    (hcap : ∀ R : ℝ, T ≤ R → ∀ s : ℝ≥0,
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).1 s =
        O.u (R + s) ∧
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).2 s =
        O.w (R + s))
    (hsmall : ∀ R : ℝ, T ≤ R →
      ‖Complex.exp (-(R : ℂ)) * (O.w R - κ) * (a + O.u R)‖ ≤ (1 / 2 : ℝ)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ r : ℝ, T ≤ r →
      O.u r * Complex.exp (stableTrajectoryCorrection a κ d₀ d₁ (μ : ℂ)
        σ hσ hσ1 φ (Complex.exp (-(r : ℂ)), O.u r)) =
          C * Complex.exp (-(μ : ℂ) * (r : ℂ)) := by
  let u : ℝ≥0 → ℂ := fun s => O.u (T + s)
  let j : ℝ≥0 → ℂ := fun s => stableTrajectoryCorrection a κ d₀ d₁ (μ : ℂ)
    σ hσ hσ1 φ (Complex.exp (-((T + (s : ℝ) : ℝ) : ℂ)), O.u (T + s))
  let q : ℝ≥0 → ℂ := fun s => stableRu a κ d₀ d₁ (μ : ℂ)
    (Complex.exp (-((T + (s : ℝ) : ℝ) : ℂ)), O.u (T + s), O.w (T + s))
  let r₀ := stableTrajectoryCorrectionFactor a κ d₀ d₁ (μ : ℂ) σ hσ hσ1 φ
    (Complex.exp (-(T : ℂ)), O.u T)
  have hfactor (s : ℝ≥0) : expDecayBCF σ hσ.le s * r₀ s = q s := by
    have hh := stableTrajectoryCorrectionFactor_mul_decay a κ d₀ d₁ (μ : ℂ) hμc
      σ hσ hσ1 φ (Complex.exp (-(T : ℂ)), O.u T)
      (fun s => O.u (T + s)) (fun s => O.w (T + s))
      (fun s => (hcap T le_rfl s).1) (fun s => (hcap T le_rfl s).2) ?_ s
    · simpa only [q, ← stable_real_exp_shift] using hh
    · intro t
      simpa only [← stable_real_exp_shift] using
        hsmall (T + t) (le_add_of_nonneg_right t.coe_nonneg)
  have hj (s : ℝ≥0) : j s = expDecayBCF σ hσ.le s * stableTail σ hσ r₀ s :=
    stableTrajectoryCorrection_real_tail_identity a κ d₀ d₁ (μ : ℂ) hμc
      σ hσ hσ1 φ O.u O.w T hcap hsmall s
  have huc : Continuous u := O.continuous_shifted_u hT
  have hjc : Continuous j := by
    have heq : j = fun s => expDecayBCF σ hσ.le s * stableTail σ hσ r₀ s := funext hj
    rw [heq]
    exact (expDecayBCF σ hσ.le).continuous.mul (stableTail σ hσ r₀).continuous
  have hud : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => u (Real.toNNReal s))
        (-(μ : ℂ) * u (Real.toNNReal t) +
          u (Real.toNNReal t) * q (Real.toNNReal t)) t := by
    intro t ht
    simpa only [u, q, ← stable_real_exp_shift] using O.shifted_u_hasDerivAt hT ht
  have hjd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => j (Real.toNNReal s)) (-q (Real.toNNReal t)) t := by
    intro t ht
    have hd := stable_correction_hasDerivAt_of_tail_identity σ hσ r₀ j hj ht
    convert hd using 1
    rw [← hfactor]
    ring
  let C := Complex.exp ((μ : ℂ) * (T : ℂ)) * (u 0 * Complex.exp (j 0))
  have hu0 : u 0 ≠ 0 := by
    simpa only [u, NNReal.coe_zero, add_zero] using O.u_ne_zero T hT
  refine ⟨C, mul_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero hu0 (Complex.exp_ne_zero _)), ?_⟩
  intro r hr
  let τ : ℝ≥0 := Real.toNNReal (r - T)
  have hτ : (τ : ℝ) = r - T := Real.coe_toNNReal _ (sub_nonneg.mpr hr)
  have hTτ : T + (τ : ℝ) = r := by rw [hτ]; ring
  have hformula := stable_linearized_exponential_formula μ hμ u j q huc hjc hud hjd τ
  have hformula' : O.u r * Complex.exp (stableTrajectoryCorrection a κ d₀ d₁ (μ : ℂ)
      σ hσ hσ1 φ (Complex.exp (-(r : ℂ)), O.u r)) =
      (Real.exp (-μ * (r - T)) : ℂ) * (u 0 * Complex.exp (j 0)) := by
    simpa only [u, j, hτ, show T + (r - T) = r by ring] using hformula
  exact hformula'.trans (stable_exponential_rescale μ T r (u 0 * Complex.exp (j 0)))

/-- The analytic stable model is constructed from an actual scalar
orbit. The same H,V,J work for the complete sufficiently late real tail,
and the leading constant is proved nonzero internally. -/
theorem StableRealScalarOrbit.exists_analytic_real_models
    {a κ d₀ d₁ e₁ e₂ e₃ : ℂ} {μ : ℝ}
    (O : StableRealScalarOrbit a κ d₀ d₁ e₁ e₂ e₃ μ)
    (hμ : 0 < μ) (hμc : (μ : ℂ) = -(κ ^ 2 * d₀)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∃ H V J : ℂ × ℂ → ℂ,
      AnalyticAt ℂ H 0 ∧ AnalyticAt ℂ V 0 ∧ H 0 = 0 ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 0,
        H p * Complex.exp (J (p.1, H p)) = p.2) ∧
      ∃ T : ℝ, ∀ r : ℝ, T ≤ r →
        O.u r = H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))) ∧
        O.w r = V (Complex.exp (-(r : ℂ)), O.u r) + κ := by
  obtain ⟨σ, hσ, hσtop⟩ := exists_between
    (lt_min zero_lt_one (half_pos hμ) : (0 : ℝ) < min 1 (μ / 2))
  have hσ1 : σ < 1 := hσtop.trans_le (min_le_left _ _)
  have hσhalf : σ ≤ μ / 2 := hσtop.le.trans (min_le_right _ _)
  have hσμ : σ < μ := hσhalf.trans_lt (half_lt_self hμ)
  obtain ⟨φ, hφa, hφ0, hφr, hφunique⟩ :=
    exists_analytic_weighted_trajectory_graph a κ d₀ d₁ e₁ e₂ e₃ μ σ hμc hσ hσ1 hσμ
  let J := stableTrajectoryCorrection a κ d₀ d₁ (μ : ℂ) σ hσ hσ1 φ
  have hJa : AnalyticAt ℂ J 0 :=
    analyticAt_stableTrajectoryCorrection a κ d₀ d₁ (μ : ℂ) σ hσ hσ1 φ hφa hφ0
  have hJ0 : J 0 = 0 :=
    stableTrajectoryCorrection_zero a κ d₀ d₁ (μ : ℂ) σ hσ hσ1 φ hφ0
  obtain ⟨H, hHa, hH0, hHaxis, hHderiv, hInv, hHunique⟩ :=
    exists_analytic_stable_coordinate_inverse hJa hJ0
  let V : ℂ × ℂ → ℂ := fun p => (φ p).2 0 - κ
  have hVa : AnalyticAt ℂ V 0 := by
    have hpart : AnalyticAt ℂ (fun p : ℂ × ℂ => (φ p).2) 0 :=
      analyticAt_snd.fun_comp (f := φ) (x := 0) hφa
    let ev : (ℝ≥0 →ᵇ ℂ) →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ (0 : ℝ≥0)
    exact ((ev.analyticAt _).fun_comp
      (f := fun p : ℂ × ℂ => (φ p).2) (x := 0) hpart).sub
      analyticAt_const
  let X : ℝ → ℂ := fun r => Complex.exp (-(r : ℂ))
  let p : ℝ → ℂ × ℂ := fun r => (X r, O.u r)
  let Q : ℝ → ℂ := fun r => O.u r * Complex.exp (J (p r))
  have hx : Tendsto X atTop (𝓝 0) := by
    simpa only [X, Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using
      (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
  have hp : Tendsto p atTop (𝓝 0) := hx.prodMk_nhds O.u_tendsto
  have hj : Tendsto (fun r => J (p r)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hJ0] using hJa.continuousAt.tendsto.comp hp
  have hQ : Tendsto Q atTop (𝓝 0) := by
    simpa only [Q, Function.comp_def, Complex.exp_zero, zero_mul] using
      O.u_tendsto.mul (Complex.continuous_exp.continuousAt.tendsto.comp hj)
  have harg : Tendsto (fun r => ((X r, Q r), O.u r)) atTop (𝓝 0) :=
    (hx.prodMk_nhds hQ).prodMk_nhds O.u_tendsto
  have hHcapture : ∀ᶠ r : ℝ in atTop, H (X r, Q r) = O.u r := by
    filter_upwards [harg.eventually hHunique] with r hr
    exact hr rfl
  have hcapEvent := O.eventually_weighted_graph_capture hμ hσ hσ1 hσμ hσhalf φ hφunique
  obtain ⟨B, hB, Rb, hb⟩ := exists_uniform_scalar_stable_tail_bounds
    a κ e₁ e₂ e₃ X O.u O.w hx O.u_tendsto O.w_tendsto
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hcapEvent.and (hHcapture.and (eventually_ge_atTop (max O.lower Rb))))
  have hTlower : O.lower ≤ T := (le_max_left _ _).trans (hT T le_rfl).2.2
  have hcap : ∀ R : ℝ, T ≤ R → ∀ s : ℝ≥0,
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).1 s =
        O.u (R + s) ∧
      expDecayBCF σ hσ.le s * (φ (Complex.exp (-(R : ℂ)), O.u R)).2 s =
        O.w (R + s) := fun R hR => (hT R hR).1
  have hsmall : ∀ R : ℝ, T ≤ R →
      ‖Complex.exp (-(R : ℂ)) * (O.w R - κ) * (a + O.u R)‖ ≤ (1 / 2 : ℝ) := by
    intro R hR
    exact (hb R ((le_max_right _ _).trans (hT R hR).2.2)).2.2
  obtain ⟨C, hC, hCformula⟩ := O.linearized_formula_of_capture hμ hμc hσ hσ1 φ
    T hTlower hcap hsmall
  refine ⟨C, hC, H, V, J, hHa, hVa, hH0, hInv, T, ?_⟩
  intro r hr
  constructor
  · have hh := (hT r hr).2.1
    change H (Complex.exp (-(r : ℂ)),
      O.u r * Complex.exp (J (Complex.exp (-(r : ℂ)), O.u r))) = O.u r at hh
    rw [hCformula r hr] at hh
    exact hh.symm
  · have hw := (hcap r hr 0).2
    have hw0 : (φ (Complex.exp (-(r : ℂ)), O.u r)).2 0 = O.w r := by
      simpa only [expDecayBCF_zero, NNReal.coe_zero, add_zero, one_mul] using hw
    change O.w r = ((φ (Complex.exp (-(r : ℂ)), O.u r)).2 0 - κ) + κ
    rw [sub_add_cancel, hw0]

theorem ExponentialPair.exists_canonical_real_stable_formula
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∃ j : Fin 3, ∃ μ : ℝ, 0 < μ ∧ ∃ C : ℂ, C ≠ 0 ∧
      ∃ H V J : ℂ × ℂ → ℂ,
        AnalyticAt ℂ H 0 ∧ AnalyticAt ℂ V 0 ∧ H 0 = 0 ∧
        (∀ᶠ p : ℂ × ℂ in 𝓝 0,
          H p * Complex.exp (J (p.1, H p)) = p.2) ∧
        (∀ᶠ r : ℝ in atTop,
          chartFiniteMap (sphereGermValue f (r : ℂ)) =
            a j + H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))) ∧
          (chartFiniteMap (sphereGermValue g (r : ℂ)))⁻¹ = Complex.exp (-(r : ℂ)) *
            V (Complex.exp (-(r : ℂ)),
              H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))))) := by
  obtain ⟨j, μ, hμ, hμc, O, hu, hw⟩ := h.exists_canonical_real_scalar_orbit
  obtain ⟨C, hC, H, V, J, hHa, hVa, hH0, hInv, T, hformula⟩ :=
    O.exists_analytic_real_models hμ hμc
  refine ⟨j, μ, hμ, C, hC, H, V, J, hHa, hVa, hH0, hInv, ?_⟩
  apply eventually_atTop.mpr
  refine ⟨T, ?_⟩
  intro r hr
  have hmodel := hformula r hr
  have hf : chartFiniteMap (sphereGermValue f (r : ℂ)) - a j =
      H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))) :=
    (hu r).symm.trans hmodel.1
  constructor
  · calc
      _ = a j + (chartFiniteMap (sphereGermValue f (r : ℂ)) - a j) := by ring
      _ = _ := by rw [hf]
  · have hratio : Complex.exp (r : ℂ) /
        chartFiniteMap (sphereGermValue g (r : ℂ)) =
        V (Complex.exp (-(r : ℂ)), O.u r) :=
      add_right_cancel ((hw r).symm.trans hmodel.2)
    rw [← hmodel.1, ← hratio, div_eq_mul_inv, ← mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- The final existence theorem has only the original ExponentialPair
input. Every field of Data is constructed; no stable-model existence is
passed to the original main theorem as a new premise. -/
theorem ExponentialPair.exists_real_stable_data
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    Nonempty (ExponentialRealStableData a f g) := by
  obtain ⟨j, μ, hμ, C, hC, H, V, J, hHa, hVa, hH0, hInv, heq⟩ :=
    h.exists_canonical_real_stable_formula
  exact h.real_stable_data_of_canonical_real_tail j hμ C hC hHa hVa hH0 hInv heq


end ThreeIM
