module

public import RequestProject.ThreeIM.SecondMainLocal
public import RequestProject.ThreeIM.Holomorphic
public import RequestProject.ThreeIM.LogDerivFactor

/-!
# Integrated proximity estimates for the second main theorem

The derivative is nonzero off a discrete set. Integrating the finite-target
pointwise estimate on a circle therefore gives a proximity estimate, including
circles passing through zeros or poles. The remaining lemmas keep the bounded
constants in the first main theorem explicit.
-/

@[expose] public section

open Filter Set Metric MeasureTheory Real

namespace ThreeIM

theorem proximity_sum_finite_le {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    {q : ℕ} (a : Fin q → ℂ) (ha : Function.Injective a) {r : ℝ} (hr : r ≠ 0) :
    (∑ i, ValueDistribution.proximity f (a i) r) ≤
      ValueDistribution.proximity (deriv f)⁻¹ ⊤ r +
        (∑ i, ValueDistribution.proximity (fun z => deriv f z / (f z - a i)) ⊤ r) +
          finiteValueSeparationConstant a := by
  have hm : Meromorphic f := fun z => hf.1 z (mem_univ z)
  have hdm : Meromorphic (deriv f) := hm.deriv
  have hne : ∀ᶠ z in codiscrete ℂ, deriv f z ≠ 0 := by
    rw [Filter.Eventually, mem_codiscrete]
    intro x
    rw [disjoint_principal_right, compl_compl]
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hdm x)).1
      (order_deriv_of_nonconst hf (mem_univ x)).1
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin q)),
      CircleIntegrable (fun z => Real.posLog ‖(f z - a i)⁻¹‖) 0 r := by
    intro i _
    exact circleIntegrable_posLog_norm_meromorphicOn
      (fun z _ => ((hm z).sub (MeromorphicAt.const (a i) z)).inv)
  have hj : ∀ i ∈ (Finset.univ : Finset (Fin q)),
      CircleIntegrable (fun z => Real.posLog ‖deriv f z / (f z - a i)‖) 0 r := by
    intro i _
    exact circleIntegrable_posLog_norm_meromorphicOn
      (fun z _ => (hdm z).div ((hm z).sub (MeromorphicAt.const (a i) z)))
  have hk : CircleIntegrable (fun z => Real.posLog ‖(deriv f z)⁻¹‖) 0 r :=
    circleIntegrable_posLog_norm_meromorphicOn (fun z _ => (hdm z).inv)
  have hmono := circleAverage_mono_codiscrete hr
    (CircleIntegrable.fun_sum Finset.univ hi)
    ((hk.add (CircleIntegrable.fun_sum Finset.univ hj)).add
      (circleIntegrable_const _ _ _))
    (by
      have hne' := codiscreteWithin.mono (subset_univ (sphere (0 : ℂ) |r|)) hne
      filter_upwards [hne'] with z hz
      exact finite_values_proximity_pointwise_explicit a ha (f z) (deriv f z) hz)
  rw [circleAverage_fun_sum hi,
    circleAverage_add (hk.add (CircleIntegrable.fun_sum Finset.univ hj))
      (circleIntegrable_const _ _ _),
    circleAverage_add hk (CircleIntegrable.fun_sum Finset.univ hj),
    circleAverage_fun_sum hj, circleAverage_const] at hmono
  simpa only [ValueDistribution.proximity_coe, ValueDistribution.proximity_top,
    Pi.inv_apply, norm_inv] using hmono

/-- A constant bounding the change in characteristic under reciprocation. -/
noncomputable def inverseFirstMainConstant (f : ℂ → ℂ) : ℝ :=
  max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|

theorem inverseFirstMainConstant_nonneg (f : ℂ → ℂ) :
    0 ≤ inverseFirstMainConstant f :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem proximity_inv_add_count_le {f : ℂ → ℂ} (hf : Meromorphic f) (r : ℝ) :
    ValueDistribution.proximity f⁻¹ ⊤ r + ValueDistribution.logCounting f 0 r ≤
      charT f r + inverseFirstMainConstant f := by
  have habs := ValueDistribution.characteristic_sub_characteristic_inv_le (R := r) hf
  have hlower := (abs_le.1 habs).1
  simp only [inverseFirstMainConstant] at *
  unfold charT
  simp only [ValueDistribution.characteristic, Pi.add_apply,
    ValueDistribution.logCounting_inv] at hlower ⊢
  linarith

/-- A radius-independent first-main-theorem error for a finite target. -/
noncomputable def finiteFirstMainConstant (f : ℂ → ℂ) (a : ℂ) : ℝ :=
  Real.posLog ‖a‖ + Real.log 2 + inverseFirstMainConstant (fun z => f z - a)

theorem finiteFirstMainConstant_nonneg (f : ℂ → ℂ) (a : ℂ) :
    0 ≤ finiteFirstMainConstant f a := by
  unfold finiteFirstMainConstant
  exact add_nonneg (add_nonneg Real.posLog_nonneg (Real.log_nonneg (by norm_num)))
    (inverseFirstMainConstant_nonneg _)

theorem charT_le_proximity_add_count_finite {f : ℂ → ℂ} (hf : Meromorphic f)
    (a : ℂ) (r : ℝ) :
    charT f r ≤ ValueDistribution.proximity f a r +
      ValueDistribution.logCounting f a r + finiteFirstMainConstant f a := by
  let F : ℂ → ℂ := fun z => f z - a
  have hFm : Meromorphic F := fun z => (hf z).sub (MeromorphicAt.const a z)
  have hshift := (abs_le.1
    (ValueDistribution.abs_characteristic_sub_characteristic_shift_le
      (a₀ := a) (r := r) hf)).2
  have hinv := (abs_le.1
    (ValueDistribution.characteristic_sub_characteristic_inv_le (R := r) hFm)).2
  have hid : ValueDistribution.characteristic F⁻¹ ⊤ r =
      ValueDistribution.proximity f a r + ValueDistribution.logCounting f a r := by
    rw [ValueDistribution.characteristic, Pi.add_apply, ValueDistribution.proximity_top,
      ValueDistribution.logCounting_inv, ValueDistribution.logCounting_zero,
      ValueDistribution.logCounting_coe, ValueDistribution.proximity_coe]
    simp only [F, Pi.inv_apply, norm_inv]
  change ValueDistribution.characteristic f ⊤ r ≤ _
  change ValueDistribution.characteristic f ⊤ r -
    ValueDistribution.characteristic F ⊤ r ≤ _ at hshift
  rw [hid] at hinv
  change ValueDistribution.characteristic F ⊤ r -
      (ValueDistribution.proximity f a r + ValueDistribution.logCounting f a r) ≤
    inverseFirstMainConstant F at hinv
  unfold finiteFirstMainConstant
  linarith

end ThreeIM
