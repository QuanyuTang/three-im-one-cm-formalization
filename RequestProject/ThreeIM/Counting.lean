module

public import RequestProject.ThreeIM.Basic

/-!
# Reduced fiber divisors and counting functions

The reduced counting function and finite-measure exceptional-set predicate are
the literal definitions used in the manuscript. This module puts them below
the second main theorem in the dependency graph. Truncating a nonnegative
divisor replaces each positive multiplicity by one.
-/

@[expose] public section

open Filter Set MeasureTheory

namespace ThreeIM

/-- The logarithmic counting function of a fiber, with each multiplicity
replaced by one. The summand at the origin is compensated separately. -/
noncomputable def reducedCounting (f : ℂ → ℂ) (b : Sphere) (r : ℝ) : ℝ :=
  (∑ᶠ z ∈ {z : ℂ | ‖z‖ ≤ r ∧ 0 < mult f b z}, Real.log (r * ‖z‖⁻¹)) +
    if 0 < mult f b 0 then Real.log r else 0

/-- A property holds for every sufficiently large radius outside a measurable
set of finite linear measure. -/
def OutsideFiniteMeasure (P : ℝ → Prop) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ⊤ ∧ ∃ r₀, ∀ r ≥ r₀, r ∉ E → P r

/-- Replace the positive coefficients of a locally finite divisor by one,
and all other coefficients by zero. -/
noncomputable def truncatePositiveDivisor (D : Function.locallyFinsupp ℂ ℤ) :
    Function.locallyFinsupp ℂ ℤ where
  toFun z := if 0 < D z then 1 else 0
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := D.supportLocallyFiniteWithinDomain z hz
    refine ⟨t, ht, hfin.subset ?_⟩
    intro w hw
    refine ⟨hw.1, ?_⟩
    have hpos : 0 < D w := by
      by_contra h
      exact hw.2 (by simp [h])
    exact ne_of_gt hpos

@[simp] theorem truncatePositiveDivisor_apply
    (D : Function.locallyFinsupp ℂ ℤ) (z : ℂ) :
    truncatePositiveDivisor D z = if 0 < D z then 1 else 0 := rfl

theorem truncatePositiveDivisor_nonneg (D : Function.locallyFinsupp ℂ ℤ) :
    0 ≤ truncatePositiveDivisor D := by
  intro z
  simp only [truncatePositiveDivisor_apply]
  split_ifs <;> norm_num

theorem truncatePositiveDivisor_le (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) :
    truncatePositiveDivisor D ≤ D := by
  intro z
  rw [truncatePositiveDivisor_apply]
  split_ifs with hz
  · exact Int.add_one_le_iff.mpr hz
  · exact hD z

/-- The nonnegative divisor of the fiber over a finite or infinite value. -/
noncomputable def fiberDivisor (f : ℂ → ℂ) (b : Sphere) :
    Function.locallyFinsupp ℂ ℤ :=
  WithTop.recTopCoe (MeromorphicOn.divisor f univ)⁻
    (fun c : ℂ => (MeromorphicOn.divisor (fun w => f w - c) univ)⁺) b

/-- The reduced divisor of a fiber. -/
noncomputable def reducedFiberDivisor (f : ℂ → ℂ) (b : Sphere) :
    Function.locallyFinsupp ℂ ℤ :=
  truncatePositiveDivisor (fiberDivisor f b)

theorem fiberDivisor_nonneg (f : ℂ → ℂ) (b : Sphere) : 0 ≤ fiberDivisor f b := by
  induction b using WithTop.recTopCoe with
  | top => exact negPart_nonneg _
  | coe c => exact posPart_nonneg _

/-- Logarithmic counting of the fiber divisor is the usual counting function. -/
theorem fiberDivisor_logCounting (f : ℂ → ℂ) (b : Sphere) :
    (fiberDivisor f b).logCounting = ValueDistribution.logCounting f b := by
  induction b using WithTop.recTopCoe with
  | top => exact ValueDistribution.logCounting_top.symm
  | coe c => exact ValueDistribution.logCounting_coe.symm

/-- Fiber-divisor coefficients are the germ-based local degrees. -/
theorem fiberDivisor_apply {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (b : Sphere) (z : ℂ) : fiberDivisor f b z = (mult f b z : ℤ) := by
  induction b using WithTop.recTopCoe with
  | top =>
    change (MeromorphicOn.divisor f univ)⁻ z = (mult f ⊤ z : ℤ)
    rw [Function.locallyFinsuppWithin.negPart_apply,
      MeromorphicOn.divisor_apply hf (mem_univ z), mult_top]
    induction meromorphicOrderAt f z using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg,
        WithTop.untop₀_coe, WithTop.untop₀_coe, Int.toNat_eq_max]
      rfl
  | coe c =>
    have hshift : MeromorphicOn (fun w => f w - c) univ := fun w _ =>
      (hf w (mem_univ w)).sub (MeromorphicAt.const c w)
    change (MeromorphicOn.divisor (fun w => f w - c) univ)⁺ z =
      (mult f (c : Sphere) z : ℤ)
    rw [Function.locallyFinsuppWithin.posPart_apply,
      MeromorphicOn.divisor_apply hshift (mem_univ z), mult_coe, Int.toNat_eq_max]
    rfl

@[simp] theorem reducedFiberDivisor_apply {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (b : Sphere) (z : ℂ) :
    reducedFiberDivisor f b z = if 0 < mult f b z then 1 else 0 := by
  rw [reducedFiberDivisor, truncatePositiveDivisor_apply, fiberDivisor_apply hf]
  simp only [Nat.cast_pos]

/-- Reduced counting agrees with the logarithmic count of the truncated
fiber divisor. This identity uses the origin convention on both sides. -/
theorem reducedCounting_eq_reducedFiberDivisor {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (b : Sphere) {r : ℝ} (hr : 0 ≤ r) :
    reducedCounting f b r = (reducedFiberDivisor f b).logCounting r := by
  unfold reducedCounting Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  · rw [finsum_mem_def]
    congr 1
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) |r|
    · rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz,
        reducedFiberDivisor_apply hf]
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg hr] at hz
      by_cases hm : 0 < mult f b z
      · simp [hm, hz, indicator_of_mem]
      · simp [hm]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg hr] at hz
      simp [hz]
  · rw [reducedFiberDivisor_apply hf]
    split_ifs <;> simp

theorem reducedCounting_nonneg {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (b : Sphere) {r : ℝ} (hr : 1 ≤ r) : 0 ≤ reducedCounting f b r := by
  rw [reducedCounting_eq_reducedFiberDivisor hf b (by linarith)]
  exact Function.locallyFinsuppWithin.logCounting_nonneg
    (truncatePositiveDivisor_nonneg _) hr

theorem reducedCounting_le_logCounting {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (b : Sphere) {r : ℝ} (hr : 1 ≤ r) :
    reducedCounting f b r ≤ ValueDistribution.logCounting f b r := by
  rw [reducedCounting_eq_reducedFiberDivisor hf b (by linarith),
    ← fiberDivisor_logCounting f b]
  exact Function.locallyFinsuppWithin.logCounting_le
    (truncatePositiveDivisor_le _ (fiberDivisor_nonneg f b)) hr

theorem reducedCounting_top_le_charT {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    {r : ℝ} (hr : 1 ≤ r) : reducedCounting f ⊤ r ≤ charT f r := by
  have hred := reducedCounting_le_logCounting hf ⊤ hr
  have hprox := ValueDistribution.proximity_nonneg (f := f) (a := ⊤) r
  simp only [Pi.zero_apply] at hprox
  unfold charT ValueDistribution.characteristic
  simp only [Pi.add_apply]
  linarith

end ThreeIM
