module

public import RequestProject.ThreeIM.ClusterMarkedDivisor

/-! # Distinct retained marks from logarithmic counting

The finite set consists of the actual support in the closed disk. In
particular zero is included precisely when its divisor coefficient is
nonzero. The compensated term at zero therefore does not create a
spurious extra marked point.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real Classical
open scoped BigOperators

namespace ThreeIM

/-- A global locally finite divisor vanishes in a sufficiently small
punctured disk, whether or not its coefficient at the origin is zero. -/
theorem locallyFiniteDivisor_exists_origin_gap (D : Function.locallyFinsupp ℂ ℤ) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < rstar → D z = 0 := by
  have heq : D =ᶠ[codiscrete ℂ] 0 := D.eq_zero_codiscreteWithin
  have h := (mem_codiscrete.1 heq) (0 : ℂ)
  rw [Filter.disjoint_principal_right, compl_compl] at h
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z = 0 := h
  have h' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → D z = 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp hne)
  obtain ⟨ρ, hρ, hh⟩ := Metric.eventually_nhds_iff.mp h'
  refine ⟨min 1 ρ, lt_min zero_lt_one hρ, min_le_left _ _, ?_⟩
  intro z hz hzr
  apply hh
  · simpa only [dist_zero_right] using hzr.trans_le (min_le_right 1 ρ)
  · exact norm_pos_iff.mp hz

/-- The actual support of a divisor inside the closed disk. -/
noncomputable def divisorDiskPoints (D : Function.locallyFinsupp ℂ ℤ) (r : ℝ) : Finset ℂ :=
  ((D.toClosedBall r).finiteSupport (isCompact_closedBall (0 : ℂ) |r|)).toFinset

@[simp] theorem mem_divisorDiskPoints (D : Function.locallyFinsupp ℂ ℤ) (r : ℝ) (z : ℂ) :
    z ∈ divisorDiskPoints D r ↔ D.toClosedBall r z ≠ 0 := by
  classical
  simp only [divisorDiskPoints, Set.Finite.mem_toFinset, Function.mem_support]

theorem divisorDiskPoints_mem_closedBall (D : Function.locallyFinsupp ℂ ℤ)
    {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : z ∈ divisorDiskPoints D r) : ‖z‖ ≤ r := by
  have hmem := (D.toClosedBall r).supportWithinDomain (mem_divisorDiskPoints D r z |>.mp hz)
  simpa only [mem_closedBall, dist_zero_right, abs_of_nonneg hr] using hmem

/-- A divisor with coefficients at most three has logarithmic counting
bounded by three times the number of its actual support points. The
origin coefficient is handled within this same finite set. -/
theorem divisor_logCounting_le_three_card (D : Function.locallyFinsupp ℂ ℤ)
    (hD3 : ∀ z, D z ≤ 3) {rstar r : ℝ}
    (hstar : 0 < rstar) (hstar1 : rstar ≤ 1)
    (hgap : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < rstar → D z = 0) (hr : 1 ≤ r) :
    D.logCounting r ≤ 3 * ((divisorDiskPoints D r).card : ℝ) * log (r / rstar) := by
  classical
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  let DR := D.toClosedBall r
  let S := divisorDiskPoints D r
  let b : ℂ → ℝ := fun z => (DR z : ℝ) * log (r * ‖z‖⁻¹)
  let k : ℂ → ℝ := fun z => b z + if z = 0 then (D 0 : ℝ) * log r else 0
  have hDR (z : ℂ) (hz : ‖z‖ ≤ r) : DR z = D z := by
    apply Function.locallyFinsuppWithin.toClosedBall_eval_within
    simpa only [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using hz
  have hsum : (∑ᶠ z, b z) = ∑ z ∈ S, b z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    apply (mem_divisorDiskPoints D r z).mpr
    intro hzero
    exact hz (by simp only [b, DR, hzero, Int.cast_zero, zero_mul])
  have hcomp : (∑ z ∈ S, if z = 0 then (D 0 : ℝ) * log r else 0) = (D 0 : ℝ) * log r := by
    by_cases hzero : 0 ∈ S
    · simp only [Finset.sum_ite_eq', hzero, ↓reduceIte]
    · have hDzero : D 0 = 0 := by
        have hDRzero : DR 0 = 0 := by
          by_contra h
          exact hzero ((mem_divisorDiskPoints D r 0).mpr h)
        simpa only [hDR 0 (by simpa using hrpos.le)] using hDRzero
      simp only [hDzero, Int.cast_zero, zero_mul, ite_self, Finset.sum_const_zero]
  have hfull : (∑ z ∈ S, k z) = D.logCounting r := by
    change (∑ z ∈ S, (b z + if z = 0 then (D 0 : ℝ) * log r else 0)) = _
    rw [Finset.sum_add_distrib, hcomp, ← hsum]
    rfl
  have hpoint : ∀ z ∈ S, k z ≤ 3 * log (r / rstar) := by
    intro z hz
    have hnormle := divisorDiskPoints_mem_closedBall D hrpos.le hz
    have hcoeff : (D z : ℝ) ≤ 3 := by exact_mod_cast hD3 z
    by_cases hz0 : z = 0
    · subst z
      have hlog : log r ≤ log (r / rstar) :=
        Real.log_le_log hrpos ((le_div_iff₀ hstar).mpr (mul_le_of_le_one_right hrpos.le hstar1))
      have hfirst : (D 0 : ℝ) * log r ≤ 3 * log r :=
        mul_le_mul_of_nonneg_right hcoeff (Real.log_nonneg hr)
      have hsecond : 3 * log r ≤ 3 * log (r / rstar) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      simpa only [k, b, norm_zero, inv_zero, mul_zero, Real.log_zero,
        zero_add, ↓reduceIte] using hfirst.trans hsecond
    · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hDz : D z ≠ 0 := by
        have h := (mem_divisorDiskPoints D r z).mp hz
        rwa [← hDR z hnormle]
      have hstarnorm : rstar ≤ ‖z‖ := by
        apply le_of_not_gt
        intro hlt
        exact hDz (hgap z hnorm hlt)
      have hlog0 : 0 ≤ log (r / ‖z‖) := Real.log_nonneg ((one_le_div hnorm).mpr hnormle)
      have hlog : log (r / ‖z‖) ≤ log (r / rstar) :=
        Real.log_le_log (div_pos hrpos hnorm)
          (div_le_div_of_nonneg_left hrpos.le hstar hstarnorm)
      have hfirst : (D z : ℝ) * log (r / ‖z‖) ≤ 3 * log (r / ‖z‖) :=
        mul_le_mul_of_nonneg_right hcoeff hlog0
      have hsecond : 3 * log (r / ‖z‖) ≤ 3 * log (r / rstar) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      simpa only [k, hz0, ↓reduceIte, add_zero, b, hDR z hnormle,
        div_eq_mul_inv] using hfirst.trans hsecond
  calc
    D.logCounting r = ∑ z ∈ S, k z := hfull.symm
    _ ≤ ∑ _z ∈ S, 3 * log (r / rstar) := Finset.sum_le_sum hpoint
    _ = 3 * ((divisorDiskPoints D r).card : ℝ) * log (r / rstar) := by
      simp only [Finset.sum_const, nsmul_eq_mul, S]
      ring

/-- In particular the canonical retained divisor admits this honest
distinct-mark count, without excluding a possible mark at zero. -/
theorem NormalizedPair.markedDefect_logCounting_le_card
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ ∀ r : ℝ, 1 ≤ r →
      (totalMarkedDefectDivisor a f g).logCounting r ≤
        3 * ((divisorDiskPoints (totalMarkedDefectDivisor a f g) r).card : ℝ) * log (r / rstar) := by
  obtain ⟨rstar, hstar, hstar1, hgap⟩ :=
    locallyFiniteDivisor_exists_origin_gap (totalMarkedDefectDivisor a f g)
  exact ⟨rstar, hstar, hstar1, fun r hr => divisor_logCounting_le_three_card _
    hp.totalMarkedDefectDivisor_le_three hstar hstar1 hgap hr⟩

end ThreeIM
