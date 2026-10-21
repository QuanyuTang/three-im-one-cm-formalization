module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A local finite-zero count from Jensen's formula

This is a local analytic ingredient for counting q-points inside the divisor
clusters of the finite-disk branch lemma. It needs no global meromorphic
extension and no argument-principle or curvature input. A later cluster
estimate must supply the bound for the normalized analytic numerator.
-/

@[expose] public section

open Set Metric Real

namespace ThreeIM

/-- A normalized analytic function with boundary bound `exp L` has at most
`L / log(R/r)` distinct zeros in the smaller closed disk. All analyticity
assumptions are local to the closed outer disk. -/
theorem finite_zero_card_mul_log_le (s : Finset ℂ) {f : ℂ → ℂ} {c : ℂ}
    {r R L : ℝ} (hr : 0 < r) (hrR : r < R) (hL : 0 ≤ L)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c = 1)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp L)
    (hzeros : ∀ z ∈ s, z ∈ closedBall c r ∧ f z = 0) :
    (s.card : ℝ) * Real.log (R / r) ≤ L := by
  classical
  have hR : 0 < R := hr.trans hrR
  have hc : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hfc0 : f c ≠ 0 := by simp [hfc]
  have hordc : meromorphicOrderAt f c = 0 :=
    (hf c hc).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfc0
  have hfinite : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hc hz
    simp [hordc]
  let D := MeromorphicOn.divisor f (closedBall c R)
  have hDnonneg : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hfin := D.finiteSupport (isCompact_closedBall c R)
  let T : Finset ℂ := hfin.toFinset
  have hDc : D c = 0 := by
    change MeromorphicOn.divisor f (closedBall c R) c = 0
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hc, hordc]
    rfl
  have hzeroD : ∀ z ∈ s, 1 ≤ D z := by
    intro z hz
    have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR.le (hzeros z hz).1
    have hne : meromorphicOrderAt f z ≠ 0 := by
      intro hzero
      exact ((hf z hzR).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hzero)
        (hzeros z hz).2
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z :=
      lt_of_le_of_ne (hf z hzR).meromorphicOrderAt_nonneg (Ne.symm hne)
    have hcoe : ((D z : ℤ) : WithTop ℤ) = meromorphicOrderAt f z := by
      dsimp [D]
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzR]
      exact WithTop.coe_untop₀_of_ne_top (hfinite z hzR)
    have hdpos : (0 : ℤ) < D z := by
      exact_mod_cast (show (0 : WithTop ℤ) < (D z : WithTop ℤ) by rw [hcoe]; exact hpos)
    linarith
  have hST : s ⊆ T := by
    intro z hz
    simp only [T, Set.Finite.mem_toFinset, Function.mem_support]
    have := hzeroD z hz
    linarith
  have hsum :
      (∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)) =
        ∑ u ∈ T, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
    intro hzero
    exact hu (by simp [hzero])
  have hJ := (show MeromorphicOn f (closedBall c |R|) by
    simpa only [abs_of_pos hR] using hf.meromorphicOn).circleAverage_log_norm hR.ne'
  rw [abs_of_pos hR] at hJ
  change circleAverage (fun z => Real.log ‖f z‖) c R =
    (∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)) +
      (D c : ℝ) * Real.log R + Real.log ‖meromorphicTrailingCoeffAt f c‖ at hJ
  rw [hsum, hDc, (hf c hc).meromorphicTrailingCoeffAt_of_ne_zero hfc0, hfc] at hJ
  simp only [Int.cast_zero, zero_mul, add_zero, norm_one, Real.log_one] at hJ
  have havg : circleAverage (fun z => Real.log ‖f z‖) c R ≤ L := by
    apply circleAverage_mono_on_of_le_circle
      (circleIntegrable_log_norm_meromorphicOn (show MeromorphicOn f (sphere c |R|) by
        intro z hz
        exact hf.meromorphicOn z (sphere_subset_closedBall
          (by simpa only [abs_of_pos hR] using hz))))
    intro z hz
    have hzR : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
    by_cases hz0 : f z = 0
    · simpa only [hz0, norm_zero, Real.log_zero] using hL
    · simpa only [Real.log_exp] using
        Real.log_le_log (norm_pos_iff.mpr hz0) (hbound z hzR)
  have hterm : ∀ u ∈ T, 0 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    apply mul_nonneg (by exact_mod_cast hDnonneg u)
    by_cases huc : u = c
    · simp [huc]
    · have huR : u ∈ closedBall c R := D.supportWithinDomain (by simpa [T] using hu)
      have hnorm : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
      have hdist : ‖c - u‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using huR
      rw [← div_eq_mul_inv]
      exact Real.log_nonneg ((le_div_iff₀ hnorm).mpr (by simpa using hdist))
  have hlog : 0 ≤ Real.log (R / r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hsingle : ∀ z ∈ s,
      Real.log (R / r) ≤ (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
    intro z hz
    have hzc : z ≠ c := by
      intro heq
      have hz0 := (hzeros z hz).2
      rw [heq, hfc] at hz0
      exact one_ne_zero hz0
    have hnorm : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzc))
    have hdist : ‖c - z‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using (hzeros z hz).1
    have hcompare : Real.log (R / r) ≤ Real.log (R * ‖c - z‖⁻¹) := by
      rw [← div_eq_mul_inv]
      exact Real.log_le_log (div_pos hR hr) (div_le_div_of_nonneg_left hR.le hnorm hdist)
    calc
      Real.log (R / r) = 1 * Real.log (R / r) := (one_mul _).symm
      _ ≤ (D z : ℝ) * Real.log (R / r) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hzeroD z hz) hlog
      _ ≤ (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹) :=
        mul_le_mul_of_nonneg_left hcompare (by exact_mod_cast hDnonneg z)
  calc
    (s.card : ℝ) * Real.log (R / r) = ∑ _z ∈ s, Real.log (R / r) := by simp
    _ ≤ ∑ z ∈ s, (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := Finset.sum_le_sum hsingle
    _ ≤ ∑ z ∈ T, (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hST (fun z hz _ => hterm z hz)
    _ = circleAverage (fun z => Real.log ‖f z‖) c R := hJ.symm
    _ ≤ L := havg

end ThreeIM
