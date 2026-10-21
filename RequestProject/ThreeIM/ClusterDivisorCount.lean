module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The divisor budget from one outer counting radius

Every divisor point in the inner disk contributes at least log(R/rho)
per unit of multiplicity to the outer logarithmic counting function.
The coefficient at zero is handled by its actual compensated log(R)
term. This is the single-radius counting input of the finite-disk lemma.
-/

@[expose] public section

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- A nonnegative locally finite divisor has its total multiplicity in a
finite inner set controlled by its logarithmic count at the outer radius.
In particular a divisor at zero is counted by log(R), not log(R/0). -/
theorem weighted_divisor_count_mul_log_le (s : Finset ℂ)
    (D : Function.locallyFinsupp ℂ ℤ) {ρ R : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρR : ρ < R)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ) :
    (∑ z ∈ s, (D z : ℝ)) * Real.log (R / ρ) ≤ D.logCounting R := by
  classical
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hRpos : 0 < R := hρpos.trans hρR
  have hRone : 1 ≤ R := hρ.trans hρR.le
  let DR := Function.locallyFinsuppWithin.toClosedBall R D
  have hfin := DR.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  let T : Finset ℂ := insert 0 (s ∪ hfin.toFinset)
  let b : ℂ → ℝ := fun z => (DR z : ℝ) * Real.log (R * ‖z‖⁻¹)
  let k : ℂ → ℝ := fun z => b z + if z = 0 then (D 0 : ℝ) * Real.log R else 0
  have hDR (z : ℂ) (hz : ‖z‖ ≤ R) : DR z = D z := by
    apply Function.locallyFinsuppWithin.toClosedBall_eval_within
    simpa only [mem_closedBall, dist_zero_right, abs_of_pos hRpos] using hz
  have hb : ∀ z, 0 ≤ b z := by
    intro z
    by_cases hz0 : z = 0
    · simp [b, hz0]
    by_cases hzR : ‖z‖ ≤ R
    · change 0 ≤ (DR z : ℝ) * Real.log (R * ‖z‖⁻¹)
      rw [hDR z hzR, ← div_eq_mul_inv]
      apply mul_nonneg (by exact_mod_cast hD z)
      exact Real.log_nonneg ((le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr (by simpa using hzR))
    · have houtside : z ∉ closedBall (0 : ℂ) |R| := by
        simpa only [mem_closedBall, dist_zero_right, abs_of_pos hRpos] using hzR
      have hzero := DR.apply_eq_zero_of_notMem houtside
      simp only [b, hzero, Int.cast_zero, zero_mul, le_refl]
  have hk : ∀ z, 0 ≤ k z := by
    intro z
    apply add_nonneg (hb z)
    split_ifs
    · exact mul_nonneg (by exact_mod_cast hD 0) (Real.log_nonneg hRone)
    · exact le_refl 0
  have hsum : (∑ᶠ z, b z) = ∑ z ∈ T, b z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    have hdz : DR z ≠ 0 := by
      intro hzero
      exact hz (by simp only [b, hzero, Int.cast_zero, zero_mul])
    exact Finset.mem_insert_of_mem (Finset.mem_union_right s (hfin.mem_toFinset.mpr hdz))
  have hfull : (∑ z ∈ T, k z) = D.logCounting R := by
    change (∑ z ∈ T, (b z + if z = 0 then (D 0 : ℝ) * Real.log R else 0)) = _
    rw [Finset.sum_add_distrib]
    have hcomp : (∑ z ∈ T, if z = 0 then (D 0 : ℝ) * Real.log R else 0) =
        (D 0 : ℝ) * Real.log R := by simp [T]
    rw [hcomp, ← hsum]
    rfl
  have hpoint : ∀ z ∈ s, (D z : ℝ) * Real.log (R / ρ) ≤ k z := by
    intro z hz
    have hDpos : (0 : ℝ) ≤ D z := by exact_mod_cast hD z
    by_cases hz0 : z = 0
    · subst hz0
      have hlog : Real.log (R / ρ) ≤ Real.log R :=
        Real.log_le_log (div_pos hRpos hρpos) (div_le_self hRpos.le hρ)
      simpa only [k, b, norm_zero, inv_zero, mul_zero, Real.log_zero,
        zero_add, ↓reduceIte] using mul_le_mul_of_nonneg_left hlog hDpos
    · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hlog : Real.log (R / ρ) ≤ Real.log (R * ‖z‖⁻¹) := by
        rw [← div_eq_mul_inv]
        exact Real.log_le_log (div_pos hRpos hρpos)
          (div_le_div_of_nonneg_left hRpos.le hnorm (hs z hz))
      simpa only [k, hz0, ↓reduceIte, add_zero, b, hDR z ((hs z hz).trans hρR.le)] using
        mul_le_mul_of_nonneg_left hlog hDpos
  calc
    (∑ z ∈ s, (D z : ℝ)) * Real.log (R / ρ) =
        ∑ z ∈ s, (D z : ℝ) * Real.log (R / ρ) := by rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ s, k z := Finset.sum_le_sum hpoint
    _ ≤ ∑ z ∈ T, k z := Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)) (fun z _ _ => hk z)
    _ = D.logCounting R := hfull

end ThreeIM
