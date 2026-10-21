module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Packing separated points in a complex disk

This is the area-packing step in the quantitative inverse-branch lemma used by
Proposition 6.3 (selection). It bounds a finite set of separated bad points in one
physical disk. The analytic separation estimate, the divisor-cluster estimates,
and the selection proposition are separate results.

The proof uses the disjoint-ball argument of
`Besicovitch.card_le_of_separated`, with arbitrary disk and separation radii.
All constants are explicit, and no hypothesis on the separation of divisor
points is needed.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace ThreeIM

/-- The total area of the disjoint disks of radius `δ / 2` around `s` is at most
the area of the disk of radius `R + δ / 2` containing them, after cancelling the
common unit-disk area. -/
theorem card_mul_sq_le_of_separated_complex (s : Finset ℂ) (c : ℂ) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (hmem : ∀ z ∈ s, dist z c ≤ R)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → δ ≤ dist z w) :
    (s.card : ℝ) * (δ / 2) ^ 2 ≤ (R + δ / 2) ^ 2 := by
  borelize ℂ
  let μ : Measure ℂ := Measure.addHaar
  have hhalf : 0 < δ / 2 := half_pos hδ
  have houter : 0 < R + δ / 2 := add_pos_of_nonneg_of_pos hR hhalf
  have hdisj : Set.PairwiseDisjoint (↑s : Set ℂ) (fun z => ball z (δ / 2)) := by
    intro z hz w hw hzw
    apply ball_disjoint_ball
    convert hsep z hz w hw hzw using 1
    ring
  have hsub : (⋃ z ∈ s, ball z (δ / 2)) ⊆ ball c (R + δ / 2) := by
    refine iUnion₂_subset fun z hz => ball_subset_ball' ?_
    calc
      δ / 2 + dist z c ≤ δ / 2 + R := add_le_add le_rfl (hmem z hz)
      _ = R + δ / 2 := add_comm _ _
  have harea :
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) * μ (ball 0 1) ≤
        ENNReal.ofReal ((R + δ / 2) ^ 2) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) * μ (ball 0 1) =
          μ (⋃ z ∈ s, ball z (δ / 2)) := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hhalf, Complex.finrank_real_complex,
          Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball c (R + δ / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((R + δ / 2) ^ 2) * μ (ball 0 1) := by
        rw [μ.addHaar_ball_of_pos _ houter, Complex.finrank_real_complex]
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) ≤
        ENNReal.ofReal ((R + δ / 2) ^ 2) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 harea
  have hreal := ENNReal.toReal_le_of_le_ofReal (sq_nonneg (R + δ / 2)) hcancel
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (sq_nonneg (δ / 2))] using hreal

/-- A `δ`-separated finite set in a complex disk of radius `R` has at most
`(1 + 2 * R / δ)²` points. This supplies the quantitative packing bound in
Step 3 of the manuscript's inverse-branch lemma. -/
theorem card_le_sq_of_separated_complex (s : Finset ℂ) (c : ℂ) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (hmem : ∀ z ∈ s, dist z c ≤ R)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → δ ≤ dist z w) :
    (s.card : ℝ) ≤ (1 + 2 * R / δ) ^ 2 := by
  have harea := card_mul_sq_le_of_separated_complex s c hR hδ hmem hsep
  have hsq : 0 < (δ / 2) ^ 2 := sq_pos_of_pos (half_pos hδ)
  apply (mul_le_mul_iff_left₀ hsq).1
  calc
    (s.card : ℝ) * (δ / 2) ^ 2 ≤ (R + δ / 2) ^ 2 := harea
    _ = (1 + 2 * R / δ) ^ 2 * (δ / 2) ^ 2 := by
      field_simp [hδ.ne']
      ring

end ThreeIM
