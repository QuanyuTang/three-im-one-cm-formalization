module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A quantitative inverse disk for a holomorphic map

This is the near-linear inverse-disk step in the manuscript's quantitative
inverse-branch lemma, used in the selection proposition. A derivative within
one quarter of a nonzero constant gives injectivity and a disk in the image.

The image estimate uses Mathlib's quantitative inverse-function theorem on
smaller closed disks. Passing to their union gives the stated open-disk
conclusion without assuming differentiability on the boundary of the original
disk. The divisor estimates needed to apply this result are separate.
-/

@[expose] public section

open Metric Set
open scoped NNReal

namespace ThreeIM

/-- Integrating the derivative error over a segment gives a quantitative
near-linear estimate on a complex disk. -/
theorem norm_sub_sub_mul_le_of_deriv_close {F : ℂ → ℂ} {z A : ℂ} {ρ C : ℝ}
    (hF : DifferentiableOn ℂ F (ball z ρ))
    (hclose : ∀ w ∈ ball z ρ, ‖deriv F w - A‖ ≤ C)
    {x y : ℂ} (hx : x ∈ ball z ρ) (hy : y ∈ ball z ρ) :
    ‖F x - F y - (x - y) * A‖ ≤ C * ‖x - y‖ := by
  have hderiv : ∀ w ∈ ball z ρ,
      HasDerivWithinAt (fun w => F w - w * A) (deriv F w - A) (ball z ρ) w := by
    intro w hw
    exact ((hF.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub
      (hasDerivAt_mul_const A)).hasDerivWithinAt
  have hsegment := (convex_ball z ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hclose hy hx
  convert hsegment using 1
  congr 1
  ring

/-- A holomorphic map whose derivative stays within `‖A‖ / 4` of `A ≠ 0`
is injective on the source disk, and its image contains the concentric target
disk of radius `3 * ‖A‖ * ρ / 4`. -/
theorem quantitative_inverse_disk {F : ℂ → ℂ} {z A : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hA : A ≠ 0) (hF : DifferentiableOn ℂ F (ball z ρ))
    (hclose : ∀ w ∈ ball z ρ, ‖deriv F w - A‖ ≤ ‖A‖ / 4) :
    InjOn F (ball z ρ) ∧
      ball (F z) (3 * ‖A‖ * ρ / 4) ⊆ F '' ball z ρ := by
  let L : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight A
  let C : ℝ≥0 := ‖A‖₊ / 4
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have happrox : ApproximatesLinearOn F L (ball z ρ) C := by
    intro x hx y hy
    simpa [L, C, ContinuousLinearMap.smulRight_apply, smul_eq_mul] using
      norm_sub_sub_mul_le_of_deriv_close hF hclose hx hy
  let Linv : L.NonlinearRightInverse := {
    toFun := fun w => w / A
    nnnorm := ‖A‖₊⁻¹
    bound' := fun w => by simp [div_eq_mul_inv, mul_comm]
    right_inv' := fun w => by
      change (w / A) * A = w
      exact div_mul_cancel₀ w hA
  }
  constructor
  · intro x hx y hy hxy
    have h := happrox x hx y hy
    have hnorm : ‖x - y‖ * ‖A‖ ≤ ‖A‖ / 4 * ‖x - y‖ := by
      simpa [L, C, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hxy,
        norm_mul] using h
    have hratio : ‖x - y‖ ≤ ‖x - y‖ / 4 := by
      apply (mul_le_mul_iff_left₀ hAnorm).mp
      nlinarith [hnorm]
    have hzero : ‖x - y‖ = 0 := by
      linarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro v hv
    have hcoef : 0 < 3 * ‖A‖ / 4 := by linarith
    have hsmall : dist v (F z) / (3 * ‖A‖ / 4) < ρ := by
      rw [div_lt_iff₀ hcoef]
      have := mem_ball.mp hv
      nlinarith
    obtain ⟨r, hr, hrρ⟩ := exists_between (max_lt hρ hsmall)
    have hrpos : 0 < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hdist : dist v (F z) / (3 * ‖A‖ / 4) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    have hsub : closedBall z r ⊆ ball z ρ := closedBall_subset_ball hrρ
    have hclosed := happrox.mono_set hsub
    have hsurj := hclosed.surjOn_closedBall_of_nonlinearRightInverse Linv
      (b := z) (ε := r) hrpos.le (Subset.refl _)
    have htarget : v ∈ closedBall (F z) (((Linv.nnnorm : ℝ)⁻¹ - C) * r) := by
      rw [mem_closedBall]
      have hrad : ((Linv.nnnorm : ℝ)⁻¹ - C) * r = 3 * ‖A‖ * r / 4 := by
        simp only [Linv, C, NNReal.coe_inv, coe_nnnorm, inv_inv, NNReal.coe_div,
          NNReal.coe_ofNat]
        ring
      rw [hrad]
      have := (div_lt_iff₀ hcoef).mp hdist
      nlinarith
    obtain ⟨w, hw, hwv⟩ := hsurj htarget
    exact ⟨w, hsub hw, hwv⟩

end ThreeIM
