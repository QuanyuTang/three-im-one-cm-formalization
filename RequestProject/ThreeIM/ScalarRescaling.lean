module

public import RequestProject.ThreeIM.AffineCovariance
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! # The exact scalar equation after an affine source change -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem affine_first_second_derivatives {f : ℂ → ℂ} (c z₀ w : ℂ)
    (hf : AnalyticAt ℂ f (z₀ + c * w)) :
    deriv (fun x => f (z₀ + c * x)) w = c * deriv f (z₀ + c * w) ∧
    deriv (deriv (fun x => f (z₀ + c * x))) w =
      c ^ 2 * deriv (deriv f) (z₀ + c * w) := by
  have ha (x : ℂ) : HasDerivAt (fun y : ℂ => z₀ + c * y) c x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).const_mul c).const_add z₀)
  have had (x : ℂ) : deriv (fun y : ℂ => z₀ + c * y) x = c := (ha x).deriv
  have hadd : deriv (deriv (fun y : ℂ => z₀ + c * y)) w = 0 := by
    have heq : deriv (fun y : ℂ => z₀ + c * y) = fun _ => c := funext had
    rw [heq, deriv_const]
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, mul_comm] using
      (hf.differentiableAt.hasDerivAt.comp w (ha w)).deriv
  · have hA : AnalyticAt ℂ (fun y : ℂ => z₀ + c * y) w := by fun_prop
    have htwo := iteratedDeriv_comp_two (g := f) (f := fun y : ℂ => z₀ + c * y)
      hf.contDiffAt hA.contDiffAt
    simpa only [Function.comp_def, iteratedDeriv_succ, iteratedDeriv_zero,
      had, hadd, mul_zero, add_zero, mul_comm] using htwo

theorem scalar_equation_comp_affine {Ω V : Set ℂ} (hΩ : IsOpen Ω)
    {H C B : ℂ → ℂ} (hH : DifferentiableOn ℂ H Ω)
    (heq : ∀ z ∈ Ω, C z * H z * (H z - 1) * deriv (deriv H) z
      - deriv C z * H z * (H z - 1) * deriv H z
      - (C z * (3 * H z - 1) + B z) * deriv H z ^ 2 = 0)
    (c z₀ : ℂ) (hmaps : MapsTo (fun w => z₀ + c * w) V Ω) :
    ∀ w ∈ V,
      C (z₀ + c * w) * H (z₀ + c * w) * (H (z₀ + c * w) - 1) *
        deriv (deriv (fun x => H (z₀ + c * x))) w
      - (c * deriv C (z₀ + c * w)) * H (z₀ + c * w) * (H (z₀ + c * w) - 1) *
        deriv (fun x => H (z₀ + c * x)) w
      - (C (z₀ + c * w) * (3 * H (z₀ + c * w) - 1) + B (z₀ + c * w)) *
        deriv (fun x => H (z₀ + c * x)) w ^ 2 = 0 := by
  intro w hw
  have hd := affine_first_second_derivatives c z₀ w (hH.analyticOnNhd hΩ _ (hmaps hw))
  rw [hd.1, hd.2]
  linear_combination c ^ 2 * heq (z₀ + c * w) (hmaps hw)

end ThreeIM
