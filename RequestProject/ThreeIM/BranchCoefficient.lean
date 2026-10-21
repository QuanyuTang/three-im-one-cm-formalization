module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sign of a square root on an inverse sheet

The normalized logarithmic coordinate makes the square of the auxiliary
ratio equal to an exponential. Its value at the marked point fixes the sign
throughout the disk. No global normal-family assertion is used here.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- Prescribing the central value selects the holomorphic square root of an
exponential throughout a disk. -/
theorem eq_exp_half_of_sq_eq {H : ℂ → ℂ} {R : ℝ} {q : ℂ}
    (hR : 0 < R) (hq : q ≠ 0) (hH : DifferentiableOn ℂ H (ball 0 R))
    (hH0 : H 0 = q) (hsq : ∀ s ∈ ball 0 R, H s ^ 2 = q ^ 2 * Complex.exp s) :
    ∀ s ∈ ball 0 R, H s = q * Complex.exp (s / 2) := by
  let J : ℂ → ℂ := fun s => H s / Complex.exp (s / 2)
  have hJ : DifferentiableOn ℂ J (ball 0 R) := by
    have hexp : Differentiable ℂ (fun s : ℂ => Complex.exp (s / 2)) := by fun_prop
    exact hH.div hexp.differentiableOn (fun s _ => Complex.exp_ne_zero _)
  have hJsq : ∀ s ∈ ball 0 R, J s ^ 2 = q ^ 2 := by
    intro s hs
    have he : Complex.exp (s / 2) ^ 2 = Complex.exp s := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    dsimp [J]
    rw [div_pow, hsq s hs, he, mul_div_cancel_right₀ _ (Complex.exp_ne_zero s)]
  have hJne : ∀ s ∈ ball 0 R, J s ≠ 0 := by
    intro s hs hzero
    have he := hJsq s hs
    rw [hzero, zero_pow (by norm_num)] at he
    exact pow_ne_zero 2 hq he.symm
  have hJd : ∀ s ∈ ball 0 R, deriv J s = 0 := by
    intro s hs
    have hd := hJ.differentiableAt (isOpen_ball.mem_nhds hs)
    have he : (fun w => J w ^ 2) =ᶠ[𝓝 s] (fun _ => q ^ 2) :=
      eventually_of_mem (isOpen_ball.mem_nhds hs) hJsq
    have hp := (hd.hasDerivAt.pow 2).deriv
    change deriv (fun w => J w ^ 2) s = (2 : ℂ) * J s ^ (2 - 1) * deriv J s at hp
    rw [he.deriv_eq, deriv_const] at hp
    have hprod : (2 : ℂ) * J s * deriv J s = 0 := by simpa using hp.symm
    exact (mul_eq_zero.1 hprod).resolve_left (mul_ne_zero (by norm_num) (hJne s hs))
  have hconst : ∀ s ∈ ball 0 R, J s = q := by
    intro s hs
    have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
      hJ hJd hs (mem_ball_self hR)
    simpa only [J, zero_div, Complex.exp_zero, div_one, hH0] using he
  intro s hs
  have he := hconst s hs
  exact (div_eq_iff (Complex.exp_ne_zero _)).1 he

/-- The U/V and U*V identities determine both normalized coefficients with
the prescribed central square-root sign. -/
theorem inverse_sheet_coefficients {U V σ : ℂ → ℂ} {R : ℝ} {q : ℂ}
    (hR : 0 < R) (hq : q ≠ 0)
    (hU : DifferentiableOn ℂ U (ball 0 R))
    (hσ : DifferentiableOn ℂ σ (ball 0 R))
    (hσne : ∀ s ∈ ball 0 R, σ s ≠ 0)
    (hVne : ∀ s ∈ ball 0 R, V s ≠ 0)
    (hproduct : ∀ s ∈ ball 0 R, U s * V s = σ s ^ 2)
    (hratio : ∀ s ∈ ball 0 R, U s / V s = q ^ 2 * Complex.exp s)
    (hcenter : U 0 / σ 0 = q) :
    ∀ s ∈ ball 0 R,
      U s / σ s = q * Complex.exp (s / 2) ∧
        V s / σ s = q⁻¹ * Complex.exp (-s / 2) := by
  have hH : DifferentiableOn ℂ (fun s => U s / σ s) (ball 0 R) := hU.div hσ hσne
  have hsq : ∀ s ∈ ball 0 R, (U s / σ s) ^ 2 = q ^ 2 * Complex.exp s := by
    intro s hs
    rw [← hratio s hs]
    have hp := hproduct s hs
    field_simp [hσne s hs, hVne s hs]
    linear_combination U s * hp
  have hfirst := eq_exp_half_of_sq_eq hR hq hH hcenter hsq
  intro s hs
  have hσs := hσne s hs
  have hu := hfirst s hs
  have hp := hproduct s hs
  refine ⟨hu, ?_⟩
  have hu' : U s = (q * Complex.exp (s / 2)) * σ s := (div_eq_iff hσs).1 hu
  rw [hu'] at hp
  have hp' : q * Complex.exp (s / 2) * V s = σ s := by
    apply mul_left_cancel₀ hσs
    linear_combination hp
  rw [neg_div, Complex.exp_neg]
  field_simp [hq, hσs, Complex.exp_ne_zero]
  linear_combination hp'

end ThreeIM
