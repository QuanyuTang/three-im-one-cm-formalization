module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A holomorphic logarithm with narrow dependencies

This is the elementary primitive-of-g'/g proof also used in LogDerivHolo,
isolated here so divisor extraction does not import the full Mathlib root
through the project Basic module. The hypotheses and mathematics are the
same; no original source module is changed.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric

namespace ThreeIM

/-- A zero-free holomorphic function on a ball has a holomorphic logarithm,
normalized by the principal logarithm at the center. -/
theorem exists_analytic_log_on_ball {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧
      (∀ z ∈ ball c R, Complex.exp (h z) = g z) ∧ h c = Complex.log (g c) := by
  have hdg : DifferentiableOn ℂ (deriv g) (ball c R) := hg.deriv isOpen_ball
  have hφ : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) := hdg.div hg hg0
  obtain ⟨H, hH⟩ := hφ.isExactOn_ball
  have hHd : DifferentiableOn ℂ H (ball c R) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  let Q : ℂ → ℂ := fun z => g z * Complex.exp (-H z)
  have hQd : DifferentiableOn ℂ Q (ball c R) := hg.mul hHd.neg.cexp
  have hQ' : (ball c R).EqOn (deriv Q) 0 := by
    intro z hz
    have hgz := (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hd : HasDerivAt Q (deriv g z * Complex.exp (-H z) +
        g z * (Complex.exp (-H z) * -(deriv g z / g z))) z := hgz.mul ((hH z hz).neg.cexp)
    rw [hd.deriv]
    simp only [Pi.zero_apply]
    field_simp [hg0 z hz]
    ring
  have hc : c ∈ ball c R := mem_ball_self hR
  have hQc : ∀ z ∈ ball c R, Q z = Q c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hQd hQ' hz hc
  refine ⟨fun z => H z - H c + Complex.log (g c), (hHd.sub_const _).add_const _, ?_, ?_⟩
  · intro z hz
    have heq := hQc z hz
    change g z * Complex.exp (-H z) = g c * Complex.exp (-H c) at heq
    rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log (hg0 c hc)]
    rw [Complex.exp_neg] at heq
    field_simp [Complex.exp_ne_zero] at heq ⊢
    rw [Complex.exp_neg] at heq
    field_simp [Complex.exp_ne_zero] at heq
    linear_combination (-1 : ℂ) * heq
  · simp

end ThreeIM
