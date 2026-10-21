module

public import RequestProject.ThreeIM.ExponentialData

/-! # Real stable data for exclusion of exponential defects

An existence proof must construct all these fields from the original
exponential pair. The exponent is a positive real number at this stage.
The explicit inverse identity is retained for the irrational-phase argument.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Topology

namespace ThreeIM

structure ExponentialRealStableData (a : Fin 3 → ℂ) (f g : ℂ → ℂ) where
  index : Fin 3
  μ : ℝ
  μ_pos : 0 < μ
  C : ℂ
  C_ne_zero : C ≠ 0
  H : ℂ × ℂ → ℂ
  V : ℂ × ℂ → ℂ
  J : ℂ × ℂ → ℂ
  H_analytic : AnalyticAt ℂ H 0
  V_analytic : AnalyticAt ℂ V 0
  H_zero : H 0 = 0
  coordinate_inverse : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
    H p * Complex.exp (J (p.1, H p)) = p.2
  R₀ : ℝ
  formula : ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
    f z = a index + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)) ∧
      (g z)⁻¹ = Complex.exp (-z) *
        V (Complex.exp (-z), H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)))

end ThreeIM
