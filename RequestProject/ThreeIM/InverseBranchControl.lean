module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Logarithmic control of the inverse-branch coefficient

Normalized logarithms of A and Psi give a chosen square root of Psi and a
normalized logarithm of K = A/sqrt(Psi). The square-root value at the center
is prescribed, so the sign can later be chosen to match the marked fiber.
These are estimates on actual holomorphic functions, before pullback to an
inverse sheet. The finite-disk divisor bounds producing the logarithms are
not assumed proved by this module.
-/

@[expose] public section

open Set Complex

namespace ThreeIM

/-- The coefficient logarithm is the difference of the A logarithm and half
the Psi logarithm. A prescribed nonzero square-root value fixes its sign. -/
theorem quotient_sqrt_log_control {Ω : Set ℂ} {A Ψ LA LP : ℂ → ℂ} {z v : ℂ}
    {cA cP : ℝ} (hA : DifferentiableOn ℂ A Ω)
    (hLA : DifferentiableOn ℂ LA Ω) (hLP : DifferentiableOn ℂ LP Ω)
    (hAz : A z ≠ 0) (hv : v ≠ 0) (hvΨ : v ^ 2 = Ψ z)
    (hLAz : LA z = 0) (hLPz : LP z = 0)
    (heA : ∀ w ∈ Ω, A w = A z * Complex.exp (LA w))
    (heP : ∀ w ∈ Ω, Ψ w = Ψ z * Complex.exp (LP w))
    (hcA : ∀ w ∈ Ω, ‖LA w‖ ≤ cA) (hcP : ∀ w ∈ Ω, ‖LP w‖ ≤ cP) :
    ∃ σ K ℓ : ℂ → ℂ,
      DifferentiableOn ℂ σ Ω ∧ DifferentiableOn ℂ K Ω ∧ DifferentiableOn ℂ ℓ Ω ∧
      σ z = v ∧ K z = A z / v ∧ ℓ z = 0 ∧
      ∀ w ∈ Ω, σ w ≠ 0 ∧ K w ≠ 0 ∧ σ w ^ 2 = Ψ w ∧ K w = A w / σ w ∧
        Complex.exp (ℓ w) = K w / K z ∧ ‖ℓ w‖ ≤ cA + cP / 2 := by
  let σ : ℂ → ℂ := fun w => v * Complex.exp (LP w / 2)
  let K : ℂ → ℂ := fun w => A w / σ w
  let ℓ : ℂ → ℂ := fun w => LA w - LP w / 2
  have hσ : DifferentiableOn ℂ σ Ω := by
    dsimp [σ]
    fun_prop
  have hσne : ∀ w, σ w ≠ 0 := fun w => mul_ne_zero hv (Complex.exp_ne_zero _)
  have hK : DifferentiableOn ℂ K Ω := hA.div hσ (fun w _ => hσne w)
  have hℓ : DifferentiableOn ℂ ℓ Ω := hLA.sub (hLP.div_const 2)
  have hσz : σ z = v := by simp only [σ, hLPz, zero_div, Complex.exp_zero, mul_one]
  have hKz : K z = A z / v := by simp only [K, hσz]
  refine ⟨σ, K, ℓ, hσ, hK, hℓ, hσz, hKz, ?_, fun w hw => ?_⟩
  · simp only [ℓ, hLAz, hLPz, zero_div, sub_zero]
  · have hAw : A w ≠ 0 := by rw [heA w hw]; exact mul_ne_zero hAz (Complex.exp_ne_zero _)
    refine ⟨hσne w, div_ne_zero hAw (hσne w), ?_, rfl, ?_, ?_⟩
    · change (v * Complex.exp (LP w / 2)) ^ 2 = Ψ w
      rw [mul_pow, hvΨ]
      have he : Complex.exp (LP w / 2) ^ 2 = Complex.exp (LP w) := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring
      rw [he, ← heP w hw]
    · change Complex.exp (LA w - LP w / 2) = (A w / σ w) / K z
      rw [Complex.exp_sub, heA w hw, hKz]
      dsimp [σ]
      field_simp [hAz, hv, Complex.exp_ne_zero]
    · change ‖LA w - LP w / 2‖ ≤ cA + cP / 2
      calc
        ‖LA w - LP w / 2‖ ≤ ‖LA w‖ + ‖LP w / 2‖ := norm_sub_le _ _
        _ = ‖LA w‖ + ‖LP w‖ / 2 := by rw [norm_div, Complex.norm_two]
        _ ≤ cA + cP / 2 := by linarith [hcA w hw, hcP w hw]

/-- The central bound for K has constant nine when A and Psi have constant six. -/
theorem log_norm_quotient_sqrt_bound {A v Ψ : ℂ} {B : ℝ}
    (hA : A ≠ 0) (hv : v ≠ 0) (hvΨ : v ^ 2 = Ψ)
    (hAb : |Real.log ‖A‖| ≤ 6 * B ^ 2)
    (hΨb : |Real.log ‖Ψ‖| ≤ 6 * B ^ 2) :
    |Real.log ‖A / v‖| ≤ 9 * B ^ 2 := by
  have hroot : 2 * Real.log ‖v‖ = Real.log ‖Ψ‖ := by
    rw [← hvΨ, norm_pow, Real.log_pow]
    norm_num
  rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hA) (norm_ne_zero_iff.2 hv)]
  have hlogv : |Real.log ‖v‖| ≤ 3 * B ^ 2 := by
    have he : |2 * Real.log ‖v‖| = |Real.log ‖Ψ‖| := congrArg abs hroot
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
    linarith
  calc
    |Real.log ‖A‖ - Real.log ‖v‖| ≤ |Real.log ‖A‖| + |Real.log ‖v‖| := abs_sub _ _
    _ ≤ 9 * B ^ 2 := by linarith

end ThreeIM
