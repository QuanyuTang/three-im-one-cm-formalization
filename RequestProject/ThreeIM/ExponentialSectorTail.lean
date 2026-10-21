module

public import RequestProject.ThreeIM.ExponentialRay

/-! # A uniform horizontal-tail estimate for the inverse second component -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem norm_mul_exp_add_le_of_deriv_error {y y' : ℝ → ℂ} {κ t : ℂ} {η : ℝ}
    (hd : ∀ s : ℝ, 0 ≤ s → HasDerivAt y (y' s) s)
    (hb : ∀ s : ℝ, 0 ≤ s → ‖y' s * Complex.exp (t + (s : ℂ)) - κ‖ ≤ η)
    (hy : Tendsto y atTop (𝓝 0)) : ‖y 0 * Complex.exp t + κ‖ ≤ η := by
  let d : ℂ := κ * Complex.exp (-t)
  let z : ℝ → ℂ := fun s => y s + d * Complex.exp (-(s : ℂ))
  have hzD (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt z (y' s - d * Complex.exp (-(s : ℂ))) s := by
    have he := ((hasDerivAt_id (s : ℂ)).neg.cexp).comp_ofReal
    simp only [Pi.neg_apply, id_eq] at he
    convert (hd s hs).add (he.const_mul d) using 1 <;> (try dsimp only [z]) <;> ring
  have he0 : Tendsto (fun s : ℝ => Complex.exp (-(s : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hz0 : Tendsto z atTop (𝓝 0) := by
    simpa only [z, mul_zero, add_zero] using hy.add (he0.const_mul d)
  have hzB (s : ℝ) (hs : 0 ≤ s) :
      ‖y' s - d * Complex.exp (-(s : ℂ))‖ ≤
        (η * Real.exp (-t.re)) * Real.exp (-(1 : ℝ) * s) := by
    have heq : y' s - d * Complex.exp (-(s : ℂ)) =
        (y' s * Complex.exp (t + (s : ℂ)) - κ) * Complex.exp (-(t + (s : ℂ))) := by
      calc
        _ = y' s - κ * Complex.exp (-(t + (s : ℂ))) := by
          dsimp only [d]
          rw [neg_add, Complex.exp_add]
          ring
        _ = _ := by
          rw [sub_mul, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    have hnorm : ‖Complex.exp (-(t + (s : ℂ)))‖ =
        Real.exp (-t.re) * Real.exp (-s) := by
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, neg_add]
      exact Real.exp_add _ _
    rw [heq, norm_mul, hnorm]
    calc
      _ ≤ η * (Real.exp (-t.re) * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_right (hb s hs) (by positivity)
      _ = (η * Real.exp (-t.re)) * Real.exp (-(1 : ℝ) * s) := by
        simp only [neg_mul, one_mul]
        ring
  have hbound := norm_le_of_deriv_tail (σ := 1) (δ := η * Real.exp (-t.re))
    (s₀ := 0) zero_lt_one hzD hzB hz0 0 le_rfl
  have hsmall : ‖y 0 + d‖ ≤ η * Real.exp (-t.re) := by
    simpa only [z, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one,
      div_one, zero_mul, mul_zero, Real.exp_zero] using hbound
  have heq : y 0 * Complex.exp t + κ = (y 0 + d) * Complex.exp t := by
    dsimp only [d]
    rw [add_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [heq, norm_mul, Complex.norm_exp]
  calc
    _ ≤ (η * Real.exp (-t.re)) * Real.exp t.re :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = η := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end ThreeIM
