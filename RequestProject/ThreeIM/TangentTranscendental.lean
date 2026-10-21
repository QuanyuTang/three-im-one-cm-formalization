module

public import RequestProject.ThreeIM.TangentCoeff
public import RequestProject.ThreeIM.WVTranscendentalDefinition
public import RequestProject.ThreeIM.WVTangentTranscendental

/-!
# The scalar equation of the tangent system: transcendental solutions

A transcendental entire function cannot solve the scalar equation of the tangent system.  On
the proved real-slope maximum-modulus arcs the equation divided by `c H (H')²` forces
`(c'/c) z / ν → -2` (`tan_balance`).  At arc points away from the zeros of `c` this gives
`ν = O(r)`, so the arcs are long, and at arc points with `|Re z| → ∞`, where `c'/c → ±1/2`, it
gives `z / ν → ∓4`, which contradicts the sign of `Re z`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

lemma tan_balance_pointwise {c c' b h d e w ν : ℂ} (hc : c ≠ 0) (hh : h ≠ 0) (hd : d ≠ 0)
    (hw : w ≠ 0) (hν : ν ≠ 0) (hh1 : h - 1 ≠ 0)
    (hs : c * h * (h - 1) * e - c' * h * (h - 1) * d - (c * (3 * h - 1) + b) * d ^ 2 = 0) :
    c' / c * (w / ν) = ((h * e / d ^ 2) * (1 - h⁻¹) - 3 + h⁻¹ - b / c * h⁻¹) *
      (w * d / (ν * h)) / (1 - h⁻¹) := by
  have e1 : 1 - h⁻¹ = (h - 1) / h := by field_simp
  rw [e1]
  field_simp
  linear_combination -hs

/-- **The balance relation** (proof of Lemma 7.13): along points where `H` behaves like a
Wiman–Valiron monomial of degree `ν`, the scalar equation forces `(c'/c) z / ν → -2`. -/
lemma tan_balance {α β : ℂ} {H : ℂ → ℂ} (hs : TanScalar α β H) {w : ℕ → ℂ} {ν : ℕ → ℝ}
    (hν : ∀ n, ν n ≠ 0) (hc0 : ∀ᶠ n in atTop, tanC α β (w n) ≠ 0)
    (h1 : Tendsto (fun n => w n * deriv H (w n) / (ν n * H (w n))) atTop (𝓝 1))
    (h2 : Tendsto (fun n => H (w n) * deriv (deriv H) (w n) / deriv H (w n) ^ 2) atTop (𝓝 1))
    (h3 : Tendsto (fun n => (H (w n))⁻¹) atTop (𝓝 0))
    (h4 : Tendsto (fun n => tanB β (w n) / tanC α β (w n) * (H (w n))⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => tanC' α β (w n) / tanC α β (w n) * (w n / ν n)) atTop (𝓝 (-2)) := by
  have hev1 : ∀ᶠ n in atTop, w n * deriv H (w n) / (ν n * H (w n)) ≠ 0 :=
    h1.eventually_ne one_ne_zero
  have hev2 : ∀ᶠ n in atTop, (H (w n))⁻¹ ≠ 1 := h3.eventually_ne zero_ne_one
  have hlim := ((((h2.mul ((tendsto_const_nhds (x := (1 : ℂ))).sub h3)).sub
    (tendsto_const_nhds (x := (3 : ℂ)))).add h3).sub h4).mul h1 |>.div
    ((tendsto_const_nhds (x := (1 : ℂ))).sub h3) (by norm_num : (1 : ℂ) - 0 ≠ 0)
  have hval : ((1 : ℂ) * (1 - 0) - 3 + 0 - 0) * 1 / (1 - 0) = -2 := by norm_num
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev1, hev2, hc0] with n hn1 hn2 hn3
  have hH : H (w n) ≠ 0 := fun h0 => hn1 (by simp [h0])
  have hd : deriv H (w n) ≠ 0 := fun h0 => hn1 (by simp [h0])
  have hw : w n ≠ 0 := fun h0 => hn1 (by simp [h0])
  have hh1 : H (w n) - 1 ≠ 0 := fun h0 => hn2 (by rw [sub_eq_zero.1 h0, inv_one])
  exact (tan_balance_pointwise hn3 hH hd hw (by exact_mod_cast hν n) hh1 (hs (w n))).symm

/-- Limits along points of Wiman–Valiron arcs. -/
lemma arc_limits {H : ℂ → ℂ} {w : ℕ → ℂ} {ν M ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hM : Tendsto M atTop atTop) (hM1 : ∀ n, 1 ≤ M n)
    (hb : ∀ n, M n / 2 ≤ ‖H (w n)‖ ∧
      ‖w n * deriv H (w n) / (ν n * H (w n)) - 1‖ ≤ ε n ∧
      ‖H (w n) * deriv (deriv H) (w n) / deriv H (w n) ^ 2 - 1‖ ≤ ε n) :
    Tendsto (fun n => w n * deriv H (w n) / (ν n * H (w n))) atTop (𝓝 1) ∧
    Tendsto (fun n => H (w n) * deriv (deriv H) (w n) / deriv H (w n) ^ 2) atTop (𝓝 1) ∧
    Tendsto (fun n => (H (w n))⁻¹) atTop (𝓝 0) ∧ ∀ n, ‖(H (w n))⁻¹‖ ≤ 2 / M n := by
  have hinv : ∀ n, ‖(H (w n))⁻¹‖ ≤ 2 / M n := by
    intro n
    have hM0 : 0 < M n / 2 := by linarith [hM1 n]
    rw [norm_inv]
    calc ‖H (w n)‖⁻¹ ≤ (M n / 2)⁻¹ := inv_anti₀ hM0 (hb n).1
      _ = 2 / M n := by rw [inv_div]
  refine ⟨?_, ?_, ?_, hinv⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hb n).2.1) hε
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hb n).2.2) hε
  · refine squeeze_zero_norm hinv ?_
    have := (tendsto_inv_atTop_zero.comp hM).const_mul 2
    simpa [div_eq_mul_inv] using this

/-- If `Re w_n → +∞` then `1/(e^{w_n - z_*} - 1) → 0`. -/
lemma tendsto_inv_exp_sub_one_of_re_atTop {w : ℕ → ℂ} {z₀ : ℂ}
    (hw : Tendsto (fun n => (w n).re) atTop atTop) :
    Tendsto (fun n => (Complex.exp (w n - z₀) - 1)⁻¹) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖Complex.exp (w n - z₀)‖) atTop atTop := by
    simp only [Complex.norm_exp, Complex.sub_re]
    exact Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _ hw)
  have hnorm' : Tendsto (fun n => ‖Complex.exp (w n - z₀) - 1‖) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right _ (-1) hnorm)
    have := norm_sub_norm_le (Complex.exp (w n - z₀)) 1
    rw [norm_one] at this
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact tendsto_inv_atTop_zero.comp hnorm'

/-- If `Re w_n → -∞` then `e^{w_n - z_*} - 1 → -1`. -/
lemma tendsto_exp_sub_one_of_re_atBot {w : ℕ → ℂ} {z₀ : ℂ}
    (hw : Tendsto (fun n => (w n).re) atTop atBot) :
    Tendsto (fun n => Complex.exp (w n - z₀) - 1) atTop (𝓝 (-1)) := by
  have h0 : Tendsto (fun n => Complex.exp (w n - z₀)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp, Complex.sub_re]
    exact Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ _ hw)
  simpa using h0.sub_const 1

lemma exp_sub_one_ne_zero_of_re_ne {w z₀ : ℂ} (h : w.re ≠ z₀.re) :
    Complex.exp (w - z₀) - 1 ≠ 0 := by
  intro h0
  have h1 : ‖Complex.exp (w - z₀)‖ = 1 := by rw [sub_eq_zero.1 h0, norm_one]
  rw [Complex.norm_exp, Real.exp_eq_one_iff, Complex.sub_re, sub_eq_zero] at h1
  exact h h1

/-- **Lemma 7.13, transcendental case.**  No transcendental entire function solves the scalar
equation of the tangent system. -/
theorem tanScalar_transcendental_false {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (htr : Transcendental H) (hs : TanScalar α β H) : False := by
  change WVNonPolynomial H at htr
  exact wv_tanScalar_nonPolynomial_false hα hβ hH htr hs

end ThreeIM
