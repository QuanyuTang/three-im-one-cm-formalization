module

public import RequestProject.ThreeIM.Basic

/-!
# Derivative estimates near a Wiman–Valiron point (proof of Lemma 7.11)

If `H(z_r e^τ) = H(z_r) e^{ντ} (1 + φ(τ))` with `|φ| ≤ η` for `|τ| ≤ ρ`, then Cauchy's estimates
for `φ` on discs of radius comparable to `ρ` give, on the arc `z_r e^{iθ}`, `|θ| ≤ ρ/4`,
`|H| ≥ M/2`, `z H'/(ν H) = 1 + O(η)` and `H H''/(H')² = 1 + O(η + 1/ν)`.
-/

@[expose] public section

open Filter Set Topology Metric

namespace ThreeIM

/-- An algebraic identity used for `H H''/(H')²`. -/
lemma wv_key_identity {A u z s1 s2 ν : ℂ} (hA : A ≠ 0) (hz : z ≠ 0) (hL : ν * u + s1 ≠ 0) :
    A * u * ((A * (ν ^ 2 * u + 2 * ν * s1 + s2) - A * (ν * u + s1)) / z ^ 2) /
        (A * (ν * u + s1) / z) ^ 2 - 1 =
      (u * s2 - ν * u ^ 2 - u * s1 - s1 ^ 2) / (ν * u + s1) ^ 2 := by
  generalize hLd : ν * u + s1 = L at *
  have hs1 : s1 = L - ν * u := by rw [← hLd]; ring
  subst hs1
  field_simp
  ring

/-- The final real-arithmetic step of `wv_local`. -/
lemma wv_final_arith {N D ν η : ℝ} (hν : 1 ≤ ν) (hη0 : 0 ≤ η)
    (hN : N ≤ 10 * η * ν ^ 2 + 2 * ν + 3 * η * ν) (hD : ν ^ 2 / 4 ≤ D) :
    N ≤ (200 * η + 8 / ν) * D := by
  have hνpos : 0 < ν := by linarith
  have h8 : 8 / ν * (ν ^ 2 / 4) = 2 * ν := by field_simp; ring
  have hνsq : ν ≤ ν ^ 2 := by nlinarith
  have h1 : η * ν ≤ η * ν ^ 2 := mul_le_mul_of_nonneg_left hνsq hη0
  have h7 := mul_nonneg hη0 (sq_nonneg ν)
  have hc : 0 ≤ 200 * η + 8 / ν := by positivity
  calc N ≤ (200 * η + 8 / ν) * (ν ^ 2 / 4) := by rw [add_mul, h8]; nlinarith
    _ ≤ (200 * η + 8 / ν) * D := mul_le_mul_of_nonneg_left hD hc

/-- The local Wiman–Valiron estimates on an arc. -/
lemma wv_local {H : ℂ → ℂ} (hH : Differentiable ℂ H) {zr : ℂ} (hzr0 : zr ≠ 0) {ν M η ρ : ℝ}
    (hν : 1 ≤ ν) (hM : 1 ≤ M) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 16) (hρ0 : 0 < ρ)
    (hρν : 1 ≤ ρ * ν) (hzr : (1 - η) * M ≤ ‖H zr‖)
    (hexp : ∀ τ : ℂ, ‖τ‖ ≤ ρ →
      ‖H (zr * Complex.exp τ) - H zr * Complex.exp (ν * τ)‖ ≤ η * ‖H zr * Complex.exp (ν * τ)‖)
    {θ : ℝ} (hθ : |θ| ≤ ρ / 4) :
    M / 2 ≤ ‖H (zr * Complex.exp (θ * Complex.I))‖ ∧
    ‖zr * Complex.exp (θ * Complex.I) * deriv H (zr * Complex.exp (θ * Complex.I)) /
        (ν * H (zr * Complex.exp (θ * Complex.I))) - 1‖ ≤ 8 * η ∧
    ‖H (zr * Complex.exp (θ * Complex.I)) * deriv (deriv H) (zr * Complex.exp (θ * Complex.I)) /
        deriv H (zr * Complex.exp (θ * Complex.I)) ^ 2 - 1‖ ≤ 200 * η + 8 / ν := by
  have hHzr : H zr ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzr
    nlinarith
  set A0 := H zr with hA0
  set K : ℂ → ℂ := fun τ => H (zr * Complex.exp τ) with hKdef
  set φ : ℂ → ℂ := fun τ => K τ * Complex.exp (-(ν * τ)) / A0 - 1 with hφdef
  have hg : ∀ τ, HasDerivAt (fun τ => zr * Complex.exp τ) (zr * Complex.exp τ) τ := fun τ =>
    (Complex.hasDerivAt_exp τ).const_mul zr
  have hK : Differentiable ℂ K := fun τ => ((hH _).hasDerivAt.comp τ (hg τ)).differentiableAt
  have hφ : Differentiable ℂ φ := by
    intro τ
    have h1 : DifferentiableAt ℂ (fun τ : ℂ => Complex.exp (-(ν * τ))) τ := by fun_prop
    exact (((hK τ).mul h1).div_const A0).sub_const 1
  have hKF : ∀ τ, K τ = A0 * Complex.exp (ν * τ) * (1 + φ τ) := by
    intro τ
    simp only [hφdef]
    rw [Complex.exp_neg]
    have := Complex.exp_ne_zero (ν * τ)
    field_simp
    ring
  have hφb : ∀ τ, ‖τ‖ ≤ ρ → ‖φ τ‖ ≤ η := by
    intro τ hτ
    have hne : A0 * Complex.exp (ν * τ) ≠ 0 := mul_ne_zero hHzr (Complex.exp_ne_zero _)
    have : φ τ = (K τ - A0 * Complex.exp (ν * τ)) / (A0 * Complex.exp (ν * τ)) := by
      simp only [hφdef]
      rw [Complex.exp_neg]
      have := Complex.exp_ne_zero (ν * τ)
      field_simp
    rw [this, norm_div, div_le_iff₀ (norm_pos_iff.2 hne)]
    exact hexp τ hτ
  have hφ' : ∀ τ₁ : ℂ, ‖τ₁‖ ≤ ρ / 2 → ‖deriv φ τ₁‖ ≤ 2 * η / ρ := by
    intro τ₁ hτ₁
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := τ₁) (half_pos hρ0)
      hφ.diffContOnCl (fun τ hτ => hφb τ (by
        rw [mem_sphere_iff_norm] at hτ
        calc ‖τ‖ ≤ ‖τ - τ₁‖ + ‖τ₁‖ := by
              have := norm_add_le (τ - τ₁) τ₁; simpa using this
          _ ≤ ρ := by linarith))
    calc ‖deriv φ τ₁‖ ≤ η / (ρ / 2) := this
      _ = 2 * η / ρ := by field_simp
  have hφd : Differentiable ℂ (deriv φ) := fun τ => ((hφ.analyticAt τ).deriv).differentiableAt
  set τ₀ : ℂ := θ * Complex.I with hτ₀
  have hτ₀n : ‖τ₀‖ ≤ ρ / 4 := by
    rw [hτ₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hθ
  have hφ'' : ‖deriv (deriv φ) τ₀‖ ≤ 8 * η / ρ ^ 2 := by
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := τ₀) (by positivity : 0 < ρ / 4)
      hφd.diffContOnCl (fun τ hτ => hφ' τ (by
        rw [mem_sphere_iff_norm] at hτ
        calc ‖τ‖ ≤ ‖τ - τ₀‖ + ‖τ₀‖ := by
              have := norm_add_le (τ - τ₀) τ₀; simpa using this
          _ ≤ ρ / 2 := by linarith))
    calc ‖deriv (deriv φ) τ₀‖ ≤ 2 * η / ρ / (ρ / 4) := this
      _ = 8 * η / ρ ^ 2 := by field_simp; ring
  -- derivatives of `K` by the chain rule
  have hH'd : Differentiable ℂ (deriv H) := fun z => ((hH.analyticAt z).deriv).differentiableAt
  have hdK : ∀ τ, deriv K τ = deriv H (zr * Complex.exp τ) * (zr * Complex.exp τ) := fun τ =>
    ((hH _).hasDerivAt.comp τ (hg τ)).deriv
  have hdKfun : deriv K = fun τ => deriv H (zr * Complex.exp τ) * (zr * Complex.exp τ) :=
    funext hdK
  have hdK2 : deriv (deriv K) τ₀ = deriv (deriv H) (zr * Complex.exp τ₀) * (zr * Complex.exp τ₀) *
      (zr * Complex.exp τ₀) + deriv H (zr * Complex.exp τ₀) * (zr * Complex.exp τ₀) := by
    rw [hdKfun]
    have h1 : HasDerivAt (fun τ => deriv H (zr * Complex.exp τ))
        (deriv (deriv H) (zr * Complex.exp τ₀) * (zr * Complex.exp τ₀)) τ₀ :=
      (hH'd _).hasDerivAt.comp τ₀ (hg τ₀)
    exact (h1.mul (hg τ₀)).deriv
  -- derivatives of `K` from the product form
  have hF : K = fun τ => A0 * Complex.exp (ν * τ) * (1 + φ τ) := funext hKF
  have hE : ∀ τ, HasDerivAt (fun τ : ℂ => Complex.exp (ν * τ)) (ν * Complex.exp (ν * τ)) τ := by
    intro τ
    have := ((hasDerivAt_id τ).const_mul (ν : ℂ)).cexp
    simpa [mul_comm] using this
  have hdF : ∀ τ, deriv K τ = A0 * Complex.exp (ν * τ) * (ν * (1 + φ τ) + deriv φ τ) := by
    intro τ
    rw [hF]
    have h : HasDerivAt (fun τ => A0 * Complex.exp (ν * τ) * (1 + φ τ))
        (A0 * (ν * Complex.exp (ν * τ)) * (1 + φ τ) + A0 * Complex.exp (ν * τ) * deriv φ τ) τ :=
      ((hE τ).const_mul A0).mul ((hφ τ).hasDerivAt.const_add 1)
    rw [h.deriv]; ring
  have hdFfun : deriv K = fun τ => A0 * Complex.exp (ν * τ) * (ν * (1 + φ τ) + deriv φ τ) :=
    funext hdF
  have hdF2 : deriv (deriv K) τ₀ = A0 * Complex.exp (ν * τ₀) *
      (ν ^ 2 * (1 + φ τ₀) + 2 * ν * deriv φ τ₀ + deriv (deriv φ) τ₀) := by
    rw [hdFfun]
    have h1 := (hE τ₀).const_mul A0
    have h2 : HasDerivAt (fun τ => (ν : ℂ) * (1 + φ τ) + deriv φ τ)
        (ν * deriv φ τ₀ + deriv (deriv φ) τ₀) τ₀ :=
      (((hφ τ₀).hasDerivAt.const_add 1).const_mul (ν : ℂ)).add (hφd τ₀).hasDerivAt
    have h : HasDerivAt (fun τ => A0 * Complex.exp (ν * τ) * (ν * (1 + φ τ) + deriv φ τ))
        (A0 * (ν * Complex.exp (ν * τ₀)) * (ν * (1 + φ τ₀) + deriv φ τ₀) +
          A0 * Complex.exp (ν * τ₀) * (ν * deriv φ τ₀ + deriv (deriv φ) τ₀)) τ₀ := h1.mul h2
    rw [h.deriv]; ring
  -- the local quantities
  set z := zr * Complex.exp τ₀ with hz
  set A := A0 * Complex.exp (ν * τ₀) with hA
  set u := 1 + φ τ₀ with hu
  set s1 := deriv φ τ₀ with hs1
  set s2 := deriv (deriv φ) τ₀ with hs2
  have hHz : H z = A * u := hKF τ₀
  have hz1 : deriv H z * z = A * (ν * u + s1) := by rw [← hdK, hdF]
  have hz2 : deriv (deriv H) z * z * z + deriv H z * z = A * (ν ^ 2 * u + 2 * ν * s1 + s2) := by
    rw [← hdK2, hdF2]
  have hz0 : z ≠ 0 := mul_ne_zero hzr0 (Complex.exp_ne_zero _)
  have hAn : ‖A‖ = ‖A0‖ := by
    rw [hA, norm_mul, Complex.norm_exp]
    simp [hτ₀]
  have hu1 : ‖u - 1‖ ≤ η := by
    rw [hu, add_sub_cancel_left]; exact hφb τ₀ (hτ₀n.trans (by linarith))
  have hs1b0 : ‖s1‖ ≤ 2 * η / ρ := hφ' τ₀ (hτ₀n.trans (by linarith))
  clear_value s2 s1 u A z
  clear hdF2 hdK2 hdFfun hdF hE hF hdKfun hdK hφd hφ' hφb hKF hφ hK hg hexp
  have hρinv : 1 / ρ ≤ ν := by rw [div_le_iff₀ hρ0]; linarith
  have hνpos : 0 < ν := by linarith
  have hulo : 15 / 16 ≤ ‖u‖ := by
    have := norm_sub_norm_le 1 (1 - u)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have huhi : ‖u‖ ≤ 17 / 16 := by
    have := norm_le_insert' u 1
    have h2 : ‖u‖ ≤ ‖u - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (u - 1) 1; simpa using this
    rw [norm_one] at h2
    linarith
  have hs1b : ‖s1‖ ≤ 2 * η * ν := by
    calc ‖s1‖ ≤ 2 * η / ρ := hs1b0
      _ = 2 * η * (1 / ρ) := by ring
      _ ≤ 2 * η * ν := mul_le_mul_of_nonneg_left hρinv (by positivity)
  have hs2b : ‖s2‖ ≤ 8 * η * ν ^ 2 := by
    calc ‖s2‖ ≤ 8 * η / ρ ^ 2 := hφ''
      _ = 8 * η * (1 / ρ) ^ 2 := by ring
      _ ≤ 8 * η * ν ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hρinv 2
  have hu0 : u ≠ 0 := norm_pos_iff.1 (by linarith)
  have hA0' : A ≠ 0 := hA ▸ mul_ne_zero hHzr (Complex.exp_ne_zero _)
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hνpos.ne'
  have hL : ν / 2 ≤ ‖(ν : ℂ) * u + s1‖ := by
    have h1 := norm_sub_norm_le ((ν : ℂ) * u) (-s1)
    rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hνpos] at h1
    nlinarith
  have hL0 : (ν : ℂ) * u + s1 ≠ 0 := norm_pos_iff.1 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · -- `|H| ≥ M/2`
    rw [hHz, norm_mul, hAn]
    have h1 : (15 / 16) * M ≤ ‖A0‖ := le_trans (by nlinarith) hzr
    nlinarith
  · -- `z H'/(ν H) = 1 + s1/(ν u)`
    have key : z * deriv H z / (ν * H z) - 1 = s1 / (ν * u) := by
      rw [mul_comm z, hz1, hHz]
      field_simp
      ring
    rw [key, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνpos,
      div_le_iff₀ (by positivity)]
    have h := mul_nonneg (mul_nonneg hη0 hνpos.le) (by linarith : (0 : ℝ) ≤ 8 * ‖u‖ - 2)
    calc ‖s1‖ ≤ 2 * η * ν := hs1b
      _ ≤ 8 * η * (ν * ‖u‖) := by linarith
  · -- `H H''/(H')² = 1 + O(η + 1/ν)`
    have hH' : deriv H z = A * (ν * u + s1) / z := by
      rw [eq_div_iff hz0]; exact hz1
    have hH'' : deriv (deriv H) z = (A * (ν ^ 2 * u + 2 * ν * s1 + s2) - A * (ν * u + s1)) / z ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hz0)]; linear_combination hz2 - hz1
    have key : H z * deriv (deriv H) z / deriv H z ^ 2 - 1 =
        (u * s2 - ν * u ^ 2 - u * s1 - s1 ^ 2) / (ν * u + s1) ^ 2 := by
      rw [hHz, hH', hH'']
      exact wv_key_identity hA0' hz0 hL0
    rw [key, norm_div, norm_pow]
    have hnum : ‖u * s2 - ν * u ^ 2 - u * s1 - s1 ^ 2‖ ≤
        ‖u‖ * ‖s2‖ + ν * ‖u‖ ^ 2 + ‖u‖ * ‖s1‖ + ‖s1‖ ^ 2 := by
      have e1 := norm_sub_le (u * s2 - ν * u ^ 2 - u * s1) (s1 ^ 2)
      have e2 := norm_sub_le (u * s2 - ν * u ^ 2) (u * s1)
      have e3 := norm_sub_le (u * s2) (ν * u ^ 2)
      rw [norm_mul] at e2 e3
      rw [norm_pow] at e1
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνpos] at e3
      linarith
    have hnum2 : ‖u * s2 - ν * u ^ 2 - u * s1 - s1 ^ 2‖ ≤ 10 * η * ν ^ 2 + 2 * ν + 3 * η * ν := by
      refine hnum.trans ?_
      have hu0' : 0 ≤ ‖u‖ := norm_nonneg _
      have t1 : ‖u‖ * ‖s2‖ ≤ (17 / 16) * (8 * η * ν ^ 2) :=
        mul_le_mul huhi hs2b (norm_nonneg _) (by norm_num)
      have t2 : ν * ‖u‖ ^ 2 ≤ ν * (17 / 16) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0' huhi 2) hνpos.le
      have t3 : ‖u‖ * ‖s1‖ ≤ (17 / 16) * (2 * η * ν) :=
        mul_le_mul huhi hs1b (norm_nonneg _) (by norm_num)
      have t4 : ‖s1‖ ^ 2 ≤ (2 * η * ν) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs1b 2
      have t5 : (2 * η * ν) ^ 2 ≤ (1 / 4) * η * ν ^ 2 := by
        have : η * η ≤ η / 16 := by nlinarith
        calc (2 * η * ν) ^ 2 = 4 * (η * η) * ν ^ 2 := by ring
          _ ≤ 4 * (η / 16) * ν ^ 2 := by gcongr
          _ = (1 / 4) * η * ν ^ 2 := by ring
      have h6 := mul_nonneg hη0 hνpos.le
      have h7 := mul_nonneg hη0 (sq_nonneg ν)
      linarith
    have hden : ν ^ 2 / 4 ≤ ‖(ν : ℂ) * u + s1‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hL 2
      linarith [show (ν / 2) ^ 2 = ν ^ 2 / 4 by ring]
    rw [div_le_iff₀ (by positivity)]
    exact wv_final_arith hν hη0 hnum2 hden

end ThreeIM
