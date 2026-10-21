module

public import RequestProject.ThreeIM.TangentPoly
public import RequestProject.ThreeIM.TangentCoeff
public import RequestProject.ThreeIM.WVMacintyreArcs

/-!
# The tangent scalar equation: a pure maximum-modulus proof

A transcendental entire function cannot solve the scalar equation of the tangent system.  On
the proved real-slope maximum-modulus arcs the equation divided by `c H (H')²` forces
`(c'/c) z / ν → -2` (`wv_tan_balance`).  At arc points away from the zeros of `c` this gives
`ν = O(r)`, so the arcs are long, and at arc points with `|Re z| → ∞`, where `c'/c → ±1/2`, it
gives `z / ν → ∓4`, which contradicts the sign of `Re z`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

lemma wv_tan_balance_pointwise {c c' b h d e w ν : ℂ} (hc : c ≠ 0) (hh : h ≠ 0) (hd : d ≠ 0)
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
lemma wv_tan_balance {α β : ℂ} {H : ℂ → ℂ} (hs : TanScalar α β H) {w : ℕ → ℂ} {ν : ℕ → ℝ}
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
  exact (wv_tan_balance_pointwise hn3 hH hd hw (by exact_mod_cast hν n) hh1 (hs (w n))).symm

/-- Limits along points of Wiman–Valiron arcs. -/
lemma wv_arc_limits {H : ℂ → ℂ} {w : ℕ → ℂ} {ν M ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
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
lemma wv_tendsto_inv_exp_sub_one_of_re_atTop {w : ℕ → ℂ} {z₀ : ℂ}
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
lemma wv_tendsto_exp_sub_one_of_re_atBot {w : ℕ → ℂ} {z₀ : ℂ}
    (hw : Tendsto (fun n => (w n).re) atTop atBot) :
    Tendsto (fun n => Complex.exp (w n - z₀) - 1) atTop (𝓝 (-1)) := by
  have h0 : Tendsto (fun n => Complex.exp (w n - z₀)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp, Complex.sub_re]
    exact Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ _ hw)
  simpa using h0.sub_const 1

lemma wv_exp_sub_one_ne_zero_of_re_ne {w z₀ : ℂ} (h : w.re ≠ z₀.re) :
    Complex.exp (w - z₀) - 1 ≠ 0 := by
  intro h0
  have h1 : ‖Complex.exp (w - z₀)‖ = 1 := by rw [sub_eq_zero.1 h0, norm_one]
  rw [Complex.norm_exp, Real.exp_eq_one_iff, Complex.sub_re, sub_eq_zero] at h1
  exact h h1

/-- **Lemma 7.13, transcendental case.**  No transcendental entire function solves the scalar
equation of the tangent system. -/
theorem wv_tanScalar_nonPolynomial_false {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (htr : WVNonPolynomial H) (hs : TanScalar α β H) : False := by
  obtain ⟨r, ν, M, ε, κ, zr, hν, hε, hκνinf, hr1, hν1, hzr, hM1, hνM,
    hκ0, hκ1, hκνone, harc⟩ := wv_real_arcs hH htr
  set zs := tanZ α β with hzs
  have hpi := Real.pi_pos
  have hνpos : ∀ n, 0 < ν n := fun n => by linarith [hν1 n]
  have hν0 : ∀ n, ν n ≠ 0 := fun n => (hνpos n).ne'
  have hrpos : ∀ n, 0 < r n := fun n => by linarith [hr1 n]
  -- `M → ∞`
  have hMinf : Tendsto M atTop atTop := by
    have hlog : Tendsto (fun n => Real.log (M n)) atTop atTop := by
      have hsq : ∀ n, Real.sqrt (ν n) ≤ Real.log (M n) := fun n => by
        have h0 : 0 ≤ Real.log (M n) := Real.log_nonneg (hM1 n)
        calc Real.sqrt (ν n) ≤ Real.sqrt (Real.log (M n) ^ 2) := Real.sqrt_le_sqrt (hνM n)
          _ = Real.log (M n) := Real.sqrt_sq h0
      exact tendsto_atTop_mono hsq (Real.tendsto_sqrt_atTop.comp hν)
    refine tendsto_atTop_mono (fun n => ?_) hlog
    have := Real.log_le_sub_one_of_pos (by linarith [hM1 n] : 0 < M n)
    linarith
  have hlogM : Tendsto (fun n => Real.log (M n) ^ 2 / M n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hMinf
    simpa [Function.comp_def] using this
  have hinvM : Tendsto (fun n => 1 / M n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hMinf
  -- The real-slope construction gives variable widths with κν → ∞.
  have hκinv : ∀ n, (κ n)⁻¹ ≤ ν n := fun n =>
    (inv_le_iff_one_le_mul₀ (hκ0 n)).mpr (by simpa only [mul_comm] using hκνone n)
  have harcL : ∀ θ : ℕ → ℝ, (∀ n, |θ n| ≤ κ n / 4) →
      Tendsto (fun n => zr n * Complex.exp (θ n * Complex.I) *
        deriv H (zr n * Complex.exp (θ n * Complex.I)) /
        (ν n * H (zr n * Complex.exp (θ n * Complex.I)))) atTop (𝓝 1) ∧
      Tendsto (fun n => H (zr n * Complex.exp (θ n * Complex.I)) *
        deriv (deriv H) (zr n * Complex.exp (θ n * Complex.I)) /
        deriv H (zr n * Complex.exp (θ n * Complex.I)) ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun n => (H (zr n * Complex.exp (θ n * Complex.I)))⁻¹) atTop (𝓝 0) ∧
      ∀ n, ‖(H (zr n * Complex.exp (θ n * Complex.I)))⁻¹‖ ≤ 2 / M n := fun θ hθ =>
    wv_arc_limits (w := fun n => zr n * Complex.exp (θ n * Complex.I)) hε hMinf hM1
      (fun n => harc n (θ n) (hθ n))
  -- Step 1: arc points away from the zeros of `c`
  set ℓ : ℕ → ℝ := fun n => min (1 / 2) (r n * κ n / 4) with hℓdef
  have hℓ0 : ∀ n, 0 < ℓ n := fun n =>
    lt_min (by norm_num) (by have := hrpos n; have := hκ0 n; positivity)
  have hℓ : ∀ n, ℓ n ≤ 1 / 2 := fun n => min_le_left _ _
  choose θp hθp hfar using fun n =>
    exists_arc_point_far (w₀ := zs) (hr1 n) (hzr n) (hℓ0 n) (hℓ n)
  have hθpb : ∀ n, |θp n| ≤ κ n / 4 := by
    intro n
    rcases hθp n with h | h
    · rw [h, abs_zero]; exact (div_pos (hκ0 n) four_pos).le
    · have h' : θp n = ℓ n / r n := h
      rw [h', abs_of_pos (div_pos (hℓ0 n) (hrpos n)), div_le_iff₀ (hrpos n)]
      have := min_le_right (1 / 2 : ℝ) (r n * κ n / 4)
      simp only [hℓdef]
      linarith
  set p : ℕ → ℂ := fun n => zr n * Complex.exp (θp n * Complex.I) with hpdef
  have hE : ∀ n, ℓ n / Real.pi / 3 ≤ ‖Complex.exp (p n - zs) - 1‖ := fun n =>
    norm_exp_sub_one_ge_of_dist (by
      rw [div_le_one hpi]; linarith [hℓ n, Real.pi_gt_three]) (hfar n)
  have hEpos : ∀ n, 0 < ‖Complex.exp (p n - zs) - 1‖ := fun n =>
    lt_of_lt_of_le (by have := hℓ0 n; positivity) (hE n)
  have hcp : ∀ n, tanC α β (p n) ≠ 0 := fun n => by
    rw [tanC_eq_mul hα hβ]
    exact mul_ne_zero (tanB_ne_zero hβ _) (norm_pos_iff.1 (hEpos n))
  have hinvℓ : ∀ n, 1 / ℓ n ≤ 2 + 4 / (r n * κ n) := by
    intro n
    have hR0 : 0 < r n * κ n := mul_pos (hrpos n) (hκ0 n)
    rcases min_choice (1 / 2 : ℝ) (r n * κ n / 4) with h | h
    · simp only [hℓdef, h]; have : 0 ≤ 4 / (r n * κ n) := by positivity
      norm_num; linarith
    · simp only [hℓdef, h]; rw [one_div_div]; linarith
  have hinvE : ∀ n, ‖(Complex.exp (p n - zs) - 1)⁻¹‖ ≤ 3 * Real.pi * (2 + 4 / (r n * κ n)) := by
    intro n
    rw [norm_inv]
    calc ‖Complex.exp (p n - zs) - 1‖⁻¹ ≤ (ℓ n / Real.pi / 3)⁻¹ :=
          inv_anti₀ (by have := hℓ0 n; positivity) (hE n)
      _ = 3 * Real.pi * (1 / ℓ n) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hinvℓ n) (by positivity)
  have hRinv : ∀ n, 4 / (r n * κ n) ≤ 4 * ν n := by
    intro n
    rw [div_le_iff₀ (mul_pos (hrpos n) (hκ0 n))]
    have h1 : 1 ≤ κ n * ν n := by
      have := hκinv n
      rw [inv_le_iff_one_le_mul₀ (hκ0 n)] at this
      linarith
    nlinarith [hr1 n, hκ0 n, hνpos n]
  obtain ⟨h1p, h2p, h3p, hHp⟩ := harcL θp hθpb
  have h4p : Tendsto (fun n => tanB β (p n) / tanC α β (p n) * (H (p n))⁻¹) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖tanB β (p n) / tanC α β (p n) * (H (p n))⁻¹‖ ≤
        12 * Real.pi * (1 / M n) + 24 * Real.pi * (Real.log (M n) ^ 2 / M n) := by
      intro n
      rw [tanB_div_tanC hα hβ, one_div, norm_mul]
      have hM0 : 0 < M n := by linarith [hM1 n]
      calc ‖(Complex.exp (p n - zs) - 1)⁻¹‖ * ‖(H (p n))⁻¹‖
          ≤ (3 * Real.pi * (2 + 4 * ν n)) * (2 / M n) := by
            apply mul_le_mul _ (hHp n) (norm_nonneg _) (by have := hνpos n; positivity)
            exact (hinvE n).trans (mul_le_mul_of_nonneg_left (by linarith [hRinv n])
              (by positivity))
        _ ≤ (3 * Real.pi * (2 + 4 * Real.log (M n) ^ 2)) * (2 / M n) := by
            gcongr; exact hνM n
        _ = _ := by ring
    refine squeeze_zero_norm hbound ?_
    simpa using (hinvM.const_mul (12 * Real.pi)).add (hlogM.const_mul (24 * Real.pi))
  have hTp := wv_tan_balance hs hν0 (Eventually.of_forall hcp) h1p h2p h3p h4p
  -- Step 2: the arcs are long, `R = r κ → ∞`, using `κν → ∞`.
  have hR : Tendsto (fun n => r n * κ n) atTop atTop := by
    have hTn : ∀ᶠ n in atTop, 1 ≤ ‖tanC' α β (p n) / tanC α β (p n) * (p n / ν n)‖ :=
      hTp.norm.eventually (eventually_ge_nhds (by norm_num : (1 : ℝ) < ‖(-2 : ℂ)‖))
    have hsmall : ∀ᶠ n in atTop, 12 * Real.pi / (κ n * ν n) ≤ 1 / 2 := by
      have : Tendsto (fun n => 12 * Real.pi / (κ n * ν n)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_inv_atTop_zero.comp hκνinf).const_mul (12 * Real.pi)
      exact this.eventually (eventually_le_nhds (by norm_num))
    have hlow : ∀ᶠ n in atTop, (κ n * ν n) / (1 + 12 * Real.pi) ≤ r n * κ n := by
      filter_upwards [hTn, hsmall] with n hn hs'
      have hcc : ‖tanC' α β (p n) / tanC α β (p n)‖ ≤
          1 / 2 + 3 * Real.pi * (2 + 4 / (r n * κ n)) := by
        rw [tanC'_div_tanC hα hβ (hcp n)]
        refine (norm_add_le _ _).trans ?_
        rw [one_div (Complex.exp (p n - zs) - 1)]
        have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [h12]
        linarith [hinvE n]
      have hpn : ‖p n / (ν n : ℂ)‖ = r n / ν n := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hνpos n)]
        simp only [hpdef, norm_mul, hzr n, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [norm_mul, hpn] at hn
      have hR0 : 0 < r n * κ n := mul_pos (hrpos n) (hκ0 n)
      have key : 1 ≤ (1 / 2 + 6 * Real.pi) * (r n / ν n) + 12 * Real.pi / (κ n * ν n) := by
        have := hn.trans (mul_le_mul_of_nonneg_right hcc
          (by have := hνpos n; have := hrpos n; positivity))
        calc 1 ≤ _ := this
          _ = _ := by
            have := hκ0 n; have := hνpos n; have := hrpos n
            field_simp
            ring
      have h2 : 1 / (1 + 12 * Real.pi) ≤ r n / ν n := by
        rw [div_le_iff₀ (by positivity)]
        have : (r n / ν n) * (1 + 12 * Real.pi) = 2 * ((1 / 2 + 6 * Real.pi) * (r n / ν n)) := by
          ring
        rw [this]
        linarith
      calc (κ n * ν n) / (1 + 12 * Real.pi) = (1 / (1 + 12 * Real.pi)) * (κ n * ν n) := by
            ring
        _ ≤ (r n / ν n) * (κ n * ν n) :=
            mul_le_mul_of_nonneg_right h2 (by have := hκ0 n; have := hνpos n; positivity)
        _ = r n * κ n := by have := hνpos n; field_simp
    exact tendsto_atTop_mono' atTop hlow
      ((tendsto_div_const_atTop_of_pos (by positivity)).2 hκνinf)
  -- Step 3: arc points with `|Re z| → ∞`
  choose θq hθq hreq using fun n =>
    exists_arc_point_re (hrpos n) (hzr n) (by have := hκ0 n; positivity : 0 < κ n / 4)
      (by linarith [hκ1 n] : κ n / 4 ≤ 1 / 4)
  have hθqb : ∀ n, |θq n| ≤ κ n / 4 := by
    intro n
    have h4 : 0 ≤ κ n / 4 := (div_pos (hκ0 n) four_pos).le
    rcases hθq n with h | h | h
    · rw [h, abs_zero]; exact h4
    · rw [h, abs_of_nonneg h4]
    · rw [Set.mem_singleton_iff] at h; rw [h, abs_neg, abs_of_nonneg h4]
  set q : ℕ → ℂ := fun n => zr n * Complex.exp (θq n * Complex.I) with hqdef
  have hReq : Tendsto (fun n => |(q n).re|) atTop atTop := by
    refine tendsto_atTop_mono (fun n => hreq n) ?_
    have := (tendsto_div_const_atTop_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)).2 hR
    refine this.congr (fun n => ?_)
    ring
  obtain ⟨h1q, h2q, h3q, -⟩ := harcL θq hθqb
  by_cases hfreq : ∃ᶠ n in atTop, 0 < (q n).re
  · -- real parts `→ +∞` along a subsequence: `c'/c → 1/2`, so `z/ν → -4`
    obtain ⟨φ, hφ, hφpos⟩ := extraction_of_frequently_atTop hfreq
    have hφt := hφ.tendsto_atTop
    have hwre : Tendsto (fun n => (q (φ n)).re) atTop atTop :=
      (hReq.comp hφt).congr (fun n => abs_of_pos (hφpos n))
    have hEw := wv_tendsto_inv_exp_sub_one_of_re_atTop (z₀ := zs) hwre
    have hcw : ∀ᶠ n in atTop, tanC α β (q (φ n)) ≠ 0 := by
      filter_upwards [hwre.eventually_gt_atTop zs.re] with n hn
      rw [tanC_eq_mul hα hβ]
      exact mul_ne_zero (tanB_ne_zero hβ _) (wv_exp_sub_one_ne_zero_of_re_ne hn.ne')
    have h4 : Tendsto (fun n => tanB β (q (φ n)) / tanC α β (q (φ n)) * (H (q (φ n)))⁻¹)
        atTop (𝓝 0) := by
      have := hEw.mul (h3q.comp hφt)
      rw [zero_mul] at this
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, tanB_div_tanC hα hβ, one_div, hqdef, hzs]
    have hT := wv_tan_balance (w := fun n => q (φ n)) (ν := fun n => ν (φ n)) hs
      (fun n => hν0 (φ n)) hcw (h1q.comp hφt) (h2q.comp hφt) (h3q.comp hφt) h4
    have hcc : Tendsto (fun n => tanC' α β (q (φ n)) / tanC α β (q (φ n))) atTop
        (𝓝 (1 / 2)) := by
      have := (tendsto_const_nhds (x := (1 / 2 : ℂ))).add hEw
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [hcw] with n hn
      rw [tanC'_div_tanC hα hβ hn, one_div (Complex.exp (q (φ n) - zs) - 1)]
    have hwν : Tendsto (fun n => q (φ n) / (ν (φ n) : ℂ)) atTop (𝓝 (-4)) := by
      have := hT.div hcc (by norm_num)
      rw [show (-2 : ℂ) / (1 / 2) = -4 by norm_num] at this
      refine this.congr' ?_
      filter_upwards [hcc.eventually_ne (by norm_num : (1 / 2 : ℂ) ≠ 0), hcw] with n hn hcn
      have hc' : tanC' α β (q (φ n)) ≠ 0 := fun h => hn (by simp [h])
      have hνn : (ν (φ n) : ℂ) ≠ 0 := by exact_mod_cast hν0 (φ n)
      simp only [Pi.div_apply]
      field_simp
    have hre_lim : Tendsto (fun n => (q (φ n) / (ν (φ n) : ℂ)).re) atTop (𝓝 (-4 : ℂ).re) :=
      (Complex.continuous_re.tendsto _).comp hwν
    have hnonneg : ∀ n, 0 ≤ (q (φ n) / (ν (φ n) : ℂ)).re := fun n => by
      rw [Complex.div_ofReal_re]; exact div_nonneg (hφpos n).le (hνpos _).le
    have := ge_of_tendsto hre_lim (Eventually.of_forall hnonneg)
    norm_num at this
  · -- real parts eventually `≤ 0`, hence `→ -∞`: `c'/c → -1/2`, so `z/ν → 4`
    rw [not_frequently] at hfreq
    have hwre : Tendsto (fun n => (q n).re) atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp hReq
      refine this.congr' ?_
      filter_upwards [hfreq] with n hn
      push_neg at hn
      simp [abs_of_nonpos hn]
    have hEw := wv_tendsto_exp_sub_one_of_re_atBot (z₀ := zs) hwre
    have hEinv := hEw.inv₀ (by norm_num : (-1 : ℂ) ≠ 0)
    have hcw : ∀ᶠ n in atTop, tanC α β (q n) ≠ 0 := by
      filter_upwards [hwre.eventually_lt_atBot zs.re] with n hn
      rw [tanC_eq_mul hα hβ]
      exact mul_ne_zero (tanB_ne_zero hβ _) (wv_exp_sub_one_ne_zero_of_re_ne hn.ne)
    have h4 : Tendsto (fun n => tanB β (q n) / tanC α β (q n) * (H (q n))⁻¹) atTop (𝓝 0) := by
      have := hEinv.mul h3q
      rw [mul_zero] at this
      refine this.congr (fun n => ?_)
      simp only [tanB_div_tanC hα hβ, one_div, hqdef, hzs]
    have hT := wv_tan_balance (w := q) (ν := ν) hs hν0 hcw h1q h2q h3q h4
    have hcc : Tendsto (fun n => tanC' α β (q n) / tanC α β (q n)) atTop (𝓝 (-1 / 2)) := by
      have := (tendsto_const_nhds (x := (1 / 2 : ℂ))).add hEinv
      rw [show (1 / 2 : ℂ) + (-1)⁻¹ = -1 / 2 by norm_num] at this
      refine this.congr' ?_
      filter_upwards [hcw] with n hn
      rw [tanC'_div_tanC hα hβ hn, one_div (Complex.exp (q n - zs) - 1)]
    have hwν : Tendsto (fun n => q n / (ν n : ℂ)) atTop (𝓝 4) := by
      have := hT.div hcc (by norm_num)
      rw [show (-2 : ℂ) / (-1 / 2) = 4 by norm_num] at this
      refine this.congr' ?_
      filter_upwards [hcc.eventually_ne (by norm_num : (-1 / 2 : ℂ) ≠ 0), hcw] with n hn hcn
      have hc' : tanC' α β (q n) ≠ 0 := fun h => hn (by simp [h])
      have hνn : (ν n : ℂ) ≠ 0 := by exact_mod_cast hν0 n
      simp only [Pi.div_apply]
      field_simp
    have hre_lim : Tendsto (fun n => (q n / (ν n : ℂ)).re) atTop (𝓝 (4 : ℂ).re) :=
      (Complex.continuous_re.tendsto _).comp hwν
    have hnonpos : ∀ᶠ n in atTop, (q n / (ν n : ℂ)).re ≤ 0 := by
      filter_upwards [hfreq] with n hn
      push_neg at hn
      rw [Complex.div_ofReal_re]
      exact div_nonpos_of_nonpos_of_nonneg hn (hνpos n).le
    have := le_of_tendsto hre_lim hnonpos
    norm_num at this

/-- The original scalar classification, derived from the polynomial case
and the proved real-slope arcs, with no central-index external theorem. -/
theorem wv_tanScalar_const {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (h : TanScalar α β H) : ∀ z, H z = H 0 := by
  by_cases htr : WVNonPolynomial H
  · exact (wv_tanScalar_nonPolynomial_false hα hβ hH htr h).elim
  · simp only [WVNonPolynomial, not_forall, not_exists, not_not] at htr
    obtain ⟨p, hp⟩ := htr
    have hHp : H = fun z => p.eval z := funext hp
    rw [hHp] at h ⊢
    have hd := tanScalar_poly hα h
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp

end ThreeIM
