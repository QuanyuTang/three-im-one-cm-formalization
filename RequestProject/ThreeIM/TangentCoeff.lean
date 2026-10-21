module

public import RequestProject.ThreeIM.TangentScalar

/-!
# Exponential coefficient estimates (Lemma 7.12)

For `αβ ≠ 0` let `c = α e^{z/2} - β e^{-z/2}`, `b = β e^{-z/2}`, and choose `z_*` with
`e^{z_*} = β/α`.  Then
`c'/c = 1/2 + 1/(e^{z - z_*} - 1)` and `b/c = 1/(e^{z - z_*} - 1)`, and
`|e^w - 1| ≥ δ/3` whenever `w` has distance at least `δ ≤ 1` from `2πiℤ`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

lemma abs_exp_sub_one_ge {x : ℝ} (hx : |x| < 1) : |x| / 3 ≤ |Real.exp x - 1| := by
  have h3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
    linarith [Real.add_one_le_exp x]
  · have hlt : Real.exp x < 1 := Real.exp_lt_one_iff.2 h
    rw [abs_of_neg h, abs_of_neg (by linarith)]
    have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-1) ≤ Real.exp x := Real.exp_le_exp.2 (by linarith [(abs_lt.1 hx).1])
    have : 1 - Real.exp x = (Real.exp (-x) - 1) * Real.exp x := by
      rw [sub_mul, ← Real.exp_add]; simp
    have hpos : 0 ≤ Real.exp (-x) - 1 := by linarith
    nlinarith

lemma norm_exp_sub_one_sq (w : ℂ) :
    ‖Complex.exp w - 1‖ ^ 2 =
      (Real.exp w.re - 1) ^ 2 + 4 * Real.exp w.re * Real.sin (w.im / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.exp_re, Complex.one_re, Complex.sub_im, Complex.exp_im,
    Complex.one_im, sub_zero]
  have hc : Real.cos w.im = 1 - 2 * Real.sin (w.im / 2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (w.im / 2)
    have h := Real.cos_two_mul (w.im / 2)
    rw [show 2 * (w.im / 2) = w.im by ring] at h
    nlinarith
  have hs := Real.sin_sq_add_cos_sq w.im
  rw [hc] at hs ⊢
  linear_combination (Real.exp w.re) ^ 2 * hs

lemma sin_half_ge {y : ℝ} (hy : |y| ≤ Real.pi) : |y| / Real.pi ≤ |Real.sin (y / 2)| := by
  have h0 : 0 ≤ |y| / 2 := by positivity
  have h1 : |y| / 2 ≤ Real.pi / 2 := by linarith
  have := Real.mul_le_sin h0 h1
  have hs : |Real.sin (y / 2)| = Real.sin (|y| / 2) := by
    rcases le_or_gt 0 y with h | h
    · have hy' : y ≤ Real.pi := by rwa [abs_of_nonneg h] at hy
      rw [abs_of_nonneg h,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · have hy' : -y ≤ Real.pi := by rwa [abs_of_neg h] at hy
      rw [abs_of_neg h, show -y / 2 = -(y / 2) by ring, Real.sin_neg, abs_of_nonpos]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  rw [hs]
  calc |y| / Real.pi = 2 / Real.pi * (|y| / 2) := by field_simp
    _ ≤ _ := this

/-- Near the origin (in a period strip), `|e^w - 1| ≥ |w|/3`. -/
lemma norm_exp_sub_one_ge_near {w : ℂ} (hre : |w.re| < 1) (him : |w.im| ≤ Real.pi) :
    ‖w‖ / 3 ≤ ‖Complex.exp w - 1‖ := by
  have hx := abs_exp_sub_one_ge hre
  have hy := sin_half_ge him
  have he : 1 / 3 ≤ Real.exp w.re := by
    have h3 : 1 / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    exact h3.trans (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hre).1]))
  have hpi : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsq : (‖w‖ / 3) ^ 2 ≤ ‖Complex.exp w - 1‖ ^ 2 := by
    rw [norm_exp_sub_one_sq, div_pow, Complex.sq_norm, Complex.normSq_apply]
    have h1 : (w.re) ^ 2 / 9 ≤ (Real.exp w.re - 1) ^ 2 := by
      have := mul_self_le_mul_self (by positivity) hx
      rw [← sq_abs (Real.exp w.re - 1), ← sq_abs w.re]
      nlinarith
    have h2 : (w.im) ^ 2 / 9 ≤ 4 * Real.exp w.re * Real.sin (w.im / 2) ^ 2 := by
      have := mul_self_le_mul_self (by positivity) hy
      rw [← sq_abs (Real.sin (w.im / 2))]
      have hpi0 := Real.pi_pos
      have : (w.im) ^ 2 / Real.pi ^ 2 ≤ |Real.sin (w.im / 2)| ^ 2 := by
        rw [← sq_abs w.im, ← div_pow]; nlinarith
      have h4 : (w.im) ^ 2 / 12 ≤ (w.im) ^ 2 / Real.pi ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hpi
      nlinarith [sq_nonneg (w.im)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq

/-- Far from the imaginary axis, `|e^w - 1| ≥ 1/2`. -/
lemma norm_exp_sub_one_ge_far {w : ℂ} (hre : 1 ≤ |w.re|) : 1 / 2 ≤ ‖Complex.exp w - 1‖ := by
  have h1 : |Real.exp w.re - 1| ≤ ‖Complex.exp w - 1‖ := by
    have := abs_norm_sub_norm_le (Complex.exp w) 1
    rwa [Complex.norm_exp, norm_one] at this
  refine le_trans ?_ h1
  rcases le_or_gt 0 w.re with h | h
  · rw [abs_of_nonneg h] at hre
    rw [abs_of_nonneg (by linarith [Real.add_one_le_exp w.re])]
    linarith [Real.add_one_le_exp w.re]
  · rw [abs_of_neg h] at hre
    have hle : Real.exp w.re ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [Real.exp_one_gt_d9])
    rw [abs_of_neg (by linarith)]
    linarith

/-- If `w` has distance at least `δ ≤ 1` from every point of `2πiℤ`, then `|e^w - 1| ≥ δ/3`. -/
lemma norm_exp_sub_one_ge_of_dist {w : ℂ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (hdist : ∀ k : ℤ, δ ≤ ‖w - 2 * Real.pi * Complex.I * k‖) :
    δ / 3 ≤ ‖Complex.exp w - 1‖ := by
  by_cases hre : 1 ≤ |w.re|
  · exact le_trans (by linarith) (norm_exp_sub_one_ge_far hre)
  push_neg at hre
  set k : ℤ := round (w.im / (2 * Real.pi)) with hk
  set w' : ℂ := w - 2 * Real.pi * Complex.I * k with hw'
  have hpi := Real.pi_pos
  have hre' : w'.re = w.re := by simp [hw']
  have him' : w'.im = w.im - 2 * Real.pi * k := by simp [hw']
  have him : |w'.im| ≤ Real.pi := by
    rw [him']
    have h := abs_sub_round (w.im / (2 * Real.pi))
    rw [← hk] at h
    have : w.im - 2 * Real.pi * k = 2 * Real.pi * (w.im / (2 * Real.pi) - k) := by
      field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have hexp : Complex.exp w' = Complex.exp w := by
    rw [hw', Complex.exp_sub, show (2 * Real.pi * Complex.I * k : ℂ) = k * (2 * Real.pi * Complex.I)
      by ring, Complex.exp_int_mul_two_pi_mul_I, div_one]
  have := norm_exp_sub_one_ge_near (w := w') (by rwa [hre']) him
  rw [hexp] at this
  have hδ := hdist k
  linarith

/-- The base point `z_*` with `e^{z_*} = β/α`. -/
noncomputable def tanZ (α β : ℂ) : ℂ := Complex.log (β / α)

lemma exp_tanZ {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) : Complex.exp (tanZ α β) = β / α :=
  Complex.exp_log (div_ne_zero hβ hα)

/-- `c = b (e^{z - z_*} - 1)`. -/
lemma tanC_eq_mul {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (z : ℂ) :
    tanC α β z = tanB β z * (Complex.exp (z - tanZ α β) - 1) := by
  have h1 : Complex.exp (z - tanZ α β) = Complex.exp z * α / β := by
    rw [Complex.exp_sub, exp_tanZ hα hβ]; field_simp
  have h2 : Complex.exp z = Complex.exp (z / 2) * Complex.exp (z / 2) := by
    rw [← Complex.exp_add]; ring_nf
  have h3 : Complex.exp (-z / 2) = (Complex.exp (z / 2))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  rw [h1, tanC, tanA, tanB, h2, h3]
  have hu := Complex.exp_ne_zero (z / 2)
  field_simp

lemma tanB_div_tanC {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (z : ℂ) :
    tanB β z / tanC α β z = 1 / (Complex.exp (z - tanZ α β) - 1) := by
  rw [tanC_eq_mul hα hβ, div_mul_eq_div_div, div_self (tanB_ne_zero hβ z)]

lemma tanC'_div_tanC {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {z : ℂ} (hz : tanC α β z ≠ 0) :
    tanC' α β z / tanC α β z = 1 / 2 + 1 / (Complex.exp (z - tanZ α β) - 1) := by
  rw [← tanB_div_tanC hα hβ]
  have : tanC' α β z = tanC α β z / 2 + tanB β z := by simp only [tanC', tanC]; ring
  rw [this]
  field_simp

/-! ### Points on short arcs -/

lemma norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ = |2 * Real.sin (θ / 2)| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]

lemma norm_exp_mul_I_sub_one_ge {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    2 * |θ| / Real.pi ≤ ‖Complex.exp (θ * Complex.I) - 1‖ := by
  rw [norm_exp_mul_I_sub_one, abs_mul, abs_two]
  have := sin_half_ge hθ
  rw [mul_div_assoc]
  linarith

lemma norm_exp_mul_I_sub_one_le (θ : ℝ) : ‖Complex.exp (θ * Complex.I) - 1‖ ≤ |θ| := by
  rw [norm_exp_mul_I_sub_one, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := θ / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- On an arc `zr e^{iθ}`, `0 ≤ θ ≤ ℓ/r`, with `ℓ ≤ 1/2`, one of the two endpoints has distance at
least `ℓ/π` from the progression `w₀ + 2πiℤ`. -/
lemma exists_arc_point_far {zr w₀ : ℂ} {r ℓ : ℝ} (hr : 1 ≤ r) (hzr : ‖zr‖ = r) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ 1 / 2) :
    ∃ θ ∈ ({0, ℓ / r} : Set ℝ), ∀ k : ℤ,
      ℓ / Real.pi ≤ ‖zr * Complex.exp (θ * Complex.I) - w₀ - 2 * Real.pi * Complex.I * k‖ := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hr0 : 0 < r := by linarith
  set t := ℓ / r with ht
  have ht0 : 0 < t := div_pos hℓ0 hr0
  have htπ : |t| ≤ Real.pi := by
    rw [abs_of_pos ht0]
    calc t ≤ ℓ := div_le_self hℓ0.le hr
      _ ≤ Real.pi := by linarith
  set p := zr * Complex.exp ((0 : ℝ) * Complex.I) with hp
  set q := zr * Complex.exp (t * Complex.I) with hq
  have hp' : p = zr := by simp [hp]
  have hqp : ‖q - p‖ = r * ‖Complex.exp (t * Complex.I) - 1‖ := by
    rw [hp', hq, show zr * Complex.exp (t * Complex.I) - zr =
      zr * (Complex.exp (t * Complex.I) - 1) by ring, norm_mul, hzr]
  have hqp1 : 2 * ℓ / Real.pi ≤ ‖q - p‖ := by
    rw [hqp]
    have := norm_exp_mul_I_sub_one_ge htπ
    rw [abs_of_pos ht0] at this
    calc 2 * ℓ / Real.pi = r * (2 * t / Real.pi) := by rw [ht]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hr0.le
  have hqp2 : ‖q - p‖ ≤ ℓ := by
    rw [hqp]
    have := norm_exp_mul_I_sub_one_le t
    rw [abs_of_pos ht0] at this
    calc r * ‖Complex.exp (t * Complex.I) - 1‖ ≤ r * t := mul_le_mul_of_nonneg_left this hr0.le
      _ = ℓ := by rw [ht]; field_simp
  by_contra hcon
  push_neg at hcon
  obtain ⟨k₁, hk₁⟩ := hcon 0 (by simp)
  obtain ⟨k₂, hk₂⟩ := hcon t (by simp)
  rw [← hp] at hk₁
  rw [← hq] at hk₂
  set A := p - w₀ - 2 * Real.pi * Complex.I * k₁
  set B := q - w₀ - 2 * Real.pi * Complex.I * k₂
  have hdiff : q - p = B - A + 2 * Real.pi * Complex.I * (k₂ - k₁ : ℤ) := by
    simp only [A, B]; push_cast; ring
  by_cases hk : k₁ = k₂
  · rw [hk, sub_self, Int.cast_zero, mul_zero, add_zero] at hdiff
    have : ‖q - p‖ ≤ ‖B‖ + ‖A‖ := by rw [hdiff]; exact norm_sub_le _ _
    have : ‖q - p‖ < 2 * ℓ / Real.pi := by
      calc ‖q - p‖ ≤ ‖B‖ + ‖A‖ := this
        _ < ℓ / Real.pi + ℓ / Real.pi := add_lt_add hk₂ hk₁
        _ = 2 * ℓ / Real.pi := by ring
    linarith
  · have hkk : (1 : ℝ) ≤ |((k₂ - k₁ : ℤ) : ℝ)| := by
      have : k₂ - k₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
      exact_mod_cast Int.one_le_abs this
    have hnorm : ‖2 * Real.pi * Complex.I * ((k₂ - k₁ : ℤ) : ℂ)‖ = 2 * Real.pi * |((k₂ - k₁ : ℤ) : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_intCast]
      ring
    have h1 : 2 * Real.pi ≤ ‖2 * Real.pi * Complex.I * ((k₂ - k₁ : ℤ) : ℂ)‖ := by
      rw [hnorm]; nlinarith
    have h2 : ‖2 * Real.pi * Complex.I * ((k₂ - k₁ : ℤ) : ℂ)‖ ≤ ‖q - p‖ + ‖B‖ + ‖A‖ := by
      have : 2 * Real.pi * Complex.I * ((k₂ - k₁ : ℤ) : ℂ) = (q - p) - B + A := by
        rw [hdiff]; ring
      rw [this]
      exact (norm_add_le _ _).trans (by linarith [norm_sub_le (q - p) B])
    have hA : ‖A‖ < 1 / 2 := lt_of_lt_of_le hk₁ (by
      rw [div_le_iff₀ hpi]; nlinarith)
    have hB : ‖B‖ < 1 / 2 := lt_of_lt_of_le hk₂ (by
      rw [div_le_iff₀ hpi]; nlinarith)
    linarith

/-- On an arc `zr e^{iθ}`, `|θ| ≤ θm ≤ 1/4`, one of the points `θ ∈ {0, ±θm}` has real part of
absolute value at least `r θm / π`. -/
lemma exists_arc_point_re {zr : ℂ} {r θm : ℝ} (hr : 0 < r) (hzr : ‖zr‖ = r) (hθ0 : 0 < θm)
    (hθ : θm ≤ 1 / 4) :
    ∃ θ ∈ ({0, θm, -θm} : Set ℝ), r * θm / Real.pi ≤ |(zr * Complex.exp (θ * Complex.I)).re| := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hre : ∀ θ : ℝ, (zr * Complex.exp (θ * Complex.I)).re =
      zr.re * Real.cos θ - zr.im * Real.sin θ := by
    intro θ
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hsq : zr.re ^ 2 + zr.im ^ 2 = r ^ 2 := by
    rw [← hzr, Complex.sq_norm, Complex.normSq_apply]; ring
  by_cases h0 : r / 2 ≤ |zr.re|
  · refine ⟨0, by simp, ?_⟩
    rw [hre, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
    refine le_trans ?_ h0
    rw [div_le_div_iff₀ hpi two_pos]
    nlinarith
  · push_neg at h0
    have him : r / 2 ≤ |zr.im| := by
      by_contra hlt
      push_neg at hlt
      have h1 : |zr.re| ^ 2 < (r / 2) ^ 2 := pow_lt_pow_left₀ h0 (abs_nonneg _) two_ne_zero
      have h2 : |zr.im| ^ 2 < (r / 2) ^ 2 := pow_lt_pow_left₀ hlt (abs_nonneg _) two_ne_zero
      rw [sq_abs] at h1 h2
      nlinarith
    have hsin : 2 / Real.pi * θm ≤ Real.sin θm :=
      Real.mul_le_sin hθ0.le (by linarith)
    have hdiff : (zr * Complex.exp (θm * Complex.I)).re -
        (zr * Complex.exp (((-θm : ℝ)) * Complex.I)).re = -2 * zr.im * Real.sin θm := by
      rw [hre, hre, Real.cos_neg, Real.sin_neg]; ring
    have hbig : 2 * (r * θm / Real.pi) ≤ |(zr * Complex.exp (θm * Complex.I)).re -
        (zr * Complex.exp (((-θm : ℝ)) * Complex.I)).re| := by
      rw [hdiff, abs_mul, abs_mul, abs_neg, abs_two,
        abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith))]
      calc 2 * (r * θm / Real.pi) = 2 * (r / 2) * (2 / Real.pi * θm) := by ring
        _ ≤ 2 * |zr.im| * Real.sin θm := by gcongr
    by_contra hcon
    push_neg at hcon
    have h1 := hcon θm (by simp)
    have h2 := hcon (-θm) (by simp)
    have := abs_sub _ _ |>.trans (add_le_add h1.le h2.le)
    linarith [abs_sub (zr * Complex.exp (θm * Complex.I)).re
      (zr * Complex.exp (((-θm : ℝ)) * Complex.I)).re]

end ThreeIM
