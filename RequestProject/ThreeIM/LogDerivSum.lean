module

public import RequestProject.ThreeIM.MathlibImports

/-!
# Proximity of a finite sum of simple fractions

For finitely many points `u` with integer weights `d u`, of total mass `n = ∑ |d u|`, we prove
`m(r, ∑ d u / (z - u)) ≤ 2 log (2n + 1) + 2` for `r ≥ 1`.  This is the part of the logarithmic
derivative lemma that accounts for the zeros and poles of the function.

The proof uses `∫₀^{2π} |e^{iθ} - b|^{-1/2} dθ ≤ 4π` (from `|e^{iθ} - b| ≥ |θ - arg b|/π`),
the subadditivity `(∑ x)^{1/2} ≤ ∑ x^{1/2}` and the tangent-line inequality
`log⁺ x ≤ log⁺ λ + x/λ` (a substitute for Jensen's inequality for the concave `log`).
-/

@[expose] public section

open Real MeasureTheory Set Filter intervalIntegral
open scoped Interval

namespace ThreeIM

/-- `|t - arg b| / π ≤ |e^{it} - b|` when `|t - arg b| ≤ π`. -/
lemma abs_sub_arg_div_pi_le (b : ℂ) {t : ℝ} (ht : |t - b.arg| ≤ π) :
    |t - b.arg| / π ≤ ‖circleMap 0 1 t - b‖ := by
  set φ := b.arg
  set c := circleMap 0 1 t
  set e := Complex.exp (φ * Complex.I)
  have hc : ‖c‖ = 1 := by simp [c]
  have hb : b = ‖b‖ * e := (Complex.norm_mul_exp_arg_mul_I b).symm
  have h1 : ‖b - e‖ = |‖b‖ - 1| := by
    conv_lhs => rw [hb]
    rw [show (‖b‖ : ℂ) * e - e = ((‖b‖ - 1 : ℝ) : ℂ) * e by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h2 : |‖b‖ - 1| ≤ ‖c - b‖ := by
    rw [← hc, abs_sub_comm]; exact abs_norm_sub_norm_le c b
  have h3 : ‖c - e‖ ≤ 2 * ‖c - b‖ := by
    calc ‖c - e‖ ≤ ‖c - b‖ + ‖b - e‖ := norm_sub_le_norm_sub_add_norm_sub c b e
      _ ≤ 2 * ‖c - b‖ := by rw [h1]; linarith
  have h4 : ‖c - e‖ = ‖2 * Real.sin ((t - φ) / 2)‖ := by
    rw [← Complex.norm_exp_I_mul_ofReal_sub_one]
    have : c - e = e * (Complex.exp (Complex.I * ((t - φ : ℝ) : ℂ)) - 1) := by
      simp only [c, e, circleMap, zero_add, Complex.ofReal_one, one_mul, mul_sub, mul_one,
        ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h5 : 2 / π * |(t - φ) / 2| ≤ |Real.sin ((t - φ) / 2)| := by
    have ha : |(t - φ) / 2| ≤ π / 2 := by rw [abs_div, abs_two]; linarith
    rcases le_total 0 ((t - φ) / 2) with hp | hn
    · rw [abs_of_nonneg hp] at ha ⊢
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hp (by linarith [pi_pos]))]
      exact mul_le_sin hp ha
    · rw [abs_of_nonpos hn] at ha ⊢
      rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hn (by linarith [pi_pos])),
        ← Real.sin_neg]
      exact mul_le_sin (by linarith) ha
  rw [h4, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two] at h3
  rw [abs_div, abs_two] at h5
  rw [div_le_iff₀ pi_pos]
  have := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ π by positivity)
  field_simp at this
  nlinarith [pi_pos]


lemma intervalIntegral_abs_sub_pi_rpow :
    IntervalIntegrable (fun θ : ℝ => |θ - π| ^ (-(1/2 : ℝ))) volume 0 (2 * π) ∧
    ∫ θ in (0)..(2 * π), |θ - π| ^ (-(1/2 : ℝ)) = 4 * √π := by
  have hr : (-1 : ℝ) < -(1/2) := by norm_num
  have hI : ∫ x in (0:ℝ)..π, x ^ (-(1/2 : ℝ)) = 2 * √π := by
    rw [integral_rpow (Or.inl hr)]
    rw [Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
    norm_num; ring
  have e1 : EqOn (fun θ : ℝ => |θ - π| ^ (-(1/2 : ℝ))) (fun θ => (π - θ) ^ (-(1/2 : ℝ)))
      (uIcc 0 π) := by
    intro θ hθ
    rw [uIcc_of_le pi_pos.le] at hθ
    simp only
    rw [abs_of_nonpos (by linarith [hθ.2])]; ring_nf
  have e2 : EqOn (fun θ : ℝ => |θ - π| ^ (-(1/2 : ℝ))) (fun θ => (θ - π) ^ (-(1/2 : ℝ)))
      (uIcc π (2 * π)) := by
    intro θ hθ
    rw [uIcc_of_le (by linarith [pi_pos])] at hθ
    simp only
    rw [abs_of_nonneg (by linarith [hθ.1])]
  have i1 : IntervalIntegrable (fun θ : ℝ => (π - θ) ^ (-(1/2 : ℝ))) volume 0 π := by
    have := ((intervalIntegrable_rpow' (a := 0) (b := π) hr).comp_sub_left π)
    simpa using this.symm
  have i2 : IntervalIntegrable (fun θ : ℝ => (θ - π) ^ (-(1/2 : ℝ))) volume π (2 * π) := by
    have := ((intervalIntegrable_rpow' (a := 0) (b := π) hr).comp_sub_right π)
    convert this using 1 <;> ring
  have j1 := i1.congr (fun θ hθ => (e1 (uIoc_subset_uIcc hθ)).symm)
  have j2 := i2.congr (fun θ hθ => (e2 (uIoc_subset_uIcc hθ)).symm)
  refine ⟨j1.trans j2, ?_⟩
  rw [← integral_add_adjacent_intervals j1 j2, integral_congr e1, integral_congr e2,
    integral_comp_sub_left (fun x => x ^ (-(1/2 : ℝ))),
    integral_comp_sub_right (fun x => x ^ (-(1/2 : ℝ)))]
  simp only [sub_self, sub_zero]
  rw [show 2 * π - π = π by ring, hI]; ring

/-- `(1/2π) ∫₀^{2π} |e^{iθ} - b|^{-1/2} dθ ≤ 2`. -/
lemma circleAverage_norm_sub_rpow_le (b : ℂ) :
    CircleIntegrable (fun z => ‖z - b‖ ^ (-(1/2 : ℝ))) 0 1 ∧
    circleAverage (fun z => ‖z - b‖ ^ (-(1/2 : ℝ))) 0 1 ≤ 2 := by
  set φ := b.arg
  set η := φ - π
  set F : ℝ → ℝ := fun θ => ‖circleMap 0 1 (θ + η) - b‖ ^ (-(1/2 : ℝ)) with hF
  set G : ℝ → ℝ := fun θ => √π * |θ - π| ^ (-(1/2 : ℝ)) with hG
  obtain ⟨hGi, hGv⟩ := intervalIntegral_abs_sub_pi_rpow
  have hGi' : IntervalIntegrable G volume 0 (2 * π) := hGi.const_mul _
  have hFm : AEStronglyMeasurable F (volume.restrict (Ι 0 (2 * π))) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.pow_const
    exact ((continuous_circleMap 0 1).comp (continuous_id.add_const η)).sub
      continuous_const |>.norm.measurable
  have hle : ∀ θ ∈ Icc 0 (2 * π), θ ≠ π → F θ ≤ G θ := by
    intro θ hθ hne
    have h1 : |θ + η - φ| ≤ π := by
      rw [show θ + η - φ = θ - π by simp [η]; ring, abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    have h2 := abs_sub_arg_div_pi_le b h1
    rw [show θ + η - φ = θ - π by simp [η]; ring] at h2
    have hpos : 0 < |θ - π| / π := div_pos (abs_pos.2 (sub_ne_zero.2 hne)) pi_pos
    have h3 := Real.rpow_le_rpow_of_nonpos hpos h2 (by norm_num : (-(1/2 : ℝ)) ≤ 0)
    refine h3.trans (le_of_eq ?_)
    rw [Real.div_rpow (abs_nonneg _) pi_pos.le, Real.rpow_neg pi_pos.le, div_inv_eq_mul]
    simp only [hG, Real.sqrt_eq_rpow]; ring
  have hae0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Icc 0 (2 * π) → F θ ≤ G θ := by
    filter_upwards [Measure.ae_ne volume π] with θ hθ hmem
    exact hle θ hmem hθ
  have hae : ∀ᵐ θ ∂(volume.restrict (Ι 0 (2 * π))), ‖F θ‖ ≤ ‖G θ‖ := by
    filter_upwards [ae_restrict_of_ae hae0, ae_restrict_mem measurableSet_uIoc] with θ hθ hmem
    rw [uIoc_of_le two_pi_pos.le] at hmem
    have hF0 : 0 ≤ F θ := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_of_nonneg hF0, Real.norm_of_nonneg (by positivity)]
    exact hθ ⟨hmem.1.le, hmem.2⟩
  have hFi : IntervalIntegrable F volume 0 (2 * π) := hGi'.mono_fun hFm hae
  have hper : Function.Periodic (fun θ => ‖circleMap 0 1 θ - b‖ ^ (-(1/2 : ℝ))) (2 * π) :=
    fun θ => by simp only [periodic_circleMap 0 1 θ]
  constructor
  · show IntervalIntegrable (fun θ => ‖circleMap 0 1 θ - b‖ ^ (-(1/2 : ℝ))) volume 0 (2 * π)
    have := hFi.comp_add_right (-η)
    simp only [hF, neg_add_cancel_right, sub_neg_eq_add] at this
    apply hper.intervalIntegrable two_pi_pos.ne' (t := η)
    convert this using 1 <;> ring
  · rw [circleAverage_eq_integral_add η, smul_eq_mul]
    have hmono : ∫ θ in (0)..(2 * π), F θ ≤ ∫ θ in (0)..(2 * π), G θ := by
      apply integral_mono_ae_restrict two_pi_pos.le hFi hGi'
      filter_upwards [ae_restrict_of_ae hae0, ae_restrict_mem measurableSet_Icc] with θ hθ hmem
      exact hθ hmem
    have hGv' : ∫ θ in (0)..(2 * π), G θ = 4 * π := by
      simp only [hG]; rw [intervalIntegral.integral_const_mul, hGv, ← mul_assoc, mul_comm _ 4, mul_assoc,
        Real.mul_self_sqrt pi_pos.le]
    calc (2 * π)⁻¹ * ∫ θ in (0)..(2 * π), F θ ≤ (2 * π)⁻¹ * (4 * π) := by
          rw [← hGv']; gcongr
      _ = 2 := by field_simp; ring

/-- Scaled version: `(1/2π) ∫₀^{2π} |r e^{iθ} - u|^{-1/2} dθ ≤ 2 r^{-1/2}`. -/
lemma circleAverage_norm_sub_rpow_le' (u : ℂ) {r : ℝ} (hr : 0 < r) :
    CircleIntegrable (fun z => ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r ∧
    circleAverage (fun z => ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r ≤ 2 * r ^ (-(1/2 : ℝ)) := by
  obtain ⟨h1, h2⟩ := circleAverage_norm_sub_rpow_le (u / r)
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have key : ∀ z : ℂ, ‖r * z - u‖ ^ (-(1/2 : ℝ)) = r ^ (-(1/2 : ℝ)) * ‖z - u / r‖ ^ (-(1/2 : ℝ)) := by
    intro z
    rw [show (r : ℂ) * z - u = r * (z - u / r) by field_simp, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, Real.mul_rpow hr.le (norm_nonneg _)]
  constructor
  · have := h1.const_mul (r ^ (-(1/2 : ℝ)))
    unfold CircleIntegrable at this ⊢
    refine this.congr (fun θ _ => ?_)
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
    rw [← key]
  · rw [circleAverage_eq_circleAverage_zero_one]
    simp only [add_zero]
    simp_rw [key]
    have hs := circleAverage_fun_smul (a := r ^ (-(1/2 : ℝ)))
      (f := fun z => ‖z - u / r‖ ^ (-(1/2 : ℝ))) (c := 0) (R := 1)
    simp only [smul_eq_mul] at hs
    rw [hs]
    have : 0 ≤ r ^ (-(1/2 : ℝ)) := Real.rpow_nonneg hr.le _
    nlinarith


/-- Tangent-line inequality for `log⁺`: `log⁺ x ≤ log⁺ λ + |x| / λ` for `λ > 0`. -/
lemma posLog_le_posLog_add_div {x l : ℝ} (hl : 0 < l) : log⁺ x ≤ log⁺ l + |x| / l := by
  rw [← posLog_abs x]
  rcases le_or_gt |x| 1 with h | h
  · rw [(posLog_eq_zero_iff _).2 (by rw [abs_abs]; exact h)]
    have := posLog_nonneg (x := l)
    positivity
  · have hx : 0 < |x| := by linarith
    rw [posLog_eq_log (by rw [abs_abs]; exact h.le)]
    have h1 : log |x| = log l + log (|x| / l) := by
      rw [Real.log_div hx.ne' hl.ne']; ring
    have h2 : log (|x| / l) ≤ |x| / l - 1 := Real.log_le_sub_one_of_pos (div_pos hx hl)
    have h3 : log l ≤ log⁺ l := le_max_right _ _
    linarith

/-- Pointwise estimate behind `proximity_sum_div_sub_le`. -/
lemma posLog_norm_sum_div_sub_le (s : Finset ℂ) (d : ℂ → ℤ) (z : ℂ) {l : ℝ} (hl : 0 < l) :
    log⁺ ‖∑ u ∈ s, (d u : ℂ) / (z - u)‖ ≤
      2 * log⁺ l + 2 / l * ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ)) := by
  set Y := ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun u _ => by positivity
  have hX : ‖∑ u ∈ s, (d u : ℂ) / (z - u)‖ ≤ ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖⁻¹ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_div, div_eq_mul_inv, Complex.norm_intCast]
  have hsq : ∀ u, |(d u : ℝ)| * ‖z - u‖⁻¹ ≤ (|(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) ^ 2 := by
    intro u
    have e : (‖z - u‖ ^ (-(1/2 : ℝ))) ^ 2 = ‖z - u‖⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
      exact Real.rpow_neg_one _
    rw [mul_pow, e, sq_abs]
    have : |(d u : ℝ)| ≤ (d u : ℝ) ^ 2 := by
      rcases eq_or_ne (d u) 0 with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ |(d u : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
        nlinarith [sq_abs (d u : ℝ)]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hXY : ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖⁻¹ ≤ Y ^ 2 :=
    (Finset.sum_le_sum fun u _ => hsq u).trans
      (Finset.sum_sq_le_sq_sum_of_nonneg fun u _ => by positivity)
  calc log⁺ ‖∑ u ∈ s, (d u : ℂ) / (z - u)‖ ≤ log⁺ (Y ^ 2) :=
        posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) (hX.trans hXY)
    _ = 2 * log⁺ Y := by rw [posLog_pow]; norm_num
    _ ≤ 2 * (log⁺ l + |Y| / l) := by gcongr; exact posLog_le_posLog_add_div hl
    _ = 2 * log⁺ l + 2 / l * Y := by rw [abs_of_nonneg hY0]; ring

/-- **Proximity of a sum of simple fractions.**  For `r ≥ 1`,
`m(r, ∑ d u / (z - u)) ≤ 2 log (2n + 1) + 2`, with `n = ∑ |d u|`. -/
theorem proximity_sum_div_sub_le (s : Finset ℂ) (d : ℂ → ℤ) {r : ℝ} (hr : 1 ≤ r) :
    circleAverage (fun z => log⁺ ‖∑ u ∈ s, (d u : ℂ) / (z - u)‖) 0 r ≤
      2 * log (2 * ∑ u ∈ s, |(d u : ℝ)| + 1) + 2 := by
  have hr0 : 0 < r := by linarith
  set n := ∑ u ∈ s, |(d u : ℝ)|
  have hn : 0 ≤ n := Finset.sum_nonneg fun u _ => abs_nonneg _
  set l := 2 * n + 1
  have hl : 0 < l := by positivity
  have hint : ∀ u, CircleIntegrable (fun z => ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r :=
    fun u => (circleAverage_norm_sub_rpow_le' u hr0).1
  have hYi : CircleIntegrable (fun z => ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r := by
    unfold CircleIntegrable at *
    have := IntervalIntegrable.sum s (fun u _ => (hint u).const_mul |(d u : ℝ)|)
    convert this using 1; ext θ; simp [Finset.sum_apply]
  have hRi : CircleIntegrable (fun z => 2 * log⁺ l +
      2 / l * ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r := by
    unfold CircleIntegrable at *
    exact (_root_.intervalIntegrable_const).add (hYi.const_mul _)
  have hLi : CircleIntegrable (fun z => log⁺ ‖∑ u ∈ s, (d u : ℂ) / (z - u)‖) 0 r := by
    apply circleIntegrable_posLog_norm_meromorphicOn
    intro z _
    apply MeromorphicAt.fun_sum
    intro u _
    exact (MeromorphicAt.const _ z).div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  refine (circleAverage_mono hLi hRi fun z _ => posLog_norm_sum_div_sub_le s d z hl).trans ?_
  have hci : CircleIntegrable (fun _ : ℂ => 2 * log⁺ l) 0 r := by
    unfold CircleIntegrable; exact _root_.intervalIntegrable_const
  rw [circleAverage_fun_add hci (by unfold CircleIntegrable at *; exact hYi.const_mul _),
    circleAverage_const]
  have hs := circleAverage_fun_smul (a := 2 / l)
    (f := fun z => ∑ u ∈ s, |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) (c := 0) (R := r)
  simp only [smul_eq_mul] at hs
  rw [hs, circleAverage_fun_sum (fun u _ => by
    unfold CircleIntegrable at *; exact (hint u).const_mul |(d u : ℝ)|)]
  have hb : ∀ u ∈ s, circleAverage (fun z => |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r ≤
      |(d u : ℝ)| * 2 := by
    intro u _
    have hs' := circleAverage_fun_smul (a := |(d u : ℝ)|)
      (f := fun z => ‖z - u‖ ^ (-(1/2 : ℝ))) (c := 0) (R := r)
    simp only [smul_eq_mul] at hs'
    rw [hs']
    have h1 := (circleAverage_norm_sub_rpow_le' u hr0).2
    have h2 : r ^ (-(1/2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
    gcongr
    linarith
  have hsum : ∑ u ∈ s, circleAverage (fun z => |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r ≤
      n * 2 := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum hb
  have hlog : log⁺ l = log l := posLog_eq_log (by rw [abs_of_pos hl]; linarith)
  rw [hlog]
  have h3 : 2 / l * ∑ u ∈ s, circleAverage (fun z => |(d u : ℝ)| * ‖z - u‖ ^ (-(1/2 : ℝ))) 0 r
      ≤ 2 / l * (n * 2) := by gcongr
  have h4 : 2 / l * (n * 2) ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hl]; linarith
  linarith

end ThreeIM
