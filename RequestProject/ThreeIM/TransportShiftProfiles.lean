module

public import RequestProject.ThreeIM.TransportShiftDomains
public import RequestProject.ThreeIM.TransportEndpointBounds
public import RequestProject.ThreeIM.TransportCompactProfiles

/-!
# The original auxiliary profiles at the moving endpoint

Fixed balls about `2 log(s/ε)` remain in the original rectangles. Relative
errors therefore still tend to zero there. Multiplication by the exact
shifted denominators gives a nonzero U limit and the zero V limit.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_shift_profile_U_denominator {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (A z : ℂ) :
    (ε : ℂ) * A * Complex.exp ((((2 * Real.log (s / ε) : ℝ) : ℂ) + z) / 2) =
      (s : ℂ) * A * Complex.exp (z / 2) := by
  have he : (((2 * Real.log (s / ε) : ℝ) : ℂ) + z) / 2 =
      ((2 * Real.log (s / ε) : ℝ) : ℂ) / 2 + z / 2 := by ring
  rw [he, Complex.exp_add]
  have hscale := transportScale_endpoint hε hs
  change (ε : ℂ) * Complex.exp (((2 * Real.log (s / ε) : ℝ) : ℂ) / 2) =
    (s : ℂ) at hscale
  calc
    _ = ((ε : ℂ) * Complex.exp (((2 * Real.log (s / ε) : ℝ) : ℂ) / 2)) *
        A * Complex.exp (z / 2) := by ring
    _ = _ := by rw [hscale]

theorem transport_shift_profile_V_denominator {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (B z : ℂ) :
    (ε : ℂ) * B * Complex.exp (-(((2 * Real.log (s / ε) : ℝ) : ℂ) + z) / 2) =
      ((ε : ℂ) ^ 2 / (s : ℂ)) * (B * Complex.exp (-z / 2)) := by
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hscale := transportScale_endpoint hε hs
  change (ε : ℂ) * Complex.exp (((2 * Real.log (s / ε) : ℝ) : ℂ) / 2) =
    (s : ℂ) at hscale
  have hE : Complex.exp (((2 * Real.log (s / ε) : ℝ) : ℂ) / 2) = (s : ℂ) / ε :=
    (eq_div_iff hεc).mpr (by simpa only [mul_comm] using hscale)
  have he : -(((2 * Real.log (s / ε) : ℝ) : ℂ) + z) / 2 =
      -(((2 * Real.log (s / ε) : ℝ) : ℂ) / 2) + -z / 2 := by ring
  rw [he, Complex.exp_add, Complex.exp_neg, hE]
  field_simp [hεc, hsc]
  <;> ring

theorem transport_shift_profile_tendsto_one {ε : ℕ → ℝ} {P : ℕ → ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s)
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖P n z - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn
      (fun n z => P n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
      (fun _ => 1) atTop univ := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro η hη z _
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR' : 0 < R + |2 * Real.log s| + 1 := by positivity
  have hzB : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨ball 0 R, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzB), ?_⟩
  filter_upwards [eventually_transport_shift_closedBall_subset_rect hεpos hε hs hR,
    hprof _ hR' (η / 2) (half_pos hη)] with n hn hp w hw
  have hb := hp _ (hn w (ball_subset_closedBall hw))
  simpa only [dist_eq_norm, norm_sub_rev] using hb.trans_lt (half_lt_self hη)

private theorem shift_fixed_family_tlu (D : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => D) D atTop univ := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hη

theorem transport_shift_U_tendsto_profile {ε : ℕ → ℝ} {u : ℕ → ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) {A : ℂ} (hA : A ≠ 0)
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn
      (fun n z => u n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
      (fun z => (s : ℂ) * A * Complex.exp (z / 2)) atTop univ := by
  have hrel := transport_shift_profile_tendsto_one hεpos hε hs hprof
  let D : ℂ → ℂ := fun z => (s : ℂ) * A * Complex.exp (z / 2)
  have hD : Continuous D := by fun_prop
  have hD0 : ∀ z, D z ≠ 0 := fun z =>
    mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') hA)
      (Complex.exp_ne_zero _)
  have hprod := (hrel.mul₀ (shift_fixed_family_tlu D)
    continuousOn_const hD.continuousOn).congr_right (fun z _ => one_mul (D z))
  apply hprod.congr
  intro n z _
  change u n _ / ((ε n : ℂ) * A * Complex.exp (_ / 2)) * D z = u n _
  rw [transport_shift_profile_U_denominator (hεpos n) hs]
  exact div_mul_cancel₀ _ (hD0 z)

theorem transport_shift_V_tendsto_zero {ε : ℕ → ℝ} {v : ℕ → ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) {B : ℂ} (hB : B ≠ 0)
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn
      (fun n z => v n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
      (fun _ => 0) atTop univ := by
  have hrel := transport_shift_profile_tendsto_one hεpos hε hs hprof
  have hεc : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hε
  have hsmall : Tendsto (fun n => (ε n : ℂ) ^ 2 / (s : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using
      (hεc.pow 2).div_const (s : ℂ)
  let D : ℂ → ℂ := fun z => B * Complex.exp (-z / 2)
  have hD : Continuous D := by fun_prop
  have hden : TendstoLocallyUniformlyOn
      (fun n z => ((ε n : ℂ) ^ 2 / (s : ℂ)) * D z) (fun _ => 0) atTop univ := by
    have hm := (hsmall.tendstoUniformlyOn_const (univ : Set ℂ)).tendstoLocallyUniformlyOn.mul₀
      (shift_fixed_family_tlu D) continuousOn_const hD.continuousOn
    exact hm.congr_right (fun z _ => zero_mul (D z))
  have hp := (hrel.mul₀ hden continuousOn_const continuousOn_const).congr_right
    (fun _ _ => one_mul (0 : ℂ))
  apply hp.congr
  intro n z _
  change v n _ / ((ε n : ℂ) * B * Complex.exp (-_ / 2)) *
    (((ε n : ℂ) ^ 2 / (s : ℂ)) * (B * Complex.exp (-z / 2))) = v n _
  rw [transport_shift_profile_V_denominator (hεpos n) hs]
  exact div_mul_cancel₀ _ (mul_ne_zero
    (div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hεpos n).ne'))
      (Complex.ofReal_ne_zero.mpr hs.ne')) (mul_ne_zero hB (Complex.exp_ne_zero _)))

end ThreeIM
