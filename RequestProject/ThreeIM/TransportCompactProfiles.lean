module

public import RequestProject.ThreeIM.TransportDomains
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-compact limits of the original rectangle profiles

Relative errors on the transport rectangles give locally uniform limits on
the plane. Multiplication recovers the vanishing coefficients, while their
quotient has a separate nonzero exponential limit. These conclusions do not
assume a rate of convergence or a zero-free limit for either coefficient.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

private theorem transport_constant_family_tlu (D : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => D) D atTop univ := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  exact Eventually.of_forall fun n w _ => by simpa only [dist_self] using hη

theorem transport_profile_tendsto_one {ε : ℕ → ℝ} {P : ℕ → ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖P n z - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn P (fun _ => 1) atTop univ := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro η hη z _
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hzB : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨ball 0 R, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzB), ?_⟩
  filter_upwards [eventually_closedBall_subset_transportRect hεpos hε R,
    hprof R hR (η / 2) (half_pos hη)] with n hn hp w hw
  have hbound := hp w (hn (ball_subset_closedBall hw))
  simpa only [dist_eq_norm, norm_sub_rev] using hbound.trans_lt (half_lt_self hη)

theorem transport_coefficient_tendsto_zero {ε : ℕ → ℝ} {uₙ : ℕ → ℂ → ℂ}
    {D : ℂ → ℂ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hD : Continuous D) (hD0 : ∀ z, D z ≠ 0)
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖uₙ n z / ((ε n : ℂ) * D z) - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn uₙ (fun _ => 0) atTop univ := by
  have hrel := transport_profile_tendsto_one hεpos hε hprof
  have hεc : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hε
  have hden : TendstoLocallyUniformlyOn (fun n z => (ε n : ℂ) * D z)
      (fun _ => 0) atTop univ := by
    have hmul := (hεc.tendstoUniformlyOn_const (univ : Set ℂ)).tendstoLocallyUniformlyOn.mul₀
      (transport_constant_family_tlu D) continuousOn_const hD.continuousOn
    exact hmul.congr_right (fun z _ => zero_mul (D z))
  have hprod := (hrel.mul₀ hden continuousOn_const continuousOn_const).congr_right
    (fun _ _ => one_mul (0 : ℂ))
  apply hprod.congr
  intro n z _
  exact div_mul_cancel₀ _ (mul_ne_zero (by exact_mod_cast (hεpos n).ne') (hD0 z))

private theorem transport_relative_quotient_identity (u v c d e : ℂ)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    ((u / (c * d)) / (v / (c * e))) * (d / e) = u / v := by
  by_cases hv : v = 0
  · simp only [hv, zero_div, div_zero, zero_mul]
  · field_simp [hc, hd, he, hv]

theorem transport_quotient_tendsto_profile_ratio {ε : ℕ → ℝ} {uₙ vₙ : ℕ → ℂ → ℂ}
    {D E : ℂ → ℂ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hD : Continuous D) (hE : Continuous E) (hD0 : ∀ z, D z ≠ 0) (hE0 : ∀ z, E z ≠ 0)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖uₙ n z / ((ε n : ℂ) * D z) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖vₙ n z / ((ε n : ℂ) * E z) - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn (fun n z => uₙ n z / vₙ n z)
      (fun z => D z / E z) atTop univ := by
  have hu := transport_profile_tendsto_one hεpos hε hprofU
  have hv := transport_profile_tendsto_one hεpos hε hprofV
  have hratio : TendstoLocallyUniformlyOn
      (fun n z => (uₙ n z / ((ε n : ℂ) * D z)) / (vₙ n z / ((ε n : ℂ) * E z)))
      (fun _ => 1) atTop univ :=
    (hu.div₀ hv continuousOn_const continuousOn_const (by simp)).congr_right
      (fun _ _ => div_self (one_ne_zero : (1 : ℂ) ≠ 0))
  have hDE : Continuous (fun z => D z / E z) := hD.div hE hE0
  have hmul := (hratio.mul₀ (transport_constant_family_tlu (fun z => D z / E z))
    continuousOn_const hDE.continuousOn).congr_right (fun z _ => one_mul (D z / E z))
  apply hmul.congr
  intro n z _
  exact transport_relative_quotient_identity _ _ _ _ _
    (by exact_mod_cast (hεpos n).ne') (hD0 z) (hE0 z)

theorem transport_profile_eventually_nonzero {ε : ℕ → ℝ} {uₙ : ℕ → ℂ → ℂ} {D : ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖uₙ n z / ((ε n : ℂ) * D z) - 1‖ ≤ η)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) R, uₙ n z ≠ 0 := by
  filter_upwards [eventually_closedBall_subset_transportRect hεpos hε R,
    hprof R hR ((1 : ℝ) / 2) (by norm_num)] with n hn hp z hz hzero
  have hb := hp z (hn (ball_subset_closedBall hz))
  simp only [hzero, zero_div, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

theorem transport_exponential_profile_ratio (A B z : ℂ) :
    (A * Complex.exp (z / 2)) / (B * Complex.exp (-z / 2)) =
      (A / B) * Complex.exp z := by
  rw [mul_div_mul_comm, ← Complex.exp_sub]
  congr 2
  ring

end ThreeIM
