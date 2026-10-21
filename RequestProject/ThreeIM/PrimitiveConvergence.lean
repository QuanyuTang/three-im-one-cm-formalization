module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Normalized entire primitives and convergence from their derivatives -/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem exists_normalized_entire_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, deriv g z = f z := by
  let g : ℂ → ℂ := fun z => Complex.wedgeIntegral 0 z f
  have hg (z : ℂ) : HasDerivAt g (f z) z := by
    let R : ℝ := ‖z‖ + 1
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp only [R]
      linarith
    exact (hf.differentiableOn (s := ball (0 : ℂ) R)).isConservativeOn.hasDerivAt_wedgeIntegral
      hf.continuous.continuousOn hz
  exact ⟨g, fun z => (hg z).differentiableAt, by simp [g, Complex.wedgeIntegral],
    fun z => (hg z).deriv⟩

theorem primitive_tendstoUniformlyOn_closedBall {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball 0 (R + 1)))
    (hder : TendstoUniformlyOn (fun n => deriv (F n)) (deriv f) atTop (closedBall 0 R))
    (hzero : Tendsto (fun n => F n 0) atTop (𝓝 (f 0))) :
    TendstoUniformlyOn F f atTop (closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  let η : ℝ := δ / (2 * (R + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηid : η * (2 * (R + 1)) = δ := div_mul_cancel₀ _ (by positivity)
  have hηR : η * R < δ / 2 := by nlinarith
  have hd := Metric.tendstoUniformlyOn_iff.mp hder η hη
  have h0 := hzero.eventually (ball_mem_nhds (f 0) (half_pos hδ))
  filter_upwards [hF, hd, h0] with n hn hnd hn0 w hw
  have hdiff (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) R) :
      DifferentiableAt ℂ (F n) x := by
    have hx' : x ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball_zero_iff]
      have := mem_closedBall_zero_iff.mp hx
      linarith
    exact hn.differentiableAt (isOpen_ball.mem_nhds hx')
  have hbound (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) R) :
      ‖deriv (fun y => F n y - f y) x‖ ≤ η := by
    rw [deriv_fun_sub (hdiff x hx) (hf x)]
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hnd x hx)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hdiff x hx).sub (hf x)) hbound (convex_closedBall (0 : ℂ) R)
    (mem_closedBall_self hR.le) hw
  have hnorm : ‖w - (0 : ℂ)‖ ≤ R := by simpa only [sub_zero] using mem_closedBall_zero_iff.mp hw
  have hm' : ‖(F n w - f w) - (F n 0 - f 0)‖ ≤ η * R :=
    hm.trans (mul_le_mul_of_nonneg_left hnorm hη.le)
  have h0' : ‖F n 0 - f 0‖ < δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hn0
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖F n w - f w‖ = ‖((F n w - f w) - (F n 0 - f 0)) + (F n 0 - f 0)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(F n w - f w) - (F n 0 - f 0)‖ + ‖F n 0 - f 0‖ := norm_add_le _ _
    _ < δ := by linarith

theorem primitive_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hF : ∀ R > 0, ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball 0 R))
    (hder : TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv f) atTop univ)
    (hzero : Tendsto (fun n => F n 0) atTop (𝓝 (f 0))) :
    TendstoLocallyUniformlyOn F f atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R₀, hKbound⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right R₀ 1)
  have hKR : K ⊆ closedBall (0 : ℂ) R :=
    hKbound.trans ((ball_subset_ball (le_max_left R₀ 1)).trans ball_subset_closedBall)
  have hd := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hder
    (closedBall (0 : ℂ) R) (subset_univ _) (isCompact_closedBall _ _)
  exact (primitive_tendstoUniformlyOn_closedBall hf hR (hF (R + 1) (by positivity)) hd hzero).mono hKR

end ThreeIM
