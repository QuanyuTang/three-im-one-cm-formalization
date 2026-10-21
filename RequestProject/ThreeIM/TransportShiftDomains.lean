module

public import RequestProject.ThreeIM.TransportRealSegment

/-! # Fixed balls about the actual moving transport endpoint -/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_endpoint_log_identity {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    2 * Real.log (s / ε) = 2 * Real.log (1 / ε) + 2 * Real.log s := by
  rw [Real.log_div hs.ne' hε.ne', Real.log_div one_ne_zero hε.ne', Real.log_one]
  ring

theorem eventually_transport_shift_closedBall_subset_rect {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      ((2 * Real.log (s / ε n) : ℝ) : ℂ) + z ∈
        transportRect (ε n) (R + |2 * Real.log s| + 1) := by
  filter_upwards [eventually_transport_endpoint_after_start hεpos hε hs 0] with n hn z hz
  have hnorm : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hnorm)
  have him := (Complex.abs_im_le_norm z).trans hnorm
  simp only [transportRect, mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, zero_add]
  refine ⟨?_, ?_, by linarith [abs_nonneg (2 * Real.log s)]⟩
  · linarith [abs_nonneg (2 * Real.log s)]
  · rw [transport_endpoint_log_identity (hεpos n) hs]
    linarith [le_abs_self (2 * Real.log s)]

theorem eventually_transport_shift_closedBall_in_domains
    {ε : ℕ → ℝ} {Ω : ℕ → Set ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      ((2 * Real.log (s / ε n) : ℝ) : ℂ) + z ∈ Ω n := by
  have hR' : 0 < R + |2 * Real.log s| + 1 := by positivity
  filter_upwards [eventually_transport_shift_closedBall_subset_rect hεpos hε hs hR,
    hrect _ hR'] with n hn hΩn z hz
  exact hΩn (hn z hz)

end ThreeIM
