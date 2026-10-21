module

public import RequestProject.ThreeIM.TransportDomains
public import RequestProject.ThreeIM.TransportScale

/-! # The actual real transport segment lies in the original rectangles -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem eventually_transport_endpoint_after_start {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    ∀ᶠ n in atTop, a ≤ 2 * Real.log (δ / ε n) := by
  have hs : Tendsto (fun n => ε n * Real.exp (a / 2)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε.mul_const (Real.exp (a / 2))
  filter_upwards [hs.eventually (gt_mem_nhds hδ)] with n hn
  exact transportScale_start_le_endpoint (hεpos n) hδ hn.le

theorem transport_real_segment_mem_rect {ε δ a t : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a)
    (ht : t ∈ Icc a (2 * Real.log (δ / ε))) :
    (t : ℂ) ∈ transportRect ε 1 := by
  have hq : δ / ε ≤ 1 / ε := div_le_div_of_nonneg_right hδ1 hε.le
  have hl := Real.log_le_log (div_pos hδ hε) hq
  simp only [transportRect, mem_setOf_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
  exact ⟨by linarith [ht.1], by linarith [ht.2], by norm_num⟩

theorem eventually_transport_segment_in_domains {ε : ℕ → ℝ} {Ω : ℕ → Set ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {δ a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a)
    (hrect : ∀ᶠ n in atTop, transportRect (ε n) 1 ⊆ Ω n) :
    ∀ᶠ n in atTop, a ≤ 2 * Real.log (δ / ε n) ∧
      ∀ t ∈ Icc a (2 * Real.log (δ / ε n)), (t : ℂ) ∈ Ω n := by
  filter_upwards [eventually_transport_endpoint_after_start hεpos hε hδ a, hrect]
    with n hn hΩn
  exact ⟨hn, fun t ht => hΩn (transport_real_segment_mem_rect (hεpos n) hδ hδ1 ha ht)⟩

end ThreeIM
