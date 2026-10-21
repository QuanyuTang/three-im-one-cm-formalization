module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The expanding rectangles in the original amplitude transport lemma -/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

/-- The rectangle `-R ≤ Re z ≤ 2 log(1/ε) + R`, `|Im z| ≤ R` of Lemma 7.14. -/
def transportRect (ε R : ℝ) : Set ℂ :=
  {z | -R ≤ z.re ∧ z.re ≤ 2 * Real.log (1 / ε) + R ∧ |z.im| ≤ R}

theorem closedBall_subset_transportRect {ε R : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    closedBall (0 : ℂ) R ⊆ transportRect ε R := by
  intro z hz
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hlog : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).mpr (by simpa using hε₁))
  refine ⟨?_, ?_, him.trans hn⟩
  · linarith [(abs_le.mp (hre.trans hn)).1]
  · linarith [(abs_le.mp (hre.trans hn)).2]

theorem eventually_closedBall_subset_transportRect {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) (R : ℝ) :
    ∀ᶠ n in atTop, closedBall (0 : ℂ) R ⊆ transportRect (ε n) R := by
  filter_upwards [hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  exact closedBall_subset_transportRect (hεpos n) hn.le

theorem eventually_closedBall_subset_transport_domains {ε : ℕ → ℝ} {Ω : ℕ → Set ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ n in atTop, closedBall (0 : ℂ) R ⊆ Ω n := by
  filter_upwards [eventually_closedBall_subset_transportRect hεpos hε R, hrect R hR]
    with n hn hm
  exact hn.trans hm

end ThreeIM
