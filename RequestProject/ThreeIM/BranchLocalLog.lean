module

public import RequestProject.ThreeIM.LogDerivHolo
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Normalized logarithms on the regular disks used for inverse sheets

The finite-disk branch lemma first bounds the logarithmic derivatives of
`A` and `Psi` on a zero-free holomorphic disk. This module constructs their
normalized logarithms from those actual local hypotheses, and integrates
the derivative bound. Thus the logarithms used in `InverseBranchControl`
need not be supplied as independent data.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- A zero-free holomorphic function has a normalized logarithm whose
derivative is its logarithmic derivative. -/
theorem exists_normalized_log_on_ball_with_deriv {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ w ∈ ball c R, g w ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c R) ∧ L c = 0 ∧
      ∀ w ∈ ball c R, Complex.exp (L w) = g w / g c ∧
        deriv L w = deriv g w / g w := by
  obtain ⟨H, hH, hexp, -⟩ := exists_log_of_ne_zero hg hg0 hR
  let L : ℂ → ℂ := fun w => H w - H c
  have hL : DifferentiableOn ℂ L (ball c R) := hH.sub_const _
  have hLc : L c = 0 := sub_self _
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgc : g c ≠ 0 := hg0 c hc
  have heL : ∀ w ∈ ball c R, Complex.exp (L w) = g w / g c := by
    intro w hw
    change Complex.exp (H w - H c) = g w / g c
    rw [Complex.exp_sub, hexp w hw, hexp c hc]
  have hrep : ∀ w ∈ ball c R, g c * Complex.exp (L w) = g w := by
    intro w hw
    simpa only [mul_comm] using (eq_div_iff hgc).mp (heL w hw)
  have hdL : ∀ w ∈ ball c R, deriv L w = deriv g w / g w := by
    intro w hw
    have hd := (hL.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have hev : g =ᶠ[𝓝 w] (fun u => g c * Complex.exp (L u)) :=
      eventually_of_mem (isOpen_ball.mem_nhds hw) fun u hu => (hrep u hu).symm
    have hprod := hev.deriv_eq.trans ((hd.cexp.const_mul (g c)).deriv)
    rw [← mul_assoc, hrep w hw] at hprod
    apply (eq_div_iff (hg0 w hw)).2
    simpa only [mul_comm] using hprod.symm
  exact ⟨L, hL, hLc, fun w hw => ⟨heL w hw, hdL w hw⟩⟩

/-- A logarithmic-derivative bound gives the normalized logarithm its
distance bound on the whole disk. -/
theorem normalized_log_on_ball_of_logDeriv_bound {g : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ w ∈ ball c R, g w ≠ 0)
    (hbound : ∀ w ∈ ball c R, ‖deriv g w / g w‖ ≤ C) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c R) ∧ L c = 0 ∧
      ∀ w ∈ ball c R, Complex.exp (L w) = g w / g c ∧
        deriv L w = deriv g w / g w ∧ ‖L w‖ ≤ C * ‖w - c‖ := by
  obtain ⟨L, hL, hLc, hdata⟩ := exists_normalized_log_on_ball_with_deriv hR hg hg0
  have hc : c ∈ ball c R := mem_ball_self hR
  have hnorm : ∀ w ∈ ball c R, ‖deriv L w‖ ≤ C := by
    intro w hw
    rw [(hdata w hw).2]
    exact hbound w hw
  refine ⟨L, hL, hLc, fun w hw => ⟨(hdata w hw).1, (hdata w hw).2, ?_⟩⟩
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => hL.differentiableAt (isOpen_ball.mem_nhds hu))
    hnorm (convex_ball c R) hc hw
  simpa only [hLc, sub_zero] using hmv

/-- The regular-disk bounds from the finite-disk branch lemma yield the
normalized logarithm estimate `8 B⁻³`, without a preselected logarithm. -/
theorem normalized_log_on_good_disk {g : ℂ → ℂ} {c : ℂ} {B d : ℝ}
    (hB : 0 < B) (hd : 0 < d)
    (hg : DifferentiableOn ℂ g (ball c (d / B ^ 4)))
    (hg0 : ∀ w ∈ ball c (d / B ^ 4), g w ≠ 0)
    (hbound : ∀ w ∈ ball c (d / B ^ 4), ‖deriv g w / g w‖ ≤ 8 * B / d) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c (d / B ^ 4)) ∧ L c = 0 ∧
      ∀ w ∈ ball c (d / B ^ 4), Complex.exp (L w) = g w / g c ∧
        deriv L w = deriv g w / g w ∧ ‖L w‖ ≤ 8 * B⁻¹ ^ 3 := by
  have hR : 0 < d / B ^ 4 := div_pos hd (pow_pos hB _)
  obtain ⟨L, hL, hLc, hdata⟩ := normalized_log_on_ball_of_logDeriv_bound hR hg hg0 hbound
  have hC : 0 ≤ 8 * B / d := div_nonneg (mul_nonneg (by norm_num) hB.le) hd.le
  refine ⟨L, hL, hLc, fun w hw => ⟨(hdata w hw).1, (hdata w hw).2.1, ?_⟩⟩
  have hdist : ‖w - c‖ ≤ d / B ^ 4 := by
    simpa only [dist_eq_norm] using (mem_ball.mp hw).le
  calc
    ‖L w‖ ≤ (8 * B / d) * ‖w - c‖ := (hdata w hw).2.2
    _ ≤ (8 * B / d) * (d / B ^ 4) := mul_le_mul_of_nonneg_left hdist hC
    _ = 8 * B⁻¹ ^ 3 := by field_simp [ne_of_gt hB, ne_of_gt hd]

/-- The source's large value of B in particular implies the eighth-error
threshold used by the quantitative inverse theorem. -/
theorem eight_inv_cube_le_one_eighth {B : ℝ} (hB : 4 ≤ B) :
    8 * B⁻¹ ^ 3 ≤ 1 / 8 := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hinv : B⁻¹ ≤ (4 : ℝ)⁻¹ := (inv_le_inv₀ hBpos (by norm_num)).2 hB
  calc
    8 * B⁻¹ ^ 3 ≤ 8 * ((4 : ℝ)⁻¹) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hBpos.le) hinv 3)
        (by norm_num)
    _ = 1 / 8 := by norm_num

end ThreeIM
