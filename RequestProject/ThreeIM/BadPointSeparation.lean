module

public import RequestProject.ThreeIM.BranchLocalLog
public import RequestProject.ThreeIM.InverseBranch
public import RequestProject.ThreeIM.BranchPacking
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Separation of bad points on regular disks

This is the analytic separation step in step 3 of the manuscript's finite-disk
inverse-branch lemma. The hypotheses concern actual zero-free holomorphic
representatives on a disk free of divisors. A bad point has small logarithmic
derivative at its center. Its small disk contains at most one point of each
fiber, which allows area packing. Divisor clusters and the global selection
argument are separate steps.
-/

@[expose] public section

open Set Metric

namespace ThreeIM

/-- Source hypotheses at one bad point, after removal of the divisor clusters.
The radius `d / B^4` is the regular disk and `d / (100 B^11)` is the smaller
separation disk. These are local hypotheses, not branch-existence data. -/
structure RegularBadPoint (Φ A : ℂ → ℂ) (z : ℂ) (B d : ℝ) : Prop where
  distance_pos : 0 < d
  phi_holo : DifferentiableOn ℂ Φ (ball z (d / B ^ 4))
  phi_ne_zero : ∀ w ∈ ball z (d / B ^ 4), Φ w ≠ 0
  a_holo : DifferentiableOn ℂ A (ball z (d / B ^ 4))
  a_ne_zero : ∀ w ∈ ball z (d / B ^ 4), A w ≠ 0
  log_deriv_phi : ∀ w ∈ ball z (d / B ^ 4), deriv Φ w / Φ w = A w
  log_deriv_bound : ∀ w ∈ ball z (d / B ^ 4), ‖deriv A w / A w‖ ≤ 8 * B / d
  bad : ‖A z‖ ≤ B ^ 10 / d

/-- At a bad point the map is injective on the small separation disk.
The logarithm is first shown univalent on the larger regular disk; its small
oscillation on the separation disk then excludes the periods of the exponential. -/
theorem RegularBadPoint.injOn_small_ball {Φ A : ℂ → ℂ} {z : ℂ} {B d : ℝ}
    (h : RegularBadPoint Φ A z B d) (hB : 4 ≤ B) :
    InjOn Φ (ball z (d / (100 * B ^ 11))) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBone : 1 ≤ B := le_trans (by norm_num) hB
  have hd := h.distance_pos
  have hρ : 0 < d / B ^ 4 := div_pos hd (pow_pos hBpos _)
  have hz : z ∈ ball z (d / B ^ 4) := mem_ball_self hρ
  have hAz : A z ≠ 0 := h.a_ne_zero z hz
  have hsmallDen : 0 < 100 * B ^ 11 := mul_pos (by norm_num) (pow_pos hBpos _)
  have hrad : d / (100 * B ^ 11) ≤ d / B ^ 4 := by
    apply (div_le_div_iff₀ hsmallDen (pow_pos hBpos 4)).2
    have hpow : (1 : ℝ) ≤ B ^ 7 := one_le_pow₀ hBone
    have hp : B ^ 4 ≤ 100 * B ^ 11 := by
      calc
        B ^ 4 ≤ B ^ 4 * (100 * B ^ 7) := by
          apply le_mul_of_one_le_right (pow_nonneg hBpos.le _)
          linarith
        _ = 100 * B ^ 11 := by ring
    exact mul_le_mul_of_nonneg_left hp hd.le
  have hsub : ball z (d / (100 * B ^ 11)) ⊆ ball z (d / B ^ 4) :=
    ball_subset_ball hrad
  obtain ⟨LA, hLA, hLAz, hLAdata⟩ :=
    normalized_log_on_good_disk hBpos hd h.a_holo h.a_ne_zero h.log_deriv_bound
  obtain ⟨W, hW, hWz, hWdata⟩ :=
    exists_normalized_log_on_ball_with_deriv hρ h.phi_holo h.phi_ne_zero
  have hWd : ∀ w ∈ ball z (d / B ^ 4), deriv W w = A w := by
    intro w hw
    exact (hWdata w hw).2.trans (h.log_deriv_phi w hw)
  have hclose : ∀ w ∈ ball z (d / B ^ 4), ‖deriv W w - A z‖ ≤ ‖A z‖ / 4 := by
    intro w hw
    apply deriv_close_of_exp_log ((hLAdata w hw).2.2.trans
      (eight_inv_cube_le_one_eighth hB))
    rw [hWd w hw]
    simpa only [mul_comm] using ((eq_div_iff hAz).mp (hLAdata w hw).1).symm
  have hinj := (quantitative_inverse_disk hρ hAz hW hclose).1
  have hderiv : ∀ w ∈ ball z (d / B ^ 4), ‖deriv W w‖ ≤ 2 * ‖A z‖ := by
    intro w hw
    calc
      ‖deriv W w‖ = ‖(deriv W w - A z) + A z‖ := by rw [sub_add_cancel]
      _ ≤ ‖deriv W w - A z‖ + ‖A z‖ := norm_add_le _ _
      _ ≤ ‖A z‖ / 4 + ‖A z‖ := add_le_add (hclose w hw) le_rfl
      _ ≤ 2 * ‖A z‖ := by nlinarith [norm_nonneg (A z)]
  have hnorm : ∀ w ∈ ball z (d / (100 * B ^ 11)), ‖W w‖ ≤ 1 := by
    intro w hw
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => hW.differentiableAt (isOpen_ball.mem_nhds hu))
      hderiv (convex_ball z (d / B ^ 4)) hz (hsub hw)
    have hdist : ‖w - z‖ ≤ d / (100 * B ^ 11) := by
      simpa only [dist_eq_norm] using (mem_ball.mp hw).le
    calc
      ‖W w‖ ≤ 2 * ‖A z‖ * ‖w - z‖ := by simpa only [hWz, sub_zero] using hmv
      _ ≤ 2 * (B ^ 10 / d) * (d / (100 * B ^ 11)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h.bad (by norm_num)) hdist
          (norm_nonneg _) (by positivity)
      _ = 1 / (50 * B) := by
        field_simp [ne_of_gt hBpos, ne_of_gt hd]
        norm_num
      _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hstrip : ∀ w ∈ ball z (d / (100 * B ^ 11)),
      -Real.pi < (W w).im ∧ (W w).im ≤ Real.pi := by
    intro w hw
    have him := (Complex.abs_im_le_norm (W w)).trans (hnorm w hw)
    have hab := abs_le.mp him
    constructor <;> linarith [Real.pi_gt_three]
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi (hstrip x hx).1 (hstrip x hx).2
    (hstrip y hy).1 (hstrip y hy).2
  rw [(hWdata x (hsub hx)).1, (hWdata y (hsub hy)).1, hxy]

end ThreeIM
