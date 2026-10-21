module

public import RequestProject.ThreeIM.ClusterWronskian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial cluster count from the divisor-factor budgets

The analytic cluster engine is uniform in q. This module specializes its
parameters to the exponential bounds supplied by the planned divisor probe
estimates on an original disk of radius eta=exp(-4B). No disk merging or
boundary winding number is used. The factor estimates are still explicit
local inputs; they have not yet been derived from the characteristic budget.
-/

@[expose] public section

open Set Metric

namespace ThreeIM

private theorem cluster_count_coefficient_log_le {B : ℝ} (hB : 4 ≤ B) :
    Real.log (max 1 ((4 * Real.exp (3 * B ^ 2) /
      (Real.exp (-4 * B) * Real.exp (-77 * B ^ 2))) * Real.exp (4 * B ^ 2) +
      (1 + (4 * Real.exp (3 * B ^ 2) /
        (Real.exp (-4 * B) * Real.exp (-77 * B ^ 2))) * Real.exp (4 * B ^ 2)) *
        Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2))) ≤ 125 * B ^ 2 := by
  let t : ℝ := (4 * Real.exp (3 * B ^ 2) /
    (Real.exp (-4 * B) * Real.exp (-77 * B ^ 2))) * Real.exp (4 * B ^ 2)
  change Real.log (max 1 (t + (1 + t) * Real.exp (3 * B ^ 2) /
    Real.exp (-24 * B ^ 2))) ≤ 125 * B ^ 2
  have hB2 : 16 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 4)]
  have hBX : B ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 4)]
  have h4 : (4 : ℝ) ≤ Real.exp (2 * B ^ 2) :=
    (by nlinarith : (4 : ℝ) ≤ 2 * B ^ 2 + 1).trans (Real.add_one_le_exp _)
  have h2 : (2 : ℝ) ≤ Real.exp (B ^ 2) :=
    (by linarith : (2 : ℝ) ≤ B ^ 2 + 1).trans (Real.add_one_le_exp _)
  have ht : t = 4 * Real.exp (84 * B ^ 2 + 4 * B) := by
    have he : Real.exp ((3 * B ^ 2 + 4 * B ^ 2) - ((-4 * B) + (-77 * B ^ 2))) =
        Real.exp (3 * B ^ 2) * Real.exp (4 * B ^ 2) /
          (Real.exp (-4 * B) * Real.exp (-77 * B ^ 2)) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add]
    calc
      t = 4 * (Real.exp (3 * B ^ 2) * Real.exp (4 * B ^ 2) /
          (Real.exp (-4 * B) * Real.exp (-77 * B ^ 2))) := by dsimp [t]; ring
      _ = 4 * Real.exp ((3 * B ^ 2 + 4 * B ^ 2) - ((-4 * B) + (-77 * B ^ 2))) :=
        congrArg (fun x : ℝ => 4 * x) he.symm
      _ = 4 * Real.exp (84 * B ^ 2 + 4 * B) := by congr 2; ring
  have ht90 : t ≤ Real.exp (90 * B ^ 2) := by
    calc
      t = 4 * Real.exp (84 * B ^ 2 + 4 * B) := ht
      _ ≤ Real.exp (2 * B ^ 2) * Real.exp (84 * B ^ 2 + 4 * B) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (86 * B ^ 2 + 4 * B) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (90 * B ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hOne90 : (1 : ℝ) ≤ Real.exp (90 * B ^ 2) := by
    exact (by nlinarith : (1 : ℝ) ≤ 90 * B ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hplus : 1 + t ≤ Real.exp (91 * B ^ 2) := by
    calc
      1 + t ≤ Real.exp (90 * B ^ 2) + Real.exp (90 * B ^ 2) := add_le_add hOne90 ht90
      _ = 2 * Real.exp (90 * B ^ 2) := by ring
      _ ≤ Real.exp (B ^ 2) * Real.exp (90 * B ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (91 * B ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  have hsecond : (1 + t) * Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2) ≤
      Real.exp (118 * B ^ 2) := by
    calc
      (1 + t) * Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2) ≤
          Real.exp (91 * B ^ 2) * Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hplus (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = Real.exp ((91 * B ^ 2 + 3 * B ^ 2) - (-24 * B ^ 2)) := by
        rw [Real.exp_sub, Real.exp_add]
      _ = Real.exp (118 * B ^ 2) := by congr 1; ring
  have ht118 : t ≤ Real.exp (118 * B ^ 2) :=
    ht90.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg B]))
  have hcoeff : t + (1 + t) * Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2) ≤
      Real.exp (119 * B ^ 2) := by
    calc
      _ ≤ Real.exp (118 * B ^ 2) + Real.exp (118 * B ^ 2) := add_le_add ht118 hsecond
      _ = 2 * Real.exp (118 * B ^ 2) := by ring
      _ ≤ Real.exp (B ^ 2) * Real.exp (118 * B ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (119 * B ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  have hOne119 : (1 : ℝ) ≤ Real.exp (119 * B ^ 2) :=
    (by nlinarith [sq_nonneg B] : (1 : ℝ) ≤ 119 * B ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1
    (t + (1 + t) * Real.exp (3 * B ^ 2) / Real.exp (-24 * B ^ 2))))
    (max_le hOne119 hcoeff)
  rw [Real.log_exp] at hl
  nlinarith [sq_nonneg B]

/-- On an original eta-disk, the explicit factor/probe budgets yield at most
`250 B^2` distinct points in any cleared fiber. The bound is independent of q. -/
theorem cleared_fiber_eta_disk_card_le (s : Finset ℂ) {N Q : ℂ → ℂ}
    {q c v : ℂ} {B E : ℝ} (hB : 4 ≤ B) (hE : 0 < E)
    (hv : v ∈ closedBall c (Real.exp (-4 * B) / 2))
    (hN : AnalyticOnNhd ℂ N (closedBall c (5 * Real.exp (-4 * B))))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c (5 * Real.exp (-4 * B))))
    (hNP : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖N w‖ ≤ E * Real.exp (4 * B ^ 2))
    (hQD : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖Q w‖ ≤ Real.exp (3 * B ^ 2))
    (hQa : Real.exp (-24 * B ^ 2) ≤ ‖Q v‖)
    (hW : E * Real.exp (-77 * B ^ 2) ≤ ‖deriv N v * Q v - N v * deriv Q v‖)
    (hzeros : ∀ z ∈ s, z ∈ closedBall c (Real.exp (-4 * B)) ∧ N z = q * Q z) :
    (s.card : ℝ) ≤ 250 * B ^ 2 := by
  have hcount := cleared_fiber_card_mul_log_two_le s (Real.exp_pos _) hE
    (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _).le (Real.exp_pos _).le
    hv hN hQ hNP hQD hQa hW hzeros
  have hbound := hcount.trans (cluster_count_coefficient_log_le hB)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hhalf := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ s.card from Nat.cast_nonneg _)
  nlinarith

end ThreeIM
