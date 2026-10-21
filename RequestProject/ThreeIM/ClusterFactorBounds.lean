module

public import RequestProject.ThreeIM.ClusterProbe
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Divisor-factor estimates for the original eta-disks

The separated probe gives a uniform exponential lower bound for each linear
factor. Natural and integer weighted products then have bounds depending only
on total divisor multiplicity, with no divisor-separation assumption.
-/

@[expose] public section

open Set Metric
open scoped BigOperators

namespace ThreeIM

/-- The finite probe distance on an eta-disk is at least exp(-24B). -/
theorem eta_probe_distance_ge_exp {B : ℝ} {n : ℕ} (hB : 4 ≤ B) (hn : (n : ℝ) ≤ B) :
    Real.exp (-24 * B) ≤ Real.exp (-4 * B) / (10 * ((n : ℝ) + 1)) := by
  have hden : 0 < 10 * ((n : ℝ) + 1) := by positivity
  have hexp : 10 * ((n : ℝ) + 1) ≤ Real.exp (20 * B) := by
    exact (by linarith : 10 * ((n : ℝ) + 1) ≤ 20 * B + 1).trans (Real.add_one_le_exp _)
  calc
    Real.exp (-24 * B) = Real.exp (-4 * B) / Real.exp (20 * B) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ Real.exp (-4 * B) / (10 * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hden hexp

/-- All linear factors on the enlarged disk have the upper bound used by
the polynomial numerator and denominator estimates. -/
theorem norm_sub_le_exp_on_eta_disk (centers : Finset ℂ) {c : ℂ} {B : ℝ}
    (hB : 4 ≤ B) (hc : ‖c‖ + 5 * Real.exp (-4 * B) ≤ B)
    (hcenters : ∀ α ∈ centers, ‖α‖ ≤ B) :
    ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ∀ α ∈ centers,
      ‖w - α‖ ≤ Real.exp (3 * B) := by
  intro w hw α hα
  have hwc : ‖w - c‖ ≤ 5 * Real.exp (-4 * B) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hwB : ‖w‖ ≤ B := by
    have ht : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - c) c
    linarith
  calc
    ‖w - α‖ ≤ ‖w‖ + ‖α‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith [hcenters α hα]
    _ ≤ Real.exp (3 * B) := (by linarith : 2 * B ≤ 3 * B + 1).trans (Real.add_one_le_exp _)

/-- The actual eta-probe simultaneously has the lower and upper linear-factor
bounds needed for the cleared-numerator count. Empty divisor sets are allowed. -/
theorem exists_eta_probe_with_factor_bounds (centers : Finset ℂ) {c : ℂ} {B : ℝ}
    (hB : 4 ≤ B) (hcard : (centers.card : ℝ) ≤ B)
    (hc : ‖c‖ + 5 * Real.exp (-4 * B) ≤ B)
    (hcenters : ∀ α ∈ centers, ‖α‖ ≤ B) :
    ∃ v ∈ closedBall c (Real.exp (-4 * B) / 2), ∀ α ∈ centers,
      Real.exp (-24 * B) ≤ ‖v - α‖ ∧ ‖v - α‖ ≤ Real.exp (3 * B) := by
  obtain ⟨v, hv, hsep⟩ := exists_regular_cluster_probe centers c (Real.exp_pos (-4 * B))
  refine ⟨v, hv, fun α hα => ⟨?_, ?_⟩⟩
  · have hd := (eta_probe_distance_ge_exp hB hcard).trans (hsep α hα)
    simpa only [dist_eq_norm] using hd
  · exact norm_sub_le_exp_on_eta_disk centers hB hc hcenters v
      (closedBall_subset_closedBall (by have := Real.exp_pos (-4 * B); linarith) hv) α hα

/-- The holomorphic factor varies by at most one on the enlarged original
eta-disk, despite the source's exponential derivative bound. -/
theorem norm_sub_le_one_on_eta_disk {H : ℂ → ℂ} {c : ℂ} {B : ℝ}
    (hB : 4 ≤ B) (hH : AnalyticOnNhd ℂ H (closedBall c (5 * Real.exp (-4 * B))))
    (hderiv : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖deriv H w‖ ≤ Real.exp B) :
    ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖H w - H c‖ ≤ 1 := by
  intro w hw
  have hc : c ∈ closedBall c (5 * Real.exp (-4 * B)) := mem_closedBall_self (by positivity)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hH z hz).differentiableAt) hderiv
    (convex_closedBall c (5 * Real.exp (-4 * B))) hc hw
  have hdist : ‖w - c‖ ≤ 5 * Real.exp (-4 * B) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have h5 : (5 : ℝ) ≤ Real.exp (3 * B) :=
    (by linarith : (5 : ℝ) ≤ 3 * B + 1).trans (Real.add_one_le_exp _)
  calc
    ‖H w - H c‖ ≤ Real.exp B * ‖w - c‖ := hmv
    _ ≤ Real.exp B * (5 * Real.exp (-4 * B)) :=
      mul_le_mul_of_nonneg_left hdist (Real.exp_pos _).le
    _ = 5 * Real.exp (-3 * B) := by
      calc
        _ = 5 * (Real.exp B * Real.exp (-4 * B)) := by ring
        _ = 5 * Real.exp (B + (-4 * B)) := by rw [Real.exp_add]
        _ = _ := by congr 2; ring
    _ ≤ 1 := by
      rw [show -3 * B = -(3 * B) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact (div_le_one (Real.exp_pos _)).2 h5

/-- An original eta-disk meeting the inner radius can be enlarged by five
without leaving the source's H'-control region. This replaces the source's
disk-merging domain estimate in the Jensen route. -/
theorem eta_disk_enlargement_subset {c : ℂ} {B r Δ : ℝ} (hB : 4 ≤ B)
    (hΔ : B⁻¹ ≤ Δ) (hc : ‖c‖ ≤ r + Real.exp (-4 * B)) :
    closedBall c (5 * Real.exp (-4 * B)) ⊆ ball 0 (r + Δ / 4) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have ht := Real.pow_div_factorial_le_exp (4 * B) (by positivity : 0 ≤ 4 * B) 2
  norm_num at ht
  have hlarge : 24 * B < Real.exp (4 * B) := by
    nlinarith [sq_nonneg (B - 4)]
  have hη : Real.exp (-4 * B) < 1 / (24 * B) := by
    rw [show -4 * B = -(4 * B) by ring, Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by positivity) hlarge
  have hsmall : 6 * Real.exp (-4 * B) < Δ / 4 := by
    have hi : 6 * (1 / (24 * B)) = B⁻¹ / 4 := by ring
    have hm := mul_lt_mul_of_pos_left hη (by norm_num : (0 : ℝ) < 6)
    rw [hi] at hm
    linarith
  intro w hw
  have hdist : ‖w - c‖ ≤ 5 * Real.exp (-4 * B) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hnorm : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (w - c) c
  rw [mem_ball, dist_zero_right]
  linarith

/-- Natural-power products inherit an exponential upper bound from their
total degree. -/
theorem norm_prod_pow_le_exp (s : Finset ℂ) {f : ℂ → ℂ} {m : ℂ → ℕ} {C M : ℝ}
    (hC : 0 ≤ C) (hupper : ∀ α ∈ s, ‖f α‖ ≤ Real.exp C)
    (hdegree : (∑ α ∈ s, (m α : ℝ)) ≤ M) :
    ‖∏ α ∈ s, f α ^ m α‖ ≤ Real.exp (C * M) := by
  rw [Complex.norm_prod]
  calc
    (∏ α ∈ s, ‖f α ^ m α‖) ≤ ∏ α ∈ s, Real.exp (C * (m α : ℝ)) := by
      apply Finset.prod_le_prod₀ (fun α _ => norm_nonneg _)
      intro α hα
      rw [norm_pow]
      calc
        ‖f α‖ ^ m α ≤ (Real.exp C) ^ m α := pow_le_pow_left₀ (norm_nonneg _) (hupper α hα) _
        _ = Real.exp (C * (m α : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ = Real.exp (C * ∑ α ∈ s, (m α : ℝ)) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (C * M) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdegree hC)

/-- Natural-power products inherit an exponential lower bound, even when
some exponents vanish. -/
theorem norm_prod_pow_ge_exp (s : Finset ℂ) {f : ℂ → ℂ} {m : ℂ → ℕ} {C M : ℝ}
    (hC : 0 ≤ C) (hlower : ∀ α ∈ s, Real.exp (-C) ≤ ‖f α‖)
    (hdegree : (∑ α ∈ s, (m α : ℝ)) ≤ M) :
    Real.exp (-C * M) ≤ ‖∏ α ∈ s, f α ^ m α‖ := by
  rw [Complex.norm_prod]
  calc
    Real.exp (-C * M) ≤ Real.exp (-C * ∑ α ∈ s, (m α : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdegree (by linarith))
    _ = ∏ α ∈ s, Real.exp (-C * (m α : ℝ)) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ α ∈ s, ‖f α ^ m α‖ := by
      apply Finset.prod_le_prod₀ (fun α _ => (Real.exp_pos _).le)
      intro α hα
      rw [norm_pow]
      calc
        Real.exp (-C * (m α : ℝ)) = (Real.exp (-C)) ^ m α := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ ‖f α‖ ^ m α := pow_le_pow_left₀ (Real.exp_pos _).le (hlower α hα) _

private theorem norm_zpow_ge_exp_abs {z : ℂ} {C : ℝ}
    (hlower : Real.exp (-C) ≤ ‖z‖) (hupper : ‖z‖ ≤ Real.exp C) (n : ℤ) :
    Real.exp (-C * |(n : ℝ)|) ≤ ‖z ^ n‖ := by
  cases n with
  | ofNat k =>
    have hp := pow_le_pow_left₀ (Real.exp_pos (-C)).le hlower k
    have he : Real.exp (-C * (k : ℝ)) = (Real.exp (-C)) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simpa only [Int.ofNat_eq_natCast, Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k),
      zpow_natCast, norm_pow] using he.trans_le hp
  | negSucc k =>
    have hz : 0 < ‖z‖ := (Real.exp_pos (-C)).trans_le hlower
    have hi : Real.exp (-C) ≤ ‖z‖⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos C) hz).2 hupper
    have hp := pow_le_pow_left₀ (Real.exp_pos (-C)).le hi (k + 1)
    have he : Real.exp (-C * ((k + 1 : ℕ) : ℝ)) = (Real.exp (-C)) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simpa only [Int.cast_negSucc, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1),
      zpow_negSucc, norm_inv, norm_pow, inv_pow, Nat.cast_add, Nat.cast_one] using he.trans_le hp

/-- A rational divisor product has a lower bound controlled by the sum of
absolute integer multiplicities; both numerator and denominator factors are
handled. -/
theorem norm_prod_zpow_ge_exp (s : Finset ℂ) {f : ℂ → ℂ} {d : ℂ → ℤ} {C M : ℝ}
    (hC : 0 ≤ C)
    (hband : ∀ α ∈ s, Real.exp (-C) ≤ ‖f α‖ ∧ ‖f α‖ ≤ Real.exp C)
    (hdegree : (∑ α ∈ s, |(d α : ℝ)|) ≤ M) :
    Real.exp (-C * M) ≤ ‖∏ α ∈ s, f α ^ d α‖ := by
  rw [Complex.norm_prod]
  calc
    Real.exp (-C * M) ≤ Real.exp (-C * ∑ α ∈ s, |(d α : ℝ)|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdegree (by linarith))
    _ = ∏ α ∈ s, Real.exp (-C * |(d α : ℝ)|) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ α ∈ s, ‖f α ^ d α‖ := by
      exact Finset.prod_le_prod₀ (fun α _ => (Real.exp_pos _).le)
        (fun α hα => norm_zpow_ge_exp_abs (hband α hα).1 (hband α hα).2 (d α))

end ThreeIM
