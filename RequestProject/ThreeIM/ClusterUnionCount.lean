module

public import RequestProject.ThreeIM.ClusterFactorCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting genuine finite fibers in the original divisor-disk union

The eta-disks need not be disjoint or merged. Each disk meeting the inner
disk has its five-times enlargement in the original H'-control domain.
The analytic numerator is obtained from the actual finite meromorphic germ,
so arbitrary values of a totalized representative are never counted as fibers.
The remaining input is the step-1 factorization and its characteristic-budget
estimates; these are not asserted to follow from the original selection input
by this module.
-/

@[expose] public section

open Set Metric Filter
open scoped BigOperators Topology

namespace ThreeIM

/-- The elementary eta bound needed to control the centers of original
divisor disks which meet the inner disk. -/
theorem six_eta_le_one {B : ℝ} (hB : 4 ≤ B) :
    6 * Real.exp (-4 * B) ≤ 1 := by
  have h6 : (6 : ℝ) ≤ Real.exp (4 * B) :=
    (by linarith : (6 : ℝ) ≤ 4 * B + 1).trans (Real.add_one_le_exp _)
  rw [show -4 * B = -(4 * B) by ring, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos _)).2 h6

/-- Step-1 factor data imply a `250 B^3` count for genuine finite fiber
points in the original union of eta-disks. No disk separation, merged cover,
fiber boundary avoidance, or bound on the target value is required. -/
theorem factorized_eta_union_meromorphic_card_le (s σ : Finset ℂ)
    {Φ H h : ℂ → ℂ} {m n : ℂ → ℕ} {d : ℂ → ℤ} {ζ : ℂ} {B r Δ : ℝ}
    (hB : 4 ≤ B) (hcard : (σ.card : ℝ) ≤ B)
    (hrB : r + 1 ≤ B) (hΔ : B⁻¹ ≤ Δ)
    (hroots : ∀ α ∈ σ, ‖α‖ ≤ B)
    (hm : (∑ α ∈ σ, (m α : ℝ)) ≤ B)
    (hn : (∑ α ∈ σ, (n α : ℝ)) ≤ B)
    (hd : (∑ α ∈ σ, |(d α : ℝ)|) ≤ B)
    (hH : AnalyticOnNhd ℂ H (ball 0 (r + Δ / 4)))
    (hHderiv : ∀ w ∈ ball (0 : ℂ) (r + Δ / 4), ‖deriv H w‖ ≤ Real.exp B)
    (hhre : ∀ w ∈ ball (0 : ℂ) (r + Δ / 4), -B / 1000 ≤ (h w).re)
    (hlog : ∀ w ∈ ball (0 : ℂ) (r + Δ / 4), (∀ α ∈ σ, w ≠ α) →
      deriv (fun u => clearedDivisorNumerator σ m H u / divisorPowerProduct σ n u) w /
        (clearedDivisorNumerator σ m H w / divisorPowerProduct σ n w) =
          Complex.exp (h w) * ∏ α ∈ σ, (w - α) ^ d α)
    (hclear : clearedDivisorNumerator σ m H =ᶠ[codiscreteWithin (ball 0 (r + Δ / 4))]
      (fun w => Φ w * divisorPowerProduct σ n w))
    (hs : ∀ z ∈ s, ‖z‖ ≤ r ∧ 0 < meromorphicOrderAt (fun w => Φ w - ζ) z)
    (hcover : ∀ z ∈ s, ∃ c ∈ σ, dist z c ≤ Real.exp (-4 * B)) :
    (s.card : ℝ) ≤ 250 * B ^ 3 := by
  classical
  let η : ℝ := Real.exp (-4 * B)
  let t : ℂ → Finset ℂ := fun c => s.filter (fun z => dist z c ≤ η)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hΔpos : 0 < Δ := (inv_pos.mpr hBpos).trans_le hΔ
  have hQanalytic : ∀ z, AnalyticAt ℂ (divisorPowerProduct σ n) z := by
    intro z
    apply σ.analyticAt_fun_prod
    intro α hα
    exact (analyticAt_id.sub analyticAt_const).pow (n α)
  have hPanalytic : ∀ z, AnalyticAt ℂ (divisorPowerProduct σ m) z := by
    intro z
    apply σ.analyticAt_fun_prod
    intro α hα
    exact (analyticAt_id.sub analyticAt_const).pow (m α)
  have hfiber : ∀ z ∈ s,
      clearedDivisorNumerator σ m H z = ζ * divisorPowerProduct σ n z := by
    intro z hz
    have hzΩ : z ∈ ball (0 : ℂ) (r + Δ / 4) := by
      rw [mem_ball, dist_zero_right]
      linarith [(hs z hz).1]
    have hNanalytic := (hH z hzΩ).cexp'.mul (hPanalytic z)
    have hlim := (tendsto_zero_of_meromorphicOrderAt_pos (hs z hz).2).add_const ζ
    have hlimΦ : Tendsto Φ (𝓝[≠] z) (𝓝 ζ) := by
      simpa only [sub_add_cancel, zero_add] using hlim
    exact cleared_numerator_eq_of_codiscrete_limit isOpen_ball hzΩ
      hNanalytic.continuousAt (hQanalytic z).continuousAt hlimΦ hclear
  have hsub : s ⊆ σ.biUnion t := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hz, hzc⟩⟩
  have hcount : (s.card : ℝ) ≤ ∑ c ∈ σ, ((t c).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    (s.card : ℝ) ≤ ∑ c ∈ σ, ((t c).card : ℝ) := hcount
    _ ≤ ∑ _c ∈ σ, 250 * B ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases ht : (t c).Nonempty
      · obtain ⟨z, hz⟩ := ht
        have hzs := (Finset.mem_filter.mp hz).1
        have hzc := (Finset.mem_filter.mp hz).2
        have hcsmall : ‖c‖ ≤ r + η := by
          have ht : ‖c‖ ≤ ‖c - z‖ + ‖z‖ := by
            simpa only [sub_add_cancel] using norm_add_le (c - z) z
          have hdcz : ‖c - z‖ ≤ η := by simpa only [dist_eq_norm, norm_sub_rev] using hzc
          linarith [(hs z hzs).1]
        have hcbig : ‖c‖ + 5 * Real.exp (-4 * B) ≤ B := by
          have he := six_eta_le_one hB
          change ‖c‖ ≤ r + Real.exp (-4 * B) at hcsmall
          linarith
        have hdomain := eta_disk_enlargement_subset hB hΔ hcsmall
        apply factorized_eta_disk_card_le (t c) σ hB hcard hcbig hroots hm hn hd
          (fun w hw => hH w (hdomain hw))
          (fun w hw => hHderiv w (hdomain hw))
          (fun w hw => hhre w (hdomain hw))
          (fun w hw => hlog w (hdomain hw))
        intro w hw
        have hws := (Finset.mem_filter.mp hw).1
        exact ⟨(by simpa only [mem_closedBall] using (Finset.mem_filter.mp hw).2), hfiber w hws⟩
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp ht
        simp only [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    _ = (σ.card : ℝ) * (250 * B ^ 2) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B * (250 * B ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 250 * B ^ 3 := by ring

end ThreeIM
