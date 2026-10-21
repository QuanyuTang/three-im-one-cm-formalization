module

public import NoWanderingDomains.NormalFamilies.Zalcman

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Will (Ziang) Li

Modified by Codex for the ThreeIM project: expose the finite-chart convergence
part of sphere-valued Weierstrass as a reusable theorem, retaining the radius,
eventual omission of infinity, and uniform convergence on a closed disk.
Adapted from NoWanderingDomains.NormalFamilies.Zalcman at upstream commit
0a6497b0cc9ed39a6a705bf013449635894b56d0, with the 4.28 API backport.
-/

@[expose] public section

open Filter Set Metric Topology OnePoint NoWanderingDomains

namespace ThreeIM

/-- Near a finite value of a spherical locally uniform limit, a fixed closed
disk eventually lies in the finite chart for all members, and the actual
finite-chart readings converge uniformly there. -/
theorem exists_finite_chart_convergence {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (holF : ∀ n, SphereHolomorphicOn (F n) U)
    (hFG : TendstoLocallyUniformlyOn F G atTop U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hne : G z₀ ≠ OnePoint.infty) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ r ⊆ U ∧
      (∀ w ∈ closedBall z₀ r, G w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ r, F n w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z₀ r)) ∧
      TendstoUniformlyOn (fun n w => chartFiniteMap (F n w))
        (fun w => chartFiniteMap (G w)) atTop (closedBall z₀ r) := by
  have hGc : ContinuousOn G U :=
    hFG.continuousOn (Frequently.of_forall fun n => (holF n).continuousOn)
  obtain ⟨ε₀, hε₀, hd4⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ dist (G z₀) (∞ : ℂ̂) = 4 * ε₀ :=
    ⟨dist (G z₀) (∞ : ℂ̂) / 4, by linarith [dist_pos.mpr hne], by ring⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hGc.continuousAt (hU.mem_nhds hz₀)) ε₀ hε₀
  obtain ⟨r₁, hr₁, hr₁U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
  obtain ⟨r, hr, hrδ, hrU⟩ : ∃ r : ℝ, 0 < r ∧ r < δ ∧ closedBall z₀ r ⊆ U :=
    ⟨min r₁ (δ / 2), lt_min hr₁ (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith),
      (closedBall_subset_closedBall (min_le_left _ _)).trans hr₁U⟩
  -- values of `G` on the closed ball stay spherically far from `∞`
  have hGfar : ∀ w ∈ closedBall z₀ r, 3 * ε₀ ≤ dist (G w) (∞ : ℂ̂) := by
    intro w hw
    have h2 := dist_triangle (G z₀) (G w) (∞ : ℂ̂)
    have h3 : dist (G z₀) (G w) < ε₀ := by
      rw [dist_comm]
      exact hδ' (lt_of_le_of_lt (mem_closedBall.mp hw) hrδ)
    linarith
  -- points spherically far from `∞` are finite with bounded chart reading
  have hbound : ∀ p : ℂ̂, 2 * ε₀ ≤ dist p (∞ : ℂ̂) →
      p ≠ ∞ ∧ ‖chartFiniteMap p‖ ≤ 2 / (2 * ε₀) := by
    intro p hp
    cases p with
    | infty =>
      rw [dist_self] at hp
      exact absurd hp (not_le.mpr (by linarith))
    | coe x =>
      refine ⟨OnePoint.coe_ne_infty x, ?_⟩
      have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) = 2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
      rw [hx_eq] at hp
      have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
        calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
          _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
      have h2 : 2 * ε₀ * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := (le_div_iff₀ hs).mp hp
      have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (2 * ε₀) := by
        rw [le_div_iff₀ (by positivity)]
        linarith [mul_comm (2 * ε₀) (Real.sqrt (1 + ‖x‖ ^ 2))]
      exact hxs.trans h3
  have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
    intro p hp
    cases p with
    | infty => exact absurd rfl hp
    | coe x => rfl
  have hunif : TendstoUniformlyOn F G atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hFG _ hrU (isCompact_closedBall z₀ r)
  -- eventually the members are close to `G`, hence also far from `∞`, on the ball
  have hFev : ∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ r,
      dist (G w) (F n w) < ε₀ ∧ 2 * ε₀ ≤ dist (F n w) (∞ : ℂ̂) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif ε₀ hε₀] with n hn w hw
    have h2 := hGfar w hw
    have h3 := dist_triangle (G w) (F n w) (∞ : ℂ̂)
    exact ⟨hn w hw, by linarith [hn w hw]⟩
  -- eventually the chart readings of the members are holomorphic on the open ball
  have hudiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z₀ r) := by
    filter_upwards [hFev] with n hn
    refine SphereHolomorphicOn.differentiableOn_chartFiniteMap (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨V, hVo, hwV, hVU, hcase⟩ := holF n w (hrU (ball_subset_closedBall hw))
      refine ⟨V ∩ ball z₀ r, hVo.inter isOpen_ball, ⟨hwV, hw⟩, Set.inter_subset_right, ?_⟩
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
      · exact Or.inr ⟨fun x hx => h1 x hx.1, h2.mono Set.inter_subset_left⟩
    · exact (hbound _ (hn w (ball_subset_closedBall hw)).2).1
  obtain ⟨C, hC0, hCdef⟩ : ∃ C : ℝ, 0 < C ∧ C = (1 + (2 / (2 * ε₀)) ^ 2) / 2 :=
    ⟨(1 + (2 / (2 * ε₀)) ^ 2) / 2, by positivity, rfl⟩
  have hC0' : C ≠ 0 := ne_of_gt hC0
  -- the chart readings converge uniformly on the closed ball
  have huTLU : TendstoUniformlyOn (fun n w => chartFiniteMap (F n w))
      (fun w => chartFiniteMap (G w)) atTop (closedBall z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hFev, Metric.tendstoUniformlyOn_iff.mp hunif (ε / C) (by positivity)]
      with n hn hn2 w hw
    obtain ⟨hFne, hFbd⟩ := hbound _ (hn w hw).2
    obtain ⟨hGne, hGbd⟩ := hbound _ (le_trans (by linarith) (hGfar w hw))
    have hnorm := norm_sub_le_sphericalDist_mul hGbd hFbd
    have hds : sphericalDist ((chartFiniteMap (G w) : ℂ) : ℂ̂)
        ((chartFiniteMap (F n w) : ℂ) : ℂ̂) = dist (G w) (F n w) := by
      rw [hcoe _ hGne, hcoe _ hFne]
      rfl
    rw [hds, ← hCdef] at hnorm
    calc dist (chartFiniteMap (G w)) (chartFiniteMap (F n w))
        = ‖chartFiniteMap (G w) - chartFiniteMap (F n w)‖ := dist_eq_norm _ _
      _ ≤ C * dist (G w) (F n w) := hnorm
      _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn2 w hw) hC0
      _ = ε := by field_simp

  refine ⟨r, hr, hrU, ?_, ?_, hudiff, huTLU⟩
  · intro w hw
    exact (hbound _ (le_trans (by linarith) (hGfar w hw))).1
  · filter_upwards [hFev] with n hn w hw
    exact (hbound _ (hn w hw).2).1

end ThreeIM
