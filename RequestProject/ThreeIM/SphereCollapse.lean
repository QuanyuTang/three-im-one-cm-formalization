module

public import RequestProject.ThreeIM.SphereRescaling

/-!
# Collapse of a convergent family on shrinking source scales

A locally uniformly convergent family, viewed at centers approaching an
interior point and scales approaching zero, converges to the constant value
of its continuous limit at that point. No global continuity of the members
outside their original domain is assumed.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem rescale_tendstoUniformlyOn_const {F : ℕ → ℂ → OnePoint ℂ}
    {f : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf : ContinuousAt f z₀)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 z₀))
    (hρ : Tendsto ρ atTop (𝓝 0)) (R : ℝ) :
    TendstoUniformlyOn (fun n w => F n (z n + (ρ n : ℂ) * w))
      (fun _ => f z₀) atTop (closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hconv
    (ε / 2) (half_pos hε) z₀ hz₀
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hz₀)] at ht
  have hclose : {y : ℂ | dist (f y) (f z₀) < ε / 2} ∈ 𝓝 z₀ := by
    exact hf.tendsto.eventually (ball_mem_nhds (f z₀) (half_pos hε))
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp (inter_mem ht hclose)
  filter_upwards [hev, eventually_rescale_closedBall_subset hVo hzV hz hρ R]
    with n hn hmap w hw
  have hy := hVsub (hmap w hw)
  have h1 := hn (z n + (ρ n : ℂ) * w) hy.1
  have h2 := hy.2
  change dist (f (z n + (ρ n : ℂ) * w)) (f z₀) < ε / 2 at h2
  rw [dist_comm] at h2
  exact (dist_triangle (f z₀) (f (z n + (ρ n : ℂ) * w))
    (F n (z n + (ρ n : ℂ) * w))).trans_lt (by linarith)

theorem rescale_tendstoLocallyUniformlyOn_const {F : ℕ → ℂ → OnePoint ℂ}
    {f : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf : ContinuousAt f z₀)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 z₀))
    (hρ : Tendsto ρ atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n w => F n (z n + (ρ n : ℂ) * w))
      (fun _ => f z₀) atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  exact (rescale_tendstoUniformlyOn_const hU hz₀ hf hconv hz hρ R).mono
    (hR.trans ball_subset_closedBall)

end ThreeIM
