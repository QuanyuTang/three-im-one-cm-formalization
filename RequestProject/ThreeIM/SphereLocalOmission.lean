module

public import RequestProject.ThreeIM.SphereLimits

/-! # Local omission near a value different from the limiting value -/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem sphere_limit_local_omission {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U)
    {z : ℂ} (hz : z ∈ U) (hG : ContinuousAt G z)
    {a : OnePoint ℂ} (hne : G z ≠ a) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∀ᶠ n in atTop, ∀ w ∈ V, F n w ≠ a := by
  let d : ℝ := dist (G z) a
  have hd : 0 < d := dist_pos.mpr hne
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hconv
    (d / 3) (by positivity) z hz
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hz)] at ht
  have hc : {w : ℂ | dist (G w) (G z) < d / 3} ∈ 𝓝 z :=
    hG.tendsto.eventually (ball_mem_nhds (G z) (by positivity))
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hz) (inter_mem ht hc))
  refine ⟨V, hVo, hzV, fun w hw => (hVsub hw).1, ?_⟩
  filter_upwards [hev] with n hn w hw hwa
  have h1 := hn w (hVsub hw).2.1
  have h2 := (hVsub hw).2.2
  change dist (G w) (G z) < d / 3 at h2
  rw [hwa] at h1
  have htri := dist_triangle (G z) (G w) a
  rw [dist_comm (G z) (G w)] at htri
  change d ≤ dist (G w) (G z) + dist (G w) a at htri
  linarith

end ThreeIM
