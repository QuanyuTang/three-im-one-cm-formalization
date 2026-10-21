module

public import RequestProject.ThreeIM.SphereLimits

/-! # Normality of the range of a locally uniformly convergent sequence -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem isNormal_range_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → OnePoint ℂ} {f : ℂ → OnePoint ℂ} {U : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop U) : IsNormal (range F) U := by
  classical
  intro Q
  choose i hi using fun n => (Q n).property
  by_cases hit : Tendsto i atTop atTop
  · refine ⟨id, strictMono_id, f, ?_⟩
    have hc : TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop U := by
      intro v hv x hx
      obtain ⟨s, hs, hev⟩ := hconv v hv x hx
      exact ⟨s, hs, hit.eventually hev⟩
    apply hc.congr
    intro n w _
    exact congrFun (hi n) w
  · have hnot : ¬ ∀ N : ℕ, ∀ᶠ n in atTop, N ≤ i n :=
      fun h => hit (Filter.tendsto_atTop.2 h)
    obtain ⟨N, hN⟩ := not_forall.mp hnot
    have hfq : ∃ᶠ n in atTop, i n < N := by
      simpa only [not_le] using not_eventually.mp hN
    have hfinite : ∃ᶠ n in atTop, ∃ j : Fin N, i n = (j : ℕ) :=
      hfq.mono fun n hn => ⟨⟨i n, hn⟩, rfl⟩
    obtain ⟨j, hj⟩ := frequently_exists.mp hfinite
    obtain ⟨ψ, hψ, hindices⟩ := extraction_of_frequently_atTop hj
    refine ⟨ψ, hψ, F j, ?_⟩
    have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => F j) (F j) atTop U := by
      apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall fun n w _ => by simpa only [dist_self] using hε
    apply hconst.congr
    intro n w _
    rw [← hi (ψ n), hindices n]

theorem isNormalAt_range_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → OnePoint ℂ} {f : ℂ → OnePoint ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconv : TendstoLocallyUniformlyOn F f atTop U)
    {z : ℂ} (hz : z ∈ U) : IsNormalAt (range F) z :=
  ⟨U, hU.mem_nhds hz, isNormal_range_of_tendstoLocallyUniformlyOn hconv⟩

end ThreeIM
