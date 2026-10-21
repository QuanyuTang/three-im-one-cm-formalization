module

public import RequestProject.ThreeIM.SphereLimits

/-! # Finite prefixes do not change normality of a sequence range -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem isNormal_range_of_normal_tail (F : ℕ → ℂ → OnePoint ℂ) (N : ℕ) {U : Set ℂ}
    (hN : IsNormal (range (fun n => F (n + N))) U) : IsNormal (range F) U := by
  classical
  intro Q
  choose i hi using fun n => (Q n).property
  by_cases hfq : ∃ᶠ n in atTop, i n < N
  · have hfinite : ∃ᶠ n in atTop, ∃ j : Fin N, i n = (j : ℕ) :=
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
  · have hge : ∀ᶠ n in atTop, N ≤ i n := by
      simpa only [not_lt] using not_frequently.mp hfq
    obtain ⟨ψ, hψ, g, hc⟩ := hN (fun n =>
      ⟨F ((i n - N) + N), mem_range_self (i n - N)⟩)
    refine ⟨ψ, hψ, g, ?_⟩
    intro v hv x hx
    obtain ⟨t, ht, hev⟩ := hc v hv x hx
    refine ⟨t, ht, ?_⟩
    filter_upwards [hev, hψ.tendsto_atTop.eventually hge] with n hn hgn y hy
    have hvalue := hn y hy
    change (g y, F ((i (ψ n) - N) + N) y) ∈ v at hvalue
    rw [Nat.sub_add_cancel hgn, hi (ψ n)] at hvalue
    exact hvalue

theorem isNormalAt_range_of_normal_tail (F : ℕ → ℂ → OnePoint ℂ) (N : ℕ) {z : ℂ}
    (hN : IsNormalAt (range (fun n => F (n + N))) z) : IsNormalAt (range F) z := by
  obtain ⟨U, hU, hn⟩ := hN
  exact ⟨U, hU, isNormal_range_of_normal_tail F N hn⟩

end ThreeIM
