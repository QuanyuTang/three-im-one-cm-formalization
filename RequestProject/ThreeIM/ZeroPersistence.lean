module

public import RequestProject.ThreeIM.Hurwitz

/-!
# Persistence of an isolated zero

The omitted-zero Hurwitz lemma applied to a hypothetical zero-free
subsequence gives eventual zeros in every open neighborhood.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem eventually_exists_zero_of_locallyUniform_finite_germ
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    {z : ℂ} (hz : z ∈ U) (hf0 : f z = 0)
    (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    ∀ᶠ n in atTop, ∃ w ∈ U, F n w = 0 := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ ∃ w ∈ U, F n w = 0 :=
    not_eventually.mp hnot
  obtain ⟨ψ, hψ, hfree⟩ := extraction_of_frequently_atTop hfreq
  have hconv' : TendstoLocallyUniformlyOn (fun n => F (ψ n)) f atTop U := by
    intro v hv x hx
    obtain ⟨s, hs, hev⟩ := hconv v hv x hx
    exact ⟨s, hs, hψ.tendsto_atTop.eventually hev⟩
  have hdata : ∀ᶠ n in atTop, DifferentiableOn ℂ (F (ψ n)) U ∧
      ∀ w ∈ U, F (ψ n) w ≠ 0 := by
    filter_upwards [hψ.tendsto_atTop.eventually hF] with n hn
    exact ⟨hn, fun w hw hw0 => hfree n ⟨w, hw, hw0⟩⟩
  exact (locallyUniform_limit_ne_zero_of_finite_germ hU hdata hconv' hz hfinite) hf0

/-- A zero can be followed in any prescribed open neighborhood contained
in the convergence domain; no multiplicity statement is assumed. -/
theorem eventually_exists_zero_in_nhds {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ}
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    {z : ℂ} (hf0 : f z = 0)
    (hfinite : meromorphicOrderAt f z ≠ ⊤)
    {V : Set ℂ} (hV : IsOpen V) (hzV : z ∈ V) (hVU : V ⊆ U) :
    ∀ᶠ n in atTop, ∃ w ∈ V, F n w = 0 :=
  eventually_exists_zero_of_locallyUniform_finite_germ hV
    (hF.mono fun _ hn => hn.mono hVU) (hconv.mono hVU) hzV hf0 hfinite

end ThreeIM
