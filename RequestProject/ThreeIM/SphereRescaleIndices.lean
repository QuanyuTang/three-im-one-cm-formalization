module

public import RequestProject.ThreeIM.SphereCollapse

/-!
# A nonconstant rescaling limit escapes every finite prefix

The family elements in Zalcman's conclusion are not automatically a
subsequence of an original sequence. Continuity of each fixed member and
collapse on shrinking scales force its selected indices to tend to infinity.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem rescale_indices_tendsto_atTop {F : ℕ → ℂ → OnePoint ℂ}
    {g : ℂ → OnePoint ℂ} {z₀ : ℂ} (hF : ∀ n, ContinuousAt (F n) z₀)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ w, g w = p)
    {i : ℕ → ℕ} {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0))
    (hconv : TendstoLocallyUniformlyOn
      (fun n w => F (i n) (z n + (ρ n : ℂ) * w)) g atTop univ) :
    Tendsto i atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro N
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, i n < N := by
    simpa only [not_le] using not_eventually.mp hnot
  have hfinite : ∃ᶠ n in atTop, ∃ j : Fin N, i n = (j : ℕ) :=
    hfreq.mono fun n hn => ⟨⟨i n, hn⟩, rfl⟩
  obtain ⟨j, hj⟩ := frequently_exists.mp hfinite
  obtain ⟨ψ, hψ, hindices⟩ := extraction_of_frequently_atTop hj
  have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => F j) (F j) atTop univ := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun n w _ => by simpa only [dist_self] using hε
  have hcollapse := rescale_tendstoLocallyUniformlyOn_const isOpen_univ (mem_univ z₀)
    (hF j) hconst (hz.comp hψ.tendsto_atTop) (hρ.comp hψ.tendsto_atTop)
  apply hnc
  refine ⟨F j z₀, fun w => ?_⟩
  have hpoint := (hconv.tendsto_at (mem_univ w)).comp hψ.tendsto_atTop
  have hpoint' : Tendsto (fun n => F j (z (ψ n) + (ρ (ψ n) : ℂ) * w))
      atTop (𝓝 (g w)) := hpoint.congr fun n => by simp only [Function.comp_apply, hindices n]
  exact tendsto_nhds_unique hpoint' (hcollapse.tendsto_at (mem_univ w))

end ThreeIM
