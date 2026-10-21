module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Locally eventual agreement preserves locally uniform convergence -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem tendstoLocallyUniformlyOn_congr_locally_eventually
    {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F G : ℕ → X → Y} {f : X → Y} {U : Set X}
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (heq : ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, ∀ᶠ n in atTop, EqOn (F n) (G n) V) :
    TendstoLocallyUniformlyOn G f atTop U := by
  intro v hv x hx
  obtain ⟨T, hT, hev⟩ := hconv v hv x hx
  obtain ⟨V, hV, he⟩ := heq x hx
  refine ⟨T ∩ V, inter_mem hT hV, ?_⟩
  filter_upwards [hev, he] with n hn heq y hy
  rw [← heq hy.2]
  exact hn y hy.1

end ThreeIM
