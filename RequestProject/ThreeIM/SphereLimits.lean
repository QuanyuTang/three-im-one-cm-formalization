module

public import RequestProject.ThreeIM.SphereChartConvergence

/-!
# Spherical limits with eventual local holomorphy

Sequences on exhausting disks are only eventually holomorphic on any fixed
disk. These lemmas pass from that exact condition to chart convergence,
without imposing holomorphy on the irrelevant finite prefix.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphereHolomorphicOn_mono {F : ℂ → OnePoint ℂ} {U V : Set ℂ}
    (hF : SphereHolomorphicOn F U) (hV : IsOpen V) (hVU : V ⊆ U) :
    SphereHolomorphicOn F V := by
  intro z hz
  obtain ⟨W, hWo, hzW, _, hcase⟩ := hF z (hVU hz)
  refine ⟨W ∩ V, hWo.inter hV, ⟨hzW, hz⟩, inter_subset_right, ?_⟩
  rcases hcase with ⟨hne, hd⟩ | ⟨hne, hd⟩
  · exact Or.inl ⟨fun w hw => hne w hw.1, hd.mono inter_subset_left⟩
  · exact Or.inr ⟨fun w hw => hne w hw.1, hd.mono inter_subset_left⟩

theorem sphereHolomorphicOn_of_eventually {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U) : SphereHolomorphicOn G U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hF
  apply sphereHolomorphicOn_of_tendstoLocallyUniformlyOn (Fn := fun n => F (n + N)) hU
    (fun n => hN (n + N) (Nat.le_add_left N n))
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := hconv u hu x hx
  exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩

theorem exists_finite_chart_convergence_eventually {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U)
    {z : ℂ} (hz : z ∈ U) (hne : G z ≠ OnePoint.infty) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      (∀ w ∈ closedBall z r, G w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, ∀ w ∈ closedBall z r, F n w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z r)) ∧
      TendstoUniformlyOn (fun n w => chartFiniteMap (F n w))
        (fun w => chartFiniteMap (G w)) atTop (closedBall z r) := by
  classical
  have hG : SphereHolomorphicOn G U := sphereHolomorphicOn_of_eventually hU hF hconv
  let F' (n : ℕ) : ℂ → OnePoint ℂ := if SphereHolomorphicOn (F n) U then F n else G
  have heq : F' =ᶠ[atTop] F := hF.mono fun n hn => by simp only [F', if_pos hn]
  have hF' : ∀ n, SphereHolomorphicOn (F' n) U := by
    intro n
    dsimp only [F']
    split_ifs with hn
    · exact hn
    · exact hG
  have hc' : TendstoLocallyUniformlyOn F' G atTop U :=
    hconv.congr_inseparable (heq.mono fun n hn x _ => .of_eq (congrFun hn x).symm)
  obtain ⟨r, hr, hrU, hGfin, hFfin, hFd, hc⟩ :=
    exists_finite_chart_convergence hU hF' hc' hz hne
  refine ⟨r, hr, hrU, hGfin, ?_, ?_, ?_⟩
  · filter_upwards [hFfin, heq] with n hn he w hw
    rw [← he]
    exact hn w hw
  · filter_upwards [hFd, heq] with n hn he
    simpa only [he] using hn
  · apply hc.congr
    filter_upwards [heq] with n hn w _
    exact congrArg chartFiniteMap (congrFun hn w)

end ThreeIM
