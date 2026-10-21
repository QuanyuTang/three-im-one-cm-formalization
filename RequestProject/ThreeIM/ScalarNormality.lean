module

public import RequestProject.ThreeIM.ScalarLimits
public import RequestProject.ThreeIM.ScalarRescaling
public import RequestProject.ThreeIM.ComplexRescaleLimits
public import RequestProject.ThreeIM.SphericalAffineLimits
public import RequestProject.ThreeIM.SphereRescaleIndices
public import RequestProject.ThreeIM.SphereGlobalNormality
public import RequestProject.ThreeIM.SphereTailNormality
public import RequestProject.ThreeIM.SpherePicardDerivative
public import NoWanderingDomains.NormalFamilies.Zalcman

/-!
# Normality from the scalar differential equation

A Zalcman rescaling freezes the two coefficients and removes the derivative
of the first coefficient. On an ordinary chart two Cauchy derivative limits
give the autonomous scalar equation. Its proved meromorphic classification
excludes the nonconstant bubble, including the degenerate leading term.
The eventual-domain wrappers retain the original exhausting-disk setting.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

private theorem scalar_tlu_reindex {X : Type*} [UniformSpace X]
    {F : ℕ → ℂ → X} {f : ℂ → X} {Ω : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop Ω := by
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := h v hv x hx
  exact ⟨t, ht, hi.eventually hev⟩

theorem scalar_solutions_isNormalAt {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {H C B : ℕ → ℂ → ℂ} {c b : ℂ → ℂ}
    (hH : ∀ n, DifferentiableOn ℂ (H n) Ω)
    (hC : ∀ n, DifferentiableOn ℂ (C n) Ω)
    (hCconv : TendstoLocallyUniformlyOn C c atTop Ω)
    (hBconv : TendstoLocallyUniformlyOn B b atTop Ω)
    (hb : ContinuousOn b Ω) (hb0 : ∀ z ∈ Ω, b z ≠ 0)
    (heq : ∀ n, ∀ z ∈ Ω,
      C n z * H n z * (H n z - 1) * deriv (deriv (H n)) z
      - deriv (C n) z * H n z * (H n z - 1) * deriv (H n) z
      - (C n z * (3 * H n z - 1) + B n z) * deriv (H n) z ^ 2 = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    IsNormalAt (range (fun n => sphereGermValue (H n))) z₀ := by
  classical
  by_contra hnot
  have hhol : ∀ Q ∈ range (fun n => sphereGermValue (H n)), SphereHolomorphicOn Q Ω := by
    rintro Q ⟨n, rfl⟩
    exact sphereHolomorphicOn_sphereGermValue hΩ
      (fun z hz => ((hH n).analyticOnNhd hΩ z hz).meromorphicAt)
  obtain ⟨Q, z, ρ, L, hQ, hz, hρpos, hρ, hL, hL0, _, hQconv⟩ :=
    exists_zalcman_rescale hΩ hhol hz₀ hnot
  have hLnc : ¬ ∃ p : OnePoint ℂ, ∀ w, L w = p := by
    rintro ⟨p, hp⟩
    have he : L = fun _ => p := funext hp
    have hd := sphericalDeriv_const p 0
    rw [← he, hL0] at hd
    exact one_ne_zero hd
  choose i hi using hQ
  have hconv₀ : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue (H (i n)) (z n + (ρ n : ℂ) * w)) L atTop univ := by
    apply hQconv.congr
    intro n w _
    exact (congrFun (hi n) (z n + (ρ n : ℂ) * w)).symm
  have hit : Tendsto i atTop atTop := rescale_indices_tendsto_atTop
    (fun n => continuousAt_sphereGermValue
      (((hH n).analyticOnNhd hΩ z₀ hz₀).meromorphicAt)) hLnc hz hρ hconv₀
  have hρne : ∀ n, ρ n ≠ 0 := fun n => (hρpos n).ne'
  let A : ℕ → ℂ → ℂ := fun n w => H (i n) (z n + (ρ n : ℂ) * w)
  have hconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (A n)) L atTop univ :=
    spherical_affine_limits hΩ (fun n w hw =>
      ((hH (i n)).analyticOnNhd hΩ w hw).meromorphicAt) hz₀ hz hρ hρne hconv₀
  have hcd : DifferentiableOn ℂ c Ω :=
    hCconv.differentiableOn (Eventually.of_forall hC) hΩ
  have hcdconv := hCconv.deriv (Eventually.of_forall hC) hΩ
  have hCscaled := complex_rescale_tendstoLocallyUniformlyOn_const hΩ hz₀
    (hcd.continuousOn.continuousAt (hΩ.mem_nhds hz₀))
    (scalar_tlu_reindex hCconv hit) hz hρ
  have hBscaled := complex_rescale_tendstoLocallyUniformlyOn_const hΩ hz₀
    (hb.continuousAt (hΩ.mem_nhds hz₀)) (scalar_tlu_reindex hBconv hit) hz hρ
  have hDscaled := complex_rescale_coefficient_tendsto_zero hΩ hz₀
    ((hcd.analyticOnNhd hΩ).deriv.continuousOn.continuousAt (hΩ.mem_nhds hz₀))
    (scalar_tlu_reindex hcdconv hit) hz hρ
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℂ, L w ≠ OnePoint.infty := by
    by_contra h
    push_neg at h
    exact hLnc ⟨OnePoint.infty, h⟩
  let R : ℝ := ‖w₀‖ + 1
  let D : Set ℂ := ball (0 : ℂ) R
  have hwD : w₀ ∈ D := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  have hmap := eventually_rescale_closedBall_subset hΩ hz₀ hz hρ R
  have hAholo : ∀ᶠ n in atTop, DifferentiableOn ℂ (A n) D := by
    filter_upwards [hmap] with n hn w hw
    exact (((hH (i n)).analyticOnNhd hΩ _ (hn w (ball_subset_closedBall hw))).comp
      (f := fun x : ℂ => z n + (ρ n : ℂ) * x)
      (by fun_prop : AnalyticAt ℂ (fun x : ℂ => z n + (ρ n : ℂ) * x) w)).differentiableAt.differentiableWithinAt
  have hAeq : ∀ᶠ n in atTop, ∀ w ∈ D,
      C (i n) (z n + (ρ n : ℂ) * w) * A n w * (A n w - 1) * deriv (deriv (A n)) w
      - ((ρ n : ℂ) * deriv (C (i n)) (z n + (ρ n : ℂ) * w)) * A n w * (A n w - 1) * deriv (A n) w
      - (C (i n) (z n + (ρ n : ℂ) * w) * (3 * A n w - 1) + B (i n) (z n + (ρ n : ℂ) * w)) * deriv (A n) w ^ 2 = 0 := by
    filter_upwards [hmap] with n hn
    exact scalar_equation_comp_affine hΩ (hH (i n)) (heq (i n))
      (ρ n : ℂ) (z n) (fun w hw => hn w (ball_subset_closedBall hw))
  have hsphere : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (A n)) D :=
    hAholo.mono fun n hn => sphereHolomorphicOn_sphereGermValue isOpen_ball
      (fun w hw => (hn.analyticOnNhd isOpen_ball w hw).meromorphicAt)
  obtain ⟨r, hr, hrD, _, _, _, hchartconv⟩ :=
    exists_finite_chart_convergence_eventually isOpen_ball hsphere
      (hconv.mono (subset_univ D)) hwD hw₀
  let E : Set ℂ := ball w₀ r
  have hED : E ⊆ D := ball_subset_closedBall.trans hrD
  have hchart : TendstoLocallyUniformlyOn
      (fun n w => chartFiniteMap (sphereGermValue (A n) w))
      (fun w => chartFiniteMap (L w)) atTop E :=
    hchartconv.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hraw : TendstoLocallyUniformlyOn A (fun w => chartFiniteMap (L w)) atTop E := by
    apply tendstoLocallyUniformlyOn_congr_locally_eventually hchart
    intro w _
    refine ⟨E, self_mem_nhdsWithin, ?_⟩
    filter_upwards [hAholo] with n hn x hx
    change chartFiniteMap (sphereGermValue (A n) x) = A n x
    rw [sphereGermValue_eq_coe_of_analytic (hn.analyticOnNhd isOpen_ball x (hED hx))]
    rfl
  have heqlimit := scalar_equation_limit_on_chart isOpen_ball
    (hAholo.mono fun n hn => hn.mono hED) hraw
    (hCscaled.mono (subset_univ E)) (hDscaled.mono (subset_univ E))
    (hBscaled.mono (subset_univ E)) (hAeq.mono fun n hn w hw => hn w (hED hw))
  have hnc := isNonconstMeroOn_chartFiniteMap hL hLnc
  exact nonconstant_scalar_limit_impossible hnc (b z₀) (c z₀) (hb0 z₀ hz₀)
    (scalar_equation_global_of_local (fun w => hnc.1 w (mem_univ w))
      (b z₀) (c z₀) isOpen_ball (mem_ball_self hr) heqlimit)

theorem scalar_solutions_isNormalAt_eventually {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {H C B : ℕ → ℂ → ℂ} {c b : ℂ → ℂ}
    (hseq : ∀ᶠ n in atTop, DifferentiableOn ℂ (H n) Ω ∧
      DifferentiableOn ℂ (C n) Ω ∧ ∀ z ∈ Ω,
        C n z * H n z * (H n z - 1) * deriv (deriv (H n)) z
        - deriv (C n) z * H n z * (H n z - 1) * deriv (H n) z
        - (C n z * (3 * H n z - 1) + B n z) * deriv (H n) z ^ 2 = 0)
    (hCconv : TendstoLocallyUniformlyOn C c atTop Ω)
    (hBconv : TendstoLocallyUniformlyOn B b atTop Ω)
    (hb : ContinuousOn b Ω) (hb0 : ∀ z ∈ Ω, b z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    IsNormalAt (range (fun n => sphereGermValue (H n))) z₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hseq
  have htail (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  exact isNormalAt_range_of_normal_tail (fun n => sphereGermValue (H n)) N
    (scalar_solutions_isNormalAt hΩ (fun n => (htail n).1) (fun n => (htail n).2.1)
      (scalar_tlu_reindex hCconv (tendsto_add_atTop_nat N))
      (scalar_tlu_reindex hBconv (tendsto_add_atTop_nat N)) hb hb0
      (fun n => (htail n).2.2) hz₀)

theorem scalar_solutions_isNormal_of_locally_eventually
    {H C B : ℕ → ℂ → ℂ} {c b : ℂ → ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (H n) Ω ∧
        DifferentiableOn ℂ (C n) Ω ∧ ∀ w ∈ Ω,
          C n w * H n w * (H n w - 1) * deriv (deriv (H n)) w
          - deriv (C n) w * H n w * (H n w - 1) * deriv (H n) w
          - (C n w * (3 * H n w - 1) + B n w) * deriv (H n) w ^ 2 = 0)
    (hCconv : TendstoLocallyUniformlyOn C c atTop univ)
    (hBconv : TendstoLocallyUniformlyOn B b atTop univ)
    (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0) :
    IsNormal (range (fun n => sphereGermValue (H n))) univ := by
  apply sphere_isNormal_of_forall_isNormalAt
  intro z
  obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
  exact scalar_solutions_isNormalAt_eventually hΩ hev
    (hCconv.mono (subset_univ Ω)) (hBconv.mono (subset_univ Ω))
    hb.continuousOn (fun w _ => hb0 w) hzΩ

end ThreeIM
