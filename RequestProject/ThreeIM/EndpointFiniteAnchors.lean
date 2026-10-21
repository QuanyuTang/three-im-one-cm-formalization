module

public import RequestProject.ThreeIM.EndpointAuxiliaryNormality
public import RequestProject.ThreeIM.FiniteConstantChartLimits

/-! # Finite anchors at an auxiliary endpoint

Constant infinity is excluded by two explicit honest spherical anchors.
These anchors are intermediate data to be derived from the bootstrap, not
additional assumptions on the original transport theorem.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

/-- When both honest spherical limits are already finite constants, the
cleared U identity forces the first constant to be a root of the cubic. -/
theorem auxiliary_endpoint_finite_constant_limits_cubic
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu0 : u 0 ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {c d : ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (fun _ => (c : OnePoint ℂ)) atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (fun _ => (d : OnePoint ℂ)) atTop univ) : cubicP a c = 0 := by
  have hseqR (R : ℝ) (_hR : 0 < R) :
      ∀ᶠ n in atTop, AuxiliaryPairOn (ball 0 R) (F n) (G n) (uₙ n) (vₙ n) a := by
    filter_upwards [hr.eventually (eventually_ge_atTop R)] with n hn
    exact (hseq n).restrict (ball_subset_ball hn)
  have hFs (R : ℝ) (hR : 0 < R) :
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) (ball 0 R) :=
    (hseqR R hR).mono fun n hn => sphereHolomorphicOn_sphereGermValue
      isOpen_ball hn.pair.nonconst_f.1
  have hGs (R : ℝ) (hR : 0 < R) :
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (G n)) (ball 0 R) :=
    (hseqR R hR).mono fun n hn => sphereHolomorphicOn_sphereGermValue
      isOpen_ball hn.pair.nonconst_g.1
  let C : ℕ → ℂ → ℂ := fun n z => chartFiniteMap (sphereGermValue (F n) z)
  let D : ℕ → ℂ → ℂ := fun n z => chartFiniteMap (sphereGermValue (G n) z)
  have hCd : ∀ᶠ n in atTop, DifferentiableOn ℂ (C n) (ball 0 1) :=
    finite_constant_chart_eventually_holomorphic c hFs hFconv (by norm_num)
  have hDd : ∀ᶠ n in atTop, DifferentiableOn ℂ (D n) (ball 0 1) :=
    finite_constant_chart_eventually_holomorphic d hGs hGconv (by norm_num)
  have hCc : TendstoLocallyUniformlyOn C (fun _ => c) atTop (ball 0 1) :=
    (finite_constant_chart_locallyUniformly c hFs hFconv).mono (subset_univ _)
  have hDc : TendstoLocallyUniformlyOn D (fun _ => d) atTop (ball 0 1) :=
    (finite_constant_chart_locallyUniformly d hGs hGconv).mono (subset_univ _)
  have hclear : ∀ᶠ n in atTop,
      (∀ z ∈ ball (0 : ℂ) 1,
        (C n z - D n z) * deriv (C n) z = uₙ n z * cubicP a (C n z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        (C n z - D n z) * deriv (D n) z = vₙ n z * cubicP a (D n z)) := by
    filter_upwards [hseqR 1 (by norm_num), hCd, hDd] with n hn hnC hnD
    have heF : F n =ᶠ[codiscreteWithin (ball 0 1)] C n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_f.1
    have heG : G n =ᶠ[codiscreteWithin (ball 0 1)] D n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_g.1
    have hCn := hn.pair.nonconst_f.congr_codiscreteWithin isOpen_ball heF
    have hDn := hn.pair.nonconst_g.congr_codiscreteWithin isOpen_ball heG
    have haux := auxiliary_congr_codiscreteWithin isOpen_ball heF heG a
    have hdiff : ContinuousOn (fun z => C n z - D n z) (ball 0 1) :=
      hnC.continuousOn.sub hnD.continuousOn
    exact ⟨auxiliary_cleared_eqOn a isOpen_ball (hnC.analyticOnNhd isOpen_ball) hCn
        hdiff hn.holo_u.continuousOn (haux.1.symm.trans hn.u_eq),
      auxiliary_cleared_eqOn a isOpen_ball (hnD.analyticOnNhd isOpen_ball) hDn
        hdiff hn.holo_v.continuousOn (haux.2.1.symm.trans hn.v_eq)⟩
  have hlimit := auxiliary_cleared_limit isOpen_ball a hCd hDd hCc hDc
    (huconv.mono (subset_univ _)) (hvconv.mono (subset_univ _))
    (hclear.mono fun n hn => hn.1) (hclear.mono fun n hn => hn.2)
  have hz : (0 : ℂ) = u 0 * cubicP a c := by
    simpa only [deriv_const, mul_zero] using hlimit.1 0 (mem_ball_self (by norm_num))
  exact (mul_eq_zero.mp hz.symm).resolve_left hu0

/-- The two anchors refer to honest meromorphic germs. Raw assigned values
at removable singularities do not suffice for these hypotheses. -/
theorem auxiliary_endpoint_finite_anchors_cubic
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {H K : ℂ → OnePoint ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    {c d : ℂ}
    (hFanchor : Tendsto (fun n => sphereGermValue (F n) 0) atTop (𝓝 (c : OnePoint ℂ)))
    (hGanchor : Tendsto (fun n => sphereGermValue (G n) 0) atTop (𝓝 (d : OnePoint ℂ))) :
    cubicP a c = 0 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := auxiliary_endpoint_spherical_limits_constant
    hr hseq hu hu0 huconv hvconv hFconv hGconv
  have hH0 : H 0 = (c : OnePoint ℂ) :=
    tendsto_nhds_unique (hFconv.tendsto_at (mem_univ 0)) hFanchor
  have hK0 : K 0 = (d : OnePoint ℂ) :=
    tendsto_nhds_unique (hGconv.tendsto_at (mem_univ 0)) hGanchor
  have hH : H = fun _ => (c : OnePoint ℂ) :=
    funext fun z => (hp z).trans ((hp 0).symm.trans hH0)
  have hK : K = fun _ => (d : OnePoint ℂ) :=
    funext fun z => (hq z).trans ((hq 0).symm.trans hK0)
  rw [hH] at hFconv
  rw [hK] at hGconv
  exact auxiliary_endpoint_finite_constant_limits_cubic hr hseq (hu0 0)
    huconv hvconv hFconv hGconv

theorem auxiliary_endpoint_finite_anchors_mem_targets
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {H K : ℂ → OnePoint ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    {c d : ℂ}
    (hFanchor : Tendsto (fun n => sphereGermValue (F n) 0) atTop (𝓝 (c : OnePoint ℂ)))
    (hGanchor : Tendsto (fun n => sphereGermValue (G n) 0) atTop (𝓝 (d : OnePoint ℂ))) :
    ∃ j : Fin 3, c = a j := by
  have hc := auxiliary_endpoint_finite_anchors_cubic
    hr hseq hu hu0 huconv hvconv hFconv hGconv hFanchor hGanchor
  simp only [cubicP, mul_eq_zero, sub_eq_zero] at hc
  rcases hc with (h0 | h1) | h2
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩
  · exact ⟨2, h2⟩

private theorem endpoint_finite_of_bounded_coe {X : ℕ → OnePoint ℂ} {p : OnePoint ℂ}
    (hX : Tendsto X atTop (𝓝 p)) {v : ℕ → ℂ} {M : ℝ}
    (hvalues : ∀ᶠ n in atTop, X n = (v n : OnePoint ℂ))
    (hbound : ∀ᶠ n in atTop, ‖v n‖ ≤ M) :
    ∃ c : ℂ, ‖c‖ ≤ M ∧ p = (c : OnePoint ℂ) := by
  let S : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' closedBall (0 : ℂ) M
  have hS : IsClosed S := ((isCompact_closedBall (0 : ℂ) M).image
    OnePoint.continuous_coe).isClosed
  have hmem : ∀ᶠ n in atTop, X n ∈ S := by
    filter_upwards [hvalues, hbound] with n hn hb
    exact ⟨v n, by simpa only [mem_closedBall, dist_zero_right] using hb, hn.symm⟩
  obtain ⟨c, hc, hcp⟩ := hS.mem_of_tendsto hX hmem
  exact ⟨c, by simpa only [mem_closedBall, dist_zero_right] using hc, hcp.symm⟩

/-- A bootstrap can supply bounded analytic values representing the honest
germs, instead of having to choose the two finite anchors beforehand. -/
theorem auxiliary_endpoint_bounded_values_cubic
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {H K : ℂ → OnePoint ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    {vF vG : ℕ → ℂ} {MF MG : ℝ}
    (hFvalues : ∀ᶠ n in atTop, sphereGermValue (F n) 0 = (vF n : OnePoint ℂ))
    (hGvalues : ∀ᶠ n in atTop, sphereGermValue (G n) 0 = (vG n : OnePoint ℂ))
    (hFbound : ∀ᶠ n in atTop, ‖vF n‖ ≤ MF)
    (hGbound : ∀ᶠ n in atTop, ‖vG n‖ ≤ MG) :
    ∃ c d : ℂ, ‖c‖ ≤ MF ∧ ‖d‖ ≤ MG ∧
      (∀ z, H z = (c : OnePoint ℂ)) ∧
      (∀ z, K z = (d : OnePoint ℂ)) ∧ cubicP a c = 0 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := auxiliary_endpoint_spherical_limits_constant
    hr hseq hu hu0 huconv hvconv hFconv hGconv
  have hFp := hFconv.tendsto_at (mem_univ (0 : ℂ))
  have hGq := hGconv.tendsto_at (mem_univ (0 : ℂ))
  rw [hp 0] at hFp
  rw [hq 0] at hGq
  obtain ⟨c, hc, hpc⟩ := endpoint_finite_of_bounded_coe hFp hFvalues hFbound
  obtain ⟨d, hd, hqd⟩ := endpoint_finite_of_bounded_coe hGq hGvalues hGbound
  have hFanchor : Tendsto (fun n => sphereGermValue (F n) 0) atTop (𝓝 (c : OnePoint ℂ)) := by
    simpa only [hpc] using hFp
  have hGanchor : Tendsto (fun n => sphereGermValue (G n) 0) atTop (𝓝 (d : OnePoint ℂ)) := by
    simpa only [hqd] using hGq
  exact ⟨c, d, hc, hd, (fun z => (hp z).trans hpc), (fun z => (hq z).trans hqd),
    auxiliary_endpoint_finite_anchors_cubic hr hseq hu hu0 huconv hvconv
      hFconv hGconv hFanchor hGanchor⟩

end ThreeIM
