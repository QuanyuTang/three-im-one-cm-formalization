module

public import RequestProject.ThreeIM.ExponentialSectorCanonical
public import RequestProject.ThreeIM.ExponentialSectorInverseLimit
public import RequestProject.ThreeIM.SphereInverseChart
public import RequestProject.ThreeIM.SphereLimits

/-! # An infinite first sector limit cannot have a finite companion point -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

private theorem exponential_auxU_eq_at_analytic
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ t : ℂ} (h : ExponentialPair a f g κ)
    (hf : AnalyticAt ℂ f t) (hg : AnalyticAt ℂ g t) (hP : cubicP a (f t) ≠ 0) :
    auxU a f g t = κ * Complex.exp t := by
  have hp : ContinuousAt (fun w => cubicP a (f w)) t := by unfold cubicP; fun_prop
  have hc : ContinuousAt (auxU a f g) t :=
    ((hf.continuousAt.sub hg.continuousAt).mul hf.deriv.continuousAt).div hp hP
  have ht := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (auxiliary_local_of_codiscreteWithin isOpen_univ h.eq_U (mem_univ t))
  have he : Tendsto (fun w => κ * Complex.exp w) (𝓝[≠] t)
      (𝓝 (κ * Complex.exp t)) :=
    (continuous_const.mul Complex.continuous_exp).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique ht he

theorem ExponentialPair.not_infinite_finite_dilate_limits
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hzΩ : z ∈ Ω) (hz : 0 < z.re)
    {K : ℂ → OnePoint ℂ}
    (hF : TendstoLocallyUniformlyOn (fun n w => sphereGermValue f ((r n : ℂ) * w))
      (fun _ => OnePoint.infty) atTop Ω)
    (hG : TendstoLocallyUniformlyOn (fun n w => sphereGermValue g ((r n : ℂ) * w)) K atTop Ω)
    (hK : K z ≠ OnePoint.infty) : False := by
  let fc : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let gc : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  let F : ℕ → ℂ → ℂ := fun n w => fc ((r n : ℂ) * w)
  let G : ℕ → ℂ → ℂ := fun n w => gc ((r n : ℂ) * w)
  have hcanon : ExponentialPair a fc gc κ := h.canonical_representatives
  have hsf := sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1
  have hsg := sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_g.1
  have hsfcomp (n : ℕ) :
      SphereHolomorphicOn (fun w => sphereGermValue f ((r n : ℂ) * w)) Ω := by
    have hh : SphereHolomorphicOn (fun w => sphereGermValue f ((r n : ℂ) * w)) univ := by
      simpa only [preimage_univ, zero_add] using hsf.comp_affine 0 (r n : ℂ)
    exact sphereHolomorphicOn_mono hh hΩ (subset_univ Ω)
  have hsgcomp (n : ℕ) :
      SphereHolomorphicOn (fun w => sphereGermValue g ((r n : ℂ) * w)) Ω := by
    have hh : SphereHolomorphicOn (fun w => sphereGermValue g ((r n : ℂ) * w)) univ := by
      simpa only [preimage_univ, zero_add] using hsg.comp_affine 0 (r n : ℂ)
    exact sphereHolomorphicOn_mono hh hΩ (subset_univ Ω)
  have hsector : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
        AnalyticAt ℂ fc t ∧ AnalyticAt ℂ gc t ∧ cubicP a (fc t) ≠ 0 := by
    intro δ hδ
    obtain ⟨R₁, _, hR₁⟩ := h.sector_canonical_analytic hδ
    obtain ⟨R₂, hR₂⟩ := hcanon.omits_shared_in_sectors hδ
    refine ⟨max R₁ R₂, fun t ht hs => ?_⟩
    obtain ⟨hf, hg⟩ := hR₁ t ((le_max_left _ _).trans ht) hs
    have hne (j : Fin 3) : fc t ≠ a j := by
      intro heq
      have hpos := (mult_finite_pos_iff_sphereGermValue_eq hf.meromorphicAt
        (hcanon.pair.nonconst_f.2 t (mem_univ t) (a j))).2
          (by
            rw [sphereGermValue_eq_coe_of_analytic hf]
            exact congrArg (fun x : ℂ => (x : OnePoint ℂ)) heq)
      rw [(hR₂ t ((le_max_right _ _).trans ht) hs j).1] at hpos
      exact lt_irrefl (0 : ℕ) hpos
    exact ⟨hf, hg, mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (hne 0))
      (sub_ne_zero.2 (hne 1))) (sub_ne_zero.2 (hne 2))⟩
  obtain ⟨ε₀, hε₀, hlocal⟩ := eventually_dilate_of_sector_property hsector hr hz
  have hpoint : ∀ᶠ n in atTop,
      AnalyticAt ℂ fc ((r n : ℂ) * z) ∧ AnalyticAt ℂ gc ((r n : ℂ) * z) ∧
        cubicP a (F n z) ≠ 0 :=
    hlocal.mono fun n hn => hn z (mem_closedBall_self hε₀.le)
  have havoid : ∀ᶠ n in atTop,
      sphereGermValue f ((r n : ℂ) * z) ≠ ((0 : ℂ) : OnePoint ℂ) :=
    (hF.tendsto_at hzΩ).eventually_ne (OnePoint.coe_ne_infty 0).symm
  have hF0 : ∀ᶠ n in atTop, F n z ≠ 0 := by
    filter_upwards [hpoint, havoid] with n hn hzero
    intro heq
    have he : sphereGermValue f ((r n : ℂ) * z) = (F n z : OnePoint ℂ) :=
      (sphereGermValue_chartFiniteMap hsf (sphereGermValue_nonconstant h.pair.nonconst_f)
        ((r n : ℂ) * z)).symm.trans (sphereGermValue_eq_coe_of_analytic hn.1)
    exact hzero (he.trans (by rw [heq]))
  have huc : UniformContinuous (fun p : OnePoint ℂ => inversionGL • p) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul inversionGL)
  have hInv : TendstoLocallyUniformlyOn
      (fun n w => inversionGL • sphereGermValue f ((r n : ℂ) * w))
      (fun _ => ((0 : ℂ) : OnePoint ℂ)) atTop Ω := by
    simpa only [Function.comp_def, inversionGL_smul_infty] using
      huc.comp_tendstoLocallyUniformlyOn hF
  obtain ⟨ε, hε, _, _, _, hXd', hXc'⟩ := exists_finite_chart_convergence_eventually
    hΩ (Eventually.of_forall fun n => (hsfcomp n).gl_smul inversionGL) hInv hzΩ
    (OnePoint.coe_ne_infty 0)
  have hx (n : ℕ) : (fun w => (F n w)⁻¹) =
      fun w => chartFiniteMap (inversionGL • sphereGermValue f ((r n : ℂ) * w)) := by
    funext w
    rw [chartFiniteMap_inversionGL]
    change (chartFiniteMap (sphereGermValue f ((r n : ℂ) * w)))⁻¹ = _
    simpa only [inv_inv] using congrArg (fun x : ℂ => x⁻¹)
      (chartFiniteMap_eq_inv_chartInftyMap (sphereGermValue f ((r n : ℂ) * w)))
  have hXd : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => (F n w)⁻¹) (ball z ε) := by
    filter_upwards [hXd'] with n hn
    rw [hx n]
    exact hn
  have hXc : TendstoLocallyUniformlyOn (fun n w => (F n w)⁻¹) (fun _ => 0)
      atTop (ball z ε) := by
    have heq : (fun n w => (F n w)⁻¹) =
        (fun n w => chartFiniteMap (inversionGL • sphereGermValue f ((r n : ℂ) * w))) :=
      funext hx
    rw [heq]
    simpa only [chartFiniteMap] using
      hXc'.tendstoLocallyUniformlyOn.mono (ball_subset_closedBall (x := z) (ε := ε))
  obtain ⟨εG, hεG, _, _, _, _, hGc⟩ := exists_finite_chart_convergence_eventually
    hΩ (Eventually.of_forall hsgcomp) hG hzΩ hK
  have hGp : Tendsto (fun n => G n z) atTop (𝓝 (chartFiniteMap (K z))) :=
    hGc.tendstoLocallyUniformlyOn.tendsto_at (mem_closedBall_self hεG.le)
  have hUzero := exponential_auxU_tendsto_zero_of_inverse_locallyUniformlyOn a
    isOpen_ball (mem_ball_self hε) hXd hXc hF0 hGp
  have hUeq : (fun n => auxU a (F n) (G n) z) =ᶠ[atTop]
      (fun n => (r n : ℂ) * κ * Complex.exp ((r n : ℂ) * z)) := by
    filter_upwards [hpoint] with n hn
    have hd : deriv (F n) z = (r n : ℂ) * deriv fc ((r n : ℂ) * z) := by
      have hl : HasDerivAt (fun w : ℂ => (r n : ℂ) * w) (r n : ℂ) z := by
        simpa only [id_eq, mul_one] using! (hasDerivAt_id z).const_mul (r n : ℂ)
      have hh := (hn.1.differentiableAt.hasDerivAt.comp z hl).deriv
      change deriv (F n) z = deriv fc ((r n : ℂ) * z) * (r n : ℂ) at hh
      exact hh.trans (mul_comm _ _)
    have hsource := exponential_auxU_eq_at_analytic hcanon hn.1 hn.2.1 hn.2.2
    calc
      auxU a (F n) (G n) z = (r n : ℂ) * auxU a fc gc ((r n : ℂ) * z) := by
        unfold auxU
        rw [hd]
        dsimp only [F, G]
        ring
      _ = (r n : ℂ) * κ * Complex.exp ((r n : ℂ) * z) := by rw [hsource]; ring
  have hcoefficient := hUzero.congr' hUeq
  have hbase : Tendsto (fun n => r n * ‖κ‖) atTop atTop := by
    simpa only [mul_comm] using hr.const_mul_atTop (norm_pos_iff.2 h.κ_ne_zero)
  have hnorm : Tendsto (fun n => ‖(r n : ℂ) * κ * Complex.exp ((r n : ℂ) * z)‖)
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hbase
    filter_upwards [hr.eventually (eventually_ge_atTop 0)] with n hn
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn, Complex.norm_exp,
      Complex.re_ofReal_mul]
    exact le_mul_of_one_le_right (mul_nonneg hn (norm_nonneg κ))
      (Real.one_le_exp (mul_nonneg hn hz.le))
  exact not_tendsto_nhds_of_tendsto_atTop hnorm 0
    (by simpa only [norm_zero] using hcoefficient.norm)

end ThreeIM
