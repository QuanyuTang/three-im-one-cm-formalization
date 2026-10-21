module

public import RequestProject.ThreeIM.ExponentialHullCompactness
public import RequestProject.ThreeIM.EndpointAuxiliaryNormality
public import NoWanderingDomains.Sphere.InversionIsometry
public import RequestProject.ThreeIM.ExponentialData
public import RequestProject.ThreeIM.AuxiliaryLimitPair
public import RequestProject.ThreeIM.SphericalAuxiliaryLimits

/-! # Honest spherical bounds and recovery of exponential hull pairs -/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem real_stable_arguments_uniform_small {μ : ℝ} (hμ : 0 < μ) (C : ℂ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      ‖(Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))‖ < δ := by
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun r : ℝ => ‖C‖ * Real.exp (-(μ * r))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      tendsto_const_nhds.mul (h1.comp (tendsto_id.const_mul_atTop hμ))
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (((tendsto_order.mp h1).2 δ hδ).and ((tendsto_order.mp h2).2 δ hδ))
  refine ⟨R, ?_⟩
  intro z hz
  rw [Prod.norm_def, max_lt_iff]
  constructor
  · simpa only [Complex.norm_exp, Complex.neg_re] using (hR z.re hz).1
  · have hre : (-(μ : ℂ) * z).re = -(μ * z.re) := by simp [Complex.mul_re]
    simpa only [norm_mul, Complex.norm_exp, hre] using (hR z.re hz).2

theorem real_stable_model_eventually_analytic
    {K : ℂ × ℂ → ℂ} (hK : AnalyticAt ℂ K 0)
    {μ : ℝ} (hμ : 0 < μ) (C : ℂ) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re → AnalyticAt ℂ
      (fun w => K (Complex.exp (-w), C * Complex.exp (-(μ : ℂ) * w))) z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hK.eventually_analyticAt
  obtain ⟨R, hR⟩ := real_stable_arguments_uniform_small hμ C hδ
  refine ⟨R, fun z hz => ?_⟩
  have hKz : AnalyticAt ℂ K (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)) :=
    hball (by simpa only [mem_ball, dist_zero_right] using hR z hz)
  have harg : AnalyticAt ℂ
      (fun w : ℂ => (Complex.exp (-w), C * Complex.exp (-(μ : ℂ) * w))) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w)) z).prod
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => C * Complex.exp (-(μ : ℂ) * w)) z)
  exact hKz.fun_comp (f := fun w : ℂ =>
    (Complex.exp (-w), C * Complex.exp (-(μ : ℂ) * w))) (x := z) harg

/-- Both explicit meromorphic models are defined on the same actual
half-plane. This supplies the model side of continuation from a real
tail, before any equality with the original pair has been established. -/
theorem real_stable_models_meromorphic_on_halfplane
    {H V : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (hV : AnalyticAt ℂ V 0)
    (hH0 : H 0 = 0) {μ : ℝ} (hμ : 0 < μ) (C a : ℂ) :
    ∃ R : ℝ,
      MeromorphicOn (fun z => a + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)))
        {z : ℂ | R < z.re} ∧
      MeromorphicOn (fun z => (Complex.exp (-z) *
        V (Complex.exp (-z), H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))))⁻¹)
        {z : ℂ | R < z.re} := by
  have hA : AnalyticAt ℂ (fun u => a + H u) 0 := analyticAt_const.add hH
  have hB : AnalyticAt ℂ (fun u : ℂ × ℂ => u.1 * V (u.1, H u)) 0 := by
    have harg : AnalyticAt ℂ (fun u : ℂ × ℂ => (u.1, H u)) 0 :=
      analyticAt_fst.prod hH
    have hVat : AnalyticAt ℂ V ((0 : ℂ × ℂ).1, H 0) := by
      rw [hH0, Prod.fst_zero]
      exact hV
    exact analyticAt_fst.mul
      (hVat.fun_comp (f := fun u : ℂ × ℂ => (u.1, H u)) (x := 0) harg)
  obtain ⟨RA, hRA⟩ := real_stable_model_eventually_analytic hA hμ C
  obtain ⟨RB, hRB⟩ := real_stable_model_eventually_analytic hB hμ C
  refine ⟨max RA RB, ?_, ?_⟩
  · intro z hz
    exact (hRA z ((le_max_left RA RB).trans hz.le)).meromorphicAt
  · intro z hz
    exact (hRB z ((le_max_right RA RB).trans hz.le)).meromorphicAt.inv

/-- A continuous model at the origin and the actual codiscrete formula
give uniform closed bounds for the honest sphere value of a meromorphic
function throughout a far right half-plane. -/
theorem sphereGermValue_right_bounds_of_real_stable_model
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    {K : ℂ × ℂ → ℂ} (hK : ContinuousAt K 0)
    {μ : ℝ} (hμ : 0 < μ) (C : ℂ) {R₀ : ℝ}
    (heq : ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
      f z = K (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue f z) (K 0 : OnePoint ℂ) ≤ ε := by
  intro ε hε
  have hKc : ContinuousAt (fun u : ℂ × ℂ => (K u : OnePoint ℂ)) 0 :=
    OnePoint.continuous_coe.continuousAt.comp hK
  have hnear : {u : ℂ × ℂ | dist (K u : OnePoint ℂ) (K 0 : OnePoint ℂ) < ε} ∈ 𝓝 0 :=
    hKc.tendsto.eventually (ball_mem_nhds (K 0 : OnePoint ℂ) hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨S, hS⟩ := real_stable_arguments_uniform_small hμ C hδ
  refine ⟨max R₀ S + 1, ?_⟩
  intro z hz
  have hzmax : max R₀ S < z.re := by linarith
  have hzΩ : R₀ < z.re := (le_max_left R₀ S).trans_lt hzmax
  have hd := (mem_codiscreteWithin.1 heq) z hzΩ
  rw [disjoint_principal_right] at hd
  have hRe : {w : ℂ | max R₀ S < w.re} ∈ 𝓝[≠] z :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzmax)
  apply le_of_tendsto ((tendsto_sphereGermValue (hf z (mem_univ z))).dist tendsto_const_nhds)
  filter_upwards [hd, hRe] with w hw hwr
  have hweq : f w = K (Complex.exp (-w), C * Complex.exp (-(μ : ℂ) * w)) := by
    by_contra hne
    exact hw ⟨(le_max_left R₀ S).trans_lt hwr, hne⟩
  rw [hweq]
  have harg : (Complex.exp (-w), C * Complex.exp (-(μ : ℂ) * w)) ∈
      ball (0 : ℂ × ℂ) δ := by
    simpa only [mem_ball, dist_zero_right] using hS w ((le_max_right R₀ S).trans hwr.le)
  exact (hball harg).le

theorem sphereGermValue_inv_of_order_ne_top {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    sphereGermValue (fun w => (f w)⁻¹) z = inversionGL • sphereGermValue f z := by
  have ht := ((continuous_gl_smul inversionGL).tendsto (sphereGermValue f z)).comp
    (tendsto_sphereGermValue hf)
  have heq : (fun w => inversionGL • (f w : OnePoint ℂ)) =ᶠ[𝓝[≠] z]
      (fun w => (((f w)⁻¹ : ℂ) : OnePoint ℂ)) := by
    filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp hfinite]
      with w hw
    rw [inversionGL_smul_coe, if_neg hw]
  exact (tendsto_nhds_unique (ht.congr' heq) (tendsto_sphereGermValue hf.inv)).symm

theorem right_infinity_bounds_of_inverse_bounds {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      dist (sphereGermValue (fun w => (f w)⁻¹) z) (0 : ℂ) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      dist (sphereGermValue f z) OnePoint.infty ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hbound ε hε
  refine ⟨R, ?_⟩
  intro z hz
  have hfinite : meromorphicOrderAt f z ≠ ⊤ := by
    simpa only [sub_zero] using hf.2 z (mem_univ z) 0
  have hi := sphericalDist_inversionGL_smul (sphereGermValue f z) OnePoint.infty
  change dist (inversionGL • sphereGermValue f z) (inversionGL • OnePoint.infty) =
    dist (sphereGermValue f z) OnePoint.infty at hi
  rw [inversionGL_smul_infty,
    ← sphereGermValue_inv_of_order_ne_top (hf.1 z (mem_univ z)) hfinite] at hi
  exact hi ▸ hR z hz

/-- This uses the real-exponent version of the original two formulae;
no rationality, periodicity or whole-half-plane analyticity is assumed. -/
theorem ExponentialPair.right_bounds_of_real_stable_formula
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {j : Fin 3} {μ : ℝ} (hμ : 0 < μ)
    (C : ℂ) {H V : ℂ × ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (hV : AnalyticAt ℂ V 0) (hH0 : H 0 = 0)
    {R₀ : ℝ}
    (heq : ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
      f z = a j + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)) ∧
      (g z)⁻¹ = Complex.exp (-z) *
        V (Complex.exp (-z), H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)))) :
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      dist (sphereGermValue f z) (a j : OnePoint ℂ) ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      dist (sphereGermValue g z) OnePoint.infty ≤ ε) := by
  constructor
  · have hb := sphereGermValue_right_bounds_of_real_stable_model h.pair.nonconst_f.1
      (continuousAt_const.add hH.continuousAt) hμ C (heq.mono fun _ hz => hz.1)
    simpa only [Pi.add_apply, hH0, add_zero] using hb
  · apply right_infinity_bounds_of_inverse_bounds h.pair.nonconst_g
    have harg : ContinuousAt (fun u : ℂ × ℂ => (u.1, H u)) 0 :=
      continuousAt_fst.prodMk hH.continuousAt
    have hcomp : ContinuousAt (fun u : ℂ × ℂ => u.1 * V (u.1, H u)) 0 := by
      have hVat : ContinuousAt V ((0 : ℂ × ℂ).1, H 0) := by
        rw [hH0, Prod.fst_zero]
        exact hV.continuousAt
      exact continuousAt_fst.mul
        (hVat.comp' (f := fun u : ℂ × ℂ => (u.1, H u)) (x := 0) harg)
    have hb := sphereGermValue_right_bounds_of_real_stable_model
      (fun z _ => (h.pair.nonconst_g.1 z (mem_univ z)).inv)
      hcomp hμ C (heq.mono fun _ hz => hz.2)
    have hginv : g⁻¹ = (fun w => (g w)⁻¹) := by funext w; rfl
    simpa only [Prod.fst_zero, zero_mul, hginv] using hb

theorem ExponentialPair.reflect_swap {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) :
    ExponentialPair a (fun z => g (-z)) (fun z => f (-z)) κ := by
  have hc := (h.toAuxiliaryPair.comp_affine (-1) 0 (by norm_num)
    (fun _ _ => mem_univ _ : MapsTo (fun w : ℂ => 0 + -1 * w) univ univ)).symm
  have hs : AuxiliaryPairOn univ (fun z => g (-z)) (fun z => f (-z))
      (fun z => κ * Complex.exp z) (fun z => κ * Complex.exp (-z)) a := by
    simpa only [zero_add, neg_one_mul, neg_neg] using hc
  exact ⟨hs.pair, h.κ_ne_zero, hs.u_eq, hs.v_eq⟩

theorem left_sphere_bounds_of_reflected_right {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) {p : OnePoint ℂ}
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re →
      dist (sphereGermValue (fun w => f (-w)) z) p ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, z.re ≤ -R →
      dist (sphereGermValue f z) p ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hRight ε hε
  refine ⟨R, ?_⟩
  intro z hz
  have he := sphereGermValue_comp_affine (f := f) (-1) 0 (-z) (by norm_num)
    (hf _ (mem_univ _))
  have hpoint : sphereGermValue (fun w => f (-w)) (-z) = sphereGermValue f z := by
    simpa only [zero_add, neg_one_mul, neg_neg] using he
  rw [← hpoint]
  exact hR (-z) (by simpa only [Complex.neg_re, neg_neg] using neg_le_neg hz)

end ThreeIM

end

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem distinct_germs_of_nonzero_auxU
    {a : Fin 3 → ℂ} {f g u : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hU : auxU a f g =ᶠ[codiscrete ℂ] u) (hu : ∀ z, u z ≠ 0) :
    ∀ z : ℂ, meromorphicOrderAt (fun w => f w - g w) z ≠ ⊤ := by
  intro z htop
  have heq : f =ᶠ[𝓝[≠] z] g :=
    (meromorphicOrderAt_eq_top_iff.mp htop).mono fun w hw => sub_eq_zero.mp hw
  have hglobal := auxiliary_globalize_identity
    (fun w => hf w (mem_univ w)) (fun w => hg w (mem_univ w)) heq
  have heqGlobal : f =ᶠ[codiscrete ℂ] g := hglobal
  obtain ⟨w, hw, hUw⟩ :=
    (eventually_nhdsNE_of_codiscrete (heqGlobal.and hU) (0 : ℂ)).exists
  apply hu w
  rw [← hUw]
  simp only [auxU, hw, sub_self, zero_mul, zero_div]

theorem normalizedPair_of_spherical_limits_of_nonzero_auxU
    {F G : ℕ → ℂ → ℂ} {f g u : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (ha : Function.Injective a)
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (sphereGermValue f) atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (sphereGermValue g) atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, NormalizedPair U (F n) (G n) a)
    (hU : auxU a f g =ᶠ[codiscrete ℂ] u) (hu : ∀ z, u z ≠ 0) :
    NormalizedPair univ f g a := by
  refine ⟨hf, hg,
    fun z _ => distinct_germs_of_nonzero_auxU hf.1 hg.1 hU hu z, ha, ?_, ?_⟩
  · intro j
    apply sharesIMOn_of_spherical_limits hf hg (a j : Sphere) hF hG
    intro z
    obtain ⟨U, hUo, hzU, hev⟩ := hloc z
    exact ⟨U, hUo, hzU, hev.mono fun n hn => ⟨hn.nonconst_f, hn.nonconst_g, hn.im j⟩⟩
  · apply sharesCMOn_top_of_spherical_limits hf hg hF hG
    intro z
    obtain ⟨U, hUo, hzU, hev⟩ := hloc z
    exact ⟨U, hUo, hzU, hev.mono fun n hn => ⟨hn.nonconst_f, hn.nonconst_g, hn.cm_top⟩⟩

private theorem hull_pair_fixed_coeff_tlu (u : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => u) u atTop univ := by
  intro e he z _
  exact ⟨univ, Filter.univ_mem, Eventually.of_forall
    (fun _ _ _ => refl_mem_uniformity he)⟩

/-- Nonconstant actual spherical limits of same-coefficient exponential
pairs again form an exponential pair. Nonconstancy is the only limit
nondegeneracy input: distinctness is derived from the nonzero coefficient,
and finite IM and pole CM sharing are passed through the true sphere germs.
-/
theorem ExponentialPair.of_spherical_limits
    {a : Fin 3 → ℂ} {F G : ℕ → ℂ → ℂ} {κ : ℂ}
    (hseq : ∀ n, ExponentialPair a (F n) (G n) κ)
    {H K : ℂ → OnePoint ℂ}
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hKnc : ¬ ∃ p : OnePoint ℂ, ∀ z, K z = p) :
    ExponentialPair a (fun z => chartFiniteMap (H z)) (fun z => chartFiniteMap (K z)) κ := by
  have hH : SphereHolomorphicOn H univ :=
    sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun n =>
        sphereHolomorphicOn_sphereGermValue isOpen_univ (hseq n).pair.nonconst_f.1) hF
  have hK : SphereHolomorphicOn K univ :=
    sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun n =>
        sphereHolomorphicOn_sphereGermValue isOpen_univ (hseq n).pair.nonconst_g.1) hG
  have hf := isNonconstMeroOn_chartFiniteMap hH hHnc
  have hg := isNonconstMeroOn_chartFiniteMap hK hKnc
  have hFrep : sphereGermValue (fun z => chartFiniteMap (H z)) = H :=
    funext (sphereGermValue_chartFiniteMap hH hHnc)
  have hGrep : sphereGermValue (fun z => chartFiniteMap (K z)) = K :=
    funext (sphereGermValue_chartFiniteMap hK hKnc)
  have haux := spherical_auxiliary_limits a hH hK hHnc hKnc hF hG
    (uₙ := fun _ z => κ * Complex.exp z) (vₙ := fun _ z => κ * Complex.exp (-z))
    (by fun_prop) (by fun_prop)
    (hull_pair_fixed_coeff_tlu (fun z => κ * Complex.exp z))
    (hull_pair_fixed_coeff_tlu (fun z => κ * Complex.exp (-z))) (fun z => by
      refine ⟨univ, isOpen_univ, mem_univ z, Eventually.of_forall fun n => ?_⟩
      exact ⟨(hseq n).pair.nonconst_f, (hseq n).pair.nonconst_g,
        by fun_prop, by fun_prop,
        (hseq n).eq_U, (hseq n).eq_V⟩)
  have hpair := normalizedPair_of_spherical_limits_of_nonzero_auxU hf hg
    (hseq 0).pair.injective (F := F) (G := G)
    (by rw [hFrep]; exact hF) (by rw [hGrep]; exact hG)
    (fun z => ⟨univ, isOpen_univ, mem_univ z,
      Eventually.of_forall fun n => (hseq n).pair⟩)
    haux.1 (fun z => mul_ne_zero (hseq 0).κ_ne_zero (Complex.exp_ne_zero z))
  exact ⟨hpair, (hseq 0).κ_ne_zero, haux.1, haux.2⟩

/-- With the same first member and the same nonzero auxiliary coefficient,
the second member is already determined as a meromorphic germ. -/
theorem ExponentialPair.companion_eq_codiscrete
    {a : Fin 3 → ℂ} {f g₁ g₂ : ℂ → ℂ} {κ : ℂ}
    (h₁ : ExponentialPair a f g₁ κ) (h₂ : ExponentialPair a f g₂ κ) :
    g₁ =ᶠ[codiscrete ℂ] g₂ := by
  filter_upwards [h₁.eq_U, h₂.eq_U] with z hz₁ hz₂
  let d : ℂ := deriv f z / cubicP a (f z)
  have he₁ : (f z - g₁ z) * d = κ * Complex.exp z := by
    simpa only [auxU, mul_div_assoc, d] using hz₁
  have he₂ : (f z - g₂ z) * d = κ * Complex.exp z := by
    simpa only [auxU, mul_div_assoc, d] using hz₂
  have hd : d ≠ 0 := by
    intro hd
    exact (mul_ne_zero h₁.κ_ne_zero (Complex.exp_ne_zero z))
      (by simpa only [hd, mul_zero] using he₁.symm)
  have hs : f z - g₁ z = f z - g₂ z := mul_right_cancel₀ hd (he₁.trans he₂.symm)
  exact sub_right_inj.mp hs

theorem ExponentialPair.companion_sphere_eq
    {a : Fin 3 → ℂ} {f g₁ g₂ : ℂ → ℂ} {κ : ℂ}
    (h₁ : ExponentialPair a f g₁ κ) (h₂ : ExponentialPair a f g₂ κ) :
    sphereGermValue g₁ = sphereGermValue g₂ := by
  funext z
  exact sphereGermValue_congr (h₁.pair.nonconst_g.1 z (mem_univ z))
    (h₂.pair.nonconst_g.1 z (mem_univ z))
    (eventually_nhdsNE_of_codiscrete (h₁.companion_eq_codiscrete h₂) z)

end ThreeIM

end
