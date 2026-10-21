module

public import RequestProject.ThreeIM.ThetaLocal
public import RequestProject.ThreeIM.ExponentialSectorMarty

/-!
# The auxiliary invariant and spherical derivatives at simple poles

These statements use the original local meromorphic germs, including the
corrected spherical representative. The spherical derivative convention is
the one in NoWanderingDomains and has the factor two in its chart formula.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem tendsto_auxPsi_simple_pole {a : Fin 3 → ℂ} {f g F G : ℂ → ℂ} {z₀ : ℂ}
    (hFa : AnalyticAt ℂ F z₀) (hF0 : F z₀ ≠ 0)
    (hGa : AnalyticAt ℂ G z₀) (hG0 : G z₀ ≠ 0)
    (hfF : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) * F z)
    (hgG : ∀ᶠ z in 𝓝[≠] z₀, g z = (z - z₀) ^ (-1 : ℤ) * G z) :
    Tendsto (auxPsi a f g) (𝓝[≠] z₀) (𝓝 (((G z₀)⁻¹ - (F z₀)⁻¹) ^ 2)) := by
  have heq : auxPsi a f g =ᶠ[𝓝[≠] z₀]
      (fun z => poleU a F G z₀ z * -poleU a G F z₀ z) := by
    filter_upwards [auxU_simple_pole a hFa hF0 hfF hgG,
      auxU_simple_pole a hGa hG0 hgG hfF] with z h1 h2
    have hV : auxV a f g z = -auxU a g f z := by simp only [auxV, auxU]; ring
    simp only [auxPsi, hV, h1, h2]
  have hlim : Tendsto (fun z => poleU a F G z₀ z * -poleU a G F z₀ z)
      (𝓝[≠] z₀) (𝓝 (poleU a F G z₀ z₀ * -poleU a G F z₀ z₀)) :=
    ((analyticAt_poleU a hFa hF0 hGa).continuousAt.mul
      (analyticAt_poleU a hGa hG0 hFa).continuousAt.neg).tendsto.mono_left nhdsWithin_le_nhds
  have heval : poleU a F G z₀ z₀ * -poleU a G F z₀ z₀ =
      ((G z₀)⁻¹ - (F z₀)⁻¹) ^ 2 := by
    rw [poleU_self a hF0, poleU_self a hG0]
    field_simp
    ring
  rw [heval] at hlim
  exact hlim.congr' heq.symm

theorem sphericalDeriv_sphereGermValue_simple_pole {f F : ℂ → ℂ} {z₀ : ℂ}
    (hfm : MeromorphicAt f z₀) (hFa : AnalyticAt ℂ F z₀) (hF0 : F z₀ ≠ 0)
    (hfF : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) * F z) :
    sphericalDeriv (sphereGermValue f) z₀ = 2 * ‖(F z₀)⁻¹‖ := by
  let H : ℂ → ℂ := fun z => (z - z₀) / F z
  have hHa : AnalyticAt ℂ H z₀ := (analyticAt_id.sub analyticAt_const).div hFa hF0
  have hH0 : H z₀ = 0 := by simp [H]
  have hHD : deriv H z₀ = (F z₀)⁻¹ := by
    have h := (((hasDerivAt_id z₀).sub_const z₀).div hFa.differentiableAt.hasDerivAt hF0).deriv
    change deriv H z₀ = _ at h
    rw [h]
    simp only [id_eq, sub_self, zero_mul, one_mul, sub_zero]
    field_simp
  have hpunct : (fun z => inversionGL • sphereGermValue f z) =ᶠ[𝓝[≠] z₀]
      (fun z => (H z : OnePoint ℂ)) := by
    filter_upwards [hfm.eventually_analyticAt, hfF,
      nhdsWithin_le_nhds (hFa.continuousAt.eventually_ne hF0), self_mem_nhdsWithin]
      with z hz hrep hFz hzz
    have ht : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
    have hfz : f z ≠ 0 := by rw [hrep]; exact mul_ne_zero (zpow_ne_zero _ ht) hFz
    rw [sphereGermValue_eq_coe_of_analytic hz, inversionGL_smul_coe, if_neg hfz]
    congr 1
    rw [hrep]
    simp only [H, zpow_neg, zpow_one]
    field_simp
  have hc : ContinuousAt (fun z => inversionGL • sphereGermValue f z) z₀ :=
    (continuous_gl_smul inversionGL).continuousAt.comp (continuousAt_sphereGermValue hfm)
  have heq := (hc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (OnePoint.continuous_coe.continuousAt.comp hHa.continuousAt)).mp hpunct
  have hsd := sphericalDeriv_eq_of_eventuallyEq_coe heq hHa.differentiableAt
  rw [sphericalDeriv_inversionGL_smul, hH0, hHD] at hsd
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, div_one] using hsd

theorem kappa_norm_le_sphericalDeriv_sum_at_simple_pole
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {z₀ κ : ℂ} (hf : meromorphicOrderAt f z₀ = -1)
    (hψ : auxPsi a f g =ᶠ[𝓝[≠] z₀] fun _ => κ ^ 2) :
    ‖κ‖ ≤ (sphericalDeriv (sphereGermValue f) z₀ +
      sphericalDeriv (sphereGermValue g) z₀) / 2 := by
  have hfm := hp.nonconst_f.1 z₀ (mem_univ z₀)
  have hgm := hp.nonconst_g.1 z₀ (mem_univ z₀)
  have hf' : meromorphicOrderAt f z₀ = ((-1 : ℤ) : WithTop ℤ) := by rw [hf]; rfl
  have hg' : meromorphicOrderAt g z₀ = ((-1 : ℤ) : WithTop ℤ) := by
    rw [order_g_at_pole hp (mem_univ z₀) (k := 1) le_rfl (by rw [hf]; rfl)]; rfl
  obtain ⟨F, hFa, hF0, hfF⟩ := exists_simple_pole_form hfm hf'
  obtain ⟨G, hGa, hG0, hgG⟩ := exists_simple_pole_form hgm hg'
  have hlim := tendsto_auxPsi_simple_pole (a := a) hFa hF0 hGa hG0 hfF hgG
  have hsquare : κ ^ 2 = ((G z₀)⁻¹ - (F z₀)⁻¹) ^ 2 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hψ.symm) hlim
  have hnorm := congrArg norm hsquare
  simp only [norm_pow] at hnorm
  have hn : ‖κ‖ = ‖(G z₀)⁻¹ - (F z₀)⁻¹‖ := by
    nlinarith [norm_nonneg κ, norm_nonneg ((G z₀)⁻¹ - (F z₀)⁻¹)]
  rw [sphericalDeriv_sphereGermValue_simple_pole hfm hFa hF0 hfF,
    sphericalDeriv_sphereGermValue_simple_pole hgm hGa hG0 hgG, hn]
  have hb := norm_sub_le ((G z₀)⁻¹) ((F z₀)⁻¹)
  linarith

end ThreeIM
