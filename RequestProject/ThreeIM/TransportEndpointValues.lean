module

public import RequestProject.ThreeIM.TransportNormalFormCoordinates
public import RequestProject.ThreeIM.AffineCovariance

/-! # Honest sphere values of the regular transport endpoint forms -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_normal_form_honest_value {Ω : Set ℂ} {F : ℂ → ℂ} {c z : ℂ}
    (hF : MeromorphicOn F Ω) (hz : z ∈ Ω)
    (hNF : AnalyticAt ℂ (transportNormalF Ω F c) z) :
    sphereGermValue F z = ((transportNormalF Ω F c z + c : ℂ) : OnePoint ℂ) := by
  have hs : MeromorphicOn (fun w => F w - c) Ω :=
    fun w hw => (hF w hw).sub (MeromorphicAt.const c w)
  have hg := hs.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have he : (fun w => transportNormalF Ω F c w + c) =ᶠ[𝓝[≠] z] F := by
    filter_upwards [hg] with w hw
    change transportNormalF Ω F c w = F w - c at hw
    rw [hw, sub_add_cancel]
  have hanalytic : AnalyticAt ℂ (fun w => transportNormalF Ω F c w + c) z :=
    hNF.add analyticAt_const
  exact (sphereGermValue_congr (hF z hz) hanalytic.meromorphicAt he.symm).trans
    (sphereGermValue_eq_coe_of_analytic hanalytic)

theorem transport_shifted_normal_form_honest_value
    {Ω : Set ℂ} {F : ℂ → ℂ} {c L : ℂ}
    (hF : MeromorphicOn F Ω) (hL : L ∈ Ω)
    (hNF : AnalyticAt ℂ (transportNormalF Ω F c) L) :
    sphereGermValue (fun w => F (L + w)) 0 =
      ((transportNormalF Ω F c L + c : ℂ) : OnePoint ℂ) := by
  have hf : MeromorphicAt F (L + 1 * 0) := by simpa only [mul_zero, add_zero] using hF L hL
  have he : sphereGermValue (fun w => F (L + w)) 0 = sphereGermValue F L := by
    simpa only [one_mul, mul_zero, add_zero] using
      sphereGermValue_comp_affine 1 L 0 one_ne_zero hf
  exact he.trans (transport_normal_form_honest_value hF hL hNF)

end ThreeIM
