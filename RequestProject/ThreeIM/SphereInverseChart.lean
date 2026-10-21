module

public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-! # Original pole multiplicities in the actual spherical inverse chart -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem chartFiniteMap_inversionGL (p : OnePoint ℂ) :
    chartFiniteMap (inversionGL • p) = chartInftyMap p := by
  cases p with
  | infty => rw [inversionGL_smul_infty]; rfl
  | coe c =>
    rw [inversionGL_smul_coe]
    split_ifs with hc
    · simp only [hc, chartFiniteMap, chartInftyMap, inv_zero]
    · rfl

theorem inverseChart_sphereGermValue_eventuallyEq {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) :
    (fun w => chartFiniteMap (inversionGL • sphereGermValue f w)) =ᶠ[𝓝[≠] z]
      (fun w => (f w)⁻¹) := by
  filter_upwards [hf.eventually_analyticAt] with w hw
  rw [chartFiniteMap_inversionGL, sphereGermValue_eq_coe_of_analytic hw]
  rfl

theorem inverseChart_sphereGermValue_order {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) :
    meromorphicOrderAt (fun w => chartFiniteMap (inversionGL • sphereGermValue f w)) z =
      -meromorphicOrderAt f z := by
  rw [meromorphicOrderAt_congr (inverseChart_sphereGermValue_eventuallyEq hf)]
  change meromorphicOrderAt f⁻¹ z = _
  exact meromorphicOrderAt_inv

theorem inverseChart_sphereGermValue_mult {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) :
    mult (fun w => chartFiniteMap (inversionGL • sphereGermValue f w))
      ((0 : ℂ) : Sphere) z = mult f ⊤ z := by
  simp only [mult_coe, mult_top, sub_zero, inverseChart_sphereGermValue_order hf]

theorem inverseChart_sphereGermValue_finite {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    meromorphicOrderAt (fun w => chartFiniteMap (inversionGL • sphereGermValue f w)) z ≠ ⊤ := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hfinite
  rw [inverseChart_sphereGermValue_order hf, ← hk, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact WithTop.coe_ne_top

end ThreeIM
