module

public import RequestProject.ThreeIM.AuxiliaryExhaustion
public import RequestProject.ThreeIM.AuxiliaryLimitPair
public import RequestProject.ThreeIM.SphereCompanionExtraction
public import RequestProject.ThreeIM.NormalizedSpherePair
public import RequestProject.ThreeIM.SphericalAuxiliaryLimits

/-! # Extracting a marked pair with its prescribed auxiliary functions -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem auxiliary_marked_extraction {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ}
    (hm : 2 ≤ m) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    (marked_F : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (marked_G : ∀ n, mult (G n) (a j : Sphere) 0 = m)
    {u v : ℂ → ℂ} (hu : Differentiable ℂ u) (hv : Differentiable ℂ v)
    (hu0 : ∀ s, u s ≠ 0) (hv0 : ∀ s, v s ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop univ)
    (hφ : ∀ s, u s = v s → deriv (fun w => u w / v w) s ≠ 0) :
    ∃ f g : ℂ → ℂ, NormalizedPair univ f g a ∧
      (auxU a f g =ᶠ[codiscrete ℂ] u) ∧
      (auxV a f g =ᶠ[codiscrete ℂ] v) ∧ IsDefect f g (a j : Sphere) 0 := by
  classical
  have hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a := by
    intro z
    refine ⟨ball z 1, isOpen_ball, mem_ball_self (by norm_num), ?_⟩
    filter_upwards [hr.eventually (eventually_ge_atTop (‖z‖ + 1))] with n hn
    apply (hseq n).restrict
    intro w hw
    rw [mem_ball_zero_iff]
    have hwz : ‖w - z‖ < 1 := mem_ball_iff_norm.mp hw
    have hnorm := norm_sub_norm_le w z
    linarith
  have hlocI (i : ℕ → ℕ) (hi : StrictMono i) :
      ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
        ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F (i n)) (G (i n)) (uₙ (i n)) (vₙ (i n)) a := by
    intro z
    obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
    exact ⟨Ω, hΩ, hzΩ, hi.tendsto_atTop.eventually hev⟩
  have hnormal := auxiliary_pairs_isNormal_of_exhaustion hr hseq
    hu.continuous hv.continuous hv0 huconv hvconv hφ
  obtain ⟨φ, hφmono, H, hFconv⟩ := hnormal
    (fun n => ⟨sphereGermValue (F n), mem_range_self n⟩)
  have hH : SphereHolomorphicOn H univ :=
    sphereHolomorphicOn_univ_of_locally_eventually hFconv (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hlocI φ hφmono z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1⟩)
  have huφ : TendstoLocallyUniformlyOn (fun n => uₙ (φ n)) u atTop univ := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := huconv e he z hz
    exact ⟨t, ht, hφmono.tendsto_atTop.eventually hev⟩
  obtain ⟨Ω₀, hΩ₀, h0Ω₀, hseq₀⟩ := hlocI φ hφmono 0
  have hmarked := marked_spherical_limit_nonconstant hΩ₀ h0Ω₀ hm hseq₀
    (fun n => marked_F (φ n)) (fun n => marked_G (φ n))
    (sphereHolomorphicOn_of_eventually hΩ₀
      (hseq₀.mono fun n hn => sphereHolomorphicOn_sphereGermValue hΩ₀ hn.pair.nonconst_f.1)
      (hFconv.mono (subset_univ Ω₀))) (hFconv.mono (subset_univ Ω₀))
    (huφ.mono (subset_univ Ω₀)) (hu0 0)
  obtain ⟨ψ, hψ, K, hK, hKnc, hGconv⟩ := exists_nonconstant_spherical_companion
    hH hmarked.2.2.2 hFconv (normalizedSphereTargets a)
    (normalizedSphereTargets_injective (hseq 0).pair.injective) (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hlocI φ hφmono z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        ⟨sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1,
          sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_g.1,
          hn.pair.sphere_shares⟩⟩)
  let σ : ℕ → ℕ := φ ∘ ψ
  have hσ : StrictMono σ := hφmono.comp hψ
  have hFσ : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F (σ n))) H atTop univ := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := hFconv e he z hz
    exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩
  have huσ : TendstoLocallyUniformlyOn (fun n => uₙ (σ n)) u atTop univ := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := huconv e he z hz
    exact ⟨t, ht, hσ.tendsto_atTop.eventually hev⟩
  have hvσ : TendstoLocallyUniformlyOn (fun n => vₙ (σ n)) v atTop univ := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := hvconv e he z hz
    exact ⟨t, ht, hσ.tendsto_atTop.eventually hev⟩
  let f : ℂ → ℂ := fun z => chartFiniteMap (H z)
  let g : ℂ → ℂ := fun z => chartFiniteMap (K z)
  have hf := isNonconstMeroOn_chartFiniteMap hH hmarked.2.2.2
  have hg := isNonconstMeroOn_chartFiniteMap hK hKnc
  have hmf : mult f (a j : Sphere) 0 = 1 := by
    apply marked_mult_one_of_analytic
      (analyticAt_chartFiniteMap_of_ne_infty hH (mem_univ 0)
        (by rw [hmarked.1]; exact OnePoint.coe_ne_infty _))
      (by simp only [hmarked.1, chartFiniteMap]) hmarked.2.2.1
  obtain ⟨Ω₁, hΩ₁, h0Ω₁, hseq₁⟩ := hlocI σ hσ 0
  have hmg := (marked_mult_ge_of_spherical_limit hΩ₁ h0Ω₁ hK hKnc
    (hGconv.mono (subset_univ Ω₁)) (hseq₁.mono fun n hn => hn.pair.nonconst_g)
    (by omega : 0 < m) (fun n => marked_G (σ n))).2
  have hdef : IsDefect f g (a j : Sphere) 0 := by
    change 0 < mult f (a j : Sphere) 0 ∧
      0 < mult g (a j : Sphere) 0 ∧ mult f (a j : Sphere) 0 ≠ mult g (a j : Sphere) 0
    rw [hmf]
    change 0 < 1 ∧ 0 < mult g (a j : Sphere) 0 ∧ 1 ≠ mult g (a j : Sphere) 0
    dsimp only [g] at *
    omega
  have hFrep : sphereGermValue f = H := funext fun z =>
    sphereGermValue_chartFiniteMap hH hmarked.2.2.2 z
  have hGrep : sphereGermValue g = K := funext fun z =>
    sphereGermValue_chartFiniteMap hK hKnc z
  have hpair := normalizedPair_of_spherical_limits_and_defect hf hg
    (hseq 0).pair.injective (by rw [hFrep]; exact hFσ) (by rw [hGrep]; exact hGconv)
    (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hlocI σ hσ z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn => hn.pair⟩) hdef
  have haux := spherical_auxiliary_limits a hH hK hmarked.2.2.2 hKnc hFσ hGconv
    hu hv huσ hvσ (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hlocI σ hσ z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        ⟨hn.pair.nonconst_f, hn.pair.nonconst_g, hn.holo_u.continuousOn,
          hn.holo_v.continuousOn, hn.u_eq, hn.v_eq⟩⟩)
  exact ⟨f, g, hpair, haux.1, haux.2, hdef⟩

end ThreeIM
