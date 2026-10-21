module

public import RequestProject.ThreeIM.AuxPhiSphericalPoint
public import RequestProject.ThreeIM.SphereCollapsedLimits
public import RequestProject.ThreeIM.SphereCompanionExtraction
public import RequestProject.ThreeIM.NormalizedSpherePair

/-!
# Constant limits when both auxiliary coefficients vanish

A nonconstant limit would have a nonconstant companion. Vanishing
coefficients make the two limits coincide, forcing their limiting Phi to
be locally one. Simple one-points exclude that possibility. A constant
companion is also incompatible with a nonconstant first limit. Marked
shared values then determine both constants without using raw junk values.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

private theorem constant_limit_tlu_reindex {X : Type*} [UniformSpace X]
    {F : ℕ → ℂ → X} {f : ℂ → X}
    (h : TendstoLocallyUniformlyOn F f atTop univ) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop univ := by
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := h v hv x hx
  exact ⟨t, ht, hi.eventually hev⟩

theorem auxiliary_vanishing_ratio_spherical_limit_constant
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ} {φ : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hH : SphereHolomorphicOn H univ)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (huconv : TendstoLocallyUniformlyOn uₙ (fun _ => 0) atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hsimple : ∀ z, φ z = 1 → deriv φ z ≠ 0)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a) :
    ∃ p : OnePoint ℂ, ∀ z, H z = p := by
  classical
  by_contra hHnc
  obtain ⟨U₀, _, _, hseq₀⟩ := hloc 0
  obtain ⟨n₀, hn₀⟩ := hseq₀.exists
  have hinj := normalizedSphereTargets_injective hn₀.pair.injective
  have hshare : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) U ∧
        SphereHolomorphicOn (sphereGermValue (G n)) U ∧
        ∀ w ∈ U, ∀ j, (sphereGermValue (F n) w = normalizedSphereTargets a j ↔
          sphereGermValue (G n) w = normalizedSphereTargets a j) := by
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hev.mono fun n hn =>
      ⟨sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_f.1,
        sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_g.1, hn.pair.sphere_shares⟩⟩
  obtain ⟨ψ, hψ, K, hK, hKnc, hGconv⟩ := exists_nonconstant_spherical_companion
    hH hHnc hFconv (normalizedSphereTargets a) hinj hshare
  have hlocψ : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F (ψ n)) (G (ψ n)) (uₙ (ψ n)) (vₙ (ψ n)) a := by
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hψ.tendsto_atTop.eventually hev⟩
  have hFψ := constant_limit_tlu_reindex hFconv hψ.tendsto_atTop
  have heq := sphere_limits_eq_of_auxiliary_limits_zero a hH hK hHnc hKnc hFψ hGconv
    (constant_limit_tlu_reindex huconv hψ.tendsto_atTop)
    (constant_limit_tlu_reindex hvconv hψ.tendsto_atTop) (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hlocψ z
      exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.pair.nonconst_f, hn.pair.nonconst_g,
        hn.holo_u.continuousOn, hn.holo_v.continuousOn, hn.u_eq, hn.v_eq⟩⟩)
  have hGψH : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G (ψ n))) H atTop univ :=
    hGconv.congr_right (fun z _ => (heq z).symm)
  exact auxPhi_spherical_diagonal_limit_impossible_of_simple_ones a hH hHnc hFψ hGψH
    (constant_limit_tlu_reindex hRatio hψ.tendsto_atTop) hsimple hlocψ

theorem auxiliary_vanishing_ratio_spherical_pair_limits_constant
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H K : ℂ → OnePoint ℂ} {φ : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hH : SphereHolomorphicOn H univ) (hK : SphereHolomorphicOn K univ)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    (huconv : TendstoLocallyUniformlyOn uₙ (fun _ => 0) atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hsimple : ∀ z, φ z = 1 → deriv φ z ≠ 0)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a) :
    (∃ p : OnePoint ℂ, ∀ z, H z = p) ∧ (∃ q : OnePoint ℂ, ∀ z, K z = q) := by
  classical
  obtain ⟨p, hp⟩ := auxiliary_vanishing_ratio_spherical_limit_constant hH hFconv
    huconv hvconv hRatio hsimple hloc
  refine ⟨⟨p, hp⟩, ?_⟩
  by_contra hKnc
  obtain ⟨U₀, _, _, hseq₀⟩ := hloc 0
  obtain ⟨n₀, hn₀⟩ := hseq₀.exists
  have hshare : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (G n)) U ∧
        SphereHolomorphicOn (sphereGermValue (F n)) U ∧
        ∀ w ∈ U, ∀ j, (sphereGermValue (G n) w = normalizedSphereTargets a j ↔
          sphereGermValue (F n) w = normalizedSphereTargets a j) := by
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hev.mono fun n hn =>
      ⟨sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_g.1,
        sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_f.1,
        fun w hw j => (hn.pair.sphere_shares w hw j).symm⟩⟩
  obtain ⟨ψ, hψ, L, _, hLnc, hLconv⟩ := exists_nonconstant_spherical_companion
    hK hKnc hGconv (normalizedSphereTargets a)
    (normalizedSphereTargets_injective hn₀.pair.injective) hshare
  have hFψ := constant_limit_tlu_reindex hFconv hψ.tendsto_atTop
  apply hLnc
  refine ⟨p, fun z => ?_⟩
  exact (tendsto_nhds_unique (hLconv.tendsto_at (mem_univ z))
    (hFψ.tendsto_at (mem_univ z))).trans (hp z)

theorem auxiliary_marked_vanishing_ratio_spherical_limits
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H K : ℂ → OnePoint ℂ} {φ : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hH : SphereHolomorphicOn H univ) (hK : SphereHolomorphicOn K univ)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    (huconv : TendstoLocallyUniformlyOn uₙ (fun _ => 0) atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hsimple : ∀ z, φ z = 1 → deriv φ z ≠ 0)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a)
    {j : Fin 3} (hmarked : ∀ᶠ n in atTop,
      0 < mult (F n) (a j : Sphere) 0 ∧ 0 < mult (G n) (a j : Sphere) 0) :
    ∀ z, H z = (a j : OnePoint ℂ) ∧ K z = (a j : OnePoint ℂ) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := auxiliary_vanishing_ratio_spherical_pair_limits_constant
    hH hK hFconv hGconv huconv hvconv hRatio hsimple hloc
  obtain ⟨U, _, h0U, hseq⟩ := hloc 0
  have hvalues : ∀ᶠ n in atTop,
      sphereGermValue (F n) 0 = (a j : OnePoint ℂ) ∧
      sphereGermValue (G n) 0 = (a j : OnePoint ℂ) := by
    filter_upwards [hseq, hmarked] with n hn hm
    exact ⟨(mult_finite_pos_iff_sphereGermValue_eq (hn.pair.nonconst_f.1 0 h0U)
      (hn.pair.nonconst_f.2 0 h0U (a j))).mp hm.1,
      (mult_finite_pos_iff_sphereGermValue_eq (hn.pair.nonconst_g.1 0 h0U)
      (hn.pair.nonconst_g.2 0 h0U (a j))).mp hm.2⟩
  have hH0 : H 0 = (a j : OnePoint ℂ) := tendsto_nhds_unique_of_eventuallyEq
    (hFconv.tendsto_at (mem_univ 0)) tendsto_const_nhds (hvalues.mono fun n hn => hn.1)
  have hK0 : K 0 = (a j : OnePoint ℂ) := tendsto_nhds_unique_of_eventuallyEq
    (hGconv.tendsto_at (mem_univ 0)) tendsto_const_nhds (hvalues.mono fun n hn => hn.2)
  exact fun z => ⟨(hp z).trans ((hp 0).symm.trans hH0),
    (hq z).trans ((hq 0).symm.trans hK0)⟩

end ThreeIM
