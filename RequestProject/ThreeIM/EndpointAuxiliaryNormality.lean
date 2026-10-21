module

public import RequestProject.ThreeIM.AuxiliaryExhaustion
public import RequestProject.ThreeIM.SphereCompanionExtraction
public import RequestProject.ThreeIM.NormalizedSpherePair
public import RequestProject.ThreeIM.SphericalAuxiliaryLimits

/-! # Constant spherical limits at an auxiliary endpoint

If U tends to a nowhere-zero entire function and V tends to zero, both
families are normal and every spherical limit is constant. Infinity is
allowed: finite anchors are a separate, necessary input in the next module.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem AuxiliaryPairOn.symm {Ω : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) :
    AuxiliaryPairOn Ω g f (fun z => -v z) (fun z => -u z) a where
  pair := h.pair.symm
  holo_u := h.holo_v.neg
  holo_v := h.holo_u.neg
  nonzero_u := fun z hz => neg_ne_zero.mpr (h.nonzero_v z hz)
  nonzero_v := fun z hz => neg_ne_zero.mpr (h.nonzero_u z hz)
  u_eq := by
    filter_upwards [h.v_eq] with z hz
    calc
      auxU a g f z = -auxV a f g z := by dsimp [auxU, auxV]; ring
      _ = -v z := congrArg Neg.neg hz
  v_eq := by
    filter_upwards [h.u_eq] with z hz
    calc
      auxV a g f z = -auxU a f g z := by dsimp [auxU, auxV]; ring
      _ = -u z := congrArg Neg.neg hz

theorem auxiliary_endpoint_pairs_locally_eventually {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a) :
    ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
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

private theorem endpoint_tlu_subsequence {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {f : X → Y} {Ω : Set X}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω := by
  intro e he z hz
  obtain ⟨t, ht, hev⟩ := h e he z hz
  exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩

/-- Both actual spherical families are normal; no finite-anchor assertion is
part of this conclusion. -/
theorem auxiliary_endpoint_isNormal {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Continuous u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ) :
    IsNormal (range (fun n => sphereGermValue (F n))) univ ∧
      IsNormal (range (fun n => sphereGermValue (G n))) univ := by
  have hloc := auxiliary_endpoint_pairs_locally_eventually hr hseq
  have hnu : TendstoLocallyUniformlyOn (fun n z => -uₙ n z) (fun z => -u z) atTop univ :=
    uniformContinuous_neg.comp_tendstoLocallyUniformlyOn huconv
  have hnv : TendstoLocallyUniformlyOn (fun n z => -vₙ n z) (fun _ => 0) atTop univ := by
    have hneg := uniformContinuous_neg.comp_tendstoLocallyUniformlyOn hvconv
    change TendstoLocallyUniformlyOn (fun n z => -vₙ n z)
      (fun _ : ℂ => -(0 : ℂ)) atTop univ at hneg
    simpa only [neg_zero] using hneg
  have hsimple (z : ℂ) (_hz : z ∈ (univ : Set ℂ))
      (he : (0 : ℂ) = -u z) : deriv (fun w => (0 : ℂ) / -u w) z ≠ 0 := by
    exact (hu0 z (neg_eq_zero.mp he.symm)).elim
  have hnG : IsNormal (range (fun n => sphereGermValue (G n))) univ :=
    auxiliary_pairs_isNormal_of_exhaustion hr (fun n => (hseq n).symm)
      continuous_const hu.neg (fun z => neg_ne_zero.mpr (hu0 z)) hnv hnu
      (fun z => hsimple z (mem_univ z))
  refine ⟨sphere_isNormal_of_forall_isNormalAt ?_, hnG⟩
  intro z
  obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hnGtail : IsNormalAt (range (fun n => sphereGermValue (G (n + N)))) z := by
    refine ⟨univ, Filter.univ_mem, hnG.of_subfamily ?_⟩
    rintro _ ⟨n, rfl⟩
    exact mem_range_self (n + N)
  have hnFtail := sphere_companion_isNormalAt
    (fun n => sphereGermValue (G (n + N))) (fun n => sphereGermValue (F (n + N)))
    hΩ (fun n => sphereHolomorphicOn_sphereGermValue hΩ
      (hN (n + N) (Nat.le_add_left N n)).pair.nonconst_g.1)
    (fun n => sphereHolomorphicOn_sphereGermValue hΩ
      (hN (n + N) (Nat.le_add_left N n)).pair.nonconst_f.1)
    (normalizedSphereTargets a) (normalizedSphereTargets_injective (hseq 0).pair.injective)
    (fun n w hw j => ((hN (n + N) (Nat.le_add_left N n)).pair.sphere_shares w hw j).symm)
    hzΩ hnGtail
  exact isNormalAt_range_of_normal_tail (fun n => sphereGermValue (F n)) N hnFtail

/-- A joint pair of nonconstant spherical limits is impossible at this
endpoint. This is a consequence of the actual limiting auxiliary equations. -/
theorem auxiliary_endpoint_nonconstant_limits_false
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H K : ℂ → OnePoint ℂ} (a : Fin 3 → ℂ)
    (hH : SphereHolomorphicOn H univ) (hK : SphereHolomorphicOn K univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hKnc : ¬ ∃ p : OnePoint ℂ, ∀ z, K z = p)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a) : False := by
  let f : ℂ → ℂ := fun z => chartFiniteMap (H z)
  let g : ℂ → ℂ := fun z => chartFiniteMap (K z)
  have hf : IsNonconstMeroOn f univ := isNonconstMeroOn_chartFiniteMap hH hHnc
  have hg : IsNonconstMeroOn g univ := isNonconstMeroOn_chartFiniteMap hK hKnc
  have hid := spherical_auxiliary_limits a hH hK hHnc hKnc hFconv hGconv hu
    (differentiable_const (0 : ℂ)) huconv hvconv (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        ⟨hn.pair.nonconst_f, hn.pair.nonconst_g, hn.holo_u.continuousOn,
          hn.holo_v.continuousOn, hn.u_eq, hn.v_eq⟩⟩)
  have hprod : (fun z => (g z - f z) * deriv g z) =ᶠ[codiscrete ℂ] (fun _ => 0) := by
    filter_upwards [hid.2, auxiliary_cubicP_ne_zero_codiscreteWithin hg a] with z hz hden
    have hzero : (f z - g z) * deriv g z = 0 := by
      simpa only [zero_mul] using (div_eq_iff hden).mp hz
    calc
      (g z - f z) * deriv g z = -((f z - g z) * deriv g z) := by ring
      _ = 0 := by rw [hzero, neg_zero]
  have heq := auxiliary_eq_of_mul_deriv_eq_zero hg hprod
  have hUlocal := auxiliary_local_of_codiscreteWithin isOpen_univ hid.1 (mem_univ (0 : ℂ))
  have heqlocal := auxiliary_local_of_codiscreteWithin isOpen_univ heq (mem_univ (0 : ℂ))
  obtain ⟨z, hzU, hzfg⟩ := (hUlocal.and heqlocal).exists
  apply hu0 z
  have hzu : auxU a f g z = u z := hzU
  rw [auxU, hzfg, sub_self, zero_mul, zero_div] at hzu
  exact hzu.symm

/-- Every spherical subsequential limit of the first member is constant.
The limit can be infinity; no finite anchor is inferred here. -/
theorem auxiliary_endpoint_spherical_limit_constant
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {H : ℂ → OnePoint ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ) :
    ∃ p : OnePoint ℂ, ∀ z, H z = p := by
  classical
  have hloc := auxiliary_endpoint_pairs_locally_eventually hr hseq
  have hH : SphereHolomorphicOn H univ :=
    sphereHolomorphicOn_univ_of_locally_eventually hFconv (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1⟩)
  by_contra hHnc
  obtain ⟨ψ, hψ, K, hK, hKnc, hGconv⟩ := exists_nonconstant_spherical_companion
    hH hHnc hFconv (normalizedSphereTargets a)
    (normalizedSphereTargets_injective (hseq 0).pair.injective) (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        ⟨sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1,
          sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_g.1,
          hn.pair.sphere_shares⟩⟩)
  exact auxiliary_endpoint_nonconstant_limits_false a hH hK hHnc hKnc
    (endpoint_tlu_subsequence hFconv hψ) hGconv hu hu0
    (endpoint_tlu_subsequence huconv hψ) (endpoint_tlu_subsequence hvconv hψ)
    (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hψ.tendsto_atTop.eventually hev⟩)

/-- Both limits in any convergent pair are constant, with infinity allowed. -/
theorem auxiliary_endpoint_spherical_limits_constant
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {H K : ℂ → OnePoint ℂ}
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ) :
    (∃ p : OnePoint ℂ, ∀ z, H z = p) ∧ (∃ q : OnePoint ℂ, ∀ z, K z = q) := by
  classical
  have hloc := auxiliary_endpoint_pairs_locally_eventually hr hseq
  refine ⟨auxiliary_endpoint_spherical_limit_constant hr hseq hu hu0 huconv hvconv hFconv, ?_⟩
  have hK : SphereHolomorphicOn K univ :=
    sphereHolomorphicOn_univ_of_locally_eventually hGconv (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_g.1⟩)
  by_contra hKnc
  obtain ⟨ψ, hψ, J, hJ, hJnc, hFJ⟩ := exists_nonconstant_spherical_companion
    hK hKnc hGconv (normalizedSphereTargets a)
    (normalizedSphereTargets_injective (hseq 0).pair.injective) (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn =>
        ⟨sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_g.1,
          sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1,
          fun w hw j => (hn.pair.sphere_shares w hw j).symm⟩⟩)
  exact hJnc (auxiliary_endpoint_spherical_limit_constant
    (hr.comp hψ.tendsto_atTop) (fun n => hseq (ψ n)) hu hu0
    (endpoint_tlu_subsequence huconv hψ) (endpoint_tlu_subsequence hvconv hψ) hFJ)

end ThreeIM
