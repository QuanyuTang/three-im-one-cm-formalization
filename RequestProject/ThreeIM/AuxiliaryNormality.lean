module

public import RequestProject.ThreeIM.AuxiliaryFiberInjectivity
public import RequestProject.ThreeIM.AuxPhiSphericalDiagonal
public import RequestProject.ThreeIM.SphereCollapsedLimits
public import RequestProject.ThreeIM.SphereCompanionExtraction
public import RequestProject.ThreeIM.SphereRescaleIndices
public import RequestProject.ThreeIM.SphereTwoFibers
public import RequestProject.ThreeIM.SphericalAffineLimits
public import RequestProject.ThreeIM.ComplexRescaleLimits
public import RequestProject.ThreeIM.NormalizedSpherePair

/-!
# Normality from zero-free auxiliary coefficients and simple one-points

A hypothetical Zalcman bubble has a nonconstant companion. Vanishing scaled
coefficients force their limits to agree, and the canceled derivative formula
forces the original auxiliary quotient to take the value one at the center.
Its simple one-point gives local injectivity. The bubble has two finite shared
preimages in a bounded disk, whereas this injectivity permits at most one.
All holomorphy and sharing assertions concern the actual eventual source disks.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

private theorem auxiliary_tlu_reindex {X : Type*} [UniformSpace X]
    {F : ℕ → ℂ → X} {f : ℂ → X} {Ω : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop Ω := by
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := h v hv x hx
  exact ⟨t, ht, hi.eventually hev⟩

private theorem auxiliary_eventual_close_one {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hf : ContinuousAt f z₀) (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    (hfz : f z₀ = 1) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧
      ∀ᶠ n in atTop, ∀ w ∈ ball z₀ r, ‖F n w - 1‖ < (1 : ℝ) / 2 := by
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hconv
    ((1 : ℝ) / 4) (by norm_num) z₀ hz₀
  rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hz₀)] at ht
  have hnear : {w | ‖f w - 1‖ < (1 : ℝ) / 4} ∈ 𝓝 z₀ := by
    have hn := hf.tendsto.eventually (ball_mem_nhds (f z₀) (by norm_num : 0 < (1 : ℝ) / 4))
    simpa only [hfz, mem_ball, dist_eq_norm, Filter.Eventually] using hn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hΩ.mem_nhds hz₀) (inter_mem ht hnear))
  refine ⟨r, hr, fun w hw => (hball hw).1, ?_⟩
  filter_upwards [hev] with n hn w hw
  have h1 : ‖F n w - f w‖ < (1 : ℝ) / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn w (hball hw).2.1
  have h2 := (hball hw).2.2
  change ‖f w - 1‖ < (1 : ℝ) / 4 at h2
  calc
    ‖F n w - 1‖ = ‖(F n w - f w) + (f w - 1)‖ := by congr 1; ring
    _ ≤ ‖F n w - f w‖ + ‖f w - 1‖ := norm_add_le _ _
    _ < (1 : ℝ) / 2 := by linarith

theorem auxiliary_pairs_isNormalAt {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    {u v : ℂ → ℂ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hv0 : ∀ z ∈ Ω, v z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop Ω)
    (hsimple : ∀ z ∈ Ω, u z = v z → deriv (fun w => u w / v w) z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    IsNormalAt (range (fun n => sphereGermValue (F n))) z₀ := by
  classical
  by_contra hnot
  have hhol : ∀ Q ∈ range (fun n => sphereGermValue (F n)), SphereHolomorphicOn Q Ω := by
    rintro Q ⟨n, rfl⟩
    exact sphereHolomorphicOn_sphereGermValue hΩ (hseq n).pair.nonconst_f.1
  obtain ⟨Q, z, ρ, H, hQ, hz, hρpos, hρ, hH, hH0, _, hQconv⟩ :=
    exists_zalcman_rescale hΩ hhol hz₀ hnot
  have hHnc : ¬ ∃ p : OnePoint ℂ, ∀ w, H w = p := by
    rintro ⟨p, hp⟩
    have he : H = fun _ => p := funext hp
    have hd := sphericalDeriv_const p 0
    rw [← he, hH0] at hd
    exact one_ne_zero hd
  choose i hi using hQ
  have hFconv₀ : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue (F (i n)) (z n + (ρ n : ℂ) * w)) H atTop univ := by
    apply hQconv.congr
    intro n w _
    exact (congrFun (hi n) (z n + (ρ n : ℂ) * w)).symm
  have hit : Tendsto i atTop atTop := rescale_indices_tendsto_atTop
    (fun n => continuousAt_sphereGermValue ((hseq n).pair.nonconst_f.1 z₀ hz₀))
    hHnc hz hρ hFconv₀
  have hρne : ∀ n, ρ n ≠ 0 := fun n => (hρpos n).ne'
  let A : ℕ → ℂ → ℂ := fun n w => F (i n) (z n + (ρ n : ℂ) * w)
  let B : ℕ → ℂ → ℂ := fun n w => G (i n) (z n + (ρ n : ℂ) * w)
  let U : ℕ → ℂ → ℂ := fun n w => (ρ n : ℂ) * uₙ (i n) (z n + (ρ n : ℂ) * w)
  let V : ℕ → ℂ → ℂ := fun n w => (ρ n : ℂ) * vₙ (i n) (z n + (ρ n : ℂ) * w)
  have hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (A n)) H atTop univ :=
    spherical_affine_limits hΩ (fun n => (hseq (i n)).pair.nonconst_f.1)
      hz₀ hz hρ hρne hFconv₀
  have hloc : ∀ w : ℂ, ∃ D : Set ℂ, IsOpen D ∧ w ∈ D ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn D (A n) (B n) (U n) (V n) a :=
    auxiliary_pairs_rescale_locally hΩ hseq hz₀ i hz hρ hρne
  have hshareloc : ∀ w : ℂ, ∃ D : Set ℂ, IsOpen D ∧ w ∈ D ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (A n)) D ∧
        SphereHolomorphicOn (sphereGermValue (B n)) D ∧
        ∀ x ∈ D, ∀ j, (sphereGermValue (A n) x = normalizedSphereTargets a j ↔
          sphereGermValue (B n) x = normalizedSphereTargets a j) := by
    intro w
    obtain ⟨D, hD, hwD, hev⟩ := hloc w
    refine ⟨D, hD, hwD, hev.mono fun n hn => ?_⟩
    exact ⟨sphereHolomorphicOn_sphereGermValue hD hn.pair.nonconst_f.1,
      sphereHolomorphicOn_sphereGermValue hD hn.pair.nonconst_g.1, hn.pair.sphere_shares⟩
  obtain ⟨ψ, hψ, K, hK, hKnc, hGconv⟩ := exists_nonconstant_spherical_companion
    hH hHnc hFconv (normalizedSphereTargets a)
      (normalizedSphereTargets_injective (hseq 0).pair.injective) hshareloc
  have hlocψ : ∀ w : ℂ, ∃ D : Set ℂ, IsOpen D ∧ w ∈ D ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn D (A (ψ n)) (B (ψ n)) (U (ψ n)) (V (ψ n)) a := by
    intro w
    obtain ⟨D, hD, hwD, hev⟩ := hloc w
    exact ⟨D, hD, hwD, hψ.tendsto_atTop.eventually hev⟩
  have huconvI := auxiliary_tlu_reindex huconv hit
  have hvconvI := auxiliary_tlu_reindex hvconv hit
  have hUconv := complex_rescale_coefficient_tendsto_zero hΩ hz₀
    (hu.continuousAt (hΩ.mem_nhds hz₀)) huconvI hz hρ
  have hVconv := complex_rescale_coefficient_tendsto_zero hΩ hz₀
    (hv.continuousAt (hΩ.mem_nhds hz₀)) hvconvI hz hρ
  have hFconvψ := auxiliary_tlu_reindex hFconv hψ.tendsto_atTop
  have hEq := sphere_limits_eq_of_auxiliary_limits_zero a hH hK hHnc hKnc hFconvψ hGconv
    (auxiliary_tlu_reindex hUconv hψ.tendsto_atTop)
    (auxiliary_tlu_reindex hVconv hψ.tendsto_atTop) (fun w => by
      obtain ⟨D, hD, hwD, hev⟩ := hlocψ w
      exact ⟨D, hD, hwD, hev.mono fun n hn => ⟨hn.pair.nonconst_f,
        hn.pair.nonconst_g, hn.holo_u.continuousOn, hn.holo_v.continuousOn, hn.u_eq, hn.v_eq⟩⟩)
  have hGconvH : TendstoLocallyUniformlyOn (fun n => sphereGermValue (B (ψ n))) H
      atTop univ := hGconv.congr_right (fun w _ => (hEq w).symm)
  let φ : ℂ → ℂ := fun w => u w / v w
  let φₙ : ℕ → ℂ → ℂ := fun n w => uₙ n w / vₙ n w
  have hφconv : TendstoLocallyUniformlyOn φₙ φ atTop Ω := huconv.div₀ hvconv hu hv hv0
  have hφc : ContinuousOn φ Ω := hu.div hv hv0
  have hφscaled := complex_rescale_tendstoLocallyUniformlyOn_const hΩ hz₀
    (hφc.continuousAt (hΩ.mem_nhds hz₀)) (auxiliary_tlu_reindex hφconv hit) hz hρ
  have hRconv : TendstoLocallyUniformlyOn (fun n w => U n w / V n w)
      (fun _ => φ z₀) atTop univ := by
    apply hφscaled.congr
    intro n w _
    have hc : (ρ n : ℂ) ≠ 0 := by exact_mod_cast hρne n
    exact (mul_div_mul_left (uₙ (i n) (z n + (ρ n : ℂ) * w))
      (vₙ (i n) (z n + (ρ n : ℂ) * w)) hc).symm
  have hφone : φ z₀ = 1 := auxPhi_spherical_diagonal_limit_eq_one a hH hHnc
    hFconvψ hGconvH (auxiliary_tlu_reindex hRconv hψ.tendsto_atTop) hlocψ
  have hderiv : deriv φ z₀ ≠ 0 := hsimple z₀ hz₀
    ((div_eq_one_iff_eq (hv0 z₀ hz₀)).mp hφone)
  have hφholo : ∀ᶠ n in atTop, DifferentiableOn ℂ (φₙ n) Ω :=
    Eventually.of_forall fun n : ℕ => (hseq n).holo_u.div (hseq n).holo_v (hseq n).nonzero_v
  obtain ⟨r₁, hr₁, hBΩ, hinj⟩ := eventual_injOn_ball_of_locallyUniformlyOn
    hΩ hz₀ hφholo hφconv hderiv
  obtain ⟨r₂, hr₂, _, hclose⟩ := auxiliary_eventual_close_one hΩ hz₀
    (hφc.continuousAt (hΩ.mem_nhds hz₀)) hφconv hφone
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hball₁ : ball z₀ r ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left r₁ r₂)
  have hball₂ : ball z₀ r ⊆ ball z₀ r₂ := ball_subset_ball (min_le_right r₁ r₂)
  have hballΩ : ball z₀ r ⊆ Ω := hball₁.trans hBΩ
  have hFlocψ : ∀ w : ℂ, ∃ D : Set ℂ, IsOpen D ∧ w ∈ D ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (A (ψ n))) D := by
    intro w
    obtain ⟨D, hD, hwD, hev⟩ := hlocψ w
    exact ⟨D, hD, hwD, hev.mono fun n hn => sphereHolomorphicOn_sphereGermValue hD
      hn.pair.nonconst_f.1⟩
  obtain ⟨R, _, htwo⟩ := eventually_two_bounded_sphere_fibers hH hHnc hFlocψ hFconvψ
    (fun j => (a j : OnePoint ℂ)) (OnePoint.coe_injective.comp (hseq 0).pair.injective)
  have hmap := eventually_rescale_closedBall_subset isOpen_ball (mem_ball_self hr)
    (hz.comp hψ.tendsto_atTop) (hρ.comp hψ.tendsto_atTop) R
  have hitψ := hit.comp hψ.tendsto_atTop
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [htwo, hmap, hitψ.eventually hinj, hitψ.eventually hclose]
      with n hn hmaps hni hnc
    obtain ⟨x, y, hx, hy, hxy, ⟨j, hj⟩, ⟨k, hk⟩⟩ := hn
    have hxB := hmaps x (ball_subset_closedBall hx)
    have hyB := hmaps y (ball_subset_closedBall hy)
    have hc : (ρ (ψ n) : ℂ) ≠ 0 := by exact_mod_cast hρne (ψ n)
    have hfx := sphereGermValue_comp_affine (ρ (ψ n) : ℂ) (z (ψ n)) x hc
      ((hseq (i (ψ n))).pair.nonconst_f.1 _ (hballΩ hxB))
    have hfy := sphereGermValue_comp_affine (ρ (ψ n) : ℂ) (z (ψ n)) y hc
      ((hseq (i (ψ n))).pair.nonconst_f.1 _ (hballΩ hyB))
    have heq := ((hseq (i (ψ n))).restrict hballΩ).finite_fibers_subsingleton isOpen_ball
      (hni.mono hball₁) (fun w hw => hnc w (hball₂ hw)) hxB hyB
      ⟨j, hfx.symm.trans hj⟩ ⟨k, hfy.symm.trans hk⟩
    apply hxy
    exact mul_left_cancel₀ hc (add_left_cancel heq)
  exact hfalse.exists.elim (fun _ h => h)

end ThreeIM
