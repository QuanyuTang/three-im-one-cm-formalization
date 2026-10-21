module

public import RequestProject.ThreeIM.ZeroPersistence
public import RequestProject.ThreeIM.SphereHurwitz

/-!
# Persistence of spherical fibers

A nonconstant entire spherical limit has preimages approximated by the
members on every open neighborhood, proved using finite charts and Hurwitz.
-/

@[expose] public section

open Filter Set Metric Topology Matrix NoWanderingDomains

namespace ThreeIM

theorem sphere_eventually_exists_zero {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ w, G w = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    {z : ℂ} (hz : G z = ((0 : ℂ) : OnePoint ℂ))
    {V : Set ℂ} (hV : IsOpen V) (hzV : z ∈ V) :
    ∀ᶠ n in atTop, ∃ w ∈ V, F n w = ((0 : ℂ) : OnePoint ℂ) := by
  obtain ⟨U, hU, hzU, hF⟩ := hloc z
  have hW : IsOpen (U ∩ V) := hU.inter hV
  have hFV : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) (U ∩ V) :=
    hF.mono fun n hn => sphereHolomorphicOn_mono hn hW inter_subset_left
  have hne : G z ≠ OnePoint.infty := by
    rw [hz]
    exact OnePoint.coe_ne_infty 0
  obtain ⟨r, hr, hrW, _, hfin, hd, hc⟩ :=
    exists_finite_chart_convergence_eventually hW hFV
      (hconv.mono (subset_univ _)) ⟨hzU, hzV⟩ hne
  have hmer := isNonconstMeroOn_chartFiniteMap hG hnc
  have hfinit : meromorphicOrderAt (fun w => chartFiniteMap (G w)) z ≠ ⊤ := by
    simpa only [sub_zero] using hmer.2 z (mem_univ z) 0
  have hzero : chartFiniteMap (G z) = 0 := by simp only [hz, chartFiniteMap]
  have hzeros := eventually_exists_zero_of_locallyUniform_finite_germ isOpen_ball hd
    (hc.tendstoLocallyUniformlyOn.mono ball_subset_closedBall)
      (mem_ball_self hr) hzero hfinit
  filter_upwards [hzeros, hfin] with n hn hnf
  obtain ⟨w, hw, hw0⟩ := hn
  refine ⟨w, (hrW (ball_subset_closedBall hw)).2, ?_⟩
  cases hv : F n w with
  | infty => exact (hnf w (ball_subset_closedBall hw) hv).elim
  | coe c =>
    have hc0 : c = 0 := by simpa only [hv, chartFiniteMap] using hw0
    simp only [hc0]

theorem sphere_eventually_exists_fiber {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {a : OnePoint ℂ} (A : GL (Fin 2) ℂ)
    (hAa : A • a = ((0 : ℂ) : OnePoint ℂ))
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ w, G w = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    {z : ℂ} (hz : G z = a) {V : Set ℂ} (hV : IsOpen V) (hzV : z ∈ V) :
    ∀ᶠ n in atTop, ∃ w ∈ V, F n w = a := by
  have hGn : ¬ ∃ p : OnePoint ℂ, ∀ w, A • G w = p := by
    rintro ⟨p, hp⟩
    exact hnc ⟨G 0, fun w => MulAction.injective A ((hp w).trans (hp 0).symm)⟩
  have hloc' : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (fun w => A • F n w) U := by
    intro z
    obtain ⟨U, hU, hzU, hF⟩ := hloc z
    exact ⟨U, hU, hzU, hF.mono fun n hn => hn.gl_smul A⟩
  have huc : UniformContinuous (fun p : OnePoint ℂ => A • p) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul A)
  have hzeros := sphere_eventually_exists_zero (hG.gl_smul A) hGn hloc'
    (huc.comp_tendstoLocallyUniformlyOn hconv) (by rw [hz]; exact hAa) hV hzV
  exact hzeros.mono fun n hn => by
    obtain ⟨w, hw, hw0⟩ := hn
    exact ⟨w, hw, MulAction.injective A (hw0.trans hAa.symm)⟩

theorem exists_sphere_coordinate_zero (a : OnePoint ℂ) :
    ∃ A : GL (Fin 2) ℂ, A • a = ((0 : ℂ) : OnePoint ℂ) := by
  cases a with
  | infty => exact ⟨inversionGL, inversionGL_smul_infty⟩
  | coe x =>
    have hx : (x : OnePoint ℂ) ≠ ((x + 1 : ℂ) : OnePoint ℂ) := by
      intro h
      have he : x = x + 1 := OnePoint.coe_eq_coe.mp h
      have ho : (1 : ℂ) = 0 := by linear_combination -he
      exact one_ne_zero ho
    obtain ⟨A, hA, _, _⟩ := exists_gl_smul_eq_zero_one_infty
      (OnePoint.coe_ne_infty x) hx (OnePoint.coe_ne_infty (x + 1)).symm
    exact ⟨A, hA⟩

theorem sphere_eventually_exists_preimage {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ w, G w = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    {z : ℂ} {a : OnePoint ℂ} (hz : G z = a)
    {V : Set ℂ} (hV : IsOpen V) (hzV : z ∈ V) :
    ∀ᶠ n in atTop, ∃ w ∈ V, F n w = a := by
  obtain ⟨A, hA⟩ := exists_sphere_coordinate_zero a
  exact sphere_eventually_exists_fiber A hA hG hnc hloc hconv hz hV hzV

end ThreeIM
