module

public import RequestProject.ThreeIM.ScalarNormality
public import RequestProject.ThreeIM.HolomorphicSphericalLimits
public import RequestProject.ThreeIM.PrimitiveConvergence

/-!
# Compactness of the scalar quotient and its normalized amplitude difference

The hypotheses record the actual scalar equation and derivative identity
obtained by amplitude elimination. They hold eventually on each fixed disk.
Scalar normality supplies a spherical subsequence; its marked value gives
an entire Euclidean limit. Integrating the difference then gives Euclidean
convergence for that difference too. No compactness premise is assumed.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

structure ScalarPrimitiveOn (Ω : Set ℂ) (D H C B : ℂ → ℂ) : Prop where
  holoD : DifferentiableOn ℂ D Ω
  holoH : DifferentiableOn ℂ H Ω
  holoC : DifferentiableOn ℂ C Ω
  scalar : ∀ z ∈ Ω, C z * H z * (H z - 1) * deriv (deriv H) z
    - deriv C z * H z * (H z - 1) * deriv H z
    - (C z * (3 * H z - 1) + B z) * deriv H z ^ 2 = 0
  derivD : ∀ z ∈ Ω, deriv D z = C z * H z + B z

private theorem amplitude_tlu_reindex {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop univ) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop univ := by
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := h v hv x hx
  exact ⟨t, ht, hi.eventually hev⟩

theorem scalar_primitives_subsequence {D H C B : ℕ → ℂ → ℂ} {c b : ℂ → ℂ}
    (hseq : ∀ R > 0, ∀ᶠ n in atTop, ScalarPrimitiveOn (ball 0 R) (D n) (H n) (C n) (B n))
    (hc : Differentiable ℂ c) (hb : Differentiable ℂ b) (hb0 : ∀ z, b z ≠ 0)
    (hCconv : TendstoLocallyUniformlyOn C c atTop univ)
    (hBconv : TendstoLocallyUniformlyOn B b atTop univ)
    (hH0 : ∀ᶠ n in atTop, H n 0 = 1) (hD0 : ∀ᶠ n in atTop, D n 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h d : ℂ → ℂ,
      Differentiable ℂ h ∧ Differentiable ℂ d ∧ h 0 = 1 ∧ d 0 = 0 ∧
      TendstoLocallyUniformlyOn (fun n => H (φ n)) h atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => D (φ n)) d atTop univ := by
  have hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, ScalarPrimitiveOn Ω (D n) (H n) (C n) (B n) := by
    intro z
    have hR : 0 < ‖z‖ + 1 := by positivity
    refine ⟨ball 0 (‖z‖ + 1), isOpen_ball, ?_, hseq _ hR⟩
    rw [mem_ball_zero_iff]
    linarith
  have hnormal : IsNormal (range (fun n => sphereGermValue (H n))) univ :=
    scalar_solutions_isNormal_of_locally_eventually (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn => ⟨hn.holoH, hn.holoC, hn.scalar⟩⟩)
      hCconv hBconv hb.continuous hb0
  obtain ⟨φ, hφ, L, hconv⟩ := hnormal (fun n => ⟨sphereGermValue (H n), mem_range_self n⟩)
  have hHloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (H (φ n)) Ω := by
    intro z
    obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
    exact ⟨Ω, hΩ, hzΩ, hφ.tendsto_atTop.eventually (hev.mono fun n hn => hn.holoH)⟩
  obtain ⟨hL0, hh, hHconv⟩ := holomorphic_spherical_limit_of_fixed_value hHloc hconv 0 1
    (hφ.tendsto_atTop.eventually hH0)
  let h : ℂ → ℂ := fun z => chartFiniteMap (L z)
  have hh0 : h 0 = 1 := by simp only [h, hL0, chartFiniteMap]
  have hrhs : Differentiable ℂ (fun z => c z * h z + b z) := (hc.mul hh).add hb
  obtain ⟨d, hd, hd0, hdder⟩ := exists_normalized_entire_primitive hrhs
  have hRconv : TendstoLocallyUniformlyOn
      (fun n z => C (φ n) z * H (φ n) z + B (φ n) z) (deriv d) atTop univ :=
    (((amplitude_tlu_reindex hCconv hφ.tendsto_atTop).mul₀ hHconv
      hc.continuous.continuousOn hh.continuous.continuousOn).add
      (amplitude_tlu_reindex hBconv hφ.tendsto_atTop)).congr_right
        (fun z _ => (hdder z).symm)
  have hderconv : TendstoLocallyUniformlyOn (fun n => deriv (D (φ n))) (deriv d) atTop univ := by
    apply tendstoLocallyUniformlyOn_congr_locally_eventually hRconv
    intro z _
    obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
    refine ⟨Ω, mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hzΩ), ?_⟩
    filter_upwards [hφ.tendsto_atTop.eventually hev] with n hn w hw
    exact (hn.derivD w hw).symm
  have hzero : Tendsto (fun n => D (φ n) 0) atTop (𝓝 (d 0)) := by
    rw [hd0]
    apply tendsto_const_nhds.congr'
    filter_upwards [hφ.tendsto_atTop.eventually hD0] with n hn
    exact hn.symm
  have hDconv := primitive_tendstoLocallyUniformlyOn hd (fun R hR =>
    hφ.tendsto_atTop.eventually ((hseq R hR).mono fun n hn => hn.holoD)) hderconv hzero
  exact ⟨φ, hφ, h, d, hh, hd, hh0, hd0, hHconv, hDconv⟩

end ThreeIM
