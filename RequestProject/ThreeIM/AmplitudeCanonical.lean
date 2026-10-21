module

public import RequestProject.ThreeIM.AmplitudeOn
public import RequestProject.ThreeIM.AmplitudeCompactness

/-!
# One canonical analytic quotient on all eventual source disks

The quotient is regularized pointwise by its meromorphic germ. It does not
require global meromorphy outside the original source domain. Every analytic
factorization X=D H on an open domain identifies this single function with H.
Consequently the scalar equation and its derivatives agree on overlapping
disks without choosing a different quotient for each disk.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

noncomputable def amplitudeQuotient (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  toMeromorphicNFAt (fun w => X w / D w) z z

theorem amplitudeQuotient_eq_analytic_quotient {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X D H : ℂ → ℂ} (hX : DifferentiableOn ℂ X Ω)
    (hD : DifferentiableOn ℂ D Ω) (hH : DifferentiableOn ℂ H Ω)
    (hDfinite : ∀ z ∈ Ω, meromorphicOrderAt D z ≠ ⊤)
    (hrep : ∀ z ∈ Ω, X z = D z * H z) :
    EqOn (amplitudeQuotient X D) H Ω := by
  intro z hz
  let Q : ℂ → ℂ := fun w => X w / D w
  have hXa := hX.analyticOnNhd hΩ z hz
  have hDa := hD.analyticOnNhd hΩ z hz
  have hHa := hH.analyticOnNhd hΩ z hz
  have hQm : MeromorphicAt Q z := hXa.meromorphicAt.div hDa.meromorphicAt
  have hDne : ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hDa.meromorphicAt).mp (hDfinite z hz)
  have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ Ω :=
    (show ∀ᶠ w in 𝓝 z, w ∈ Ω from hΩ.mem_nhds hz).filter_mono nhdsWithin_le_nhds
  have heq : Q =ᶠ[𝓝[≠] z] H := by
    filter_upwards [hmem, hDne] with w hw hn
    exact (div_eq_iff hn).mpr (by simpa only [mul_comm] using hrep w hw)
  have hNF : toMeromorphicNFAt Q z =ᶠ[𝓝[≠] z] H :=
    hQm.eq_nhdsNE_toMeromorphicNFAt.symm.trans heq
  have horder : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt Q z) z := by
    rw [meromorphicOrderAt_congr hNF]
    exact hHa.meromorphicOrderAt_nonneg
  have hNFa : AnalyticAt ℂ (toMeromorphicNFAt Q z) z :=
    (meromorphicNFAt_toMeromorphicNFAt (f := Q) (x := z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp horder
  exact ((hNFa.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hHa.continuousAt).mp hNF).eq_of_nhds

private theorem amplitude_deriv_eqOn {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f g : ℂ → ℂ} (heq : EqOn f g Ω) : EqOn (deriv f) (deriv g) Ω := by
  intro z hz
  have he : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hΩ.mem_nhds hz) heq
  exact he.deriv_eq

theorem scalarPrimitiveOn_amplitudeQuotient {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X Y a b : ℂ → ℂ} (hX : DifferentiableOn ℂ X Ω)
    (hY : DifferentiableOn ℂ Y Ω) (ha : DifferentiableOn ℂ a Ω)
    (hb : DifferentiableOn ℂ b Ω) (ha0 : ∀ z ∈ Ω, a z ≠ 0)
    (hDfinite : ∀ z ∈ Ω, meromorphicOrderAt (fun w => X w - Y w) z ≠ ⊤)
    (hXeq : ∀ z ∈ Ω, (X z - Y z) * deriv X z = a z * X z)
    (hYeq : ∀ z ∈ Ω, (X z - Y z) * deriv Y z = b z * Y z) :
    ScalarPrimitiveOn Ω (fun w => X w - Y w)
      (amplitudeQuotient X (fun w => X w - Y w)) (fun w => a w - b w) b ∧
      (∀ z ∈ Ω, X z = (X z - Y z) * amplitudeQuotient X (fun w => X w - Y w) z) ∧
      (∀ z ∈ Ω, Y z = (X z - Y z) * (amplitudeQuotient X (fun w => X w - Y w) z - 1)) := by
  obtain ⟨H, hH, hHX, hHY, hDder, hscalar⟩ := exists_scalar_amplitude_quotient hΩ
    hX hY ha hb ha0 hDfinite hXeq hYeq
  let J : ℂ → ℂ := amplitudeQuotient X (fun w => X w - Y w)
  have heq : EqOn J H Ω := amplitudeQuotient_eq_analytic_quotient hΩ hX
    (hX.sub hY) hH hDfinite hHX
  have hd := amplitude_deriv_eqOn hΩ heq
  have hdd := amplitude_deriv_eqOn hΩ hd
  have hJ : DifferentiableOn ℂ J Ω := hH.congr heq
  refine ⟨⟨hX.sub hY, hJ, ha.sub hb, ?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    change (a z - b z) * J z * (J z - 1) * deriv (deriv J) z
      - deriv (fun w => a w - b w) z * J z * (J z - 1) * deriv J z
      - ((a z - b z) * (3 * J z - 1) + b z) * deriv J z ^ 2 = 0
    rw [heq hz, hd hz, hdd hz]
    exact hscalar z hz
  · intro z hz
    change deriv (fun w => X w - Y w) z = (a z - b z) * J z + b z
    rw [heq hz]
    exact hDder z hz
  · intro z hz
    change X z = (X z - Y z) * J z
    rw [heq hz]
    exact hHX z hz
  · intro z hz
    change Y z = (X z - Y z) * (J z - 1)
    rw [heq hz]
    exact hHY z hz

end ThreeIM
