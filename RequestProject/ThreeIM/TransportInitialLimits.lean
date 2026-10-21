module

public import RequestProject.ThreeIM.TransportNormality
public import RequestProject.ThreeIM.AuxiliaryConstantLimits

/-!
# The initial constant limits from the original transport hypotheses

The original rectangle profiles give vanishing coefficients and an
independently convergent exponential quotient. Both members have global
spherical subsequences. The common marked value identifies their limits
as that finite constant, with no extra compactness or growth hypothesis.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

structure TransportCompactProfileData (F G u v : ℕ → ℂ → ℂ)
    (a : Fin 3 → ℂ) (A B : ℂ) : Prop where
  zeroU : TendstoLocallyUniformlyOn u (fun _ => 0) atTop univ
  zeroV : TendstoLocallyUniformlyOn v (fun _ => 0) atTop univ
  quotient : TendstoLocallyUniformlyOn (fun n z => u n z / v n z)
    (fun z => (A / B) * Complex.exp z) atTop univ
  simpleOne : ∀ z, (A / B) * Complex.exp z = 1 →
    deriv (fun w => (A / B) * Complex.exp w) z ≠ 0
  locallyAuxiliary : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (u n) (v n) a

theorem transport_compact_profile_data {Ω : ℕ → Set ℂ} {F G : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) {uₙ vₙ : ℕ → ℂ → ℂ}
    (huₙ : ∀ n, DifferentiableOn ℂ (uₙ n) (Ω n))
    (hvₙ : ∀ n, DifferentiableOn ℂ (vₙ n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] uₙ n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] vₙ n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖uₙ n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖vₙ n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) :
    TransportCompactProfileData F G uₙ vₙ a A B := by
  let D : ℂ → ℂ := fun z => A * Complex.exp (z / 2)
  let E : ℂ → ℂ := fun z => B * Complex.exp (-z / 2)
  have hD : Continuous D := by dsimp only [D]; fun_prop
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hD0 (z : ℂ) : D z ≠ 0 := mul_ne_zero hA (Complex.exp_ne_zero _)
  have hE0 (z : ℂ) : E z ≠ 0 := mul_ne_zero hB (Complex.exp_ne_zero _)
  have hpU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖uₙ n z / ((ε n : ℂ) * D z) - 1‖ ≤ η := by
    simpa only [D, mul_assoc] using hprofU
  have hpV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖vₙ n z / ((ε n : ℂ) * E z) - 1‖ ≤ η := by
    simpa only [E, mul_assoc] using hprofV
  refine ⟨transport_coefficient_tendsto_zero hεpos hε hD hD0 hpU,
    transport_coefficient_tendsto_zero hεpos hε hE hE0 hpV, ?_, ?_, ?_⟩
  · exact (transport_quotient_tendsto_profile_ratio hεpos hε hD hE hD0 hE0 hpU hpV).congr_right
      (fun z _ => transport_exponential_profile_ratio A B z)
  · intro z hz
    have hd := (Complex.hasDerivAt_exp z).const_mul (A / B)
    rw [hd.deriv, hz]
    exact one_ne_zero
  · intro z
    let R : ℝ := ‖z‖ + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hzB : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp only [R]
      linarith
    refine ⟨ball 0 R, isOpen_ball, hzB, ?_⟩
    filter_upwards [eventually_closedBall_subset_transport_domains hεpos hε hrect hR,
      transport_profile_eventually_nonzero hεpos hε hpU hR,
      transport_profile_eventually_nonzero hεpos hε hpV hR] with n hn hnu hnv
    have hBΩ : ball (0 : ℂ) R ⊆ Ω n := ball_subset_closedBall.trans hn
    exact ⟨(pair n).restrict hBΩ, (huₙ n).mono hBΩ, (hvₙ n).mono hBΩ, hnu, hnv,
      (hU n).filter_mono (Filter.codiscreteWithin.mono hBΩ),
      (hV n).filter_mono (Filter.codiscreteWithin.mono hBΩ)⟩

private theorem initial_tlu_reindex {X : Type*} [UniformSpace X]
    {F : ℕ → ℂ → X} {f : ℂ → X}
    (h : TendstoLocallyUniformlyOn F f atTop univ) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop univ := by
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := h v hv x hx
  exact ⟨t, ht, hi.eventually hev⟩

theorem TransportCompactProfileData.marked_subsequence
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {A B : ℂ}
    (h : TransportCompactProfileData F G u v a A B) {j : Fin 3}
    (hfmarked : ∀ n, 0 < mult (F n) (a j : Sphere) 0)
    (hgmarked : ∀ n, 0 < mult (G n) (a j : Sphere) 0) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoLocallyUniformlyOn (fun n => sphereGermValue (F (σ n)))
        (fun _ => (a j : OnePoint ℂ)) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => sphereGermValue (G (σ n)))
        (fun _ => (a j : OnePoint ℂ)) atTop univ := by
  have hφ : Continuous (fun z => (A / B) * Complex.exp z) := by fun_prop
  have hFn := auxiliary_pairs_isNormal_of_vanishing_coefficients_locally
    h.locallyAuxiliary h.zeroU h.zeroV hφ h.quotient h.simpleOne
  have hGn := auxiliary_pairs_companion_isNormal_of_locally_eventually h.locallyAuxiliary hFn
  obtain ⟨σ, hσ, H, K, hFc, hGc⟩ := sphere_pair_subsequence_of_normal hFn hGn
  have hlocσ : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F (σ n)) (G (σ n)) (u (σ n)) (v (σ n)) a := by
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := h.locallyAuxiliary z
    exact ⟨U, hU, hzU, hσ.tendsto_atTop.eventually hev⟩
  have hH : SphereHolomorphicOn H univ := sphereHolomorphicOn_univ_of_locally_eventually hFc
    (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hlocσ z
      exact ⟨U, hU, hzU, hev.mono fun n hn =>
        sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_f.1⟩)
  have hK : SphereHolomorphicOn K univ := sphereHolomorphicOn_univ_of_locally_eventually hGc
    (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hlocσ z
      exact ⟨U, hU, hzU, hev.mono fun n hn =>
        sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_g.1⟩)
  have hvalues := auxiliary_marked_vanishing_ratio_spherical_limits hH hK hFc hGc
    (initial_tlu_reindex h.zeroU hσ.tendsto_atTop)
    (initial_tlu_reindex h.zeroV hσ.tendsto_atTop)
    (initial_tlu_reindex h.quotient hσ.tendsto_atTop) h.simpleOne hlocσ
    (Eventually.of_forall fun n => ⟨hfmarked (σ n), hgmarked (σ n)⟩)
  exact ⟨σ, hσ, hFc.congr_right (fun z _ => (hvalues z).1),
    hGc.congr_right (fun z _ => (hvalues z).2)⟩

end ThreeIM
