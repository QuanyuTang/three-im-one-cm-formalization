module

public import RequestProject.ThreeIM.AuxiliaryRatioExhaustion
public import RequestProject.ThreeIM.TransportCompactProfiles

/-!
# Normality from the original transport profiles

The coefficients vanish and their quotient converges to `(A/B) exp z`.
Rectangle estimates supply zero-freeness on each fixed disk eventually.
The established simple-one-point criterion and companion normality therefore
apply directly to the original sequence, with no marked-order or growth
assumption needed for this compactness step.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem transport_pairs_isNormal {Ω : ℕ → Set ℂ} {F G : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
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
    IsNormal (range (fun n => sphereGermValue (F n))) univ ∧
      IsNormal (range (fun n => sphereGermValue (G n))) univ := by
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
  have huconv := transport_coefficient_tendsto_zero hεpos hε hD hD0 hpU
  have hvconv := transport_coefficient_tendsto_zero hεpos hε hE hE0 hpV
  let φ : ℂ → ℂ := fun z => (A / B) * Complex.exp z
  have hφ : Continuous φ := by dsimp only [φ]; fun_prop
  have hφconv : TendstoLocallyUniformlyOn (fun n z => uₙ n z / vₙ n z) φ atTop univ :=
    (transport_quotient_tendsto_profile_ratio hεpos hε hD hE hD0 hE0 hpU hpV).congr_right
      (fun z _ => transport_exponential_profile_ratio A B z)
  have hsimple (z : ℂ) (hz : φ z = 1) : deriv φ z ≠ 0 := by
    have hd : HasDerivAt φ ((A / B) * Complex.exp z) z :=
      (Complex.hasDerivAt_exp z).const_mul (A / B)
    rw [hd.deriv]
    change φ z ≠ 0
    rw [hz]
    exact one_ne_zero
  have hloc : ∀ z : ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn D (F n) (G n) (uₙ n) (vₙ n) a := by
    intro z
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
  have hFn := auxiliary_pairs_isNormal_of_vanishing_coefficients_locally
    hloc huconv hvconv hφ hφconv hsimple
  exact ⟨hFn, auxiliary_pairs_companion_isNormal_of_locally_eventually hloc hFn⟩

end ThreeIM
