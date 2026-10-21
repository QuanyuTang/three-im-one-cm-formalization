module

public import RequestProject.ThreeIM.AuxiliaryAmplitudeLimits
public import RequestProject.ThreeIM.FiniteConstantChartLimits

/-!
# Concrete amplitude data from finite constant spherical limits

All fields below are conclusions derived from the original auxiliary
identities, their relative profiles, and marked multiplicities. Holomorphy
of the corrected representatives and compactness of the amplitudes are
not added as premises.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

noncomputable def transportFiniteChart (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  chartFiniteMap (sphereGermValue F z)

noncomputable def transportAmplitude (F : ℂ → ℂ) (c : ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  (transportFiniteChart F z - c) / (ε : ℂ)

noncomputable def transportAmplitudeCoefficient (F u : ℂ → ℂ) (a : Fin 3 → ℂ) (j : Fin 3)
    (ε : ℝ) (z : ℂ) : ℂ :=
  (u z / (ε : ℂ)) * amplitudeRemainder a j (transportFiniteChart F z)

structure TransportAmplitudeData (F G u v : ℕ → ℂ → ℂ) (ε : ℕ → ℝ)
    (a : Fin 3 → ℂ) (j : Fin 3) (A B : ℂ) : Prop where
  systems : ∀ R > 0, ∀ᶠ n in atTop,
    AmplitudeSystemOn (ball 0 R)
      (transportAmplitude (F n) (a j) (ε n)) (transportAmplitude (G n) (a j) (ε n))
      (transportAmplitudeCoefficient (F n) (u n) a j (ε n))
      (transportAmplitudeCoefficient (G n) (v n) a j (ε n))
  coefficientU : TendstoLocallyUniformlyOn
    (fun n => transportAmplitudeCoefficient (F n) (u n) a j (ε n))
    (fun z => (A * amplitudeRemainder a j (a j)) * Complex.exp (z / 2)) atTop univ
  coefficientV : TendstoLocallyUniformlyOn
    (fun n => transportAmplitudeCoefficient (G n) (v n) a j (ε n))
    (fun z => (B * amplitudeRemainder a j (a j)) * Complex.exp (-z / 2)) atTop univ
  marked : ∀ᶠ n in atTop,
    transportAmplitude (F n) (a j) (ε n) 0 = 0 ∧
      transportAmplitude (G n) (a j) (ε n) 0 = 0 ∧
      deriv (transportAmplitude (F n) (a j) (ε n)) 0 ≠ 0 ∧
      deriv (transportAmplitude (G n) (a j) (ε n)) 0 = 0

theorem auxiliary_constant_limits_transport_amplitude_data
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (hseq : ∀ R > 0, ∀ᶠ n in atTop,
      AuxiliaryPairOn (ball 0 R) (F n) (G n) (u n) (v n) a)
    (hFc : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (fun _ => (a j : OnePoint ℂ)) atTop univ)
    (hGc : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (fun _ => (a j : OnePoint ℂ)) atTop univ)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η)
    {m : ℕ} (hm : 2 ≤ m)
    (hmF : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (hmG : ∀ n, mult (G n) (a j : Sphere) 0 = m) :
    TransportAmplitudeData F G u v ε a j A B := by
  have hFs : ∀ R > 0, ∀ᶠ n in atTop,
      SphereHolomorphicOn (sphereGermValue (F n)) (ball 0 R) := by
    intro R hR
    exact (hseq R hR).mono fun n hn =>
      sphereHolomorphicOn_sphereGermValue isOpen_ball hn.pair.nonconst_f.1
  have hGs : ∀ R > 0, ∀ᶠ n in atTop,
      SphereHolomorphicOn (sphereGermValue (G n)) (ball 0 R) := by
    intro R hR
    exact (hseq R hR).mono fun n hn =>
      sphereHolomorphicOn_sphereGermValue isOpen_ball hn.pair.nonconst_g.1
  have hCd (R : ℝ) (hR : 0 < R) : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (transportFiniteChart (F n)) (ball 0 R) :=
    finite_constant_chart_eventually_holomorphic (a j) hFs hFc hR
  have hEd (R : ℝ) (hR : 0 < R) : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (transportFiniteChart (G n)) (ball 0 R) :=
    finite_constant_chart_eventually_holomorphic (a j) hGs hGc hR
  have hCc := finite_constant_chart_locallyUniformly (a j) hFs hFc
  have hEc := finite_constant_chart_locallyUniformly (a j) hGs hGc
  obtain ⟨n₀, hn₀⟩ := (hseq 1 one_pos).exists
  have hainj := hn₀.pair.injective
  have hε0 (n : ℕ) : (ε n : ℂ) ≠ 0 := by exact_mod_cast (hεpos n).ne'
  have hcorrect (R : ℝ) (hR : 0 < R) : ∀ᶠ n in atTop,
      AuxiliaryPairOn (ball 0 R) (transportFiniteChart (F n))
        (transportFiniteChart (G n)) (u n) (v n) a := by
    filter_upwards [hseq R hR] with n hn
    exact hn.congr_codiscreteWithin isOpen_ball
      (chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_f.1)
      (chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_g.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    filter_upwards [hcorrect R hR, hCd R hR, hEd R hR,
      amplitudeRemainder_eventually_nonzero hainj j hCc R] with n hn hc he hq
    exact auxiliary_amplitude_system isOpen_ball j hn hc he (hε0 n)
      (fun z hz => hq z (ball_subset_closedBall hz))
  · let D : ℂ → ℂ := fun z => A * Complex.exp (z / 2)
    have hD : Continuous D := by dsimp only [D]; fun_prop
    have hD0 (z : ℂ) : D z ≠ 0 := mul_ne_zero hA (Complex.exp_ne_zero _)
    have hp : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
        ‖u n z / ((ε n : ℂ) * D z) - 1‖ ≤ η := by
      simpa only [D, mul_assoc] using hprofU
    have hu := transport_scaled_coefficient_tendsto_profile hεpos hε hD hD0 hp
    exact (auxiliary_amplitude_coefficient_limit a j hD hu hCc).congr_right
      (fun z _ => by dsimp only [D]; ring)
  · let D : ℂ → ℂ := fun z => B * Complex.exp (-z / 2)
    have hD : Continuous D := by dsimp only [D]; fun_prop
    have hD0 (z : ℂ) : D z ≠ 0 := mul_ne_zero hB (Complex.exp_ne_zero _)
    have hp : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
        ‖v n z / ((ε n : ℂ) * D z) - 1‖ ≤ η := by
      simpa only [D, mul_assoc] using hprofV
    have hv := transport_scaled_coefficient_tendsto_profile hεpos hε hD hD0 hp
    exact (auxiliary_amplitude_coefficient_limit a j hD hv hEc).congr_right
      (fun z _ => by dsimp only [D]; ring)
  · filter_upwards [hseq 1 one_pos, hCd 1 one_pos, hEd 1 one_pos] with n hn hc he
    have heF := chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_f.1
    have heG := chartFinite_sphereGerm_eq_codiscreteWithin hn.pair.nonconst_g.1
    have hz : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have hmf : mult (transportFiniteChart (F n)) (a j : Sphere) 0 = 1 :=
      (mult_congr_punctured (auxiliary_local_of_codiscreteWithin isOpen_ball heF hz)
        (a j : Sphere)).symm.trans (hmF n)
    have hmg : mult (transportFiniteChart (G n)) (a j : Sphere) 0 = m :=
      (mult_congr_punctured (auxiliary_local_of_codiscreteWithin isOpen_ball heG hz)
        (a j : Sphere)).symm.trans (hmG n)
    exact auxiliary_amplitude_marked isOpen_ball hm hc he hz hmf hmg (hε0 n)

end ThreeIM
