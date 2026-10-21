module

public import RequestProject.ThreeIM.TransportAmplitudeData
public import RequestProject.ThreeIM.TransportInitialLimits

/-!
# The amplitude data are consequences of the original transport hypotheses

Every fixed disk eventually lies in the original rectangle. The relative
profiles make the auxiliary coefficients nonzero there. After the proved
finite constant spherical subsequence, all rectangle estimates and marked
multiplicities pass through the same strict subsequence.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_eventually_auxiliary_on_balls
    {Ω : ℕ → Set ℂ} {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) :
    ∀ R > 0, ∀ᶠ n in atTop,
      AuxiliaryPairOn (ball 0 R) (F n) (G n) (u n) (v n) a := by
  intro R hR
  have hpU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / ((ε n : ℂ) * (A * Complex.exp (z / 2))) - 1‖ ≤ η := by
    simpa only [mul_assoc] using hprofU
  have hpV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / ((ε n : ℂ) * (B * Complex.exp (-z / 2))) - 1‖ ≤ η := by
    simpa only [mul_assoc] using hprofV
  filter_upwards [eventually_closedBall_subset_transport_domains hεpos hε hrect hR,
    transport_profile_eventually_nonzero hεpos hε hpU hR,
    transport_profile_eventually_nonzero hεpos hε hpV hR] with n hn hnu hnv
  have hBΩ : ball (0 : ℂ) R ⊆ Ω n := ball_subset_closedBall.trans hn
  exact ⟨(pair n).restrict hBΩ, (hu n).mono hBΩ, (hv n).mono hBΩ, hnu, hnv,
    (hU n).filter_mono (Filter.codiscreteWithin.mono hBΩ),
    (hV n).filter_mono (Filter.codiscreteWithin.mono hBΩ)⟩

theorem transport_amplitude_data_subsequence
    {Ω : ℕ → Set ℂ} {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {m : ℕ} (hm : 2 ≤ m)
    (hmF : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (hmG : ∀ n, mult (G n) (a j : Sphere) 0 = m)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TransportAmplitudeData (fun n => F (σ n)) (fun n => G (σ n))
        (fun n => u (σ n)) (fun n => v (σ n)) (fun n => ε (σ n)) a j A B := by
  have hdata := transport_compact_profile_data pair hεpos hε hA hB
    hu hv hU hV hrect hprofU hprofV
  obtain ⟨σ, hσ, hFc, hGc⟩ := hdata.marked_subsequence (j := j)
    (fun n => by rw [hmF n]; decide) (fun n => by rw [hmG n]; omega)
  have hseq := transport_eventually_auxiliary_on_balls pair hεpos hε hu hv hU hV
    hrect hprofU hprofV
  refine ⟨σ, hσ, auxiliary_constant_limits_transport_amplitude_data ?_ hFc hGc
    (fun n => hεpos (σ n)) (hε.comp hσ.tendsto_atTop) hA hB ?_ ?_
    hm (fun n => hmF (σ n)) (fun n => hmG (σ n))⟩
  · intro R hR
    exact hσ.tendsto_atTop.eventually (hseq R hR)
  · intro R hR η hη
    exact hσ.tendsto_atTop.eventually (hprofU R hR η hη)
  · intro R hR η hη
    exact hσ.tendsto_atTop.eventually (hprofV R hR η hη)

end ThreeIM
