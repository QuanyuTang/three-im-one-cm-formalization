module

public import RequestProject.ThreeIM.TransportAmplitudeSubsequence
public import RequestProject.ThreeIM.AmplitudeTangentModel

/-!
# The explicit tangent subsequence from the original transport data

The two strict subsequences are composed here. No convergence, compactness,
holomorphy of raw representatives, growth estimate, or nonconstant limiting
amplitude is added to the hypotheses of the original transport problem.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

noncomputable def transportTangentQuotient (F G : ℂ → ℂ) (c : ℂ) (ε : ℝ) : ℂ → ℂ :=
  amplitudeQuotient (transportAmplitude F c ε)
    (fun z => transportAmplitude F c ε z - transportAmplitude G c ε z)

structure TransportTangentConvergence (F G : ℕ → ℂ → ℂ) (ε : ℕ → ℝ)
    (c α : ℂ) : Prop where
  quotient : TendstoLocallyUniformlyOn
    (fun n => transportTangentQuotient (F n) (G n) c (ε n)) (fun _ => 1) atTop univ
  difference : TendstoLocallyUniformlyOn
    (fun n z => transportAmplitude (F n) c (ε n) z - transportAmplitude (G n) c (ε n) z)
    (fun z => 2 * α * (Complex.exp (z / 2) - 1)) atTop univ
  first : TendstoLocallyUniformlyOn (fun n => transportAmplitude (F n) c (ε n))
    (fun z => 2 * α * (Complex.exp (z / 2) - 1)) atTop univ
  second : TendstoLocallyUniformlyOn (fun n => transportAmplitude (G n) c (ε n))
    (fun _ => 0) atTop univ
  holomorphic : ∀ R > 0, ∀ᶠ n in atTop,
    DifferentiableOn ℂ (transportAmplitude (F n) c (ε n)) (Metric.ball 0 R) ∧
      DifferentiableOn ℂ (transportAmplitude (G n) c (ε n)) (Metric.ball 0 R) ∧
      DifferentiableOn ℂ (transportTangentQuotient (F n) (G n) c (ε n)) (Metric.ball 0 R)
  representation : ∀ R > 0, ∀ᶠ n in atTop, ∀ z ∈ Metric.ball 0 R,
    transportAmplitude (F n) c (ε n) z =
      (transportAmplitude (F n) c (ε n) z - transportAmplitude (G n) c (ε n) z) *
        transportTangentQuotient (F n) (G n) c (ε n) z ∧
    transportAmplitude (G n) c (ε n) z =
      (transportAmplitude (F n) c (ε n) z - transportAmplitude (G n) c (ε n) z) *
        (transportTangentQuotient (F n) (G n) c (ε n) z - 1)

theorem TransportAmplitudeData.tangent_subsequence
    {F G u v : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {a : Fin 3 → ℂ} {j : Fin 3} {A B : ℂ}
    (h : TransportAmplitudeData F G u v ε a j A B)
    (hainj : Function.Injective a) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TransportTangentConvergence (fun n => F (φ n)) (fun n => G (φ n))
        (fun n => ε (φ n)) (a j) (A * amplitudeRemainder a j (a j)) := by
  have hQ := amplitudeRemainder_nonzero hainj j
  obtain ⟨φ, hφ, hquot, hdiff, hfirst, hsecond⟩ := amplitude_tangent_model_subsequence
    (mul_ne_zero hA hQ) (mul_ne_zero hB hQ) h.systems h.coefficientU h.coefficientV h.marked
  refine ⟨φ, hφ, ⟨hquot, hdiff, hfirst, hsecond, ?_, ?_⟩⟩
  · intro R hR
    filter_upwards [hφ.tendsto_atTop.eventually (h.systems R hR)] with n hn
    exact ⟨hn.holoX, hn.holoY, (hn.canonical Metric.isOpen_ball).1.holoH⟩
  · intro R hR
    filter_upwards [hφ.tendsto_atTop.eventually (h.systems R hR)] with n hn z hz
    have hc := hn.canonical Metric.isOpen_ball
    exact ⟨hc.2.1 z hz, hc.2.2 z hz⟩

theorem transport_tangent_subsequence
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
      TransportTangentConvergence (fun n => F (σ n)) (fun n => G (σ n))
        (fun n => ε (σ n)) (a j) (A * amplitudeRemainder a j (a j)) := by
  obtain ⟨σ, hσ, hdata⟩ := transport_amplitude_data_subsequence pair hm hmF hmG hεpos hε
    hA hB hu hv hU hV hrect hprofU hprofV
  obtain ⟨φ, hφ, hconv⟩ := hdata.tangent_subsequence (pair 0).injective hA hB
  exact ⟨σ ∘ φ, hσ.comp hφ, hconv⟩

end ThreeIM
