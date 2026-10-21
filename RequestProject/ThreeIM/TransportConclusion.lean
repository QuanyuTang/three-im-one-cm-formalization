module

public import RequestProject.ThreeIM.TransportTrackedEndpoints
public import RequestProject.ThreeIM.TransportShiftProfiles
public import RequestProject.ThreeIM.TransportShiftAuxiliaryPairs
public import RequestProject.ThreeIM.EndpointRootSeparation

/-! # The endpoint contradiction for the original amplitude transport data -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

private theorem transport_conclusion_tlu_subsequence {X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {f : X → Y} {Ω : Set X}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    TendstoLocallyUniformlyOn (fun n => F (σ n)) f atTop Ω := by
  intro e he z hz
  obtain ⟨V, hV, hev⟩ := h e he z hz
  exact ⟨V, hV, hσ.tendsto_atTop.eventually hev⟩

theorem transport_false_of_tangent_convergence
    {Ω : ℕ → Set ℂ} (hΩ : ∀ n, IsOpen (Ω n))
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
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
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η)
    (hconv : TransportTangentConvergence F G ε (a j)
      (A * amplitudeRemainder a j (a j))) : False := by
  obtain ⟨s, hs, vF, vG, MF, MG, γ, hγ, hbounds⟩ :=
    transport_tracked_endpoints hΩ pair hεpos hε hA hB hu hv hU hV hrect
      hprofU hprofV hconv
  have hseqE := transport_eventually_shifted_auxiliary_on_balls pair hεpos hε hs
    hu hv hU hV hrect hprofU hprofV
  obtain ⟨σ, hσ, hseq⟩ := auxiliary_pairs_exhausting_subsequence hseqE
  have hrad : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have huc := transport_shift_U_tendsto_profile hεpos hε hs hA hprofU
  have hvc := transport_shift_V_tendsto_zero hεpos hε hs hB hprofV
  have hbs := hσ.tendsto_atTop.eventually hbounds
  exact auxiliary_endpoint_root_separation_false hrad hseq (by fun_prop)
    (fun z => mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') hA)
      (Complex.exp_ne_zero _))
    (transport_conclusion_tlu_subsequence huc hσ)
    (transport_conclusion_tlu_subsequence hvc hσ)
    (hbs.mono fun _ h => h.1) (hbs.mono fun _ h => h.2.1)
    (hbs.mono fun _ h => h.2.2.1) (hbs.mono fun _ h => h.2.2.2.1)
    hγ (hbs.mono fun _ h => h.2.2.2.2)

theorem transport_from_original_profiles
    {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ} (hm : 2 ≤ m) {Ω : ℕ → Set ℂ}
    (hΩ : ∀ n, IsOpen (Ω n)) {F G : ℕ → ℂ → ℂ}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    (marked_F : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (marked_G : ∀ n, mult (G n) (a j : Sphere) 0 = m)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    {u v : ℕ → ℂ → ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) : False := by
  obtain ⟨σ, hσ, hconv⟩ := transport_tangent_subsequence pair hm marked_F marked_G
    hεpos hε hA hB hu hv hU hV hrect hprofU hprofV
  exact transport_false_of_tangent_convergence
    (fun n => hΩ (σ n)) (fun n => pair (σ n))
    (fun n => hεpos (σ n)) (hε.comp hσ.tendsto_atTop) hA hB
    (fun n => hu (σ n)) (fun n => hv (σ n))
    (fun n => hU (σ n)) (fun n => hV (σ n))
    (fun R hR => hσ.tendsto_atTop.eventually (hrect R hR))
    (fun R hR η hη => hσ.tendsto_atTop.eventually (hprofU R hR η hη))
    (fun R hR η hη => hσ.tendsto_atTop.eventually (hprofV R hR η hη)) hconv

end ThreeIM
