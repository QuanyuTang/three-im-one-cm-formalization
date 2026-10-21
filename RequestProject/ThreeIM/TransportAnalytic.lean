module

public import RequestProject.ThreeIM.TransportCoordinates
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Extending transport amplitude identities between regular representatives

A codiscrete equality between continuous representatives on an open complex
domain holds at every point. Applied after clearing the auxiliary denominator,
this yields the amplitude equations even at a shared zero.

The finite-order assumptions below are precisely the local nonconstancy
condition already present in `IsNonconstMeroOn`. The amplitude equations use
analytic representatives. Further lemmas construct them on explicitly
pole-free regions, or locally at an endpoint approached along a bounded
path. No junk point value of the original meromorphic function is used.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

/-- On an open domain, codiscrete equality gives equality in the punctured
germ at each point. This assertion does not identify junk point values. -/
theorem transport_eventuallyEq_nhdsNE_of_codiscrete
    {E : Type*} {Ω : Set ℂ} {f g : ℂ → E} (hΩ : IsOpen Ω)
    (hfg : f =ᶠ[codiscreteWithin Ω] g) {x : ℂ} (hx : x ∈ Ω) :
    f =ᶠ[𝓝[≠] x] g := by
  have heq := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg x hx
  have hmem : ∀ᶠ z in 𝓝[≠] x, z ∈ Ω :=
    (show ∀ᶠ z in 𝓝 x, z ∈ Ω from hΩ.mem_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [heq, hmem] with z hz hzΩ
  rcases hz with h | h
  · exact h
  · exact (h hzΩ).elim

/-- Changing representatives on a discrete set also preserves the derivative
codiscretely. No differentiability assumption at a junk point is made. -/
theorem transport_deriv_congr_codiscrete {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hfg : f =ᶠ[codiscreteWithin Ω] g) :
    deriv f =ᶠ[codiscreteWithin Ω] deriv g := by
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
  intro x hx
  have hderiv := (transport_eventuallyEq_nhdsNE_of_codiscrete hΩ hfg hx).nhdsNE_deriv
  filter_upwards [hderiv] with z hz
  exact Or.inl hz

/-- Continuous representatives agreeing off a discrete exceptional set agree
on the whole open complex domain. The target need only be Hausdorff. -/
theorem eqOn_of_continuousOn_codiscrete {E : Type*} [TopologicalSpace E] [T2Space E]
    {Ω : Set ℂ} {f g : ℂ → E} (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (hfg : f =ᶠ[codiscreteWithin Ω] g) : EqOn f g Ω := by
  intro x hx
  have hpunctured := transport_eventuallyEq_nhdsNE_of_codiscrete hΩ hfg hx
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf.continuousAt (hΩ.mem_nhds hx)).mono_left nhdsWithin_le_nhds)
    ((hg.continuousAt (hΩ.mem_nhds hx)).mono_left nhdsWithin_le_nhds) hpunctured

/-- Local nonconstancy makes each finite fiber codiscrete. No connectedness
assumption on the open domain is necessary. -/
theorem transport_eventually_ne_of_finite_order {Ω : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Ω)
    (hfinite : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤) (c : ℂ) :
    ∀ᶠ z in codiscreteWithin Ω, F z ≠ c := by
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
  intro x hx
  have hnonzero := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    ((hF x hx).sub analyticAt_const).meromorphicAt).mp (hfinite x hx c)
  filter_upwards [hnonzero] with z hz
  exact Or.inl (sub_ne_zero.mp hz)

/-- The regular auxiliary denominator is nonzero codiscretely, as a direct
consequence of the local finite-order condition of a normalized pair. -/
theorem transport_eventually_regular_denominator {Ω : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Ω)
    (hfinite : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤) (a₂ a₃ : ℂ) :
    ∀ᶠ z in codiscreteWithin Ω, F z * transportQ a₂ a₃ (F z) ≠ 0 := by
  filter_upwards [transport_eventually_ne_of_finite_order hF hfinite 0,
    transport_eventually_ne_of_finite_order hF hfinite a₂,
    transport_eventually_ne_of_finite_order hF hfinite a₃] with z hz₀ hz₂ hz₃
  exact mul_ne_zero hz₀ (mul_ne_zero (sub_ne_zero.mpr hz₂) (sub_ne_zero.mpr hz₃))

/-- Clear an auxiliary identity on the regular set, then extend it to every
point by continuity. In particular, the conclusion also holds where `F = 0`.
The coefficient `D` may be any continuous representative, normally `F - G`. -/
theorem transport_analytic_amplitude {Ω : Set ℂ} {F D u : ℂ → ℂ} {a₂ a₃ : ℂ}
    (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω)
    (hD : ContinuousOn D Ω) (hu : ContinuousOn u Ω)
    (hfinite : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤)
    (haux : ∀ᶠ z in codiscreteWithin Ω,
      D z * deriv F z / (F z * transportQ a₂ a₃ (F z)) = u z) :
    ∀ z ∈ Ω, D z * deriv F z = (u z * transportQ a₂ a₃ (F z)) * F z := by
  have hleft : ContinuousOn (fun z => D z * deriv F z) Ω :=
    hD.mul hF.deriv.continuousOn
  have hright : ContinuousOn (fun z => (u z * transportQ a₂ a₃ (F z)) * F z) Ω :=
    (hu.mul ((hF.continuousOn.sub continuousOn_const).mul
      (hF.continuousOn.sub continuousOn_const))).mul hF.continuousOn
  apply eqOn_of_continuousOn_codiscrete hΩ hleft hright
  filter_upwards [haux, transport_eventually_regular_denominator hF hfinite a₂ a₃]
    with z hz hregular
  calc
    D z * deriv F z = u z * (F z * transportQ a₂ a₃ (F z)) :=
      (div_eq_iff hregular).mp hz
    _ = (u z * transportQ a₂ a₃ (F z)) * F z := by ring

/-- Both transport amplitude equations for analytic representatives. The
quotient equalities are assumed only codiscretely, while the resulting
derivative equations hold on the entire domain, including marked points. -/
theorem transport_analytic_amplitudes {Ω : Set ℂ} {F G u v : ℂ → ℂ} {a₂ a₃ : ℂ}
    (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω) (hG : AnalyticOnNhd ℂ G Ω)
    (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hfiniteF : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤)
    (hfiniteG : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => G w - c) z ≠ ⊤)
    (hauxU : ∀ᶠ z in codiscreteWithin Ω,
      (F z - G z) * deriv F z / (F z * transportQ a₂ a₃ (F z)) = u z)
    (hauxV : ∀ᶠ z in codiscreteWithin Ω,
      (F z - G z) * deriv G z / (G z * transportQ a₂ a₃ (G z)) = v z) :
    ∀ z ∈ Ω,
      (F z - G z) * deriv F z = (u z * transportQ a₂ a₃ (F z)) * F z ∧
      (F z - G z) * deriv G z = (v z * transportQ a₂ a₃ (G z)) * G z := by
  have hD : ContinuousOn (fun z => F z - G z) Ω := hF.continuousOn.sub hG.continuousOn
  have hFA := transport_analytic_amplitude hΩ hF hD hu hfiniteF hauxU
  have hGB := transport_analytic_amplitude hΩ hG hD hv hfiniteG hauxV
  intro z hz
  exact ⟨hFA z hz, hGB z hz⟩

/-- A bounded nontrivial approach to a point rules out negative meromorphic
order there. This is the local pole-exclusion step needed at a first-exit
endpoint; no global pole-free hypothesis is used. -/
theorem transport_order_nonneg_of_bounded_approach
    {ι : Type*} {l : Filter ι} [NeBot l] {γ : ι → ℂ} {f : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hγ : Tendsto γ l (𝓝[≠] z)) (hbound : ∀ᶠ i in l, ‖f (γ i)‖ ≤ M) :
    0 ≤ meromorphicOrderAt f z := by
  by_contra hnot
  have hnegative : meromorphicOrderAt f z < 0 := lt_of_not_ge hnot
  have hnorm : Tendsto (fun w => ‖f w‖) (𝓝[≠] z) atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr
      (tendsto_cobounded_of_meromorphicOrderAt_neg hnegative)
  have hlarge : ∀ᶠ i in l, M + 1 ≤ ‖f (γ i)‖ :=
    (tendsto_atTop.mp (hnorm.comp hγ)) (M + 1)
  obtain ⟨i, hi, hbounded⟩ := (hlarge.and hbound).exists
  linarith

/-- The bounded approach used at a transport endpoint gives a local analytic
representative of a meromorphic map. The original function's value at the
endpoint may still be junk; the conclusion identifies punctured germs. -/
theorem transport_analytic_rep_of_bounded_approach
    {ι : Type*} {l : Filter ι} [NeBot l] {γ : ι → ℂ} {f : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hf : MeromorphicAt f z) (hγ : Tendsto γ l (𝓝[≠] z))
    (hbound : ∀ᶠ i in l, ‖f (γ i)‖ ≤ M) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧ F =ᶠ[𝓝[≠] z] f := by
  have hrep : toMeromorphicNFAt f z =ᶠ[𝓝[≠] z] f :=
    hf.eq_nhdsNE_toMeromorphicNFAt.symm
  refine ⟨toMeromorphicNFAt f z, ?_, hrep⟩
  apply (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_congr hrep]
  exact transport_order_nonneg_of_bounded_approach hγ hbound

/-- A meromorphic map admits an analytic representative on a specified
pole-free region. The nonnegative-order hypothesis is essential: this lemma
does not assert that a general normalized pair is globally holomorphic.
The representative has the same punctured germs and all finite-value orders. -/
theorem transport_analytic_rep_on_pole_free {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hno : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧ f =ᶠ[codiscreteWithin Ω] F ∧
      (∀ z ∈ Ω, F =ᶠ[𝓝[≠] z] f) ∧
      (∀ z ∈ Ω, ∀ c : ℂ,
        meromorphicOrderAt (fun w => F w - c) z =
          meromorphicOrderAt (fun w => f w - c) z) := by
  let F := toMeromorphicNFOn f Ω
  have hrep : ∀ z ∈ Ω, F =ᶠ[𝓝[≠] z] f :=
    fun z hz => hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have hFa : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    apply (meromorphicNFOn_toMeromorphicNFOn f Ω hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_congr (hrep z hz)]
    exact hno z hz
  refine ⟨F, hFa, toMeromorphicNFOn_eqOn_codiscrete hf, hrep, ?_⟩
  intro z hz c
  apply meromorphicOrderAt_congr
  filter_upwards [hrep z hz] with w hw
  exact congrArg (fun y : ℂ => y - c) hw

/-- The two auxiliary quotients are invariant codiscretely under a change
of representatives, including their derivative terms. -/
theorem transport_aux_congr_codiscrete {Ω : Set ℂ} {F G F₁ G₁ : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : F =ᶠ[codiscreteWithin Ω] F₁)
    (hG : G =ᶠ[codiscreteWithin Ω] G₁) (a₂ a₃ : ℂ) :
    (fun z => (F z - G z) * deriv F z / (F z * transportQ a₂ a₃ (F z)))
      =ᶠ[codiscreteWithin Ω]
      (fun z => (F₁ z - G₁ z) * deriv F₁ z / (F₁ z * transportQ a₂ a₃ (F₁ z))) ∧
    (fun z => (F z - G z) * deriv G z / (G z * transportQ a₂ a₃ (G z)))
      =ᶠ[codiscreteWithin Ω]
      (fun z => (F₁ z - G₁ z) * deriv G₁ z / (G₁ z * transportQ a₂ a₃ (G₁ z))) := by
  constructor
  · filter_upwards [hF, hG, transport_deriv_congr_codiscrete hΩ hF] with z hzF hzG hzD
    rw [hzF, hzG, hzD]
  · filter_upwards [hF, hG, transport_deriv_congr_codiscrete hΩ hG] with z hzF hzG hzD
    rw [hzF, hzG, hzD]

/-- On an explicitly pole-free open subdomain, meromorphic maps and
codiscrete auxiliary representatives give analytic maps satisfying both
amplitude equations everywhere. No pointwise assertion about the original
maps at their removable singularities is needed. -/
theorem transport_amplitudes_on_pole_free {Ω : Set ℂ} {F G u v : ℂ → ℂ} {a₂ a₃ : ℂ}
    (hΩ : IsOpen Ω) (hF : MeromorphicOn F Ω) (hG : MeromorphicOn G Ω)
    (hnoF : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt F z)
    (hnoG : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt G z)
    (hfiniteF : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤)
    (hfiniteG : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => G w - c) z ≠ ⊤)
    (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hauxU : ∀ᶠ z in codiscreteWithin Ω,
      (F z - G z) * deriv F z / (F z * transportQ a₂ a₃ (F z)) = u z)
    (hauxV : ∀ᶠ z in codiscreteWithin Ω,
      (F z - G z) * deriv G z / (G z * transportQ a₂ a₃ (G z)) = v z) :
    ∃ F₁ G₁ : ℂ → ℂ,
      AnalyticOnNhd ℂ F₁ Ω ∧ AnalyticOnNhd ℂ G₁ Ω ∧
      F =ᶠ[codiscreteWithin Ω] F₁ ∧ G =ᶠ[codiscreteWithin Ω] G₁ ∧
      ∀ z ∈ Ω,
        (F₁ z - G₁ z) * deriv F₁ z = (u z * transportQ a₂ a₃ (F₁ z)) * F₁ z ∧
        (F₁ z - G₁ z) * deriv G₁ z = (v z * transportQ a₂ a₃ (G₁ z)) * G₁ z := by
  obtain ⟨F₁, hF₁, hFF₁, _, horderF⟩ := transport_analytic_rep_on_pole_free hF hnoF
  obtain ⟨G₁, hG₁, hGG₁, _, horderG⟩ := transport_analytic_rep_on_pole_free hG hnoG
  have hfiniteF₁ : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F₁ w - c) z ≠ ⊤ := by
    intro z hz c
    rw [horderF z hz c]
    exact hfiniteF z hz c
  have hfiniteG₁ : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => G₁ w - c) z ≠ ⊤ := by
    intro z hz c
    rw [horderG z hz c]
    exact hfiniteG z hz c
  have haux := transport_aux_congr_codiscrete hΩ hFF₁ hGG₁ a₂ a₃
  refine ⟨F₁, G₁, hF₁, hG₁, hFF₁, hGG₁, ?_⟩
  exact transport_analytic_amplitudes hΩ hF₁ hG₁ hu hv hfiniteF₁ hfiniteG₁
    (haux.1.symm.trans hauxU) (haux.2.symm.trans hauxV)

end ThreeIM
