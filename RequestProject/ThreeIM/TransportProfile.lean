module

public import RequestProject.ThreeIM.TransportLocalSystem
public import RequestProject.ThreeIM.TransportContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From relative auxiliary profiles to real-segment transport

This module combines the original codiscrete auxiliary identities, regular
coordinate reconstruction, explicit profile errors, and meromorphic patch
continuation. The final theorem is the finite-n real-tracking step of the
manuscript. Its input still includes the initial small-amplitude bounds;
normality and scalar compactness, which produce those bounds, are separate.
No global pole-free or global holomorphy premise is imposed on `F,G,W,h`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

noncomputable def transportProfileConstant (a₂ a₃ α : ℂ) (r₀ b₀ : ℝ) : ℝ :=
  let M := (2 * ‖α‖ + r₀) * (1 + b₀)
  ‖a₂ * a₃‖ + M * (M + ‖a₂‖ + ‖a₃‖)

/-- Explicit coefficient error inequalities suffice for the two strict
bootstrap improvements. All quantities in the parameter bounds are real. -/
theorem transport_bounds_of_coefficient_errors
    {a b W h α β : ℂ} {r₀ b₀ eA eB qB : ℝ}
    (hr₀ : 0 < r₀) (hrα : r₀ < ‖α‖)
    (hW : ‖W - 2 * α‖ ≤ r₀) (hh : ‖h‖ ≤ b₀)
    (hA : ‖a - α‖ ≤ eA) (hB : ‖b - β‖ ≤ eB) (hβ : ‖β‖ ≤ qB)
    (herror : eA + (‖α‖ + eA + qB + eB) * b₀ ≤ r₀ / 4)
    (hlog : (r₀ / 2 + eA + (‖α‖ + eA + qB + eB) * b₀ + qB + eB) /
      (2 * ‖α‖ - r₀) ≤ 1 / 4) :
    ‖(a - α) + (a - b) * h‖ ≤ r₀ / 4 ∧
      (-(a - b) * (1 + h) / W).re ≤ -(1 / 4 : ℝ) := by
  have heA : 0 ≤ eA := (norm_nonneg _).trans hA
  have heB : 0 ≤ eB := (norm_nonneg _).trans hB
  have hqB : 0 ≤ qB := (norm_nonneg _).trans hβ
  have hH : 0 ≤ ‖α‖ + eA + qB + eB := by positivity
  have hHh := mul_le_mul_of_nonneg_left hh hH
  have hden : 0 < 2 * ‖α‖ - r₀ := by linarith [norm_nonneg α]
  have hreverse : 2 * ‖α‖ ≤ ‖W‖ + ‖W - 2 * α‖ := by
    have htriangle := norm_sub_le W (W - 2 * α)
    rw [sub_sub_cancel, norm_mul] at htriangle
    norm_num at htriangle
    exact htriangle
  have hWlower : 2 * ‖α‖ - r₀ ≤ ‖W‖ := by linarith
  have hWpositive : 0 < ‖W‖ := hden.trans_le hWlower
  have hWne : W ≠ 0 := norm_pos_iff.mp hWpositive
  constructor
  · exact (transport_rescaled_error_bound hA hB hβ).trans
      ((add_le_add le_rfl hHh).trans herror)
  · apply transport_re_log_derivative_le
    apply (transport_log_derivative_error_bound hWne hA hB hβ).trans
    apply (div_le_iff₀ hWpositive).mpr
    have hparam := (div_le_iff₀ hden).mp hlog
    linarith

/-- Real-segment tracking from the original relative auxiliary profiles.
The initial analytic coordinate bounds are the output required from the
preceding normality/scalar-limit argument. Everywhere else, analyticity and
absence of poles are conclusions of meromorphic continuation.

The scale is allowed to be any analytic nonzero `τ` with real derivative
`τ/2`; the manuscript uses `τ(z) = ε * exp(z/2)`, and `θ(t) = exp(-t)`.
The parameter inequalities are the explicit sufficient conditions recorded
in the transport audit, rather than an additional asymptotic hypothesis. -/
theorem transport_profile_continuation
    {Ω : Set ℂ} {F G τ W h u v : ℂ → ℂ} {θ : ℝ → ℝ}
    {a b δ η θ₀ r₀ b₀ : ℝ} {a₂ a₃ A₀ B₀ : ℂ}
    (hΩ : IsOpen Ω) (hab : a ≤ b) (hA₀ : A₀ ≠ 0) (hB₀ : B₀ ≠ 0)
    (hr₀ : 0 < r₀) (hb₀ : 0 < b₀) (hrα : r₀ < ‖A₀ * (a₂ * a₃)‖)
    (hF : MeromorphicNFOn F Ω) (hG : MeromorphicNFOn G Ω)
    (hW : MeromorphicNFOn W Ω) (hh : MeromorphicNFOn h Ω)
    (hsegment : ∀ t ∈ Icc a b, (t : ℂ) ∈ Ω)
    (hτ : AnalyticOnNhd ℂ τ Ω) (hτ₀ : ∀ z ∈ Ω, τ z ≠ 0)
    (hτderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s : ℝ => τ (s : ℂ)) (τ (t : ℂ) / 2) t)
    (hWgerm : ∀ z ∈ Ω, W =ᶠ[𝓝[≠] z] fun w => (F w - G w) / τ w)
    (hhgerm : ∀ z ∈ Ω, h =ᶠ[𝓝[≠] z] fun w => G w / (F w - G w))
    (hfiniteF : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => F w - c) z ≠ ⊤)
    (hfiniteG : ∀ z ∈ Ω, ∀ c : ℂ,
      meromorphicOrderAt (fun w => G w - c) z ≠ ⊤)
    (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hauxU : (fun z => (F z - G z) * deriv F z / (F z * transportQ a₂ a₃ (F z)))
      =ᶠ[codiscreteWithin Ω] u)
    (hauxV : (fun z => (F z - G z) * deriv G z / (G z * transportQ a₂ a₃ (G z)))
      =ᶠ[codiscreteWithin Ω] v)
    (hshare : ∀ z ∈ Ω,
      0 < (meromorphicOrderAt F z).untop₀.toNat ↔ 0 < (meromorphicOrderAt G z).untop₀.toNat)
    (hθ : ∀ t ∈ Icc a b, 0 < θ t ∧ θ t ≤ θ₀)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hscale : ∀ t ∈ Icc a b, ‖τ (t : ℂ)‖ ≤ δ)
    (hprofileU : ∀ t ∈ Icc a b, ‖u (t : ℂ) / (τ (t : ℂ) * A₀) - 1‖ ≤ η)
    (hprofileV : ∀ t ∈ Icc a b,
      ‖v (t : ℂ) / (τ (t : ℂ) * (B₀ * (θ t : ℂ))) - 1‖ ≤ η)
    (hparameters :
      let α := A₀ * (a₂ * a₃)
      let C := transportProfileConstant a₂ a₃ α r₀ b₀
      let eA := ‖A₀‖ * C * (δ + η)
      let eB := ‖B₀‖ * C * θ₀ * (δ + η)
      let qB := ‖B₀ * (a₂ * a₃)‖ * θ₀
      let H := ‖α‖ + eA + qB + eB
      eA + H * b₀ ≤ r₀ / 4 ∧
        (r₀ / 2 + eA + H * b₀ + qB + eB) / (2 * ‖α‖ - r₀) ≤ 1 / 4)
    (hWa : AnalyticAt ℂ W (a : ℂ)) (hha : AnalyticAt ℂ h (a : ℂ))
    (hWinit : ‖W (a : ℂ) - 2 * (A₀ * (a₂ * a₃))‖ ≤ r₀ / 4)
    (hhinit : ‖h (a : ℂ)‖ ≤ b₀ / 2) :
    ∀ t ∈ Icc a b, AnalyticAt ℂ F (t : ℂ) ∧ AnalyticAt ℂ G (t : ℂ) ∧
      ‖W (t : ℂ) - 2 * (A₀ * (a₂ * a₃))‖ ≤ r₀ / 2 ∧
      ‖h (t : ℂ)‖ ≤ ‖h (a : ℂ)‖ ∧
      F (t : ℂ) = τ (t : ℂ) * W (t : ℂ) * (1 + h (t : ℂ)) ∧
      G (t : ℂ) = τ (t : ℂ) * W (t : ℂ) * h (t : ℂ) ∧
      F (t : ℂ) - G (t : ℂ) ≠ 0 := by
  let α := A₀ * (a₂ * a₃)
  let M := (2 * ‖α‖ + r₀) * (1 + b₀)
  let C := transportProfileConstant a₂ a₃ α r₀ b₀
  let eA := ‖A₀‖ * C * (δ + η)
  let eB := ‖B₀‖ * C * θ₀ * (δ + η)
  let qB := ‖B₀ * (a₂ * a₃)‖ * θ₀
  let H := ‖α‖ + eA + qB + eB
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC : 0 ≤ C := by dsimp only [C, transportProfileConstant]; positivity
  have hη : 0 ≤ η := (norm_nonneg _).trans (hprofileU a ⟨le_rfl, hab⟩)
  have hparameters' : eA + H * b₀ ≤ r₀ / 4 ∧
      (r₀ / 2 + eA + H * b₀ + qB + eB) / (2 * ‖α‖ - r₀) ≤ 1 / 4 := hparameters
  have hlocal : ∀ x ∈ Icc a b,
      AnalyticAt ℂ W (x : ℂ) → AnalyticAt ℂ h (x : ℂ) →
      ‖W (x : ℂ) - 2 * α‖ ≤ r₀ → ‖h (x : ℂ)‖ ≤ b₀ →
      h (x : ℂ) ≠ 0 ∧
        HasDerivAt (fun t : ℝ => W (t : ℂ))
          ((-(1 / 2 : ℝ)) • (W (x : ℂ) - 2 * α) +
            transportError a₂ a₃ u v F G τ h α x) x ∧
        HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x ∧
        ‖transportError a₂ a₃ u v F G τ h α x‖ ≤ r₀ / 4 ∧
        (deriv h (x : ℂ) / h (x : ℂ)).re ≤ 0 := by
    intro x hx hWx hhx hWbound hhbound
    have hxΩ := hsegment x hx
    have hWne : W (x : ℂ) ≠ 0 := by
      intro hzero
      have hbound := hWbound
      rw [hzero, zero_sub, norm_neg, norm_mul] at hbound
      norm_num at hbound
      linarith [norm_nonneg α]
    have hsystem := transport_local_coordinate_system (α := α) hΩ hxΩ
      (hF hxΩ) (hG hxΩ) (hτ (x : ℂ) hxΩ) (hτ₀ (x : ℂ) hxΩ) (hτderiv x hx)
      hWx hWne hhx (hWgerm (x : ℂ) hxΩ) (hhgerm (x : ℂ) hxΩ)
      (hfiniteF (x : ℂ) hxΩ) (hfiniteG (x : ℂ) hxΩ)
      (hu.continuousAt (hΩ.mem_nhds hxΩ)) (hv.continuousAt (hΩ.mem_nhds hxΩ))
      hauxU hauxV (hshare (x : ℂ) hxΩ)
    obtain ⟨_, _, _, _, hFvalue, hGvalue, _, _⟩ :=
      transport_regular_reconstruction (hF hxΩ) (hG hxΩ) (hτ (x : ℂ) hxΩ)
        (hτ₀ (x : ℂ) hxΩ) hWx hWne hhx (hWgerm (x : ℂ) hxΩ) (hhgerm (x : ℂ) hxΩ)
    have hsize := transport_coordinate_norms hFvalue hGvalue (hscale x hx) hWbound hhbound
    have hcoeff := transport_scaled_coefficients_bounds (a₂ := a₂) (a₃ := a₃) (M := M) (η := η)
      (hτ₀ (x : ℂ) hxΩ) hA₀ hB₀ (hθ x hx).1 hδ hδ₁ hM hsize.1 hsize.2
      (hprofileU x hx) (hprofileV x hx)
    have hAerror : ‖transportScaledCoefficient a₂ a₃ u F τ (x : ℂ) - α‖ ≤ eA := hcoeff.1
    have hBC : 0 ≤ (‖B₀‖ * C) * (δ + η) := by positivity
    have hBerror : ‖transportScaledCoefficient a₂ a₃ v G τ (x : ℂ) -
        (B₀ * (a₂ * a₃)) * (θ x : ℂ)‖ ≤ eB := by
      apply hcoeff.2.trans
      calc
        θ x * ((‖B₀‖ * C) * (δ + η)) ≤ θ₀ * ((‖B₀‖ * C) * (δ + η)) :=
          mul_le_mul_of_nonneg_right (hθ x hx).2 hBC
        _ = eB := by dsimp only [eB]; ring
    have hβ : ‖(B₀ * (a₂ * a₃)) * (θ x : ℂ)‖ ≤ qB := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ x hx).1.le]
      exact mul_le_mul_of_nonneg_left (hθ x hx).2 (norm_nonneg _)
    have hbounds := transport_bounds_of_coefficient_errors hr₀ hrα hWbound hhbound
      hAerror hBerror hβ hparameters'.1 hparameters'.2
    have herror : ‖transportError a₂ a₃ u v F G τ h α x‖ ≤ r₀ / 4 := hbounds.1
    have hlog : (deriv h (x : ℂ) / h (x : ℂ)).re ≤ 0 := by
      rw [hsystem.2.2.2]
      exact hbounds.2.trans (by norm_num)
    exact ⟨hsystem.1, hsystem.2.1, hsystem.2.2.1, herror, hlog⟩
  have htracked := transport_meromorphic_continuation
    (E := transportError a₂ a₃ u v F G τ h α) (v := fun t => deriv h (t : ℂ))
    hab hr₀ hb₀ hrα hW hh hsegment hWa hha
    (fun x hx hw hh hwbound hhbound => (hlocal x hx hw hh hwbound hhbound).2.1)
    (fun x hx hw hh hwbound hhbound => (hlocal x hx hw hh hwbound hhbound).2.2.1)
    (fun x hx hw hh hwbound hhbound => (hlocal x hx hw hh hwbound hhbound).2.2.2.1)
    (fun x hx hw hh hwbound hhbound => (hlocal x hx hw hh hwbound hhbound).1)
    (fun x hx hw hh hwbound hhbound => (hlocal x hx hw hh hwbound hhbound).2.2.2.2)
    hWinit hhinit
  intro t ht
  have htrack := htracked t ht
  have htΩ := hsegment t ht
  obtain ⟨hFa, hGa, _, _, hFvalue, hGvalue, _, hD⟩ :=
    transport_regular_reconstruction (hF htΩ) (hG htΩ) (hτ (t : ℂ) htΩ)
      (hτ₀ (t : ℂ) htΩ) htrack.1 htrack.2.2.2.2.2 htrack.2.1
      (hWgerm (t : ℂ) htΩ) (hhgerm (t : ℂ) htΩ)
  exact ⟨hFa, hGa, htrack.2.2.1, htrack.2.2.2.2.1, hFvalue, hGvalue, hD⟩

end ThreeIM
