module

public import RequestProject.ThreeIM.TransportReconstruction
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual local transport equations from auxiliary representatives

The auxiliary quotient identities hold only codiscretely. At a reconstructed
regular point, local finite orders allow clearing their denominators in a
punctured neighborhood. Continuity then proves the amplitude equations at
the center, even when a factor of the displayed denominator vanishes there.

The final theorem supplies the exact derivative and logarithmic-derivative
identities needed by meromorphic stable continuation. Its maps `F,G` are
normal forms; global holomorphy or absence of poles is never assumed.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

noncomputable def transportScaledCoefficient (a₂ a₃ : ℂ)
    (u F τ : ℂ → ℂ) (z : ℂ) : ℂ := u z * transportQ a₂ a₃ (F z) / τ z

noncomputable def transportError (a₂ a₃ : ℂ) (u v F G τ h : ℂ → ℂ)
    (α : ℂ) (x : ℝ) : ℂ :=
  (transportScaledCoefficient a₂ a₃ u F τ (x : ℂ) - α) +
    (transportScaledCoefficient a₂ a₃ u F τ (x : ℂ) -
      transportScaledCoefficient a₂ a₃ v G τ (x : ℂ)) * h (x : ℂ)

/-- Local clearing of an auxiliary quotient. The hypotheses concern
punctured germs and continuous representatives, not raw center values. -/
theorem transport_amplitude_at {F D u : ℂ → ℂ} {z a₂ a₃ : ℂ}
    (hF : AnalyticAt ℂ F z) (hD : ContinuousAt D z) (hu : ContinuousAt u z)
    (hfinite : ∀ c : ℂ, meromorphicOrderAt (fun w => F w - c) z ≠ ⊤)
    (haux : (fun w => D w * deriv F w / (F w * transportQ a₂ a₃ (F w)))
      =ᶠ[𝓝[≠] z] u) :
    D z * deriv F z = (u z * transportQ a₂ a₃ (F z)) * F z := by
  have hne : ∀ c : ℂ, ∀ᶠ w in 𝓝[≠] z, F w ≠ c := by
    intro c
    have h := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hF.sub analyticAt_const).meromorphicAt).mp (hfinite c)
    filter_upwards [h] with w hw
    exact sub_ne_zero.mp hw
  have hregular : ∀ᶠ w in 𝓝[≠] z, F w * transportQ a₂ a₃ (F w) ≠ 0 := by
    filter_upwards [hne 0, hne a₂, hne a₃] with w hw₀ hw₂ hw₃
    exact mul_ne_zero hw₀ (mul_ne_zero (sub_ne_zero.mpr hw₂) (sub_ne_zero.mpr hw₃))
  have heq : (fun w => D w * deriv F w)
      =ᶠ[𝓝[≠] z] fun w => (u w * transportQ a₂ a₃ (F w)) * F w := by
    filter_upwards [haux, hregular] with w hw hden
    calc
      D w * deriv F w = u w * (F w * transportQ a₂ a₃ (F w)) := (div_eq_iff hden).mp hw
      _ = _ := by ring
  have hleft := hD.mul hF.deriv.continuousAt
  have hright : ContinuousAt (fun w => (u w * transportQ a₂ a₃ (F w)) * F w) z :=
    (hu.mul ((hF.continuousAt.sub_const a₂).mul
      (hF.continuousAt.sub_const a₃))).mul hF.continuousAt
  exact ((hleft.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hright).mp heq).eq_of_nhds

/-- The local transport system at a regular coordinate point. Auxiliary
equalities are still supplied only codiscretely on the original open domain.
The displayed real derivatives are those of the regular normal forms. -/
theorem transport_local_coordinate_system
    {Ω : Set ℂ} {F G τ W h u v : ℂ → ℂ} {x : ℝ} {a₂ a₃ α : ℂ}
    (hΩ : IsOpen Ω) (hx : (x : ℂ) ∈ Ω)
    (hF : MeromorphicNFAt F (x : ℂ)) (hG : MeromorphicNFAt G (x : ℂ))
    (hτ : AnalyticAt ℂ τ (x : ℂ)) (hτ₀ : τ (x : ℂ) ≠ 0)
    (hτderiv : HasDerivAt (fun t : ℝ => τ (t : ℂ)) (τ (x : ℂ) / 2) x)
    (hW : AnalyticAt ℂ W (x : ℂ)) (hW₀ : W (x : ℂ) ≠ 0)
    (hh : AnalyticAt ℂ h (x : ℂ))
    (hWgerm : W =ᶠ[𝓝[≠] (x : ℂ)] fun z => (F z - G z) / τ z)
    (hhgerm : h =ᶠ[𝓝[≠] (x : ℂ)] fun z => G z / (F z - G z))
    (hfiniteF : ∀ c : ℂ, meromorphicOrderAt (fun w => F w - c) (x : ℂ) ≠ ⊤)
    (hfiniteG : ∀ c : ℂ, meromorphicOrderAt (fun w => G w - c) (x : ℂ) ≠ ⊤)
    (hu : ContinuousAt u (x : ℂ)) (hv : ContinuousAt v (x : ℂ))
    (hauxU : (fun z => (F z - G z) * deriv F z / (F z * transportQ a₂ a₃ (F z)))
      =ᶠ[codiscreteWithin Ω] u)
    (hauxV : (fun z => (F z - G z) * deriv G z / (G z * transportQ a₂ a₃ (G z)))
      =ᶠ[codiscreteWithin Ω] v)
    (hshare : 0 < (meromorphicOrderAt F (x : ℂ)).untop₀.toNat ↔
      0 < (meromorphicOrderAt G (x : ℂ)).untop₀.toNat) :
    h (x : ℂ) ≠ 0 ∧
      HasDerivAt (fun t : ℝ => W (t : ℂ))
        ((-(1 / 2 : ℝ)) • (W (x : ℂ) - 2 * α) +
          transportError a₂ a₃ u v F G τ h α x) x ∧
      HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x ∧
      deriv h (x : ℂ) / h (x : ℂ) =
        -(transportScaledCoefficient a₂ a₃ u F τ (x : ℂ) -
          transportScaledCoefficient a₂ a₃ v G τ (x : ℂ)) *
          (1 + h (x : ℂ)) / W (x : ℂ) := by
  obtain ⟨hFa, hGa, _, _, _, _, hDvalue, hD⟩ :=
    transport_regular_reconstruction hF hG hτ hτ₀ hW hW₀ hh hWgerm hhgerm
  have hFfinite : meromorphicOrderAt F (x : ℂ) ≠ ⊤ := by
    simpa only [sub_zero] using hfiniteF 0
  have hGfinite : meromorphicOrderAt G (x : ℂ) ≠ ⊤ := by
    simpa only [sub_zero] using hfiniteG 0
  have hhne := transport_h_ne_zero_of_shared_zero hF hG hτ hτ₀ hW hW₀ hh
    hWgerm hhgerm hFfinite hGfinite hshare
  have hDcont := hFa.continuousAt.sub hGa.continuousAt
  have hFA := transport_amplitude_at hFa hDcont hu hfiniteF
    (transport_eventuallyEq_nhdsNE_of_codiscrete hΩ hauxU hx)
  have hGB := transport_amplitude_at hGa hDcont hv hfiniteG
    (transport_eventuallyEq_nhdsNE_of_codiscrete hΩ hauxV hx)
  have hWfull : W =ᶠ[𝓝 (x : ℂ)] fun z => (F z - G z) / τ z :=
    (hW.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hFa.sub hGa).div hτ hτ₀).continuousAt).mp hWgerm
  have hhfull : h =ᶠ[𝓝 (x : ℂ)] fun z => G z / (F z - G z) :=
    (hh.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hGa.div (hFa.sub hGa) hD).continuousAt).mp hhgerm
  have hWreal : (fun t : ℝ => W (t : ℂ))
      =ᶠ[𝓝 x] fun t : ℝ => (F (t : ℂ) - G (t : ℂ)) / τ (t : ℂ) :=
    Complex.continuous_ofReal.continuousAt.eventually hWfull
  have hhreal : (fun t : ℝ => h (t : ℂ))
      =ᶠ[𝓝 x] fun t : ℝ => G (t : ℂ) / (F (t : ℂ) - G (t : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.eventually hhfull
  have hWvalue := hWfull.eq_of_nhds
  have hhvalue := hhfull.eq_of_nhds
  have hFd := hFa.differentiableAt.hasDerivAt.comp_ofReal
  have hGd := hGa.differentiableAt.hasDerivAt.comp_ofReal
  have hhd := hh.differentiableAt.hasDerivAt.comp_ofReal
  have hsystem := transport_coordinate_derivatives hFd hGd hD hFA hGB
  have hDderiv := hsystem.1
  rw [← hhvalue] at hDderiv
  have hscaled := transport_rescaled_derivative (α := α) hDderiv hτderiv hτ₀
  rw [← hWvalue] at hscaled
  have hWode : HasDerivAt (fun t : ℝ => W (t : ℂ))
      ((-(1 / 2 : ℝ)) • (W (x : ℂ) - 2 * α) +
        transportError a₂ a₃ u v F G τ h α x) x :=
    hscaled.congr_of_eventuallyEq hWreal
  have hGne : G (x : ℂ) ≠ 0 := by
    intro hzero
    apply hhne
    rw [hhvalue, hzero, zero_div]
  have hlog := transport_log_derivative hFd hGd hD hGne hFA hGB
  rw [← hhreal.deriv_eq, hhd.deriv, ← hhvalue, hDvalue] at hlog
  have hlogscaled : deriv h (x : ℂ) / h (x : ℂ) =
      -(transportScaledCoefficient a₂ a₃ u F τ (x : ℂ) -
        transportScaledCoefficient a₂ a₃ v G τ (x : ℂ)) *
        (1 + h (x : ℂ)) / W (x : ℂ) := by
    rw [hlog]
    dsimp only [transportScaledCoefficient]
    field_simp [hτ₀, hW₀]
  exact ⟨hhne, hWode, hhd, hlogscaled⟩

end ThreeIM
