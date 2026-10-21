module

public import RequestProject.ThreeIM.SphereRescaling
public import RequestProject.ThreeIM.SpherePicardDerivative

/-!
# Montel's three-omitted-values criterion

Zalcman rescaling at a nonnormal point would give an entire nonconstant
spherical limit. Local Hurwitz preserves the three omitted values on its
exhausting rescaled disks, contradicting spherical little Picard.
-/

@[expose] public section

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem isNormalAt_of_omits_three_sphere {𝓕 : Set (ℂ → OnePoint ℂ)}
    {U : Set ℂ} (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ F ∈ 𝓕, ∀ w ∈ U, F w ≠ a)
    (hb : ∀ F ∈ 𝓕, ∀ w ∈ U, F w ≠ b)
    (hc : ∀ F ∈ 𝓕, ∀ w ∈ U, F w ≠ c) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    IsNormalAt 𝓕 z₀ := by
  classical
  by_contra hnot
  obtain ⟨F, z, ρ, G, hF, hz, _, hρ, hG, hG0, _, hconv⟩ :=
    exists_zalcman_rescale hU hol hz₀ hnot
  have hGn : ¬ ∃ p : OnePoint ℂ, ∀ w, G w = p := by
    rintro ⟨p, hp⟩
    have hconstant : G = fun _ => p := funext hp
    have hz := sphericalDeriv_const p 0
    rw [← hconstant, hG0] at hz
    exact one_ne_zero hz
  have holF : ∀ n, SphereHolomorphicOn (F n) U := fun n => hol (F n) (hF n)
  obtain ⟨A, hAa, _, _⟩ := exists_gl_smul_eq_zero_one_infty hab hac hbc
  obtain ⟨B, hBb, _, _⟩ := exists_gl_smul_eq_zero_one_infty hab.symm hbc hac
  obtain ⟨C, hCc, _, _⟩ := exists_gl_smul_eq_zero_one_infty hac.symm hbc.symm hab
  have haG : ∀ w, G w ≠ a := sphere_limit_omits_of_mobius_zero A hAa hG hGn
    (rescale_locally_eventually_holo_omits hU holF (fun n w hw => ha (F n) (hF n) w hw)
      hz₀ hz hρ) hconv
  have hbG : ∀ w, G w ≠ b := sphere_limit_omits_of_mobius_zero B hBb hG hGn
    (rescale_locally_eventually_holo_omits hU holF (fun n w hw => hb (F n) (hF n) w hw)
      hz₀ hz hρ) hconv
  have hcG : ∀ w, G w ≠ c := sphere_limit_omits_of_mobius_zero C hCc hG hGn
    (rescale_locally_eventually_holo_omits hU holF (fun n w hw => hc (F n) (hF n) w hw)
      hz₀ hz hρ) hconv
  exact sphere_picard_normalized_impossible hG a b c hab hac hbc haG hbG hcG hG0

end ThreeIM
