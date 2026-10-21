module

public import RequestProject.ThreeIM.ClusterWronskian
import Mathlib.Tactic.FieldSimp

/-!
# Genuine finite germs and cleared cluster numerators

A finite meromorphic fiber is a punctured-limit assertion, not a condition on
the arbitrary value of a raw totalized representative. Clearing the poles
produces analytic numerator and denominator functions. Their center values
are recovered by continuity from the punctured identity. No denominator
nonvanishing assumption is needed for this inclusion of finite fiber points.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

/-- A genuine finite punctured limit gives a zero of the analytic cleared
numerator. This remains true if the raw representative has a junk center
value, or the chosen denominator vanishes at the center. -/
theorem cleared_numerator_eq_of_punctured_limit {Φ N Q : ℂ → ℂ} {z q : ℂ}
    (hN : ContinuousAt N z) (hQ : ContinuousAt Q z)
    (hΦ : Tendsto Φ (𝓝[≠] z) (𝓝 q))
    (hclear : N =ᶠ[𝓝[≠] z] (fun w => Φ w * Q w)) :
    N z = q * Q z := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (hN.mono_left nhdsWithin_le_nhds)
    (hΦ.mul (hQ.mono_left nhdsWithin_le_nhds)) hclear

/-- A codiscrete cleared identity on an open domain is enough for the same
finite-fiber inclusion; it need not identify the raw center value. -/
theorem cleared_numerator_eq_of_codiscrete_limit {Ω : Set ℂ} {Φ N Q : ℂ → ℂ} {z q : ℂ}
    (hΩ : IsOpen Ω) (hz : z ∈ Ω) (hN : ContinuousAt N z) (hQ : ContinuousAt Q z)
    (hΦ : Tendsto Φ (𝓝[≠] z) (𝓝 q))
    (hclear : N =ᶠ[codiscreteWithin Ω] (fun w => Φ w * Q w)) :
    N z = q * Q z := by
  have heq := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hclear z hz
  have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ Ω :=
    (show ∀ᶠ w in 𝓝 z, w ∈ Ω from hΩ.mem_nhds hz).filter_mono nhdsWithin_le_nhds
  apply cleared_numerator_eq_of_punctured_limit hN hQ hΦ
  filter_upwards [heq, hmem] with w hw hwΩ
  rcases hw with h | h
  · exact h
  · exact (h hwΩ).elim

/-- Positive meromorphic order in the fiber, rather than a raw point value,
implies vanishing of the cleared analytic numerator. -/
theorem cleared_numerator_eq_of_meromorphic_order_pos {Φ N Q : ℂ → ℂ} {z q : ℂ}
    (hN : ContinuousAt N z) (hQ : ContinuousAt Q z)
    (horder : 0 < meromorphicOrderAt (fun w => Φ w - q) z)
    (hclear : N =ᶠ[𝓝[≠] z] (fun w => Φ w * Q w)) :
    N z = q * Q z := by
  have hlim := (tendsto_zero_of_meromorphicOrderAt_pos horder).add_const q
  have hlimΦ : Tendsto Φ (𝓝[≠] z) (𝓝 q) := by
    simpa only [sub_add_cancel, zero_add] using hlim
  exact cleared_numerator_eq_of_punctured_limit hN hQ hlimΦ hclear

/-- At a regular probe, the logarithmic derivative of the actual analytic
quotient gives the Wronskian factorization. Raw derivatives at isolated junk
points are not substituted in this identity. -/
theorem wronskian_eq_num_den_mul_of_log_deriv {N Q : ℂ → ℂ} {z A : ℂ}
    (hN : DifferentiableAt ℂ N z) (hQ : DifferentiableAt ℂ Q z)
    (hN0 : N z ≠ 0) (hQ0 : Q z ≠ 0)
    (hlog : deriv (fun w => N w / Q w) z / (N z / Q z) = A) :
    deriv N z * Q z - N z * deriv Q z = N z * Q z * A := by
  have hrep : (fun w => N w / Q w) =ᶠ[𝓝 z] (fun w => N w / Q w) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hWr := cleared_fiber_wronskian_of_germ hN hQ hQ0 hrep
  have hd : deriv (fun w => N w / Q w) z = (N z / Q z) * A := by
    simpa only [mul_comm] using (div_eq_iff (div_ne_zero hN0 hQ0)).mp hlog
  rw [hWr, hd]
  field_simp [hQ0]

end ThreeIM
