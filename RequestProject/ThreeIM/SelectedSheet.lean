module

public import RequestProject.ThreeIM.Selected

/-!
# A single normalized marked sheet

These are the actual one-radius data needed to build a selected
configuration. The physical inverse-branch construction must produce this
data; the structure does not assert their existence.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

structure SelectedSheet (a : Fin 3 → ℂ) (B : ℝ) where
  j : Fin 3
  m : ℕ
  two_le_m : 2 ≤ m
  m_le_thirty : m ≤ 30
  F : ℂ → ℂ
  G : ℂ → ℂ
  k : ℂ → ℂ
  pair : NormalizedPair (ball 0 (B ^ 6 / 2)) F G a
  marked_F : mult F (a j : Sphere) 0 = 1
  marked_G : mult G (a j : Sphere) 0 = m
  k_holo : DifferentiableOn ℂ k (ball 0 (B ^ 6 / 2))
  k_ne_zero : ∀ s ∈ ball (0 : ℂ) (B ^ 6 / 2), k s ≠ 0
  coeff_U : ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (B ^ 6 / 2)),
    auxU a F G s = (Real.sqrt (1 / m) : ℂ) * Complex.exp (s / 2) / k s
  coeff_V : ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (B ^ 6 / 2)),
    auxV a F G s = (Real.sqrt (1 / m) : ℂ)⁻¹ * Complex.exp (-s / 2) / k s
  control_center : |Real.log ‖k 0‖| ≤ 9 * B ^ 2
  control_log : ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ (ball 0 (B ^ 6 / 2)) ∧ ℓ 0 = 0 ∧
    ∀ s ∈ ball (0 : ℂ) (B ^ 6 / 2),
      Complex.exp (ℓ s) = k s / k 0 ∧ ‖ℓ s‖ ≤ 12 * B⁻¹ ^ 3

end ThreeIM
