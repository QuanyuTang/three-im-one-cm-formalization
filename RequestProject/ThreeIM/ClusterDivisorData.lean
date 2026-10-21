module

public import RequestProject.ThreeIM.ClusterFactorData
public import RequestProject.ThreeIM.ClusterDivisorBudget
import Mathlib.Tactic.Linarith

/-!
# A common actual divisor set for the three extracted factors

The finite set is the union of the genuine Phi, A, and Psi divisor
supports. Its cardinality and all three weighted degrees are controlled
by the single-radius budget. Empty supports are allowed throughout.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric
open scoped BigOperators

namespace ThreeIM

noncomputable def jointDivisorSupport {Φ A Ψ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ) :
    Finset ℂ := D.support ∪ E.support ∪ P.support

noncomputable def jointDivisorMass {Φ A Ψ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ) : ℝ :=
    ∑ α ∈ jointDivisorSupport D E P,
      (|(D.exponent α : ℝ)| + |(E.exponent α : ℝ)| + |(P.exponent α : ℝ)|)

theorem jointDivisorSupport_roots {Φ A Ψ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ) :
    ∀ α ∈ jointDivisorSupport D E P, ‖α‖ ≤ ρ := by
  intro α hα
  rcases Finset.mem_union.mp hα with hDE | hP
  · rcases Finset.mem_union.mp hDE with hD | hE
    · exact D.roots α hD
    · exact E.roots α hE
  · exact P.roots α hP

/-- Every member of the union contributes at least one unit of actual
absolute integer multiplicity. This remains valid for an empty union. -/
theorem jointDivisorSupport_card_le_mass {Φ A Ψ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ) :
    ((jointDivisorSupport D E P).card : ℝ) ≤ jointDivisorMass D E P := by
  classical
  have hcard : ((jointDivisorSupport D E P).card : ℝ) =
      ∑ α ∈ jointDivisorSupport D E P, (1 : ℝ) := by simp
  rw [hcard, jointDivisorMass]
  apply Finset.sum_le_sum
  intro α hα
  rcases Finset.mem_union.mp hα with hDE | hP
  · rcases Finset.mem_union.mp hDE with hD | hE
    · have h1 : (1 : ℝ) ≤ |(D.exponent α : ℝ)| := by
        exact_mod_cast Int.one_le_abs ((D.support_iff α).mp hD)
      linarith [abs_nonneg (E.exponent α : ℝ), abs_nonneg (P.exponent α : ℝ)]
    · have h1 : (1 : ℝ) ≤ |(E.exponent α : ℝ)| := by
        exact_mod_cast Int.one_le_abs ((E.support_iff α).mp hE)
      linarith [abs_nonneg (D.exponent α : ℝ), abs_nonneg (P.exponent α : ℝ)]
  · have h1 : (1 : ℝ) ≤ |(P.exponent α : ℝ)| := by
      exact_mod_cast Int.one_le_abs ((P.support_iff α).mp hP)
    linarith [abs_nonneg (D.exponent α : ℝ), abs_nonneg (E.exponent α : ℝ)]

/-- The mass equals the sum of the three actual weighted degrees; padding
the three supports to their union adds only zero coefficients. -/
theorem jointDivisorMass_eq_sum_degrees {Φ A Ψ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ) :
    jointDivisorMass D E P = (∑ α ∈ D.support, |(D.exponent α : ℝ)|) +
      (∑ α ∈ E.support, |(E.exponent α : ℝ)|) + (∑ α ∈ P.support, |(P.exponent α : ℝ)|) := by
  classical
  have hD : D.support ⊆ jointDivisorSupport D E P := by
    intro α hα
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hα)
  have hE : E.support ⊆ jointDivisorSupport D E P := by
    intro α hα
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hα)
  have hP : P.support ⊆ jointDivisorSupport D E P := Finset.subset_union_right
  have sum_eq {F : ℂ → ℂ} (Q : DivisorFactorData F ρ)
      (hQ : Q.support ⊆ jointDivisorSupport D E P) :
      (∑ α ∈ jointDivisorSupport D E P, |(Q.exponent α : ℝ)|) =
        ∑ α ∈ Q.support, |(Q.exponent α : ℝ)| := by
    symm
    apply Finset.sum_subset hQ
    intro α _ hα
    have hz : Q.exponent α = 0 := not_not.mp (mt (Q.support_iff α).mpr hα)
    simp only [hz, Int.cast_zero, abs_zero]
  rw [jointDivisorMass, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_eq D hD, sum_eq E hE, sum_eq P hP]

/-- The actual extracted data satisfy the source's single-radius mass
bound, with no independent multiplicity or support hypothesis. -/
theorem jointDivisorMass_le_window {Φ A Ψ : ℂ → ℂ} {ρ R Δ : ℝ}
    (D : DivisorFactorData Φ ρ) (E : DivisorFactorData A ρ) (P : DivisorFactorData Ψ ρ)
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hwindow : ρ ≤ R - Δ / 8) :
    jointDivisorMass D E P ≤ 8 * R / Δ *
      (ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R) := by
  have hb := three_absolute_meromorphic_orders_le_window (jointDivisorSupport D E P)
    hΦ hA hΨ hρ hΔ hwindow (jointDivisorSupport_roots D E P)
  have heq : jointDivisorMass D E P =
      ∑ α ∈ jointDivisorSupport D E P,
        (|((meromorphicOrderAt Φ α).untop₀ : ℝ)| +
          |((meromorphicOrderAt A α).untop₀ : ℝ)| + |((meromorphicOrderAt Ψ α).untop₀ : ℝ)|) := by
    apply Finset.sum_congr rfl
    intro α hα
    have hm : α ∈ closedBall (0 : ℂ) ρ := by
      simpa only [mem_closedBall, dist_zero_right] using jointDivisorSupport_roots D E P α hα
    rw [D.exponent_eq_order α hm, E.exponent_eq_order α hm, P.exponent_eq_order α hm]
  rw [heq]
  exact hb

end ThreeIM
