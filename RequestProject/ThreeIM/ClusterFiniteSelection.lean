module

public import RequestProject.ThreeIM.ClusterCanonicalSelection
public import RequestProject.ThreeIM.ClusterActualEtaCount

/-!
# Selection from genuine fibers with the actual finite-disk budget

The common divisor set may be empty. Its truncated distance is then one.
The two analytic counts use the same extracted D/E/P and count genuine
meromorphic fibers; the selected sheet uses the honest canonical models.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- Outside the closed eta-clusters the truncated distance is at least eta,
including the empty-divisor case. -/
theorem truncatedDivisorDistance_ge_of_outside_clusters (S : Finset ℂ) {z : ℂ} {η : ℝ}
    (hη : η ≤ 1) (haway : ∀ c ∈ S, η ≤ dist z c) :
    η ≤ truncatedDivisorDistance S z := by
  classical
  by_cases hS : S = ∅
  · simpa only [hS, truncatedDivisorDistance_empty] using hη
  · have hne := Finset.nonempty_iff_ne_empty.mpr hS
    rw [truncatedDivisorDistance_of_nonempty hne]
    exact le_min hη ((le_infDist (show (S : Set ℂ).Nonempty from hne)).mpr
      (fun c hc => haway c hc))

/-- If every genuine q-point is in a divisor cluster or fails the large
log-derivative test, there are at most 2500250 B^26 such points. -/
theorem actual_exceptional_qpoints_card_le (s : Finset ℂ) {Φ A Ψ : ℂ → ℂ}
    {q : ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ r ∧ 0 < meromorphicOrderAt (fun w => Φ w - q) z)
    (hbad : ∀ z ∈ s,
      Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
        truncatedDivisorDistance (jointDivisorSupport D E P) z →
      ‖E.exponentialModel z‖ ≤ (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z) :
    (s.card : ℝ) ≤ 2500250 * (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 := by
  classical
  let B := finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)
  let S := jointDivisorSupport D E P
  let η := Real.exp (-4 * B)
  let near : ℂ → Prop := fun z => ∃ c ∈ S, dist z c ≤ η
  have hR1 : 1 ≤ R := by linarith
  have hB : 4 ≤ B := (finiteDiskBudget_basic_controls hR1 hΔ hΔ1
    (finiteDiskCoefficientMass_ge_one Φ A Ψ hR1)).1
  have hη : η ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have haway : ∀ z ∈ s.filter (fun z => ¬near z), η ≤ truncatedDivisorDistance S z := by
    intro z hz
    apply truncatedDivisorDistance_ge_of_outside_clusters S hη
    intro c hc
    exact le_of_lt (lt_of_not_ge (fun h => (Finset.mem_filter.mp hz).2 ⟨c, hc, h⟩))
  have hn := actual_eta_union_meromorphic_card_le (s.filter near) D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR
    (fun z hz => hs z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
  have hf := canonical_bad_qpoints_card_le (s.filter (fun z => ¬near z)) D E P
    hΦ hA hΨ hlog hr hΔ hΔ1 hR
    (fun z hz => (hs z (Finset.mem_filter.mp hz).1).1) haway
    (fun z hz => hbad z (Finset.mem_filter.mp hz).1 (haway z hz))
    (fun z hz => (hs z (Finset.mem_filter.mp hz).1).2)
  have hcard : ((s.filter near).card : ℝ) + ((s.filter (fun z => ¬near z)).card : ℝ) = s.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := s) near)
  have hp : B ^ 3 ≤ B ^ 26 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by decide : 3 ≤ 26)
  change ((s.filter near).card : ℝ) ≤ 250 * B ^ 3 at hn
  change ((s.filter (fun z => ¬near z)).card : ℝ) ≤ 2500000 * B ^ 26 at hf
  change (s.card : ℝ) ≤ 2500250 * B ^ 26
  linarith

/-- More than the actual polynomial exception budget gives a genuine
q-point at which the canonical inverse-sheet construction applies. -/
theorem exists_actual_good_qpoint (s : Finset ℂ) {Φ A Ψ : ℂ → ℂ}
    {q : ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ r ∧ 0 < meromorphicOrderAt (fun w => Φ w - q) z)
    (hlarge : 2500250 * (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 < s.card) :
    ∃ z ∈ s,
      Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
        truncatedDivisorDistance (jointDivisorSupport D E P) z ∧
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z < ‖E.exponentialModel z‖ := by
  classical
  by_contra h
  have hbad : ∀ z ∈ s,
      Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
        truncatedDivisorDistance (jointDivisorSupport D E P) z →
      ‖E.exponentialModel z‖ ≤ (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z := by
    intro z hz haway
    exact le_of_not_gt (fun hgood => h ⟨z, hz, haway, hgood⟩)
  exact (not_lt_of_ge (actual_exceptional_qpoints_card_le s D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR hs hbad)) hlarge

/-- A fixed finite set of possible ratio values costs only its cardinality
in the uniform exception budget. This is the actual finite-disk interface
used by bounded marked multiplicities before passing to a fixed type. -/
theorem exists_actual_good_point_in_finite_fibers (s Q : Finset ℂ) {Φ A Ψ : ℂ → ℂ}
    {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hdisk : ∀ z ∈ s, ‖z‖ ≤ r)
    (hfibers : ∀ z ∈ s, ∃ q ∈ Q, 0 < meromorphicOrderAt (fun w => Φ w - q) z)
    (hlarge : (Q.card : ℝ) * 2500250 *
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 < s.card) :
    ∃ q ∈ Q, ∃ z ∈ s, 0 < meromorphicOrderAt (fun w => Φ w - q) z ∧
      Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
        truncatedDivisorDistance (jointDivisorSupport D E P) z ∧
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z < ‖E.exponentialModel z‖ := by
  classical
  by_contra h
  let t : ℂ → Finset ℂ := fun q => s.filter (fun z => 0 < meromorphicOrderAt (fun w => Φ w - q) z)
  have hbad : ∀ z ∈ s,
      Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
        truncatedDivisorDistance (jointDivisorSupport D E P) z →
      ‖E.exponentialModel z‖ ≤ (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z := by
    intro z hz haway
    apply le_of_not_gt
    intro hgood
    obtain ⟨q, hq, hqz⟩ := hfibers z hz
    exact h ⟨q, hq, z, hz, hqz, haway, hgood⟩
  have hsub : s ⊆ Q.biUnion t := by
    intro z hz
    obtain ⟨q, hq, hqz⟩ := hfibers z hz
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hz, hqz⟩⟩
  have hcount : (s.card : ℝ) ≤ ∑ q ∈ Q, ((t q).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hupper : (∑ q ∈ Q, ((t q).card : ℝ)) ≤ (Q.card : ℝ) * 2500250 *
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 := by
    calc
      _ ≤ ∑ _q ∈ Q, 2500250 * (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 := by
        apply Finset.sum_le_sum
        intro q _
        exact actual_exceptional_qpoints_card_le (t q) D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR
          (fun z hz => ⟨hdisk z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
          (fun z hz => hbad z (Finset.mem_filter.mp hz).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  exact (not_lt_of_ge (hcount.trans hupper)) hlarge

end ThreeIM
