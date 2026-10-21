module

public import RequestProject.ThreeIM.TwoCMMixedReduction
public import RequestProject.ThreeIM.TwoCMMixedZeroExclusion

/-!
# The remaining mixed case has a nonzero scalar

The scalar hypothesis is obtained by a proved exclusion of the zero case,
not imposed on the original two-CM theorem.
-/

@[expose] public section

open Filter Set Topology ValueDistribution

namespace ThreeIM

theorem TwoCMPeriodicCounterexample.exists_canonical_mixed_nonzero {f g : ℂ → ℂ}
    {a : Fin 3 → ℂ} {j : Fin 3} (hP : TwoCMPeriodicCounterexample a j f g) :
    ∃ (b : Fin 3 → ℂ) (k : Fin 3) (F G : ℂ → ℂ),
      TwoCMPeriodicCounterexample b k F G ∧ cAux b k ≠ 0 ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting F ⊤ r ≤ C * pairL F G r) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi b k F G) z = ⊤) := by
  obtain ⟨b, k, F, G, hQ, hpole, hW⟩ := hP.exists_canonical_mixed
  have hc : cAux b k ≠ 0 := by
    intro hc
    exact twoCM_false_of_canonical_mixed_zero hQ.pair k hQ.cm_finite hQ.defect
      hQ.linear_growth hpole hc hW
  exact ⟨b, k, F, G, hQ, hc, hpole, hW⟩

end ThreeIM
