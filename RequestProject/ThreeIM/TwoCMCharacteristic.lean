module

public import RequestProject.ThreeIM.LogDerivative
public import RequestProject.ThreeIM.DerivCharacteristic
public import RequestProject.ThreeIM.Counting

/-!
# A pure characteristic estimate used below the two-CM theorem

This separates the proved derivative estimate from the list of external
theorem wrappers, so that logarithmic auxiliary functions can be used when
proving the two-CM theorem itself.
-/

@[expose] public section

open Set

namespace ThreeIM

/-- The proved logarithmic derivative lemma with its exceptional-set predicate
named explicitly, for use by the finite-measure closure lemmas. -/
theorem log_derivative_estimate {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) (a : ℂ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ValueDistribution.proximity (fun z => deriv h z / (h z - a)) ⊤ r ≤
        C * Real.log (Real.exp 1 + r * charT h r) :=
  log_derivative_lemma hh a

theorem charT_deriv_le_log_error {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (deriv h) r ≤ 2 * charT h r + C * Real.log (Real.exp 1 + r * charT h r) := by
  obtain ⟨C, E, hEm, hEv, r₀, hP⟩ := log_derivative_lemma hh 0
  refine ⟨C, E, hEm, hEv, max r₀ 1, fun r hr hrE => ?_⟩
  have h1 := charT_deriv_le hh (le_of_max_le_right hr)
  have h2 := hP r (le_of_max_le_left hr) hrE
  linarith

end ThreeIM
