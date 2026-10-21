module

public import RequestProject.ThreeIM.Selected
public import RequestProject.ThreeIM.SelectedConstruction

/-!
# Periodic counterexamples (the output of Lemma 4.12) and the selection of marked inverse
branches (Proposition 6.3)
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- The auxiliary ratio `Φ = U/V` of a pair is a nonconstant meromorphic function. -/
def PhiNonconstant (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : Prop :=
  ∀ c : ℂ, ∀ z : ℂ, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤

/-- The properties of the counterexample produced by Lemma 4.12: a normalized pair on `ℂ` with
a defect over one of the finite shared values, both members `2πi`-periodic, one of them of
infinite order, with nonconstant auxiliary ratio, and with `T(r) ≥ c r` for large `r`. -/
structure PeriodicCounterexample (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : Prop where
  pair : NormalizedPair univ f g a
  defect : ∃ j z, IsDefect f g (a j : Sphere) z
  periodic_f : ∀ t, f (t + 2 * Real.pi * Complex.I) = f t
  periodic_g : ∀ t, g (t + 2 * Real.pi * Complex.I) = g t
  infinite_order : InfiniteOrder f ∨ InfiniteOrder g
  phi_nonconst : PhiNonconstant a f g
  linear_growth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r

/-- **Proposition 6.3** (selection of marked inverse branches).  A periodic counterexample
yields a selected configuration (Definition 10.2). -/
theorem PeriodicCounterexample.selectedConfiguration {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (h : PeriodicCounterexample a f g) : Nonempty SelectedConfiguration := by
  exact h.pair.selected_configuration_from_counterexample
    h.defect h.infinite_order h.phi_nonconst h.linear_growth

end ThreeIM
