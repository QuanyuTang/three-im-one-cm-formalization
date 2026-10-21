module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The original polynomial/nonpolynomial predicate, separated from the
unused historical Wiman–Valiron central-index interface. -/

@[expose] public section

namespace ThreeIM

/-- An entire function is *transcendental* if it is not a polynomial. -/
def Transcendental (H : ℂ → ℂ) : Prop := ∀ p : Polynomial ℂ, ∃ z, H z ≠ p.eval z

end ThreeIM
