module

public import Mathlib

/-!
# Three IM values and one CM value

Independent statement for comparison with the proof in Solution.

The sphere is C together with infinity. For a finite target, multiplicity
is the positive zero order; at infinity it is the positive pole order.
Orders are meromorphic germ orders, so an arbitrary assigned value at a
pole or a removable point does not change any fiber. Nonconstancy rules
out locally constant germs; on the connected plane this is the ordinary
nonconstancy condition. IM means equality of fibers and CM means equality
of their local degrees.

The conclusion has no growth, finite-order, periodicity, defect or
stable-expansion assumption. It includes pairs with identical germs.
-/

@[expose] public section

open Filter Set

namespace ThreeIMOneCM

abbrev Sphere := WithTop ℂ

noncomputable def mult (f : ℂ → ℂ) (b : Sphere) (z : ℂ) : ℕ :=
  WithTop.recTopCoe (-(meromorphicOrderAt f z)).untop₀.toNat
    (fun c : ℂ => (meromorphicOrderAt (fun w => f w - c) z).untop₀.toNat) b

def IsNonconstMeroOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  MeromorphicOn f Ω ∧ ∀ z ∈ Ω, ∀ c : ℂ, meromorphicOrderAt (fun w => f w - c) z ≠ ⊤

def SharesIMOn (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) : Prop :=
  ∀ z ∈ Ω, (0 < mult f b z ↔ 0 < mult g b z)

def SharesCMOn (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) : Prop :=
  ∀ z ∈ Ω, mult f b z = mult g b z

/-- The unrestricted three-IM/one-CM shared-value theorem. -/
theorem three_IM_one_CM {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i : Fin 3, SharesIMOn univ f g (a i.castSucc))
    (hcm : SharesCMOn univ f g (a 3)) :
    ∀ i, SharesCMOn univ f g (a i) := by
  sorry

end ThreeIMOneCM
