module

public import RequestProject.ThreeIM.Main

/-!
# Three IM values and one CM value

Proof through the substantive main theorem and definition equivalences.

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

/-- The advertised definitions have exactly the project's germ meanings. -/
theorem mult_eq_project (f : ℂ → ℂ) (b : Sphere) (z : ℂ) :
    mult f b z = ThreeIM.mult f b z := rfl

theorem isNonconstMeroOn_iff_project (f : ℂ → ℂ) (Ω : Set ℂ) :
    IsNonconstMeroOn f Ω ↔ ThreeIM.IsNonconstMeroOn f Ω := Iff.rfl

theorem sharesIMOn_iff_project (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) :
    SharesIMOn Ω f g b ↔ ThreeIM.SharesIMOn Ω f g b := Iff.rfl

theorem sharesCMOn_iff_project (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) :
    SharesCMOn Ω f g b ↔ ThreeIM.SharesCMOn Ω f g b := Iff.rfl

/-- The same statement, proved through explicit definition equivalences. -/
theorem three_IM_one_CM {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i : Fin 3, SharesIMOn univ f g (a i.castSucc))
    (hcm : SharesCMOn univ f g (a 3)) :
    ∀ i, SharesCMOn univ f g (a i) := by
  have hf' : ThreeIM.IsNonconstMeroOn f univ :=
    (isNonconstMeroOn_iff_project f univ).mp hf
  have hg' : ThreeIM.IsNonconstMeroOn g univ :=
    (isNonconstMeroOn_iff_project g univ).mp hg
  have him' : ∀ i : Fin 3, ThreeIM.SharesIMOn univ f g (a i.castSucc) := by
    intro i
    exact (sharesIMOn_iff_project univ f g (a i.castSucc)).mp (him i)
  have hcm' : ThreeIM.SharesCMOn univ f g (a 3) :=
    (sharesCMOn_iff_project univ f g (a 3)).mp hcm
  have result := ThreeIM.three_IM_one_CM hf' hg' a ha him' hcm'
  intro i
  exact (sharesCMOn_iff_project univ f g (a i)).mpr (result i)

end ThreeIMOneCM
