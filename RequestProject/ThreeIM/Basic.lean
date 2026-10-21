module

public import RequestProject.ThreeIM.MathlibImports

/-!
# Three IM values and one CM value — basic definitions (Section 1)

We follow Mathlib's value-distribution conventions: a meromorphic function on a domain
is a function `f : ℂ → ℂ` with `MeromorphicOn f Ω` (values at poles are junk and are never
used), and the Riemann sphere is `WithTop ℂ`, with `⊤` playing the role of `∞`.

All notions below are phrased through orders of vanishing (`meromorphicOrderAt`), so they
do not depend on the junk values of `f` at its poles or removable singularities.
-/

@[expose] public section

open Filter Set

namespace ThreeIM

/-- The Riemann sphere `ℂ̂ = ℂ ∪ {∞}`, with `⊤ = ∞` (Mathlib's convention). -/
abbrev Sphere := WithTop ℂ

/-- The local degree `e_z(f)` of `f` over the target value `b`, at the point `z`, and `0` if
`z` does not lie in the fiber `f⁻¹(b)`.

* For a finite value `b = c`, this is `ord_z (f - c)` when it is positive.
* For `b = ∞`, this is the pole order `-ord_z f` when it is positive. -/
noncomputable def mult (f : ℂ → ℂ) (b : Sphere) (z : ℂ) : ℕ :=
  WithTop.recTopCoe (-(meromorphicOrderAt f z)).untop₀.toNat
    (fun c : ℂ => (meromorphicOrderAt (fun w => f w - c) z).untop₀.toNat) b

@[simp] lemma mult_top (f : ℂ → ℂ) (z : ℂ) :
    mult f ⊤ z = (-(meromorphicOrderAt f z)).untop₀.toNat := rfl

@[simp] lemma mult_coe (f : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    mult f (c : Sphere) z = (meromorphicOrderAt (fun w => f w - c) z).untop₀.toNat := rfl

/-- `f` is a nonconstant meromorphic function on `Ω`: it is meromorphic there and it does not
agree with a constant on any punctured neighbourhood of a point of `Ω` (on a domain this is
equivalent to `f` being nonconstant). -/
def IsNonconstMeroOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  MeromorphicOn f Ω ∧ ∀ z ∈ Ω, ∀ c : ℂ, meromorphicOrderAt (fun w => f w - c) z ≠ ⊤

/-- `f` and `g` share the value `b` *ignoring multiplicities* (IM) on `Ω`:
`{z ∈ Ω : f z = b} = {z ∈ Ω : g z = b}`. -/
def SharesIMOn (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) : Prop :=
  ∀ z ∈ Ω, (0 < mult f b z ↔ 0 < mult g b z)

/-- `f` and `g` share the value `b` *counting multiplicities* (CM) on `Ω`: they share it IM
and the local degrees agree at every point of the common fiber.  (With our convention that
`mult` vanishes off the fiber, this is just equality of the multiplicity functions.) -/
def SharesCMOn (Ω : Set ℂ) (f g : ℂ → ℂ) (b : Sphere) : Prop :=
  ∀ z ∈ Ω, mult f b z = mult g b z

lemma SharesCMOn.sharesIMOn {Ω : Set ℂ} {f g : ℂ → ℂ} {b : Sphere}
    (h : SharesCMOn Ω f g b) : SharesIMOn Ω f g b := by
  intro z hz; rw [h z hz]

/-- A *defect* over `b` at `z`: a common `b`-point with unequal local degrees. -/
def IsDefect (f g : ℂ → ℂ) (b : Sphere) (z : ℂ) : Prop :=
  0 < mult f b z ∧ 0 < mult g b z ∧ mult f b z ≠ mult g b z

/-- The cubic `P(w) = (w - a₁)(w - a₂)(w - a₃)` attached to three finite shared values. -/
def cubicP (a : Fin 3 → ℂ) (w : ℂ) : ℂ := (w - a 0) * (w - a 1) * (w - a 2)

/-- A *normalized pair* on `Ω` (Definition 3.5): distinct nonconstant meromorphic functions
sharing three distinct finite values `a 0, a 1, a 2` IM and the value `∞` CM. -/
structure NormalizedPair (Ω : Set ℂ) (f g : ℂ → ℂ) (a : Fin 3 → ℂ) : Prop where
  nonconst_f : IsNonconstMeroOn f Ω
  nonconst_g : IsNonconstMeroOn g Ω
  distinct : ∀ z ∈ Ω, meromorphicOrderAt (fun w => f w - g w) z ≠ ⊤
  injective : Function.Injective a
  im : ∀ j, SharesIMOn Ω f g (a j : Sphere)
  cm_top : SharesCMOn Ω f g ⊤

/-- The auxiliary function `U = (f - g) f' / P(f)` (as a meromorphic function; only its
values off a discrete set are meaningful). -/
noncomputable def auxU (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (f z - g z) * deriv f z / cubicP a (f z)

/-- The auxiliary function `V = (f - g) g' / P(g)`. -/
noncomputable def auxV (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (f z - g z) * deriv g z / cubicP a (g z)

/-- The Mues function `Ψ = U V`. -/
noncomputable def auxPsi (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => auxU a f g z * auxV a f g z

/-- The auxiliary ratio `Φ = U / V`. -/
noncomputable def auxPhi (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => auxU a f g z / auxV a f g z

/-! ### Nevanlinna theory (Definition 1.4)

We use Mathlib's Nevanlinna characteristic `ValueDistribution.characteristic f ⊤`, which is
`T(r, f) = m(r, f) + N(r, f)` with exactly the normalisation of the paper. -/

/-- The Nevanlinna characteristic `T(r, f)`. -/
noncomputable def charT (f : ℂ → ℂ) (r : ℝ) : ℝ := ValueDistribution.characteristic f ⊤ r

/-- `T(r) = max (T(r,f), T(r,g))` for a pair. -/
noncomputable def pairT (f g : ℂ → ℂ) (r : ℝ) : ℝ := max (charT f r) (charT g r)

/-- `L(r) = log (e + r T(r))`. -/
noncomputable def pairL (f g : ℂ → ℂ) (r : ℝ) : ℝ := Real.log (Real.exp 1 + r * pairT f g r)

/-- A meromorphic function has *infinite order*:
`limsup_{r→∞} log⁺ T(r,f) / log r = ∞`, i.e. `T(r,f) ≥ r^K` for arbitrarily large `r`, for
every `K`. -/
def InfiniteOrder (f : ℂ → ℂ) : Prop :=
  ∀ K : ℝ, ∃ᶠ r in atTop, r ^ K ≤ charT f r

end ThreeIM
