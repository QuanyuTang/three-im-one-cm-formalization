module

public import RequestProject.ThreeIM.Basic
public import RequestProject.ThreeIM.NevanlinnaBasic
public import RequestProject.ThreeIM.Cartan
public import RequestProject.ThreeIM.PoissonBound
public import RequestProject.ThreeIM.DerivCharacteristic
public import RequestProject.ThreeIM.LogDerivative
public import RequestProject.ThreeIM.Counting
public import RequestProject.ThreeIM.SecondMain
public import RequestProject.ThreeIM.Picard
public import RequestProject.ThreeIM.TwoCM

/-!
# External theorems (Section 2)

The paper designates a list of classical results as *External theorems*. The wrappers below
preserve the statements used by its argument. Picard's theorem is proved in `Picard.lean`
from the second main theorem and the polynomial growth criterion. The two-CM theorem
is proved in `TwoCM.lean` without growth or analytic exclusion assumptions. External theorem 2.4 is proved in
`SecondMain.lean` from the first main theorem, ramification counts, and logarithmic
derivatives. External theorem 2.3 is also fully proved: the monotonicity of `T`
(in `Cartan.lean`), the maximum-modulus bound (in `PoissonBound.lean`), the logarithmic
derivative lemma (in `LogDerivative.lean`), and the estimate
`T(r, h') ≤ 2T(r, h) + O(log(e + rT))` derived from it (using `DerivCharacteristic.lean`).

External theorem 2.13 (finite Galois theory and cyclotomic fields) is already in Mathlib
(`Polynomial.cyclotomic.irreducible_rat`, `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`,
`IsCyclotomicExtension.autEquivPow`, `IsGalois.fixedField_fixingSubgroup`, ...) and is used
directly from there.
-/

@[expose] public section

open Filter Set MeasureTheory

namespace ThreeIM

/-- **External theorem 2.1 (v)** (Picard's little theorem, meromorphic form): a nonconstant
meromorphic function on `ℂ` omits at most two points of `ℂ̂`. -/
theorem ext_picard {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (b : Fin 3 → Sphere)
    (hb : Function.Injective b) : ∃ i z, 0 < mult f (b i) z :=
  little_picard hf b hb

/-- **External theorem 2.4** (Nevanlinna's second main theorem).  For a nonconstant
meromorphic `h` and distinct `b₁, …, b_q ∈ ℂ̂`, `q ≥ 3`,
`(q - 2) T(r,h) ≤ ∑ N̄(r, b_j; h) + O(log (e + r T(r,h)))` outside a set of finite linear
measure. -/
theorem ext_second_main_theorem {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) {q : ℕ}
    (hq : 3 ≤ q) (b : Fin q → Sphere) (hb : Function.Injective b) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ((q : ℝ) - 2) * charT h r ≤ ∑ j, reducedCounting h (b j) r +
        C * Real.log (Real.exp 1 + r * charT h r) :=
  second_main_theorem hh hq b hb

/-- **External theorem 2.5** (two CM values and two IM values; Gundersen).  If nonconstant
meromorphic `f, g` on `ℂ` share four distinct values IM and at least two of them CM, then all
four are shared CM. -/
theorem ext_two_cm {f g : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i, SharesIMOn univ f g (a i)) {i₁ i₂ : Fin 4} (hi : i₁ ≠ i₂)
    (hcm₁ : SharesCMOn univ f g (a i₁)) (hcm₂ : SharesCMOn univ f g (a i₂)) :
    ∀ i, SharesCMOn univ f g (a i) :=
  twoCM_theorem hf hg a ha him hi hcm₁ hcm₂

/-- **External theorem 2.3** (characteristic and logarithmic derivative), monotonicity: the
characteristic of a meromorphic function on `ℂ` is nondecreasing in `r` (stated for `r ≥ 1`).
This part of External theorem 2.3 is proved (in `Cartan.lean`, for all `0 < r ≤ R`), via
Jensen's formula and Cartan's averaging argument. -/
theorem ext_charT_mono {h : ℂ → ℂ} (hh : MeromorphicOn h univ) {r R : ℝ} (hr : 1 ≤ r)
    (hrR : r ≤ R) : charT h r ≤ charT h R :=
  charT_mono hh (lt_of_lt_of_le one_pos hr) hrR

/-- **External theorem 2.3**, maximum modulus bound: for an entire `h` and `1 ≤ r < R`,
`log⁺ M(r, h) ≤ (R + r)/(R - r) · T(R, h)`.  This part of External theorem 2.3 is proved in
`PoissonBound.lean` (Jensen's inequality composed with a disk automorphism). -/
theorem ext_entire_posLog_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {r R : ℝ} (hr : 1 ≤ r)
    (hrR : r < R) {z : ℂ} (hz : ‖z‖ = r) :
    Real.posLog ‖h z‖ ≤ (R + r) / (R - r) * charT h R :=
  entire_posLog_le hh hr hrR hz

/-- **External theorem 2.3**, logarithmic derivative lemma: for a nonconstant meromorphic `h`
on `ℂ` and `a ∈ ℂ`, `m(r, h'/(h - a)) = O(log (e + r T(r,h)))` outside a set of finite linear
measure.  Proved in `LogDerivative.lean` (`log_derivative_lemma`). -/
theorem ext_log_derivative {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) (a : ℂ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ValueDistribution.proximity (fun z => deriv h z / (h z - a)) ⊤ r ≤
        C * Real.log (Real.exp 1 + r * charT h r) :=
  log_derivative_lemma hh a

/-- **External theorem 2.3**, characteristic of the derivative: for a nonconstant meromorphic
`h` on `ℂ`, `T(r, h') ≤ 2 T(r, h) + O(log (e + r T(r,h)))` outside a set of finite linear
measure.  This is derived from the logarithmic derivative lemma `ext_log_derivative` above,
via `T(r, h') ≤ 2T(r, h) + m(r, h'/h)` (proved in `DerivCharacteristic.lean`). -/
theorem ext_charT_deriv_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (deriv h) r ≤ 2 * charT h r + C * Real.log (Real.exp 1 + r * charT h r) := by
  obtain ⟨C, E, hEm, hEv, r₀, hP⟩ := ext_log_derivative hh 0
  refine ⟨C, E, hEm, hEv, max r₀ 1, fun r hr hrE => ?_⟩
  have h1 := charT_deriv_le hh (le_of_max_le_right hr)
  have h2 := hP r (le_of_max_le_left hr) hrE
  linarith

end ThreeIM
