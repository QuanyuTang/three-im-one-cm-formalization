module

public import RequestProject.ThreeIM.AuxiliaryMarkedExtraction

/-!
# Limits of marked pairs with convergent auxiliary functions (Lemmas 7.1–7.4 and 10.1)

This file states the compactness step shared by the proofs of Lemmas 10.4 and 10.5: from a
sequence of normalized pairs on disks exhausting `ℂ`, each with a marked `(1, m)`-point over a
finite shared value at `0`, whose auxiliary functions `U_n, V_n` converge locally uniformly to
zero-free entire functions `u, v`, one extracts a normalized pair on `ℂ` with auxiliary functions
`u, v` and a defect at `0`.

In the paper this is the combination of
* Lemma 7.4 (normality from auxiliary coefficients), applicable because `Ψ_n = U_n V_n` is
  locally bounded and zero-free and `Φ_n = U_n/V_n → φ = u/v`, where every `1`-point of `φ` is
  simple;
* a diagonal subsequence giving global spherical limits `f, g`;
* the marked derivative formula `F_n'(0) = P'(a) U_n(0) → P'(a) u(0) ≠ 0`, so `f` is
  nonconstant, and Lemma 7.1 (companion normality), so `g` is nonconstant;
* Lemma 7.3 (persistence of shared fibers and pole orders, and of the marked orders `1, ≥ m`);
* Lemma 10.1 (passage of the auxiliary identities to the limit).

The normality, spherical compactness, marked derivative and persistence steps are proved in
the imported component modules. Corrected finite charts preserve the original meromorphic
germs, including arbitrary representative values at poles and removable singularities.
The original statement below is obtained without additional hypotheses.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- **Lemmas 7.1–7.4 and 10.1 (limit extraction).**  Let `r_n → ∞` and let `(F_n, G_n)` be
normalized pairs on the disks `D(0, r_n)` (for the same three finite values `a`), each with a
marked `(1, m)`-point over `a j` at `0`, `m ≥ 2`.  Suppose that the auxiliary functions agree,
off discrete sets, with zero-free holomorphic functions `u_n, v_n` on these disks, and that
`u_n → u`, `v_n → v` locally uniformly on `ℂ`, where `u, v` are zero-free entire functions such
that every `1`-point of `φ = u/v` is simple.  Then there is a normalized pair `(f, g)` on `ℂ`
whose auxiliary functions are `u` and `v` and which has a defect over `a j` at `0`. -/
theorem limit_extraction {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {F G : ℕ → ℂ → ℂ}
    (pair : ∀ n, NormalizedPair (ball 0 (r n)) (F n) (G n) a)
    (marked_F : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (marked_G : ∀ n, mult (G n) (a j : Sphere) 0 = m)
    {uₙ vₙ : ℕ → ℂ → ℂ}
    (huₙ : ∀ n, DifferentiableOn ℂ (uₙ n) (ball 0 (r n)))
    (hvₙ : ∀ n, DifferentiableOn ℂ (vₙ n) (ball 0 (r n)))
    (huₙ0 : ∀ n, ∀ s ∈ ball (0 : ℂ) (r n), uₙ n s ≠ 0)
    (hvₙ0 : ∀ n, ∀ s ∈ ball (0 : ℂ) (r n), vₙ n s ≠ 0)
    (hU : ∀ n, ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (r n)), auxU a (F n) (G n) s = uₙ n s)
    (hV : ∀ n, ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (r n)), auxV a (F n) (G n) s = vₙ n s)
    {u v : ℂ → ℂ} (hu : Differentiable ℂ u) (hv : Differentiable ℂ v)
    (hu0 : ∀ s, u s ≠ 0) (hv0 : ∀ s, v s ≠ 0)
    (huconv : TendstoLocallyUniformly uₙ u atTop)
    (hvconv : TendstoLocallyUniformly vₙ v atTop)
    (hφ : ∀ s, u s = v s → deriv (fun w => u w / v w) s ≠ 0) :
    ∃ f g : ℂ → ℂ, NormalizedPair univ f g a ∧
      (∀ᶠ s in codiscrete ℂ, auxU a f g s = u s) ∧
      (∀ᶠ s in codiscrete ℂ, auxV a f g s = v s) ∧
      IsDefect f g (a j : Sphere) 0 := by
  exact auxiliary_marked_extraction hm hr
    (fun n => ⟨pair n, huₙ n, hvₙ n, huₙ0 n, hvₙ0 n, hU n, hV n⟩)
    marked_F marked_G hu hv hu0 hv0 huconv.tendstoLocallyUniformlyOn
    hvconv.tendstoLocallyUniformlyOn hφ

end ThreeIM
