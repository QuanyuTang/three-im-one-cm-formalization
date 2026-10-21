module

public import RequestProject.ThreeIM.Basic
public import RequestProject.ThreeIM.TransportDomains
public import RequestProject.ThreeIM.TransportConclusion

/-!
# Uniform transport of a vanishing amplitude (Lemma 7.14)

The statement of Lemma 7.14, used in the proof of Lemma 10.6.  Its proof in the paper combines
Lemma 7.4 (normality from auxiliary coefficients), Lemma 7.1 (companion normality), Lemma 7.10
(scalar compactness), Lemma 7.13 (classification of the tangent system, formalized in
`Tangent.lean`) and an ODE transport argument along the rectangles. These components and
the two finite endpoint anchors are assembled in `TransportConclusion.lean`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- **Lemma 7.14** (uniform transport of a vanishing amplitude).  Let `(F_n, G_n)` be normalized
pairs on open sets `Ω_n` (sharing `a 0, a 1, a 2` IM and `∞` CM), each with a marked point of
type `(1, m)` over `a j` at `0`, `m ≥ 2`.  Let `ε_n > 0`, `ε_n → 0`, and `A₀, B₀ ≠ 0` with
`A₀ / B₀ = 1/m`.  Suppose the auxiliary functions agree, off discrete sets, with holomorphic
functions `u_n, v_n` on `Ω_n` such that, for every fixed `R > 0`,
`u_n(z) / (ε_n A₀ e^{z/2}) → 1` and `v_n(z) / (ε_n B₀ e^{-z/2}) → 1` uniformly on the rectangles
`-R ≤ Re z ≤ 2 log(1/ε_n) + R`, `|Im z| ≤ R`, and these rectangles lie in `Ω_n` for all large
`n`.  Then no such sequence exists.

The paper normalizes the marked value to `0`; the statement here, for an arbitrary marked
value `a j`, follows by translating both functions and all three finite target values by
`-a j`, which preserves the auxiliary identities. The paper also takes `ε_n` decreasing;
this is not needed, since every
sequence `ε_n → 0` has a decreasing subsequence and all hypotheses pass to subsequences. -/
theorem transport {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ} (hm : 2 ≤ m) {Ω : ℕ → Set ℂ}
    (hΩ : ∀ n, IsOpen (Ω n)) {F G : ℕ → ℂ → ℂ}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    (marked_F : ∀ n, mult (F n) (a j : Sphere) 0 = 1)
    (marked_G : ∀ n, mult (G n) (a j : Sphere) 0 = m)
    {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A₀ B₀ : ℂ} (hA₀ : A₀ ≠ 0) (hB₀ : B₀ ≠ 0) (hAB : A₀ / B₀ = 1 / m)
    {uₙ vₙ : ℕ → ℂ → ℂ}
    (huₙ : ∀ n, DifferentiableOn ℂ (uₙ n) (Ω n)) (hvₙ : ∀ n, DifferentiableOn ℂ (vₙ n) (Ω n))
    (hU : ∀ n, ∀ᶠ s in codiscreteWithin (Ω n), auxU a (F n) (G n) s = uₙ n s)
    (hV : ∀ n, ∀ᶠ s in codiscreteWithin (Ω n), auxV a (F n) (G n) s = vₙ n s)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprof_u : ∀ R > 0, ∀ δ > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖uₙ n z / (ε n * A₀ * Complex.exp (z / 2)) - 1‖ ≤ δ)
    (hprof_v : ∀ R > 0, ∀ δ > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖vₙ n z / (ε n * B₀ * Complex.exp (-z / 2)) - 1‖ ≤ δ) :
    False := by
  exact transport_from_original_profiles hm hΩ pair marked_F marked_G hε_pos hε hA₀ hB₀
    huₙ hvₙ hU hV hrect hprof_u hprof_v

end ThreeIM
