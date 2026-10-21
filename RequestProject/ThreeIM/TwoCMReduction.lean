module

public import RequestProject.ThreeIM.Covariance
public import RequestProject.ThreeIM.Growth

/-!
# Reduction of a two-CM counterexample to a periodic pair with linear growth

The extra growth property is produced by exponential precomposition. It is
an internal reduction and is not an assumption on the original functions.
No two-CM theorem or external wrapper is imported.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- A counterexample with the CM values `∞` and `a jCM`, after exponential
precomposition. The remaining defect produces its linear growth. -/
structure TwoCMPeriodicCounterexample (a : Fin 3 → ℂ) (jCM : Fin 3)
    (f g : ℂ → ℂ) : Prop where
  pair : NormalizedPair univ f g a
  cm_finite : SharesCMOn univ f g (a jCM : Sphere)
  defect : ∃ j z, IsDefect f g (a j : Sphere) z
  periodic_f : ∀ t, f (t + 2 * Real.pi * Complex.I) = f t
  periodic_g : ∀ t, g (t + 2 * Real.pi * Complex.I) = g t
  linear_growth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r

private theorem twoCM_cm_comp_expShift {f g : ℂ → ℂ} {zs b : ℂ}
    (hcm : SharesCMOn univ f g (b : Sphere)) :
    SharesCMOn univ (f ∘ expShift zs) (g ∘ expShift zs) (b : Sphere) := by
  exact hcm.comp (expShift_analyticAt zs) (fun t => by
    rw [deriv_expShift]
    exact Complex.exp_ne_zero t)

private theorem twoCM_progression_expShift {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) {j : Fin 3} {zs : ℂ}
    (hd : IsDefect f g (a j : Sphere) zs) :
    ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT (f ∘ expShift zs) (g ∘ expShift zs) r := by
  obtain ⟨hpair, hperF, hperG, hdk⟩ := hp.comp_expShift hd
  obtain ⟨c, hc, hgrowth⟩ := linear_growth_of_progression hpair.nonconst_f.1
    (a := a j) (z₀ := 0) (ℓ := 2 * Real.pi) (by positivity) (fun k => by
      have hk := (hdk k).1
      convert hk using 2
      push_cast
      ring)
  exact ⟨c, hc, hgrowth.mono fun r hr => hr.trans (le_max_left _ _)⟩

/-- Any normalized two-CM counterexample yields a periodic one with linear
growth, while retaining its finite CM value and an actual defect. -/
theorem exists_twoCM_periodicCounterexample {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (jCM : Fin 3)
    (hcm : SharesCMOn univ f g (a jCM : Sphere))
    (hdefect : ∃ j z, IsDefect f g (a j : Sphere) z) :
    ∃ F G, TwoCMPeriodicCounterexample a jCM F G := by
  obtain ⟨j, zs, hd⟩ := hdefect
  obtain ⟨hpair, hperF, hperG, hdk⟩ := hp.comp_expShift hd
  refine ⟨f ∘ expShift zs, g ∘ expShift zs, ?_⟩
  refine { pair := hpair
           cm_finite := twoCM_cm_comp_expShift hcm
           defect := ⟨j, 0, ?_⟩
           periodic_f := hperF
           periodic_g := hperG
           linear_growth := twoCM_progression_expShift hp hd }
  simpa using hdk 0

end ThreeIM
