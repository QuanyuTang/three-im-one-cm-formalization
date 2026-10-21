module

public import RequestProject.ThreeIM.TwoCMMixedEtaProximity
public import RequestProject.ThreeIM.TwoCMMixedEtaExclusion
public import RequestProject.ThreeIM.TwoCMNormalization

/-!
# The unconditional two-CM sharing theorem

The analytic branches are proved below the external interface. All growth
properties used for the periodic counterexample are produced internally.
-/

@[expose] public section

open Filter Set Topology ValueDistribution

namespace ThreeIM

theorem twoCM_false_of_canonical_mixed_nonzero {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r)
    (hS : cAux a j ≠ 0) (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) : False := by
  have hbound (i k : Fin 3) (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
      ∃ C : ℝ, OutsideFiniteMeasure fun r =>
        logCounting f (a j : Sphere) r + reducedCounting f (a i : Sphere) r ≤
          pairT f g r + C * pairL f g r := by
    by_cases hη : ∃ w, meromorphicOrderAt (twoCMMixedEta a j (a i) f g) w ≠ ⊤
    · exact twoCM_mixedEta_counting_le hp j i k hji hjk hik hcm hW hη
    · have hηzero : twoCMMixedEta a j (a i) f g =ᶠ[codiscrete ℂ] (fun _ => 0) := by
        apply codiscrete_iff_nhdsNE.2
        intro z
        apply meromorphicOrderAt_eq_top_iff.1
        by_contra hz
        exact hη ⟨z, hz⟩
      by_cases hθ : ∃ w, meromorphicOrderAt (twoCMMixedTheta a j (a i) f g) w ≠ ⊤
      · exact twoCM_mixedTheta_counting_le hp j i k hji hjk hik hcm hW hθ
      · have hθzero : twoCMMixedTheta a j (a i) f g =ᶠ[codiscrete ℂ] (fun _ => 0) := by
          apply codiscrete_iff_nhdsNE.2
          intro z
          apply meromorphicOrderAt_eq_top_iff.1
          by_contra hz
          exact hθ ⟨z, hz⟩
        exact (twoCM_false_of_scaled_aux_zeros (χ := twoCMChi a j f g)
          hp j i k hji.symm hjk.symm hik hcm hdefect hS
          (by simpa only [Filter.EventuallyEq, twoCMMixedEta] using hηzero)
          (by simpa only [Filter.EventuallyEq, twoCMMixedTheta] using hθzero)).elim
  have hb := hbound (j + 1) (j + 2) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
  have hc := hbound (j + 2) (j + 1) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
  exact twoCM_false_of_mixed_complementary_bounds hp j hcm hdefect hgrowth hpole hb hc

theorem twoCM_periodic_excluded : TwoCMPeriodicExcluded := by
  intro a j f g hP
  obtain ⟨b, k, F, G, hQ, hS, hpole, hW⟩ := hP.exists_canonical_mixed_nonzero
  exact twoCM_false_of_canonical_mixed_nonzero hQ.pair k hQ.cm_finite hQ.defect
    hQ.linear_growth hpole hS hW

/-- Distinct sphere values shared IM, with any two shared CM, are all shared
CM. There are no growth, auxiliary nonconstancy, or analytic exclusion assumptions. -/
theorem twoCM_theorem {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i, SharesIMOn univ f g (a i)) {i₁ i₂ : Fin 4} (hi : i₁ ≠ i₂)
    (hcm₁ : SharesCMOn univ f g (a i₁)) (hcm₂ : SharesCMOn univ f g (a i₂)) :
    ∀ i, SharesCMOn univ f g (a i) :=
  twoCM_of_periodic_exclusion twoCM_periodic_excluded hf hg a ha him hi hcm₁ hcm₂

end ThreeIM
