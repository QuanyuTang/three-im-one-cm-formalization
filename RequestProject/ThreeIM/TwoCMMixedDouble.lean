module

public import RequestProject.ThreeIM.TwoCMMixedMultiplicity

/-!
# One member has double multiplicity on both remaining fibers
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

private theorem mixed_nat_double_of_ratio {m₀ n₀ m n : ℕ}
    (hlt : m₀ < n₀) (hm : 0 < m) (hrel : n₀ * m = m₀ * n) : 2 ≤ n := by
  by_contra hn
  have hn1 : n ≤ 1 := by omega
  have hm1 : 1 ≤ m := by omega
  nlinarith [Nat.mul_le_mul_left m₀ hn1, Nat.mul_le_mul_left n₀ hm1]

theorem twoCM_double_other_fibers_of_ratio {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z) (k : ℂ)
    (hrel : ∀ (i : Fin 3), i ≠ j → ∀ z,
      (mult f (a i : Sphere) z : ℂ) = k * (mult g (a i : Sphere) z : ℂ)) :
    (∀ i : Fin 3, i ≠ j →
      reducedFiberDivisor f (a i : Sphere) + reducedFiberDivisor f (a i : Sphere) ≤ fiberDivisor f (a i : Sphere)) ∨
    (∀ i : Fin 3, i ≠ j →
      reducedFiberDivisor f (a i : Sphere) + reducedFiberDivisor f (a i : Sphere) ≤ fiberDivisor g (a i : Sphere)) := by
  obtain ⟨d, z₀, hd⟩ := hdefect
  have hdj : d ≠ j := by
    intro he
    subst d
    exact hd.2.2 (hcm z₀ (mem_univ z₀))
  have hcross (i : Fin 3) (hi : i ≠ j) (z : ℂ) :
      mult g (a d : Sphere) z₀ * mult f (a i : Sphere) z =
        mult f (a d : Sphere) z₀ * mult g (a i : Sphere) z := by
    have hcomplex : (mult g (a d : Sphere) z₀ : ℂ) * (mult f (a i : Sphere) z : ℂ) =
        (mult f (a d : Sphere) z₀ : ℂ) * (mult g (a i : Sphere) z : ℂ) := by
      linear_combination (mult g (a d : Sphere) z₀ : ℂ) * (hrel i hi z) -
        (mult g (a i : Sphere) z : ℂ) * (hrel d hdj z₀)
    exact_mod_cast hcomplex
  rcases lt_or_gt_of_ne hd.2.2 with hlt | hgt
  · right
    intro i hi z
    rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      reducedFiberDivisor_apply hp.nonconst_f.1, fiberDivisor_apply hp.nonconst_g.1]
    by_cases hpos : 0 < mult f (a i : Sphere) z
    · rw [if_pos hpos]
      have hn : 2 ≤ mult g (a i : Sphere) z := mixed_nat_double_of_ratio hlt hpos (hcross i hi z)
      have hnZ : (2 : ℤ) ≤ (mult g (a i : Sphere) z : ℤ) := by exact_mod_cast hn
      convert hnZ using 1 <;> norm_num
    · rw [if_neg hpos]
      simp
  · left
    intro i hi z
    rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      reducedFiberDivisor_apply hp.nonconst_f.1, fiberDivisor_apply hp.nonconst_f.1]
    by_cases hpos : 0 < mult f (a i : Sphere) z
    · rw [if_pos hpos]
      have hposg := (hp.im i z (mem_univ z)).1 hpos
      have hn : 2 ≤ mult f (a i : Sphere) z := mixed_nat_double_of_ratio hgt hposg (hcross i hi z).symm
      have hnZ : (2 : ℤ) ≤ (mult f (a i : Sphere) z : ℤ) := by exact_mod_cast hn
      convert hnZ using 1 <;> norm_num
    · rw [if_neg hpos]
      simp

theorem twoCM_reduced_other_sum_le_pairT_of_double {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hdouble :
      (∀ i : Fin 3, i ≠ j →
        reducedFiberDivisor f (a i : Sphere) + reducedFiberDivisor f (a i : Sphere) ≤ fiberDivisor f (a i : Sphere)) ∨
      (∀ i : Fin 3, i ≠ j →
        reducedFiberDivisor f (a i : Sphere) + reducedFiberDivisor f (a i : Sphere) ≤ fiberDivisor g (a i : Sphere))) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      reducedCounting f (a (j + 1) : Sphere) r + reducedCounting f (a (j + 2) : Sphere) r ≤ pairT f g r + K := by
  have h₁ : j + 1 ≠ j := by fin_cases j <;> decide
  have h₂ : j + 2 ≠ j := by fin_cases j <;> decide
  have hresult (h : ℂ → ℂ) (hh : Meromorphic h)
      (hd : ∀ i : Fin 3, i ≠ j →
        reducedFiberDivisor f (a i : Sphere) + reducedFiberDivisor f (a i : Sphere) ≤ fiberDivisor h (a i : Sphere))
      (hT : ∀ r, charT h r ≤ pairT f g r) :
      ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
        reducedCounting f (a (j + 1) : Sphere) r + reducedCounting f (a (j + 2) : Sphere) r ≤ pairT f g r + K := by
    obtain ⟨K₁, hK₁⟩ := twoCM_logCounting_finite_le_charT hh (a (j + 1))
    obtain ⟨K₂, hK₂⟩ := twoCM_logCounting_finite_le_charT hh (a (j + 2))
    refine ⟨(|K₁| + |K₂|) / 2, fun r hr => ?_⟩
    have hN₁ := Function.locallyFinsuppWithin.logCounting_le (hd (j + 1) h₁) hr
    have hN₂ := Function.locallyFinsuppWithin.logCounting_le (hd (j + 2) h₂) hr
    simp only [map_add, Pi.add_apply, fiberDivisor_logCounting] at hN₁ hN₂
    rw [← reducedCounting_eq_reducedFiberDivisor hp.nonconst_f.1 _ (by linarith)] at hN₁ hN₂
    linarith [hK₁ r hr, hK₂ r hr, hT r, le_abs_self K₁, le_abs_self K₂]
  rcases hdouble with hd | hd
  · exact hresult f hp.nonconst_f.meromorphic hd fun r => le_max_left _ _
  · exact hresult g hp.nonconst_g.meromorphic hd fun r => le_max_right _ _

end ThreeIM
