module

public import RequestProject.ThreeIM.TwoCMOppositePowers
public import RequestProject.ThreeIM.TwoCMCharTransforms
public import RequestProject.ThreeIM.TwoCMBothSmall

/-!
# Excluding the opposite-sign case by characteristic comparison
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

theorem twoCM_charT_weighted_crossRatio_abs_le {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {b c : ℂ} (hbc : b ≠ c) (n m : ℕ) {C : ℂ} (hC : C ≠ 0)
    (heq : (fun w => twoCMCrossRatio b c f w ^ n) =ᶠ[codiscrete ℂ]
      (fun w => C * twoCMCrossRatio b c g w ^ m)) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r → |(n : ℝ) * charT f r - (m : ℝ) * charT g r| ≤ K := by
  let F := twoCMCrossRatio b c f
  let G := twoCMCrossRatio b c g
  have hF : Meromorphic F := twoCM_meromorphic_crossRatio hf b c
  have hG : Meromorphic G := twoCM_meromorphic_crossRatio hg b c
  have hGm : Meromorphic (fun w => G w ^ m) := fun w => (hG w).pow m
  have hGmf : ∀ z, meromorphicOrderAt (fun w => G w ^ m) z ≠ ⊤ := by
    intro z
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hGm z)).2
    exact ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hG z)).1
      (twoCM_crossRatio_order_ne_top hg b c z)).mono fun w hw => pow_ne_zero m hw
  obtain ⟨Kf, hKf⟩ := charT_crossRatio_abs_le hf hbc
  obtain ⟨Kg, hKg⟩ := charT_crossRatio_abs_le hg hbc
  refine ⟨(n : ℝ) * Kf + (m : ℝ) * Kg + (log⁺ ‖C‖ + log⁺ ‖C⁻¹‖), fun r hr => ?_⟩
  have hpowF : charT (fun w => F w ^ n) r = (n : ℝ) * charT F r := by
    change characteristic (F ^ n) ⊤ r = (n : ℝ) * characteristic F ⊤ r
    simpa using congrFun (characteristic_pow_top (n := n) hF) r
  have hpowG : charT (fun w => G w ^ m) r = (m : ℝ) * charT G r := by
    change characteristic (G ^ m) ⊤ r = (m : ℝ) * characteristic G ⊤ r
    simpa using congrFun (characteristic_pow_top (n := m) hG) r
  have hscale := charT_const_mul_abs_le hGm hGmf hC hr
  have hchars : charT (fun w => F w ^ n) r = charT (fun w => C * G w ^ m) r :=
    characteristic_congr_codiscrete heq (by linarith)
  rw [← hchars, hpowF, hpowG] at hscale
  have hfb := abs_le.1 (hKf r hr)
  have hgb := abs_le.1 (hKg r hr)
  change -Kf ≤ charT F r - charT f r ∧ charT F r - charT f r ≤ Kf at hfb
  change -Kg ≤ charT G r - charT g r ∧ charT G r - charT g r ≤ Kg at hgb
  have hfblo := mul_le_mul_of_nonneg_left hfb.1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hfbhi := mul_le_mul_of_nonneg_left hfb.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hgblo := mul_le_mul_of_nonneg_left hgb.1 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hgbhi := mul_le_mul_of_nonneg_left hgb.2 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [abs_le] at hscale ⊢
  constructor <;> nlinarith [hscale.1, hscale.2]

theorem twoCM_false_of_weighted_characteristic {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (n m : ℕ) (hnm : n ≠ m)
    (hweighted : ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      |(n : ℝ) * charT f r - (m : ℝ) * charT g r| ≤ K) : False := by
  obtain ⟨K, hK⟩ := hweighted
  obtain ⟨C, hC0, hC⟩ := abs_charT_sub_le_pairL hp
  let δ : ℝ := |(n : ℝ) - (m : ℝ)|
  have hδ : 0 < δ := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hnm))
  have hbound : OutsideFiniteMeasure fun r =>
      pairT f g r ≤ ((|K| + ((n : ℝ) + m) * C) / δ) * pairL f g r := by
    apply hC.mono
    intro r hr hcomp
    have hf0 : 0 ≤ charT f r := charT_nonneg hr
    have hg0 : 0 ≤ charT g r := charT_nonneg hr
    have hL : 1 ≤ pairL f g r := one_le_pairL hr
    have hL0 : 0 ≤ pairL f g r := by linarith
    have hKa : K ≤ |K| * pairL f g r :=
      (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
    have hmabs : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (Nat.cast_nonneg m)
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    have hTf : δ * charT f r ≤ K + (m : ℝ) * C * pairL f g r := by
      have heq : ((n : ℝ) - m) * charT f r =
          ((n : ℝ) * charT f r - (m : ℝ) * charT g r) -
            (m : ℝ) * (charT f r - charT g r) := by ring
      have ht := abs_sub ((n : ℝ) * charT f r - (m : ℝ) * charT g r)
        ((m : ℝ) * (charT f r - charT g r))
      rw [← heq, abs_mul, abs_of_nonneg hf0] at ht
      rw [abs_mul, hmabs] at ht
      dsimp only [δ]
      nlinarith [hK r hr, mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hTg : δ * charT g r ≤ K + (n : ℝ) * C * pairL f g r := by
      have heq : ((n : ℝ) - m) * charT g r =
          ((n : ℝ) * charT f r - (m : ℝ) * charT g r) -
            (n : ℝ) * (charT f r - charT g r) := by ring
      have ht := abs_sub ((n : ℝ) * charT f r - (m : ℝ) * charT g r)
        ((n : ℝ) * (charT f r - charT g r))
      rw [← heq, abs_mul, abs_of_nonneg hg0] at ht
      rw [abs_mul, hnabs] at ht
      dsimp only [δ]
      nlinarith [hK r hr, mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hm0 : 0 ≤ (m : ℝ) * C * pairL f g r := by positivity
    have hn0 : 0 ≤ (n : ℝ) * C * pairL f g r := by positivity
    have hmax : δ * pairT f g r ≤ (|K| + ((n : ℝ) + m) * C) * pairL f g r := by
      rcases le_total (charT f r) (charT g r) with h | h
      · rw [pairT, max_eq_right h]
        nlinarith
      · rw [pairT, max_eq_left h]
        nlinarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hmax)
  obtain ⟨c, hc, hG⟩ := hgrowth
  apply false_of_linear_growth hc hG
  apply hbound.mono
  intro r hr h
  change pairT f g r ≤ |((|K| + ((n : ℝ) + m) * C) / δ)| * (pairL f g r + log r)
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hlog : 0 ≤ log r := Real.log_nonneg hr
  exact h.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hL0).trans
    (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)))

/-- The opposite sign is impossible for a normalized counterexample with
its internally generated linear growth. Neither squared identity nor a
nonzero scalar hypothesis is needed for this exclusion. -/
theorem twoCM_false_of_opposite {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (hopp : thetaAux a j f g =ᶠ[codiscrete ℂ] (fun z => -twoCMChi a j f g z)) : False := by
  obtain ⟨d, z, hd⟩ := hdefect
  have hjd : j ≠ d := by
    intro heq
    subst d
    exact hd.2.2 (hcm z (mem_univ z))
  have hindex : d = j + 1 ∨ d = j + 2 := by
    fin_cases j <;> fin_cases d <;> simp_all
  have hdc : a d = a (j + 1) ∨ a d = a (j + 2) :=
    hindex.imp (congrArg a) (congrArg a)
  have hbc : a (j + 1) ≠ a (j + 2) := hp.injective.ne (by fin_cases j <;> decide)
  obtain ⟨k, hk, hquad⟩ := twoCM_quadDerivative_ratio_of_opposite hp j hopp
  obtain ⟨C, hC, hpower⟩ := twoCM_crossRatio_powers_of_quad_ratio
    hp.nonconst_f hp.nonconst_g hbc hdc hd.1 hd.2.1 hquad
  apply twoCM_false_of_weighted_characteristic hp hgrowth
    (mult g (a d : Sphere) z) (mult f (a d : Sphere) z) hd.2.2.symm
  exact twoCM_charT_weighted_crossRatio_abs_le hp.nonconst_f hp.nonconst_g hbc
    (mult g (a d : Sphere) z) (mult f (a d : Sphere) z) hC hpower

/-- Exactly the two mixed counting/identity cases remain after the proved
both-small, same-sign and opposite-sign exclusions. -/
theorem TwoCMPeriodicCounterexample.two_cases {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (hP : TwoCMPeriodicCounterexample a j f g) :
    ((∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤)) ∨
    ((∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)) := by
  rcases hP.three_cases with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (twoCM_false_of_opposite hP.pair j hP.cm_finite hP.defect hP.linear_growth h.2.2).elim

end ThreeIM
