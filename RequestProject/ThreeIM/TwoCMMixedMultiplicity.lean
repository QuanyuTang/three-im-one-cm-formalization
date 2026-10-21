module

public import RequestProject.ThreeIM.TwoCMMixedReciprocal

/-!
# Multiplicity ratios in the zero-scalar mixed case
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem twoCM_order_relation_of_log_deriv_nonneg {U V : ℂ → ℂ}
    (hU : Meromorphic U) (hV : Meromorphic V)
    (hUf : ∀ z, meromorphicOrderAt U z ≠ ⊤) (hVf : ∀ z, meromorphicOrderAt V z ≠ ⊤)
    (p q : ℂ) (z : ℂ)
    (hnn : 0 ≤ meromorphicOrderAt (fun w => p * (deriv U w / U w) - q * (deriv V w / V w)) z) :
    p * (ordZ U z : ℂ) = q * (ordZ V z : ℂ) := by
  obtain ⟨E, hE, he⟩ := logDeriv_local_ordZ (hU z) (hUf z)
  obtain ⟨F, hF, hf⟩ := logDeriv_local_ordZ (hV z) (hVf z)
  have heq : ∀ᶠ w in 𝓝[≠] z,
      p * (deriv U w / U w) - q * (deriv V w / V w) =
      (p * (ordZ U z : ℂ) - q * (ordZ V z : ℂ)) / (w - z) + (p * E w - q * F w) := by
    filter_upwards [he, hf] with w he hf
    rw [he, hf]
    ring
  have hres : p * (ordZ U z : ℂ) - q * (ordZ V z : ℂ) = 0 := by
    by_contra hn
    have ho := (order_of_local_form
      ((analyticAt_const.mul hE).sub (analyticAt_const.mul hF)) heq).2.2 hn
    rw [ho] at hnn
    exact (not_le.2 (by decide : (-1 : WithTop ℤ) < 0)) hnn
  exact sub_eq_zero.1 hres

theorem twoCM_crossRatio_residue_relation_of_quartic {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hc : cAux a j = 0) {k : ℂ} (hk : k ≠ 0)
    (hquad : twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) g z)) (z : ℂ) :
    (ordZ (twoCMCrossRatio (a (j + 1)) (a (j + 2)) f) z : ℂ) =
      k * (ordZ (twoCMCrossRatio (a (j + 1)) (a (j + 2)) g) z : ℂ) := by
  let H := twoCMReciprocalDifference (a j) k f g
  have hH : IsNonconstMeroOn H univ := twoCM_reciprocalDifference_nonconst_of_defect hp hdefect (a j) hk
  have hHnn := twoCM_reciprocalDifference_order_nonneg hp j hcm hc hquad z
  have hHd := (order_deriv_of_nonconst hH (mem_univ z)).2 hHnn
  have hder := twoCM_deriv_reciprocalDifference_of_quartic_ratio hp.nonconst_f hp.nonconst_g hc hquad
  let U := twoCMCrossRatio (a (j + 1)) (a (j + 2)) f
  let V := twoCMCrossRatio (a (j + 1)) (a (j + 2)) g
  have heq : (fun w => deriv U w / U w - k * (deriv V w / V w)) =ᶠ[codiscrete ℂ]
      (fun w => (-(a (j + 1) - a (j + 2))) * deriv H w) := by
    filter_upwards [twoCM_logDeriv_crossRatio hp.nonconst_f (a (j + 1)) (a (j + 2)),
      twoCM_logDeriv_crossRatio hp.nonconst_g (a (j + 1)) (a (j + 2)), hder]
      with w hf hg hd
    change deriv (twoCMCrossRatio (a (j + 1)) (a (j + 2)) f) w / U w -
      k * (deriv (twoCMCrossRatio (a (j + 1)) (a (j + 2)) g) w / V w) = _
    rw [hf, hg]
    change _ = (-(a (j + 1) - a (j + 2))) * deriv (twoCMReciprocalDifference (a j) k f g) w
    rw [hd]
    ring
  have hnn : 0 ≤ meromorphicOrderAt (fun w => deriv U w / U w - k * (deriv V w / V w)) z := by
    rw [meromorphicOrderAt_congr (codiscrete_iff_nhdsNE.1 heq z)]
    change 0 ≤ meromorphicOrderAt ((fun _ => -(a (j + 1) - a (j + 2))) * deriv H) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const _ z) (hH.meromorphic z).deriv]
    exact add_nonneg (order_const_nonneg _) hHd
  have hh := twoCM_order_relation_of_log_deriv_nonneg
    (twoCM_meromorphic_crossRatio hp.nonconst_f _ _) (twoCM_meromorphic_crossRatio hp.nonconst_g _ _)
    (twoCM_crossRatio_order_ne_top hp.nonconst_f _ _) (twoCM_crossRatio_order_ne_top hp.nonconst_g _ _)
    1 k z (by simpa only [one_mul] using hnn)
  simpa only [one_mul] using hh

theorem twoCM_multiplicity_relation_of_quartic {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hc : cAux a j = 0) {k : ℂ} (hk : k ≠ 0)
    (hquad : twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) g z))
    (i : Fin 3) (hi : i ≠ j) (z : ℂ) :
    (mult f (a i : Sphere) z : ℂ) = k * (mult g (a i : Sphere) z : ℂ) := by
  by_cases hpos : 0 < mult f (a i : Sphere) z
  · have hposg := (hp.im i z (mem_univ z)).1 hpos
    have hbc : a (j + 1) ≠ a (j + 2) := hp.injective.ne (by fin_cases j <;> decide)
    have hres := twoCM_crossRatio_residue_relation_of_quartic hp j hcm hdefect hc hk hquad z
    have hindex : i = j + 1 ∨ i = j + 2 := by fin_cases j <;> fin_cases i <;> simp_all
    rcases hindex with rfl | rfl
    · rw [twoCM_crossRatio_order_at_first hp.nonconst_f hbc hpos,
        twoCM_crossRatio_order_at_first hp.nonconst_g hbc hposg] at hres
      simpa only [Int.cast_natCast] using hres
    · rw [twoCM_crossRatio_order_at_second hp.nonconst_f hbc hpos,
        twoCM_crossRatio_order_at_second hp.nonconst_g hbc hposg] at hres
      push_cast at hres
      linear_combination -hres
  · have hf0 : mult f (a i : Sphere) z = 0 := by omega
    have hg0 : mult g (a i : Sphere) z = 0 := by
      by_contra hn
      exact hpos ((hp.im i z (mem_univ z)).2 (Nat.pos_of_ne_zero hn))
    simp [hf0, hg0]

end ThreeIM
