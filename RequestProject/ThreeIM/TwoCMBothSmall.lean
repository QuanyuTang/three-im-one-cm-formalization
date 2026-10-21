module

public import RequestProject.ThreeIM.TwoCMChiCounting
public import RequestProject.ThreeIM.TwoCMReduction
public import RequestProject.ThreeIM.Density

/-!
# Excluding the case of two small CM counting functions

Ramification bounds the defect indicator. The second main theorem then
makes the total defect count small when both CM counting functions are
small. A single actual defect suffices for the Lambda counting estimate;
there is no assumption of a defect in every marked fiber.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

/-- A first-main bound for the full counting function at any finite target. -/
theorem twoCM_logCounting_finite_le_charT {h : ℂ → ℂ} (hh : Meromorphic h) (c : ℂ) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r → logCounting h (c : Sphere) r ≤ charT h r + K := by
  have hshift : Meromorphic (fun w => h w - c) := fun z => (hh z).sub (MeromorphicAt.const _ _)
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hshift
  refine ⟨K + log⁺ ‖c‖ + log 2, fun r hr => ?_⟩
  have hfirst := hK r hr
  have hdiff := abs_characteristic_sub_characteristic_shift_le (a₀ := c) (r := r) hh
  rw [abs_le] at hdiff
  rw [logCounting_coe_eq_logCounting_sub_const_zero]
  change logCounting (fun w => h w - c) 0 r ≤ _
  change - (log⁺ ‖c‖ + log 2) ≤ charT h r - charT (fun w => h w - c) r ∧ _ at hdiff
  linarith [hdiff.1]

theorem twoCM_logCounting_eq_of_sharesCM {b : Sphere}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hcm : SharesCMOn univ f g b) : logCounting f b = logCounting g b := by
  have hD : fiberDivisor f b = fiberDivisor g b := by
    ext z
    rw [fiberDivisor_apply hf, fiberDivisor_apply hg, hcm z (mem_univ z)]
  rw [← fiberDivisor_logCounting, ← fiberDivisor_logCounting, hD]

/-- Unequal shared positive multiplicities consume at least one unit of
ramification in one member. -/
theorem twoCM_defectDivisor_le_ramification {b : Sphere}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (him : SharesIMOn univ f g b) :
    defectDivisor f g b ≤ fiberDivisor f b + fiberDivisor g b - 2 • reducedFiberDivisor f b := by
  intro z
  simp only [Function.locallyFinsuppWithin.coe_sub, Function.locallyFinsuppWithin.coe_add,
    Function.locallyFinsuppWithin.coe_nsmul, Pi.sub_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  rw [defectDivisor_apply hf hg, fiberDivisor_apply hf, fiberDivisor_apply hg, reducedFiberDivisor_apply hf]
  have hi := him z (mem_univ z)
  by_cases hpos : 0 < mult f b z
  · rw [if_pos hpos]
    have hposg := hi.1 hpos
    by_cases hne : mult f b z ≠ mult g b z
    · rw [if_pos hne]
      omega
    · rw [if_neg hne]
      omega
  · have hf0 : mult f b z = 0 := by omega
    have hg0 : mult g b z = 0 := by
      by_contra hg0
      exact hpos (hi.2 (Nat.pos_of_ne_zero hg0))
    simp [hf0, hg0]

theorem twoCM_defectCounting_le_ramification {b : Sphere}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (him : SharesIMOn univ f g b) {r : ℝ} (hr : 1 ≤ r) :
    defectCounting f g b r ≤ logCounting f b r + logCounting g b r - 2 * reducedCounting f b r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (twoCM_defectDivisor_le_ramification hf hg him) hr
  rw [map_sub, map_add, map_nsmul, fiberDivisor_logCounting, fiberDivisor_logCounting] at h
  simpa only [Pi.sub_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
    Nat.cast_ofNat, Pi.ofNat_apply, defectCounting,
    ← reducedCounting_eq_reducedFiberDivisor hf b (le_trans zero_le_one hr)] using h

theorem twoCM_totalDefectCounting_le_ramification (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) : totalDefectCounting a f g r ≤
      (∑ i, logCounting f (a i : Sphere) r) + (∑ i, logCounting g (a i : Sphere) r) -
        2 * ∑ i, reducedCounting f (a i : Sphere) r := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    twoCM_defectCounting_le_ramification hp.nonconst_f.1 hp.nonconst_g.1 (hp.im i) hr
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h

private lemma twoCM_sum_three_cyclic (R : Fin 3 → ℝ) (j : Fin 3) :
    ∑ i, R i = R j + R (j + 1) + R (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

private lemma twoCM_sum_full_le_twoT_except {h : ℂ → ℂ} (hh : Meromorphic h)
    (a : Fin 3 → ℂ) (j : Fin 3) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r → (∑ i, logCounting h (a i : Sphere) r) ≤
      2 * charT h r + logCounting h (a j : Sphere) r + K := by
  obtain ⟨Kb, hKb⟩ := twoCM_logCounting_finite_le_charT hh (a (j + 1))
  obtain ⟨Kc, hKc⟩ := twoCM_logCounting_finite_le_charT hh (a (j + 2))
  refine ⟨Kb + Kc, fun r hr => ?_⟩
  rw [twoCM_sum_three_cyclic (fun i => logCounting h (a i : Sphere) r) j]
  linarith [hKb r hr, hKc r hr]

/-- Both small CM counting functions force a small total defect count. -/
theorem twoCM_defects_small_of_both_counts_small (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hfinite : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => totalDefectCounting a f g r ≤ C * pairL f g r := by
  obtain ⟨Ca, hCa⟩ := hfinite
  obtain ⟨Cp, hCp⟩ := hpole
  obtain ⟨Cs, hCs0, hCs⟩ := second_main_pair_max hp
  obtain ⟨Kf, hKf⟩ := twoCM_sum_full_le_twoT_except hp.nonconst_f.meromorphic a j
  obtain ⟨Kg, hKg⟩ := twoCM_sum_full_le_twoT_except hp.nonconst_g.meromorphic a j
  refine ⟨2 * Ca + 2 * Cp + 2 * Cs + |Kf + Kg|,
    ((hCa.and hCp).and hCs).mono fun r hr ⟨⟨ha, hpole⟩, hs⟩ => ?_⟩
  have hD := twoCM_totalDefectCounting_le_ramification hp hr
  have hf := hKf r hr
  have hg := hKg r hr
  have hCMN : logCounting g (a j : Sphere) r = logCounting f (a j : Sphere) r :=
    (congrFun (twoCM_logCounting_eq_of_sharesCM hp.nonconst_f.1 hp.nonconst_g.1 hcm) r).symm
  rw [hCMN] at hg
  have hNp := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
  have hTf : charT f r ≤ pairT f g r := le_max_left _ _
  have hTg : charT g r ≤ pairT f g r := le_max_right _ _
  have hconst : Kf + Kg ≤ |Kf + Kg| * pairL f g r :=
    (le_abs_self (Kf + Kg)).trans (le_mul_of_one_le_right (abs_nonneg _)
      (one_le_pairL (f := f) (g := g) hr))
  rw [add_mul, add_mul, add_mul]
  linarith

/-- Only the selected defect witness is used in this fiber estimate. -/
theorem twoCM_reduced_defectFiber_small_of_total_small (hp : NormalizedPair univ f g a)
    (d : Fin 3) (hd : ∃ z, IsDefect f g (a d : Sphere) z)
    (hD : ∃ C : ℝ, OutsideFiniteMeasure fun r => totalDefectCounting a f g r ≤ C * pairL f g r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => reducedCounting f (a d : Sphere) r ≤ C * pairL f g r := by
  obtain ⟨CD, hCD⟩ := hD
  obtain ⟨CE, hCE⟩ := logCounting_EAux_zero_le_defect hp d
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  refine ⟨2 * CD + CE + CP, ((hCD.and hCE).and hCP).mono fun r hr ⟨⟨hD, hE⟩, hP⟩ => ?_⟩
  have hlocal := reducedCounting_le_defect_EAux hp d hd hr
  have hsingle : defectCounting f g (a d : Sphere) r ≤ totalDefectCounting a f g r :=
    Finset.single_le_sum (fun i _ => defectCounting_nonneg f g (a i : Sphere) hr) (Finset.mem_univ d)
  rw [add_mul, add_mul]
  linarith

private lemma twoCM_sum_three_le_two_terms {R : Fin 3 → ℝ} {j d : Fin 3} {B : ℝ}
    (hjd : j ≠ d) (hR : ∀ i, R i ≤ B) : (∑ i, R i) ≤ R j + R d + B := by
  have h0 := hR 0
  have h1 := hR 1
  have h2 := hR 2
  fin_cases j <;> fin_cases d <;> simp_all [Fin.sum_univ_three] <;>
    linarith [hR 0, hR 1, hR 2]

/-- A counterexample with linear growth cannot have both CM counting
functions logarithmically small. -/
theorem twoCM_false_of_both_counts_small (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (hfinite : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) : False := by
  obtain ⟨d, z, hd⟩ := hdefect
  have hjd : j ≠ d := by
    intro heq
    subst d
    exact hd.2.2 (hcm z (mem_univ z))
  obtain ⟨CD, hCD⟩ := twoCM_reduced_defectFiber_small_of_total_small hp d ⟨z, hd⟩
    (twoCM_defects_small_of_both_counts_small hp j hcm hfinite hpole)
  obtain ⟨Ca, hCa⟩ := hfinite
  obtain ⟨Cp, hCp⟩ := hpole
  obtain ⟨Cs, hCs0, hCs⟩ := second_main_pair_max hp
  choose K hK using fun i : Fin 3 => twoCM_logCounting_finite_le_charT hp.nonconst_f.meromorphic (a i)
  let B : ℝ := ∑ i, |K i|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hKle (i : Fin 3) : K i ≤ B := (le_abs_self (K i)).trans
    (Finset.single_le_sum (fun k _ => abs_nonneg (K k)) (Finset.mem_univ i))
  have hbound : ∃ C : ℝ, OutsideFiniteMeasure fun r => pairT f g r ≤ C * pairL f g r := by
    refine ⟨Ca + CD + Cp + Cs + B,
      (((hCa.and hCD).and hCp).and hCs).mono fun r hr ⟨⟨⟨ha, hd⟩, hpole⟩, hs⟩ => ?_⟩
    have hRa := reducedCounting_le_logCounting hp.nonconst_f.1 (a j : Sphere) hr
    have hRp := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
    have hR : ∀ i, reducedCounting f (a i : Sphere) r ≤ pairT f g r + B := by
      intro i
      have h1 := reducedCounting_le_logCounting hp.nonconst_f.1 (a i : Sphere) hr
      have h2 := hK i r hr
      have h3 : charT f r ≤ pairT f g r := le_max_left _ _
      linarith [hKle i]
    have hsum := twoCM_sum_three_le_two_terms hjd hR
    have hconst := le_mul_of_one_le_right hB0 (one_le_pairL (f := f) (g := g) hr)
    rw [add_mul, add_mul, add_mul, add_mul]
    linarith
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨c, hc, hG⟩ := hgrowth
  apply false_of_linear_growth hc hG
  refine hC.mono fun r hr h => ?_
  change pairT f g r ≤ |C| * (pairL f g r + log r)
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hlog : 0 ≤ log r := Real.log_nonneg hr
  calc pairT f g r ≤ C * pairL f g r := h
    _ ≤ |C| * pairL f g r := mul_le_mul_of_nonneg_right (le_abs_self C) hL0
    _ ≤ |C| * (pairL f g r + log r) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)

/-- The both-small branch and the all-CM branch are impossible for an actual
periodic counterexample. Three explicit analytic cases remain. -/
theorem TwoCMPeriodicCounterexample.three_cases {j : Fin 3}
    (hP : TwoCMPeriodicCounterexample a j f g) :
    ((∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤)) ∨
    ((∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)) ∨
    ((∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) ∧
      thetaAux a j f g =ᶠ[codiscrete ℂ] (fun z => -twoCMChi a j f g z)) := by
  rcases twoCM_four_cases hP.pair j hP.cm_finite with hboth | hfirst | hsecond | hlast
  · exact (twoCM_false_of_both_counts_small hP.pair j hP.cm_finite hP.defect
      hP.linear_growth hboth.2 hboth.1).elim
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · rcases hlast with hCM | hopp
    · obtain ⟨d, z, hd⟩ := hP.defect
      exact (hd.2.2 (hCM (a d : Sphere) (hP.pair.im d) z (mem_univ z))).elim
    · exact Or.inr (Or.inr hopp)

end ThreeIM
