module

public import RequestProject.ThreeIM.TwoCMMixedEtaLocal
public import RequestProject.ThreeIM.TwoCMMixedEtaCounting
public import RequestProject.ThreeIM.TwoCMMixedZeroCounting

/-! # Sharp proximity estimate for the mixed auxiliary -/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

theorem twoCM_mixedEta_proximity_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (twoCMMixedEta a j (a i) f g) ⊤ r ≤
        proximity (fun z => (g z - a i)⁻¹) ⊤ r + C * pairL f g r := by
  let LA : ℂ → ℂ := fun z => deriv f z / (f z - a j)
  let LC : ℂ → ℂ := fun z => deriv f z / (f z - a k)
  let D : ℂ → ℂ := fun z => LA z - LC z
  let P : ℂ → ℂ := fun z => twoCMChi a j f g z - cAux a j / (a j - a k) * D z
  let Q : ℂ → ℂ := fun z => cAux a j * (LA z + (a k - a i) / (a j - a k) * D z)
  let H : ℂ → ℂ := fun z => (g z - a i)⁻¹
  have hLA : Meromorphic LA := meromorphic_logDeriv_sub hp.nonconst_f.meromorphic (a j)
  have hLC : Meromorphic LC := meromorphic_logDeriv_sub hp.nonconst_f.meromorphic (a k)
  have hD : Meromorphic D := hLA.sub hLC
  have hχ := twoCM_meromorphic_chi hp j
  have hP : Meromorphic P := fun z => (hχ z).sub
    ((MeromorphicAt.const _ z).mul (hD z))
  have hQ : Meromorphic Q := fun z => (MeromorphicAt.const _ z).mul
    ((hLA z).add ((MeromorphicAt.const _ z).mul (hD z)))
  have hH : Meromorphic H := fun z =>
    ((hp.nonconst_g.meromorphic z).sub (MeromorphicAt.const _ z)).inv
  have bLA : PairProximityBound f g LA := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a j)
    exact ⟨C, hC.mono fun _ _ h => h.1⟩
  have bLC : PairProximityBound f g LC := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a k)
    exact ⟨C, hC.mono fun _ _ h => h.1⟩
  have bD : PairProximityBound f g D := bLA.sub bLC hLA hLC
  have bP : PairProximityBound f g P :=
    (twoCM_proximity_chi_le hp j).sub
      (bD.const_mul hD (cAux a j / (a j - a k))) hχ
      (fun z => (MeromorphicAt.const _ z).mul (hD z))
  have bQ : PairProximityBound f g Q :=
    (bLA.add (bD.const_mul hD ((a k - a i) / (a j - a k))) hLA
      (fun z => (MeromorphicAt.const _ z).mul (hD z))).const_mul
        (fun z => (hLA z).add ((MeromorphicAt.const _ z).mul (hD z))) (cAux a j)
  obtain ⟨CP, hCP⟩ := bP
  obtain ⟨CQ, hCQ⟩ := bQ
  refine ⟨CP + CQ + log 2, (hCP.and hCQ).mono fun r hr ⟨hPr, hQr⟩ => ?_⟩
  have hadd := proximity_add_top_le hP (hQ.mul hH) r
  have hmul := proximity_mul_top_le hQ hH r
  simp only [Pi.add_apply] at hadd hmul
  have heq : twoCMMixedEta a j (a i) f g =ᶠ[codiscrete ℂ] P + Q * H :=
    twoCM_mixedEta_partial_fraction hp j i k hji hjk hik
  rw [proximity_congr_codiscrete heq (by linarith)]
  have hlog := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    (one_le_pairL (f := f) (g := g) hr)
  change proximity (P + Q * H) ⊤ r ≤ proximity H ⊤ r + (CP + CQ + log 2) * pairL f g r
  rw [add_mul, add_mul]
  linarith

/-- The finite-target first main theorem is used only after the reciprocal
factor has appeared with coefficient exactly one. -/
theorem twoCM_mixedEta_proximity_le_target {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (twoCMMixedEta a j (a i) f g) ⊤ r ≤
        charT g r - logCounting g (a i : Sphere) r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedEta_proximity_le hp j i k hji hjk hik
  obtain ⟨K, hK⟩ := twoCM_proximity_reciprocal_le hp.nonconst_g (a i)
  refine ⟨C + |K|, hC.mono fun r hr h => ?_⟩
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K)
      (one_le_pairL (f := f) (g := g) hr))
  have hrec := hK r hr
  rw [add_mul]
  linarith

theorem twoCM_mixedTheta_proximity_le_target {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (twoCMMixedTheta a j (a i) f g) ⊤ r ≤
        charT f r - logCounting f (a i : Sphere) r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedEta_proximity_le_target hp.symm j i k hji hjk hik
  refine ⟨C, hC.mono fun r _ h => ?_⟩
  have hneg : proximity (fun z => -twoCMMixedTheta a j (a i) f g z) ⊤ r =
      proximity (twoCMMixedTheta a j (a i) f g) ⊤ r := by simp [proximity]
  rw [twoCM_mixedEta_swap, hneg] at h
  simpa only [pairL, pairT, max_comm] using h

theorem twoCM_mixedEta_charT_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (twoCMMixedEta a j (a i) f g) r ≤
        pairT f g r - reducedCounting f (a i : Sphere) r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedEta_proximity_le_target hp j i k hji hjk hik
  refine ⟨C, hC.mono fun r hr h => ?_⟩
  have hN := twoCM_logCounting_mixedEta_poles_le hp j i hW hr
  rw [← reducedCounting_eq_of_sharesIM (hp.im i) r] at hN
  have hT : charT g r ≤ pairT f g r := le_max_right _ _
  change proximity (twoCMMixedEta a j (a i) f g) ⊤ r +
    logCounting (twoCMMixedEta a j (a i) f g) ⊤ r ≤ _
  linarith

theorem twoCM_mixedTheta_charT_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (twoCMMixedTheta a j (a i) f g) r ≤
        pairT f g r - reducedCounting f (a i : Sphere) r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedTheta_proximity_le_target hp j i k hji hjk hik
  refine ⟨C, hC.mono fun r hr h => ?_⟩
  have hN := twoCM_logCounting_mixedTheta_poles_le hp j i hW hr
  have hT : charT f r ≤ pairT f g r := le_max_left _ _
  change proximity (twoCMMixedTheta a j (a i) f g) ⊤ r +
    logCounting (twoCMMixedTheta a j (a i) f g) ⊤ r ≤ _
  linarith

theorem twoCM_mixedEta_counting_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤)
    (hH : ∃ w, meromorphicOrderAt (twoCMMixedEta a j (a i) f g) w ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r + reducedCounting f (a i : Sphere) r ≤
        pairT f g r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedEta_charT_le hp j i k hji hjk hik hW
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT (twoCM_meromorphic_mixedEta hp j (a i))
  refine ⟨C + CP + |K|, (hC.and hCP).mono fun r hr ⟨hCr, hPr⟩ => ?_⟩
  have hN := twoCM_logCounting_finite_le_mixedEta hp j (a i) (hp.injective.ne hji) hcm hH hr
  have hzero := hK r hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K)
      (one_le_pairL (f := f) (g := g) hr))
  rw [add_mul, add_mul]
  linarith

theorem twoCM_mixedTheta_counting_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤)
    (hH : ∃ w, meromorphicOrderAt (twoCMMixedTheta a j (a i) f g) w ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r + reducedCounting f (a i : Sphere) r ≤
        pairT f g r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := twoCM_mixedTheta_charT_le hp j i k hji hjk hik hW
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT (twoCM_meromorphic_mixedTheta hp j (a i))
  refine ⟨C + CP + |K|, (hC.and hCP).mono fun r hr ⟨hCr, hPr⟩ => ?_⟩
  have hN := twoCM_logCounting_finite_le_mixedTheta hp j (a i) (hp.injective.ne hji) hcm hH hr
  have hzero := hK r hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K)
      (one_le_pairL (f := f) (g := g) hr))
  rw [add_mul, add_mul]
  linarith

end ThreeIM
