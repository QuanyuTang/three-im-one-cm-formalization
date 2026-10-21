module

public import RequestProject.ThreeIM.ClusterMarkedDivisor
public import RequestProject.ThreeIM.Density

/-! # The actual marked-defect density

Discarding large marked multiplicities costs at most one thirty-second
of the six full fiber counts. Zeros of Psi have only a logarithmic cost.
Together with the previously proved defect density, this gives the
manuscript's coefficient 17/80 for the retained genuine marked divisor.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter ValueDistribution Real Classical
open scoped BigOperators

namespace ThreeIM

/-- The pointwise marked-divisor inequality integrates with the original
logarithmic counting convention, including the origin contribution. -/
theorem NormalizedPair.defectCounting_le_marked_full_auxPsi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (j : Fin 3) {r : ℝ} (hr : 1 ≤ r) :
    32 * defectCounting f g (a j : Sphere) r ≤
      32 * (markedDefectDivisor a f g j).logCounting r +
        logCounting f (a j : Sphere) r + logCounting g (a j : Sphere) r +
          32 * logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (hp.defect_le_marked_fibers_auxPsi j) hr
  rw [map_add, map_add, map_add, map_nsmul, map_nsmul, map_nsmul,
    fiberDivisor_logCounting, fiberDivisor_logCounting] at h
  simpa only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Nat.cast_ofNat,
    Pi.ofNat_apply,
    defectCounting, ← ValueDistribution.logCounting_zero] using h

/-- Sum over the three actual marked finite values. -/
theorem NormalizedPair.totalDefectCounting_le_marked_full_auxPsi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) :
    32 * totalDefectCounting a f g r ≤
      32 * (totalMarkedDefectDivisor a f g).logCounting r +
        (∑ j, logCounting f (a j : Sphere) r) +
          (∑ j, logCounting g (a j : Sphere) r) + 96 * logCounting (auxPsi a f g) 0 r := by
  have h0 := hp.defectCounting_le_marked_full_auxPsi 0 hr
  have h1 := hp.defectCounting_le_marked_full_auxPsi 1 hr
  have h2 := hp.defectCounting_le_marked_full_auxPsi 2 hr
  simp only [totalDefectCounting, totalMarkedDefectDivisor,
    Fin.sum_univ_three, map_add, Pi.add_apply]
  linarith

/-- A first-main estimate at any fixed finite target. This local copy of
the elementary estimate avoids importing the two-CM exclusion machinery
into the independent selection argument. -/
theorem cluster_logCounting_finite_le_charT {h : ℂ → ℂ} (hh : Meromorphic h) (c : ℂ) :
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

/-- The six full marked-fiber counts cost at most six times the actual
pair characteristic, up to a radius-independent constant. -/
theorem cluster_six_finite_counting_le_pairT {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      (∑ j, logCounting f (a j : Sphere) r) +
        (∑ j, logCounting g (a j : Sphere) r) ≤ 6 * pairT f g r + K := by
  choose Kf hKf using fun j : Fin 3 => cluster_logCounting_finite_le_charT hf (a j)
  choose Kg hKg using fun j : Fin 3 => cluster_logCounting_finite_le_charT hg (a j)
  refine ⟨(∑ j, Kf j) + ∑ j, Kg j, fun r hr => ?_⟩
  have hsf := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hKf j r hr
  have hsg := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hKg j r hr
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsf hsg
  have hTf : charT f r ≤ pairT f g r := le_max_left _ _
  have hTg : charT g r ≤ pairT f g r := le_max_right _ _
  linarith

/-- The manuscript's retained marked-defect density. All inputs are the
original normalized-pair and genuine-defect conditions; no selection or
inverse-branch conclusion is used in this proof. -/
theorem NormalizedPair.markedDefect_density {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a)
    (hdefects : ∀ j, ∃ z, IsDefect f g (a j : Sphere) z) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      (17 / 80 : ℝ) * pairT f g r ≤
        (totalMarkedDefectDivisor a f g).logCounting r + C * pairL f g r := by
  obtain ⟨CD, hCD⟩ := two_pairT_le_five_defects hp hdefects
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := cluster_six_finite_counting_le_pairT
    hp.nonconst_f.meromorphic hp.nonconst_g.meromorphic (a := a)
  refine ⟨CD / 5 + |K| / 32 + 3 * CP,
    (hCD.and hCP).mono fun r hr ⟨hD, hP⟩ => ?_⟩
  have h := hp.totalDefectCounting_le_marked_full_auxPsi hr
  have hfull := hK r hr
  have hL := one_le_pairL (f := f) (g := g) hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  linarith

end ThreeIM
