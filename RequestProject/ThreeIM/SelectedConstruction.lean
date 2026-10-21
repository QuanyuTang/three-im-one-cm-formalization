module

public import RequestProject.ThreeIM.SelectedMarkedRadii
public import RequestProject.ThreeIM.SelectedFactory
public import RequestProject.ThreeIM.ClusterAuxiliaryBudget
public import RequestProject.ThreeIM.ClusterMarkedDensity
public import RequestProject.ThreeIM.ClusterMarkedCount
public import RequestProject.ThreeIM.ClusterFiniteSelection
public import RequestProject.ThreeIM.ClusterSelectedSheet
public import RequestProject.ThreeIM.Defects

/-! # Selected configurations from the original counterexample data

The global marked divisor, finite-disk coefficient mass, genuine fibers,
and physical inverse branches are all constructed from the normalized
pair. This module is below Reduction and does not assume a selected
configuration or import the theorem that it is intended to prove.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real Classical

namespace ThreeIM

theorem NormalizedPair.markedDefect_of_mem_diskPoints
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) {z : ℂ}
    (hz : z ∈ divisorDiskPoints (totalMarkedDefectDivisor a f g) r) :
    ∃ j, IsBoundedMarkedDefect a f g j z := by
  have hn := divisorDiskPoints_mem_closedBall (totalMarkedDefectDivisor a f g)
    (by linarith : 0 ≤ r) hz
  have heq : (totalMarkedDefectDivisor a f g).toClosedBall r z =
      totalMarkedDefectDivisor a f g z := by
    apply Function.locallyFinsuppWithin.toClosedBall_eval_within
    simpa only [mem_closedBall, dist_zero_right, abs_of_nonneg (by linarith : 0 ≤ r)] using hn
  apply hp.exists_markedDefect_of_total_ne_zero
  have h := (mem_divisorDiskPoints (totalMarkedDefectDivisor a f g) r z).mp hz
  rwa [heq] at h

/-- At an actual radius with enough genuine retained support points,
construct a selected sheet using the canonical factors and the finite
set of at most fifty-eight multiplicity ratios. -/
theorem NormalizedPair.selected_sheet_of_large_marked_count
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤)
    {r R : ℝ} (hr : 1 ≤ r) (hrR : r < R) (hgap : R - r ≤ 1)
    (hlarge : (58 : ℝ) * 2500250 *
      selectedBranchParameter r R
        (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R) ^ 26 <
      ((divisorDiskPoints (totalMarkedDefectDivisor a f g) r).card : ℝ)) :
    Nonempty (SelectedSheet a (selectedBranchParameter r R
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R))) := by
  let Δ := R - r
  have hΔ : 0 < Δ := sub_pos.mpr hrR
  have hR : R = r + Δ := by dsimp only [Δ]; ring
  obtain ⟨D, E, P, -, -⟩ := hp.exists_finite_disk_auxiliary_control hNC hr hΔ hgap hR
  let S := divisorDiskPoints (totalMarkedDefectDivisor a f g) r
  have hdisk (z : ℂ) (hz : z ∈ S) : ‖z‖ ≤ r :=
    divisorDiskPoints_mem_closedBall _ (by linarith : 0 ≤ r) hz
  have hmark (z : ℂ) (hz : z ∈ S) : ∃ j, IsBoundedMarkedDefect a f g j z :=
    hp.markedDefect_of_mem_diskPoints hr hz
  have hfiber (z : ℂ) (hz : z ∈ S) :
      ∃ q ∈ boundedMarkedRatios, 0 < meromorphicOrderAt (fun w => auxPhi a f g w - q) z := by
    obtain ⟨j, hj⟩ := hmark z hz
    exact ⟨(mult f (a j : Sphere) z : ℂ) / mult g (a j : Sphere) z,
      hp.boundedMarkedDefect_ratio_mem hj,
      hp.auxPhi_fiber_order_pos_of_multiplicities hj.1.1 hj.1.2.1 rfl rfl⟩
  have hbig : (boundedMarkedRatios.card : ℝ) * 2500250 *
      (finiteDiskBudget R Δ
        (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ^ 26 <
      (S.card : ℝ) := by
    have hcard : (boundedMarkedRatios.card : ℝ) ≤ 58 := by
      exact_mod_cast boundedMarkedRatios_card_le
    have hnonneg : 0 ≤ (finiteDiskBudget R Δ
        (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ^ 26 :=
      pow_nonneg (by
        exact (by norm_num : (0 : ℝ) ≤ 1000000).trans (finiteDiskBudget_ge_million
          (by linarith : 0 ≤ R) hΔ ((by norm_num : (0 : ℝ) ≤ 1).trans
            (finiteDiskCoefficientMass_ge_one _ _ _ (by linarith : 1 ≤ R))))) 26
    have hle := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 2500250)) hnonneg
    exact hle.trans_lt hlarge
  obtain ⟨q, -, z, hz, -, haway, hgood⟩ := exists_actual_good_point_in_finite_fibers
    S boundedMarkedRatios D E P
    (fun w _ => hp.meromorphic_auxPhi w)
    (fun w _ => (hp.meromorphic_auxPhi w).deriv.div (hp.meromorphic_auxPhi w))
    (fun w _ => hp.meromorphic_auxPsi w) rfl hr hΔ hgap hR hdisk hfiber hbig
  obtain ⟨j, hj⟩ := hmark z hz
  exact exists_actual_marked_selected_sheet hp D E P hr hΔ hgap hR hj (hdisk z hz) haway hgood

/-- The exact original counterexample fields suffice for Proposition6.3.
No periodicity, compactness, factor, marked point, or growth estimate is
assumed beyond those fields; every physical selection datum is derived. -/
theorem NormalizedPair.selected_configuration_from_counterexample
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hdefect : ∃ j z, IsDefect f g (a j : Sphere) z)
    (hInf : InfiniteOrder f ∨ InfiniteOrder g)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤)
    (hlinear : ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ≤ pairT f g r) :
    Nonempty SelectedConfiguration := by
  have hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere) := by
    intro hcm
    obtain ⟨j, z, hz⟩ := hdefect
    exact hz.2.2 (hcm j z (mem_univ z))
  obtain ⟨rstar, hstar, -, hcount⟩ := hp.markedDefect_logCounting_le_card
  let M : ℝ → ℝ := finiteDiskCoefficientMass
    (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g)
  have hM (R : ℝ) (hR : 1 ≤ R) : 0 ≤ M R :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (finiteDiskCoefficientMass_ge_one _ _ _ hR)
  obtain ⟨r, R, hr2, -, -, hgap, hBpos, hBlim, hlarge⟩ :=
    selected_large_marked_radii hp.nonconst_f.1 hp.nonconst_g.1 hInf hlinear hM
      (hp.finiteDiskCoefficientMass_le_pairL hNC)
      (hp.markedDefect_density (hp.exists_defect hnot)) hcount hstar
      (by norm_num : (0 : ℝ) < 17 / 80) (by norm_num : (0 : ℝ) ≤ 58 * 2500250)
  apply selected_configuration_of_eventual_sheets hBpos hBlim
  filter_upwards [hlarge] with n hn
  exact hp.selected_sheet_of_large_marked_count hNC (by linarith [hr2 n])
    (hgap n).1 (hgap n).2 hn

end ThreeIM
