module

public import RequestProject.ThreeIM.ClusterAuxiliaryModels
public import RequestProject.ThreeIM.AffineCovariance
public import RequestProject.ThreeIM.BranchCoefficient
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! # Pulling actual auxiliary units back to a quantitative inverse sheet

Raw f,g may have poles. Chain-rule identities are used only codiscretely;
the central square-root sign is prescribed through analytic U/V models.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real

namespace ThreeIM

/-- The honest U/V models fix the sheet phase and give exactly the two
coefficient identities required by SelectedConfiguration. -/
theorem CanonicalAuxiliaryModels.pullback_profiles
    {a : Fin 3 → ℂ} {f g phi A psi : ℂ → ℂ} {z v c : ℂ} {B d : ℝ}
    (hp : NormalizedPair univ f g a)
    (h : CanonicalAuxiliaryModels a f g phi psi (ball z (d / B ^ 4)))
    (b : GoodPointBranch phi A psi z v B d)
    (hB : 0 < B) (hA : ∀ w ∈ ball z (d / B ^ 4), A w ≠ 0)
    (hc : c ≠ 0) (hphi : phi z = c ^ 2) (hcenter : h.u z / v = c) :
    (auxU a (f ∘ b.gamma) (g ∘ b.gamma) =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
      (fun s => c * Complex.exp (s / 2) / b.k s)) ∧
    (auxV a (f ∘ b.gamma) (g ∘ b.gamma) =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
      (fun s => c⁻¹ * Complex.exp (-s / 2) / b.k s)) := by
  have hR : 0 < B ^ 6 / 2 := by positivity
  have hgamma : DifferentiableOn ℂ b.gamma (ball 0 (B ^ 6 / 2)) := b.gamma_analytic.differentiableOn
  have hT : ∀ s ∈ ball (0 : ℂ) (B ^ 6 / 2),
      Tendsto b.gamma (𝓝[≠] s) (𝓝[≠] (b.gamma s)) := fun s hs =>
    (b.gamma_analytic s hs).differentiableAt.hasDerivAt.tendsto_nhdsNE (b.gamma_deriv_ne_zero s hs)
  have hcoef := inverse_sheet_coefficients hR hc
    (h.holo_u.comp hgamma b.gamma_maps) (b.sigma_holo.comp hgamma b.gamma_maps)
    (fun s hs => b.sigma_ne_zero _ (b.gamma_maps hs))
    (fun s hs => h.nonzero_v _ (b.gamma_maps hs))
    (fun s hs => (h.product _ (b.gamma_maps hs)).trans (b.sigma_sq _ (b.gamma_maps hs)).symm)
    (fun s hs => by
      change h.u (b.gamma s) / h.v (b.gamma s) = c ^ 2 * Complex.exp s
      rw [h.ratio _ (b.gamma_maps hs), b.gamma_exp s hs, hphi])
    (by simpa only [Function.comp_apply, b.gamma_zero, b.sigma_center] using hcenter)
  simp only [Function.comp_apply] at hcoef
  have hFa := codiscreteWithin_comp_source
    (MeromorphicOn.eventually_codiscreteWithin_analyticAt f hp.nonconst_f.1)
    (fun _ _ => mem_univ _) hT
  have hGa := codiscreteWithin_comp_source
    (MeromorphicOn.eventually_codiscreteWithin_analyticAt g hp.nonconst_g.1)
    (fun _ _ => mem_univ _) hT
  have hU := codiscreteWithin_comp_source h.u_eq b.gamma_maps hT
  have hV := codiscreteWithin_comp_source h.v_eq b.gamma_maps hT
  have huExact : ∀ s ∈ ball (0 : ℂ) (B ^ 6 / 2),
      deriv b.gamma s * h.u (b.gamma s) = c * Complex.exp (s / 2) / b.k s := by
    intro s hs
    have hσ := b.sigma_ne_zero _ (b.gamma_maps hs)
    have hAs := hA _ (b.gamma_maps hs)
    have hu := (div_eq_iff hσ).mp (hcoef s hs).1
    rw [b.gamma_deriv s hs, b.k_eq s hs, hu]
    field_simp [hAs, hσ]
  have hvExact : ∀ s ∈ ball (0 : ℂ) (B ^ 6 / 2),
      deriv b.gamma s * h.v (b.gamma s) = c⁻¹ * Complex.exp (-s / 2) / b.k s := by
    intro s hs
    have hσ := b.sigma_ne_zero _ (b.gamma_maps hs)
    have hAs := hA _ (b.gamma_maps hs)
    have hv := (div_eq_iff hσ).mp (hcoef s hs).2
    rw [b.gamma_deriv s hs, b.k_eq s hs, hv]
    field_simp [hAs, hσ]
  constructor
  · filter_upwards [hFa, hU, self_mem_codiscreteWithin (ball (0 : ℂ) (B ^ 6 / 2))] with s hfs hus hs
    rw [auxU_comp hfs.differentiableAt (b.gamma_analytic s hs).differentiableAt, hus]
    exact huExact s hs
  · filter_upwards [hGa, hV, self_mem_codiscreteWithin (ball (0 : ℂ) (B ^ 6 / 2))] with s hgs hvs hs
    rw [auxV_comp hgs.differentiableAt (b.gamma_analytic s hs).differentiableAt, hvs]
    exact hvExact s hs

/-- Original marked multiplicities give a genuine fiber germ for Phi.
This is the punctured-limit theorem, not a raw auxiliary center value. -/
theorem NormalizedPair.auxPhi_fiber_order_pos_of_multiplicities
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {z : ℂ} {j : Fin 3} {m n : ℕ} (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hm : mult f (a j : Sphere) z = m) (hn : mult g (a j : Sphere) z = n) :
    0 < meromorphicOrderAt (fun w => auxPhi a f g w - (m : ℂ) / n) z := by
  have hmpos : 0 < mult f (a j : Sphere) z := by rw [hm]; exact hm1
  have hnpos : 0 < mult g (a j : Sphere) z := by rw [hn]; exact hn1
  have hom := order_sub_eq_mult hmpos
  have hon := order_sub_eq_mult hnpos
  rw [hm] at hom
  rw [hn] at hon
  have hlim := tendsto_auxPhi_at_shared (hp.nonconst_f.meromorphic z)
    (hp.nonconst_g.meromorphic z) hp.injective hm1 hn1 hom hon (hp.distinct z (mem_univ z))
  apply (tendsto_zero_iff_meromorphicOrderAt_pos
    ((hp.meromorphic_auxPhi z).sub (MeromorphicAt.const ((m : ℂ) / n) z))).mp
  have hfun : (auxPhi a f g - fun _ => (m : ℂ) / n) =
      (fun w => auxPhi a f g w - (m : ℂ) / n) := by
    funext w
    exact Pi.sub_apply _ _ _
  rw [hfun]
  simpa only [sub_self] using hlim.sub_const ((m : ℂ) / n)

/-- From an actual good point of the genuine c^2-fiber, construct the
normalized pulled-back pair and both original coefficient profiles. All
multiplicities at the center are preserved. Phase fixing uses analytic
models, so no value of a raw 0/0 auxiliary is substituted. -/
theorem exists_actual_fiber_sheet_with_profiles
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r R Δ : ℝ}
    (D : DivisorFactorData (auxPhi a f g) (r + 7 * Δ / 8))
    (E : DivisorFactorData (logDeriv (auxPhi a f g)) (r + 7 * Δ / 8))
    (P : DivisorFactorData (auxPsi a f g) (r + 7 * Δ / 8))
    (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    {z c : ℂ} (hc : c ≠ 0) (hz : ‖z‖ ≤ r)
    (haway : Real.exp (-4 * finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z)
    (hgood : (finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ^ 10 /
      truncatedDivisorDistance (jointDivisorSupport D E P) z < ‖E.exponentialModel z‖)
    (hfiber : 0 < meromorphicOrderAt (fun w => auxPhi a f g w - c ^ 2) z) :
    let B := finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)
    let d := truncatedDivisorDistance (jointDivisorSupport D E P) z
    ∃ (v : ℂ) (b : GoodPointBranch D.exponentialModel E.exponentialModel P.exponentialModel z v B d),
      NormalizedPair (ball 0 (B ^ 6 / 2)) (f ∘ b.gamma) (g ∘ b.gamma) a ∧
      (∀ β : Sphere, mult (f ∘ b.gamma) β 0 = mult f β z ∧ mult (g ∘ b.gamma) β 0 = mult g β z) ∧
      (auxU a (f ∘ b.gamma) (g ∘ b.gamma) =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
        (fun s => c * Complex.exp (s / 2) / b.k s)) ∧
      (auxV a (f ∘ b.gamma) (g ∘ b.gamma) =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
        (fun s => c⁻¹ * Complex.exp (-s / 2) / b.k s)) := by
  let B := finiteDiskBudget R Δ
    (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)
  let d := truncatedDivisorDistance (jointDivisorSupport D E P) z
  have hPhi : MeromorphicOn (auxPhi a f g) univ := fun w _ => hp.meromorphic_auxPhi w
  have hA : MeromorphicOn (logDeriv (auxPhi a f g)) univ := fun w _ =>
    (hp.meromorphic_auxPhi w).deriv.div (hp.meromorphic_auxPhi w)
  have hPsi : MeromorphicOn (auxPsi a f g) univ := fun w _ => hp.meromorphic_auxPsi w
  have hd := canonical_regular_branch_data D E P hPhi hA hPsi rfl hr hΔ hΔ1 hR hz haway
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hd.budget_large
  have hzΩ : z ∈ ball z (d / B ^ 4) := mem_ball_self (div_pos hd.distance_pos (pow_pos hB 4))
  have hzρ : z ∈ ball (0 : ℂ) (r + 7 * Δ / 8) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hne : ∀ α ∈ D.support, z ≠ α := by
    intro α hα heq
    have hdist := truncatedDivisorDistance_le_norm_sub
      (show α ∈ jointDivisorSupport D E P from Finset.mem_union_left _ (Finset.mem_union_left _ hα)) (z := z)
    have hzero : ‖z - α‖ = 0 := by simp only [heq, sub_self, norm_zero]
    rw [hzero] at hdist
    linarith only [hdist, hd.distance_pos]
  have hvalue := D.exponentialModel_eq_of_fiber_order_pos hzρ hne hfiber
  obtain ⟨models⟩ := exists_actual_regular_auxiliary_models hp D E P hr hΔ hΔ1 hR hz haway
  have hu0 := models.nonzero_u z hzΩ
  have hv0 := models.nonzero_v z hzΩ
  have hratio : models.u z / models.v z = c ^ 2 := (models.ratio z hzΩ).trans hvalue
  have hu : models.u z = c ^ 2 * models.v z := (div_eq_iff hv0).mp hratio
  have hprod := models.product z hzΩ
  have hU2 : models.u z ^ 2 = c ^ 2 * P.exponentialModel z := by
    calc
      models.u z ^ 2 = models.u z * models.u z := by ring
      _ = models.u z * (c ^ 2 * models.v z) := congrArg (fun t => models.u z * t) hu
      _ = c ^ 2 * (models.u z * models.v z) := by ring
      _ = c ^ 2 * P.exponentialModel z := congrArg (fun t => c ^ 2 * t) hprod
  let v0 := models.u z / c
  have hv : v0 ^ 2 = P.exponentialModel z := by
    change (models.u z / c) ^ 2 = _
    rw [div_pow, hU2, mul_div_cancel_left₀ _ (pow_ne_zero 2 hc)]
  obtain ⟨b, -⟩ := canonical_good_qpoint_branch D E P hPhi hA hPsi rfl hr hΔ hΔ1 hR
    hz haway hgood hfiber hv
  have hcenter : models.u z / v0 = c := by
    dsimp [v0]
    field_simp [hu0, hc]
  have hprofiles := CanonicalAuxiliaryModels.pullback_profiles hp models b hB hd.a_ne_zero hc hvalue hcenter
  refine ⟨v0, b, hp.comp_source (fun s hs => b.gamma_analytic s hs)
    b.gamma_deriv_ne_zero (fun _ _ => mem_univ _), ?_, hprofiles.1, hprofiles.2⟩
  intro β
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) (B ^ 6 / 2) := mem_ball_self (by positivity)
  constructor
  · rw [mult_comp_of_deriv_ne_zero (b.gamma_analytic 0 hzero) (b.gamma_deriv_ne_zero 0 hzero) β, b.gamma_zero]
  · rw [mult_comp_of_deriv_ne_zero (b.gamma_analytic 0 hzero) (b.gamma_deriv_ne_zero 0 hzero) β, b.gamma_zero]

end ThreeIM
