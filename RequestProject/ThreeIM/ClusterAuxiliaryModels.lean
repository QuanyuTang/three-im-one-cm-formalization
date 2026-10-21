module

public import RequestProject.ThreeIM.ClusterCanonicalSelection
public import RequestProject.ThreeIM.ClusterAuxiliaryInputs
public import RequestProject.ThreeIM.TransportAnalytic

/-! # Honest auxiliary units on an actual regular disk

The original f,g remain meromorphic and may have poles. Only U,V, whose
nonnegative orders are already proved for normalized pairs, are replaced
by analytic representatives. The ratio/product identities are extended
from codiscrete equality by continuity.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real

namespace ThreeIM

structure CanonicalAuxiliaryModels (a : Fin 3 → ℂ) (f g phi psi : ℂ → ℂ) (Ω : Set ℂ) where
  u : ℂ → ℂ
  v : ℂ → ℂ
  holo_u : DifferentiableOn ℂ u Ω
  holo_v : DifferentiableOn ℂ v Ω
  nonzero_u : ∀ w ∈ Ω, u w ≠ 0
  nonzero_v : ∀ w ∈ Ω, v w ≠ 0
  u_eq : auxU a f g =ᶠ[codiscreteWithin Ω] u
  v_eq : auxV a f g =ᶠ[codiscreteWithin Ω] v
  product : ∀ w ∈ Ω, u w * v w = psi w
  ratio : ∀ w ∈ Ω, u w / v w = phi w

/-- Canonical U/V representatives are units wherever the actual Psi
model is nonzero. No raw auxiliary value at the center is used. -/
theorem exists_canonical_auxiliary_models
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {ρ : ℝ} (D : DivisorFactorData (auxPhi a f g) ρ) (P : DivisorFactorData (auxPsi a f g) ρ)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩρ : Ω ⊆ ball (0 : ℂ) ρ)
    (hphi : DifferentiableOn ℂ D.exponentialModel Ω)
    (hpsi : DifferentiableOn ℂ P.exponentialModel Ω)
    (hpsi0 : ∀ w ∈ Ω, P.exponentialModel w ≠ 0) :
    Nonempty (CanonicalAuxiliaryModels a f g D.exponentialModel P.exponentialModel Ω) := by
  obtain ⟨u, hua, hueq, -, -⟩ := transport_analytic_rep_on_pole_free (Ω := Ω)
    (fun w _ => hp.meromorphic_auxU w) (fun w _ => (hp.order_aux (mem_univ w)).1.1)
  obtain ⟨v, hva, hveq, -, -⟩ := transport_analytic_rep_on_pole_free (Ω := Ω)
    (fun w _ => hp.meromorphic_auxV w) (fun w _ => (hp.order_aux (mem_univ w)).2.1.1)
  have hprod : EqOn (fun w => u w * v w) P.exponentialModel Ω := by
    apply eqOn_of_continuousOn_codiscrete hΩ (hua.continuousOn.mul hva.continuousOn) hpsi.continuousOn
    filter_upwards [hueq, hveq, P.exponentialModel_eq_codiscrete hΩρ] with w hu hv hP
    simpa only [auxPsi, hu, hv, Pi.mul_apply] using hP
  have hu0 : ∀ w ∈ Ω, u w ≠ 0 := by
    intro w hw hzero
    have h : u w * v w = P.exponentialModel w := hprod hw
    rw [hzero, zero_mul] at h
    exact hpsi0 w hw h.symm
  have hv0 : ∀ w ∈ Ω, v w ≠ 0 := by
    intro w hw hzero
    have h : u w * v w = P.exponentialModel w := hprod hw
    rw [hzero, mul_zero] at h
    exact hpsi0 w hw h.symm
  have hratio : EqOn (fun w => u w / v w) D.exponentialModel Ω := by
    apply eqOn_of_continuousOn_codiscrete hΩ (hua.continuousOn.div hva.continuousOn hv0) hphi.continuousOn
    filter_upwards [hueq, hveq, D.exponentialModel_eq_codiscrete hΩρ] with w hu hv hD
    simpa only [auxPhi, hu, hv, Pi.div_apply] using hD
  exact ⟨{
    u := u
    v := v
    holo_u := hua.differentiableOn
    holo_v := hva.differentiableOn
    nonzero_u := hu0
    nonzero_v := hv0
    u_eq := hueq
    v_eq := hveq
    product := fun w hw => hprod hw
    ratio := fun w hw => hratio hw }⟩

/-- The actual finite-disk hypotheses alone produce the auxiliary units
needed to fix the square-root sign on a selected sheet. -/
theorem exists_actual_regular_auxiliary_models
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r R Δ : ℝ}
    (D : DivisorFactorData (auxPhi a f g) (r + 7 * Δ / 8))
    (E : DivisorFactorData (logDeriv (auxPhi a f g)) (r + 7 * Δ / 8))
    (P : DivisorFactorData (auxPsi a f g) (r + 7 * Δ / 8))
    (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (haway : Real.exp (-4 * finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z) :
    Nonempty (CanonicalAuxiliaryModels a f g D.exponentialModel P.exponentialModel
      (ball z (truncatedDivisorDistance (jointDivisorSupport D E P) z /
        (finiteDiskBudget R Δ (finiteDiskCoefficientMass (auxPhi a f g)
          (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ^ 4))) := by
  have hPhi : MeromorphicOn (auxPhi a f g) univ := fun w _ => hp.meromorphic_auxPhi w
  have hA : MeromorphicOn (logDeriv (auxPhi a f g)) univ := fun w _ =>
    (hp.meromorphic_auxPhi w).deriv.div (hp.meromorphic_auxPhi w)
  have hPsi : MeromorphicOn (auxPsi a f g) univ := fun w _ => hp.meromorphic_auxPsi w
  have hd := canonical_regular_branch_data D E P hPhi hA hPsi rfl hr hΔ hΔ1 hR hz haway
  have hR1 : 1 ≤ R := by linarith
  have hM := finiteDiskCoefficientMass_ge_one (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) hR1
  obtain ⟨_, _, hi, _⟩ := finiteDiskBudget_basic_controls hR1 hΔ hΔ1 hM
  have hInv : (finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R))⁻¹ ≤ Δ := by
    have h := inv_anti₀ (inv_pos.mpr hΔ) hi
    simpa only [inv_inv] using h
  have hgeo := regular_disk_geometry (jointDivisorSupport D E P) hd.budget_large hInv hz hd.distance_pos
  apply exists_canonical_auxiliary_models hp D P isOpen_ball
    (fun w hw => ball_subset_ball (by linarith : r + Δ / 2 ≤ r + 7 * Δ / 8) (hgeo.1 hw))
    hd.phi_holo hd.psi_holo hd.psi_ne_zero

end ThreeIM
