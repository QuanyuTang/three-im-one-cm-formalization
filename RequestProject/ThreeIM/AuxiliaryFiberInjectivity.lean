module

public import RequestProject.ThreeIM.AuxiliaryPair
public import RequestProject.ThreeIM.SimpleLocalInjectivity

/-!
# Shared finite fibers in a disk where the auxiliary quotient is injective

The zero-free prescribed coefficients give order zero for Psi through their
punctured germs. Near the value one, every shared finite fiber is simple and
the quotient is exactly one. Thus an injective quotient permits at most one
point in the union of the three finite shared fibers.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem AuxiliaryPairOn.psi_order_eq_zero {Ω : Set ℂ} {f g u v : ℂ → ℂ}
    {a : Fin 3 → ℂ} (h : AuxiliaryPairOn Ω f g u v a) (hΩ : IsOpen Ω)
    {z : ℂ} (hz : z ∈ Ω) : meromorphicOrderAt (auxPsi a f g) z = 0 := by
  have hU := auxiliary_local_of_codiscreteWithin hΩ h.u_eq hz
  have hV := auxiliary_local_of_codiscreteWithin hΩ h.v_eq hz
  have heq : auxPsi a f g =ᶠ[𝓝[≠] z] (fun w => u w * v w) := hU.mul hV
  rw [meromorphicOrderAt_congr heq]
  have ha := (h.holo_u.analyticOnNhd hΩ z hz).mul (h.holo_v.analyticOnNhd hΩ z hz)
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ha.meromorphicAt).mp
    ⟨u z * v z, mul_ne_zero (h.nonzero_u z hz) (h.nonzero_v z hz),
      ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem AuxiliaryPairOn.quotient_eq_one_at_finite_fiber
    {Ω : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    {j : Fin 3} (hj : sphereGermValue f z = (a j : OnePoint ℂ))
    (hclose : ‖u z / v z - 1‖ < (1 : ℝ) / 2) : u z / v z = 1 := by
  have hm : 0 < mult f (a j : Sphere) z :=
    (mult_finite_pos_iff_sphereGermValue_eq (h.pair.nonconst_f.1 z hz)
      (h.pair.nonconst_f.2 z hz (a j))).mpr hj
  have hcont := ((h.holo_u z hz).differentiableAt (hΩ.mem_nhds hz)).continuousAt.div
    ((h.holo_v z hz).differentiableAt (hΩ.mem_nhds hz)).continuousAt (h.nonzero_v z hz)
  exact (shared_simple_of_auxPhi_near_one h.pair hz hm (h.psi_order_eq_zero hΩ hz)
    hcont (auxiliary_local_of_codiscreteWithin hΩ h.phi_eq hz) hclose).2.2

theorem AuxiliaryPairOn.finite_fibers_subsingleton
    {Ω : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) (hΩ : IsOpen Ω)
    (hinj : InjOn (fun z => u z / v z) Ω)
    (hclose : ∀ z ∈ Ω, ‖u z / v z - 1‖ < (1 : ℝ) / 2)
    {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hxf : ∃ j, sphereGermValue f x = (a j : OnePoint ℂ))
    (hyf : ∃ k, sphereGermValue f y = (a k : OnePoint ℂ)) : x = y := by
  obtain ⟨j, hj⟩ := hxf
  obtain ⟨k, hk⟩ := hyf
  exact hinj hx hy ((h.quotient_eq_one_at_finite_fiber hΩ hx hj (hclose x hx)).trans
    (h.quotient_eq_one_at_finite_fiber hΩ hy hk (hclose y hy)).symm)

end ThreeIM
