module

public import RequestProject.ThreeIM.ExponentialRealStableData
public import RequestProject.ThreeIM.ExponentialHullGeometry
public import RequestProject.ThreeIM.ExponentialStableOrbit
import Mathlib.Analysis.Complex.Convex

/-! # Continuing actual canonical real-tail stable formulae

The real orbit uses the finite charts of honest sphere germs. After
meromorphic continuation on a connected half-plane, codiscrete equality
transfers the formulae to the original representatives.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.real_stable_formula_of_canonical_real_tail
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (j : Fin 3) {μ : ℝ} (hμ : 0 < μ) (C : ℂ)
    {H V : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (hV : AnalyticAt ℂ V 0)
    (hH0 : H 0 = 0)
    (heq : ∀ᶠ r : ℝ in atTop,
      chartFiniteMap (sphereGermValue f (r : ℂ)) =
        a j + H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))) ∧
      (chartFiniteMap (sphereGermValue g (r : ℂ)))⁻¹ = Complex.exp (-(r : ℂ)) *
        V (Complex.exp (-(r : ℂ)),
          H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))))) :
    ∃ R₀ : ℝ, ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
      f z = a j + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)) ∧
      (g z)⁻¹ = Complex.exp (-z) *
        V (Complex.exp (-z), H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))) := by
  let F : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue f z)
  let G : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue g z)
  let M : ℂ → ℂ := fun z => a j + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))
  let N : ℂ → ℂ := fun z => (Complex.exp (-z) *
    V (Complex.exp (-z), H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z))))⁻¹
  have hc : ExponentialPair a F G κ := h.canonical_representatives
  obtain ⟨R₁, hM, hN⟩ := real_stable_models_meromorphic_on_halfplane hH hV hH0 hμ C (a j)
  obtain ⟨R₂, htail⟩ := eventually_atTop.mp heq
  let R : ℝ := max R₁ R₂
  let U : Set ℂ := {z | R < z.re}
  have hUsub : U ⊆ {z : ℂ | R₁ < z.re} := fun z hz =>
    (le_max_left R₁ R₂).trans_lt hz
  have hU : IsConnected U := (convex_halfSpace_re_gt R).isConnected
    ⟨((R + 1 : ℝ) : ℂ), by simp [U]⟩
  have hxU : ((R + 1 : ℝ) : ℂ) ∈ U := by simp [U]
  have hx : R < R + 1 := by linarith
  have hF : F =ᶠ[codiscreteWithin U] M :=
    meromorphic_eq_codiscreteWithin_of_eq_real_tail
      (fun z _ => hc.pair.nonconst_f.1 z (mem_univ z))
      (fun z hz => hM z (hUsub hz))
      hU hxU hx (fun r hr => (htail r ((le_max_right R₁ R₂).trans hr.le)).1)
  have hG : G =ᶠ[codiscreteWithin U] N :=
    meromorphic_eq_codiscreteWithin_of_eq_real_tail
      (fun z _ => hc.pair.nonconst_g.1 z (mem_univ z))
      (fun z hz => hN z (hUsub hz))
      hU hxU hx (fun r hr => by
        have hrG := (htail r ((le_max_right R₁ R₂).trans hr.le)).2
        simpa only [G, N, inv_inv] using congrArg (fun z : ℂ => z⁻¹) hrG)
  have hrawF : f =ᶠ[codiscreteWithin U] F :=
    chartFinite_sphereGerm_eq_codiscreteWithin
      (show MeromorphicOn f U from fun z _ => h.pair.nonconst_f.1 z (mem_univ z))
  have hrawG : g =ᶠ[codiscreteWithin U] G :=
    chartFinite_sphereGerm_eq_codiscreteWithin
      (show MeromorphicOn g U from fun z _ => h.pair.nonconst_g.1 z (mem_univ z))
  refine ⟨R, ?_⟩
  filter_upwards [hrawF, hrawG, hF, hG] with z hzF hzG hzM hzN
  refine ⟨hzF.trans hzM, ?_⟩
  rw [hzG, hzN]
  simp only [N, inv_inv]

/-- Once the actual canonical real orbit has supplied its formulae, all
fields of the original-representative stable data are constructed. -/
theorem ExponentialPair.real_stable_data_of_canonical_real_tail
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (j : Fin 3) {μ : ℝ} (hμ : 0 < μ)
    (C : ℂ) (hC : C ≠ 0) {H V J : ℂ × ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (hV : AnalyticAt ℂ V 0) (hH0 : H 0 = 0)
    (hInv : ∀ᶠ p : ℂ × ℂ in 𝓝 0, H p * Complex.exp (J (p.1, H p)) = p.2)
    (heq : ∀ᶠ r : ℝ in atTop,
      chartFiniteMap (sphereGermValue f (r : ℂ)) =
        a j + H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))) ∧
      (chartFiniteMap (sphereGermValue g (r : ℂ)))⁻¹ = Complex.exp (-(r : ℂ)) *
        V (Complex.exp (-(r : ℂ)),
          H (Complex.exp (-(r : ℂ)), C * Complex.exp (-(μ : ℂ) * (r : ℂ))))) :
    Nonempty (ExponentialRealStableData a f g) := by
  obtain ⟨R₀, hformula⟩ := h.real_stable_formula_of_canonical_real_tail j hμ C hH hV hH0 heq
  exact ⟨{
    index := j
    μ := μ
    μ_pos := hμ
    C := C
    C_ne_zero := hC
    H := H
    V := V
    J := J
    H_analytic := hH
    V_analytic := hV
    H_zero := hH0
    coordinate_inverse := hInv
    R₀ := R₀
    formula := hformula
  }⟩

end ThreeIM
