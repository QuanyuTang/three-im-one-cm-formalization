module

public import RequestProject.ThreeIM.ExponentialRealStableData
public import RequestProject.ThreeIM.ExponentialPhaseHulls
public import RequestProject.ThreeIM.ExponentialPeriodFromFormula
import Mathlib.NumberTheory.Real.Irrational

/-! # Excluding a genuine exponential defect from derived real stable data

The two members and their reflected swap need their actual stable expansions.
The irrational branch uses a genuine critical fiber. The rational branch
constructs the common period and applies rational descent.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem positive_rational_real_complex_ratio {μ : ℝ} (hμ : 0 < μ)
    (hRat : ¬ Irrational μ) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (μ : ℂ) = (p : ℂ) / q := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hRat
  have hrpos : (0 : ℚ) < r := by
    exact_mod_cast (show (0 : ℝ) < (r : ℝ) by rw [← hr]; exact hμ)
  have hn : 0 < r.num := Rat.num_pos.mpr hrpos
  have hncast : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hn.le
  have hnC : (r.num.toNat : ℂ) = (r.num : ℂ) := by exact_mod_cast hncast
  refine ⟨r.num.toNat, r.den, ?_, r.pos, ?_⟩
  · omega
  · calc
      (μ : ℂ) = ((r : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hr
      _ = (r : ℂ) := by norm_cast
      _ = (r.num : ℂ) / r.den := Rat.cast_def r
      _ = (r.num.toNat : ℂ) / r.den := by rw [hnC]

/-- An actual positive rational real exponent in the supplied formula
gives the finite CM conclusion with no universal expansion theorem. -/
theorem ExponentialPair.sharesCM_of_real_stable_data
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (D : ExponentialRealStableData a f g)
    (hRat : ¬ Irrational D.μ) :
    ∀ j, SharesCMOn univ f g (a j : Sphere) := by
  obtain ⟨p, q, -, hq, hμ⟩ := positive_rational_real_complex_ratio D.μ_pos hRat
  have hexp : ∀ᶠ z in codiscreteWithin {z : ℂ | D.R₀ < z.re},
      f z = a D.index + D.H (Complex.exp (-z), D.C * Complex.exp (-((p : ℂ) / q) * z)) ∧
        (g z)⁻¹ = Complex.exp (-z) *
          D.V (Complex.exp (-z), D.H (Complex.exp (-z),
            D.C * Complex.exp (-((p : ℂ) / q) * z))) := by
    simpa only [hμ] using D.formula
  obtain ⟨hpf, hpg⟩ := h.period_of_rational_stable_formula hq hexp
  obtain ⟨R, S, hRS⟩ := h.eq_rational_exp_of_period hq hpf hpg
  exact h.sharesCM_of_rational_exp hq hRS

/-- The actual expansions of a pair and its reflected swap give both
sets of half-plane bounds. A genuine first-member critical fiber then
forces a rational exponent, whose CM consequence contradicts its order. -/
theorem ExponentialPair.false_of_critical_real_stable_data
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (D : ExponentialRealStableData a f g)
    (E : ExponentialRealStableData a (fun z => g (-z)) (fun z => f (-z)))
    (j : Fin 3) (z : ℂ) (hm : 2 ≤ mult f (a j : Sphere) z) : False := by
  have hr := h.right_bounds_of_real_stable_formula D.μ_pos D.C
    D.H_analytic D.V_analytic D.H_zero D.formula
  have he := h.reflect_swap.right_bounds_of_real_stable_formula E.μ_pos E.C
    E.H_analytic E.V_analytic E.H_zero E.formula
  have hlf := left_sphere_bounds_of_reflected_right h.pair.nonconst_f.1 he.2
  have hlg := left_sphere_bounds_of_reflected_right h.pair.nonconst_g.1 he.1
  have hRat := h.not_irrational_stable_exponent_of_critical
    D.μ_pos D.C (a D.index) D.C_ne_zero D.H_analytic
    (D.formula.mono fun _ hz => hz.1) D.coordinate_inverse
    (by simp : (a D.index : OnePoint ℂ) ≠ OnePoint.infty)
    (by simp : OnePoint.infty ≠ (a E.index : OnePoint ℂ))
    hr.1 hlf hr.2 hlg j z hm
  have hcm := h.sharesCM_of_real_stable_data D hRat j z (mem_univ z)
  have hp : 0 < mult f (a j : Sphere) z := by omega
  have hmin := (h.shared_point hp).1
  rw [← hcm, min_self] at hmin
  omega

/-- A stable-data factory will be instantiated by the actual existence
theorem. The defect is assumed only inside this contradiction proof. -/
theorem ExponentialPair.not_isDefect_of_real_stable_data_factory
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ)
    (hdata : ∀ F G : ℂ → ℂ, ExponentialPair a F G κ →
      Nonempty (ExponentialRealStableData a F G))
    (j : Fin 3) (z : ℂ) : ¬ IsDefect f g (a j : Sphere) z := by
  intro hd
  obtain ⟨F, G, w, hFG, hm⟩ := h.exists_critical_first_of_defect hd
  obtain ⟨D⟩ := hdata F G hFG
  obtain ⟨E⟩ := hdata (fun w => G (-w)) (fun w => F (-w)) hFG.reflect_swap
  exact hFG.false_of_critical_real_stable_data D E j w hm

end ThreeIM
