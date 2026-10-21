module

public import RequestProject.ThreeIM.ExponentialSectorRootLimit
public import RequestProject.ThreeIM.ExponentialExponent

/-! # The real positive stable exponent, with all ray inputs derived -/

@[expose] public section

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem tendsto_ray_rightSector (θ : ℝ) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (θ * Complex.I)) atTop
      (rightSectorAtTop (Real.cos θ)) := by
  let e : ℂ := Complex.exp (θ * Complex.I)
  have hn : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hre : e.re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
  have hnorm : Tendsto (fun r : ℝ => ‖(r : ℂ) * e‖) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]
    rfl
  change Tendsto (fun r : ℝ => (r : ℂ) * e) atTop
    (comap (fun t : ℂ => ‖t‖) atTop ⊓ 𝓟 {t : ℂ | Real.cos θ * ‖t‖ ≤ t.re})
  apply tendsto_inf.mpr
  refine ⟨tendsto_comap_iff.mpr hnorm, tendsto_principal.mpr ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simp only [norm_mul, hn, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr, Complex.re_ofReal_mul, hre]
  exact le_of_eq (mul_comm _ _)

theorem ExponentialPair.exists_canonical_marked_limit_positive_exponent
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∃ j : Fin 3,
      (∀ δ : ℝ, 0 < δ → Tendsto (fun t => chartFiniteMap (sphereGermValue f t))
        (rightSectorAtTop δ) (𝓝 (a j))) ∧
      (-(κ ^ 2 * deriv (cubicP a) (a j))).im = 0 ∧
      0 < (-(κ ^ 2 * deriv (cubicP a) (a j))).re := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let G : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  have hcanon : ExponentialPair a F G κ := h.canonical_representatives
  obtain ⟨j, hj⟩ := h.canonical_f_tendsto_marked_rightSectors
  refine ⟨j, hj, hcanon.stable_exponent_pos j ?_⟩
  intro θ hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hray := tendsto_ray_rightSector θ
  refine ⟨?_, (hj (Real.cos θ) hcos).comp hray,
    (h.canonical_cubic_logDeriv_tendsto_rightSector hcos).comp hray⟩
  filter_upwards [hray.eventually (h.canonical_analytic_eventually_rightSector hcos)] with r hr
  exact hr.1.differentiableAt

end ThreeIM
