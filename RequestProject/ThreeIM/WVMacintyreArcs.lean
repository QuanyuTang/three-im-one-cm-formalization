module

public import RequestProject.ThreeIM.WVNormalRadii
public import RequestProject.ThreeIM.WVMacintyreLocal
public import RequestProject.ThreeIM.WVLocal

/-!
# Sequential large-value arcs from the maximum-modulus method

The slope is real, not a central index. The arc widths are allowed to vary;
their products with the slopes tend to infinity, which is the property used
by the tangent-system argument.
-/

@[expose] public section

open Set Filter Topology

namespace ThreeIM

set_option autoImplicit false

theorem wv_real_arcs_step {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h : WVNonPolynomial H) (n : ℕ) :
    ∃ (r ν M κ : ℝ) (zr : ℂ),
      (n : ℝ) + 1 ≤ ν ∧ (n : ℝ) + 1 ≤ κ * ν ∧
      1 ≤ r ∧ ‖zr‖ = r ∧ 1 ≤ M ∧ ν ≤ Real.log M ^ 2 ∧ 0 < κ ∧ κ ≤ 1 ∧
      ∀ θ : ℝ, |θ| ≤ κ / 4 →
        M / 2 ≤ ‖H (zr * Complex.exp (θ * Complex.I))‖ ∧
        ‖zr * Complex.exp (θ * Complex.I) * deriv H (zr * Complex.exp (θ * Complex.I)) /
            (ν * H (zr * Complex.exp (θ * Complex.I))) - 1‖ ≤ 200 / ((n : ℝ) + 16) + 8 / ν ∧
        ‖H (zr * Complex.exp (θ * Complex.I)) *
            deriv (deriv H) (zr * Complex.exp (θ * Complex.I)) /
            deriv H (zr * Complex.exp (θ * Complex.I)) ^ 2 - 1‖ ≤
          200 / ((n : ℝ) + 16) + 8 / ν := by
  let η : ℝ := 1 / ((n : ℝ) + 16)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη16 : η ≤ 1 / 16 := by
    dsimp only [η]
    gcongr
    linarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n)]
  let γ : ℝ := Real.log (1 + η / 4) / 7
  have hγ : 0 < γ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have hB : 1 ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  obtain ⟨x, k, _, hx2, hAx, hρ, hρ1, hνB, hprodB, hνA, hflat⟩ :=
    wv_good_log_radius hH h hγ hB 1
  let ν := wvLogSlope H x
  let ρ := wvGridWidth γ (k + 1)
  let κ := ρ / 2
  let r := Real.exp x
  let M := wvMaximumModulus H r
  have hν : (n : ℝ) + 1 ≤ ν := by dsimp only [ν]; linarith
  have hν1 : 1 ≤ ν := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hκ : 0 < κ := half_pos hρ
  have hκ1 : κ ≤ 1 := by dsimp only [κ]; linarith
  have hκν : (n : ℝ) + 1 ≤ κ * ν := by dsimp only [κ]; nlinarith
  have hMpos : 0 < M := wvMaximumModulus_pos hH h.exists_nonzero (Real.exp_pos x)
  have hM1 : 1 ≤ M := by
    have hh : 0 ≤ Real.log M := by exact le_trans (by norm_num : (0 : ℝ) ≤ 216) hAx
    exact (Real.log_nonneg_iff hMpos).mp hh
  obtain ⟨zr, hzr, hmax⟩ := wvMaximumModulus_attained hH.continuous (Real.exp_pos x).le
  have hHzr : H zr ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hmax]
    exact hMpos
  have hzr0 : zr ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at hzr
    exact (Real.exp_pos x).ne' hzr.symm
  have hγε : 4 * (Real.exp (7 * γ) - 1) = η := by
    rw [show 7 * γ = Real.log (1 + η / 4) by dsimp only [γ]; ring,
      Real.exp_log (by positivity : 0 < 1 + η / 4)]
    ring
  have hexp : ∀ τ : ℂ, ‖τ‖ ≤ κ →
      ‖H (zr * Complex.exp τ) - H zr * Complex.exp ((ν : ℂ) * τ)‖ ≤
        η * ‖H zr * Complex.exp ((ν : ℂ) * τ)‖ := by
    intro τ hτ
    have hh := wv_local_monomial_of_affine_bound hH hzr hmax hHzr hρ
      (by positivity : 0 < 7 * γ)
      (fun t ht => (abs_le.mp (hflat t ht)).2) τ hτ
    rwa [hγε] at hh
  refine ⟨r, ν, M, κ, zr, hν, hκν, ?_, hzr, hM1, hνA, hκ, hκ1, ?_⟩
  · dsimp only [r]
    exact Real.one_le_exp (by linarith)
  · intro θ hθ
    have hκν1 : 1 ≤ κ * ν := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hmax' : (1 - η) * M ≤ ‖H zr‖ := by
      rw [hmax]
      change (1 - η) * M ≤ M
      nlinarith
    obtain ⟨h1, h2, h3⟩ := wv_local hH hzr0 hν1 hM1 hη.le hη16 hκ hκν1 hmax' hexp hθ
    have he : 8 * η ≤ 200 / ((n : ℝ) + 16) + 8 / ν := by
      have hνpos : 0 < ν := by linarith
      dsimp only [η]
      have hh : 8 / ((n : ℝ) + 16) ≤ 200 / ((n : ℝ) + 16) := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
      rw [mul_one_div]
      exact hh.trans (le_add_of_nonneg_right (div_nonneg (by norm_num) hνpos.le))
    refine ⟨h1, h2.trans he, ?_⟩
    simpa only [η, mul_one_div] using h3

theorem wv_real_arcs {H : ℂ → ℂ} (hH : Differentiable ℂ H) (h : WVNonPolynomial H) :
    ∃ (r ν M ε κ : ℕ → ℝ) (zr : ℕ → ℂ),
      Tendsto ν atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n => κ n * ν n) atTop atTop ∧
      (∀ n, 1 ≤ r n) ∧ (∀ n, 1 ≤ ν n) ∧ (∀ n, ‖zr n‖ = r n) ∧ (∀ n, 1 ≤ M n) ∧
      (∀ n, ν n ≤ Real.log (M n) ^ 2) ∧ (∀ n, 0 < κ n) ∧ (∀ n, κ n ≤ 1) ∧
      (∀ n, 1 ≤ κ n * ν n) ∧
      ∀ n (θ : ℝ), |θ| ≤ κ n / 4 →
        M n / 2 ≤ ‖H (zr n * Complex.exp (θ * Complex.I))‖ ∧
        ‖zr n * Complex.exp (θ * Complex.I) * deriv H (zr n * Complex.exp (θ * Complex.I)) /
            (ν n * H (zr n * Complex.exp (θ * Complex.I))) - 1‖ ≤ ε n ∧
        ‖H (zr n * Complex.exp (θ * Complex.I)) *
            deriv (deriv H) (zr n * Complex.exp (θ * Complex.I)) /
            deriv H (zr n * Complex.exp (θ * Complex.I)) ^ 2 - 1‖ ≤ ε n := by
  choose r ν M κ zr hνn hκνn hr hzr hM hνM hκ hκ1 hest using wv_real_arcs_step hH h
  have hν1 : ∀ n, 1 ≤ ν n := fun n =>
    le_trans (show (1 : ℝ) ≤ (n : ℝ) + 1 by
      linarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n)]) (hνn n)
  have hκν1 : ∀ n, 1 ≤ κ n * ν n := fun n =>
    le_trans (show (1 : ℝ) ≤ (n : ℝ) + 1 by
      linarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n)]) (hκνn n)
  have hνinf : Tendsto ν atTop atTop := tendsto_atTop_mono hνn
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨r, ν, M, fun n => 200 / ((n : ℝ) + 16) + 8 / ν n, κ, zr,
    hνinf, ?_, ?_, hr, hν1, hzr, hM, hνM, hκ, hκ1, hκν1, hest⟩
  · have h1 : Tendsto (fun n : ℕ => 200 / ((n : ℝ) + 16)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 16 tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n => 8 / ν n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hνinf
    simpa using h1.add h2
  · exact tendsto_atTop_mono hκνn
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

end ThreeIM
