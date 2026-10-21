module

public import RequestProject.ThreeIM.SphereMontel
public import RequestProject.ThreeIM.SphereTailNormality
public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-!
# Normality of dilates from omission in proper sectors

The input is eventual omission on each proper sector. No sharing-pair
normality, exponential stable expansion, or periodicity is used.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem exists_rightHalfplane_sector_ball {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m : ℝ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ w ∈ closedBall z₀ ε, m ≤ ‖w‖ ∧ δ * ‖w‖ ≤ w.re := by
  let ε : ℝ := z₀.re / 2
  let M : ℝ := ‖z₀‖ + ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hM : 0 < M := by dsimp [M]; linarith [norm_nonneg z₀]
  refine ⟨ε, hε, ε, hε, ε / M, div_pos hε hM, ?_⟩
  intro w hw
  have hd : ‖w - z₀‖ ≤ ε := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hr : ε ≤ w.re := by
    have hdre : |w.re - z₀.re| ≤ ‖w - z₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z₀)
    have hab : |w.re - z₀.re| ≤ ε := hdre.trans hd
    dsimp [ε] at hab ⊢
    linarith [(abs_le.mp hab).1]
  have hn : ‖w‖ ≤ M := by
    calc
      ‖w‖ = ‖(w - z₀) + z₀‖ := by congr 1; ring
      _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ M := by dsimp [M]; linarith
  refine ⟨hr.trans (Complex.re_le_norm w), ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hn (div_pos hε hM).le
  have hcancel : ε / M * M = ε := by field_simp
  rw [hcancel] at hmul
  exact hmul.trans hr

theorem eventually_dilate_of_sector_property {P : ℂ → Prop}
    (hP : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → P t)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ ε,
      P ((r n : ℂ) * w) := by
  obtain ⟨ε, hε, m, hm, δ, hδ, hwindow⟩ := exists_rightHalfplane_sector_ball hz₀
  obtain ⟨R, hR⟩ := hP δ hδ
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hr.eventually (eventually_ge_atTop (max 0 (R / m)))] with n hn w hw
  have hr0 : 0 ≤ r n := (le_max_left _ _).trans hn
  have hnorm : ‖(r n : ℂ) * w‖ = r n * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  apply hR
  · rw [hnorm]
    have hRm : R ≤ r n * m :=
      (div_le_iff₀ hm).mp ((le_max_right _ _).trans hn)
    exact hRm.trans (mul_le_mul_of_nonneg_left (hwindow w hw).1 hr0)
  · rw [hnorm, Complex.re_ofReal_mul]
    calc
      δ * (r n * ‖w‖) = r n * (δ * ‖w‖) := by ring
      _ ≤ r n * w.re := mul_le_mul_of_nonneg_left (hwindow w hw).2 hr0
      _ ≤ |r n * w.re| := le_abs_self _

theorem isNormalAt_dilates_of_sector_omission {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ) (a : Fin 3 → OnePoint ℂ)
    (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, F t ≠ a j)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    IsNormalAt (range (fun n w => F ((r n : ℂ) * w))) z₀ := by
  classical
  obtain ⟨ε, hε, hev⟩ := eventually_dilate_of_sector_property homit hr hz₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply isNormalAt_range_of_normal_tail (fun n w => F ((r n : ℂ) * w)) N
  have hol (n : ℕ) : SphereHolomorphicOn
      (fun w => F ((r (n + N) : ℂ) * w)) (ball z₀ ε) := by
    have hglobal : SphereHolomorphicOn (fun w => F ((r (n + N) : ℂ) * w)) univ := by
      simpa only [preimage_univ, zero_add] using hF.comp_affine 0 (r (n + N) : ℂ)
    exact sphereHolomorphicOn_mono hglobal isOpen_ball (subset_univ _)
  apply isNormalAt_of_omits_three_sphere (U := ball z₀ ε) isOpen_ball
    (fun H hH => by obtain ⟨n, rfl⟩ := hH; exact hol n)
    (a 0) (a 1) (a 2) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
  · rintro H ⟨n, rfl⟩ w hw
    exact hN (n + N) (by omega) w (ball_subset_closedBall hw) 0
  · rintro H ⟨n, rfl⟩ w hw
    exact hN (n + N) (by omega) w (ball_subset_closedBall hw) 1
  · rintro H ⟨n, rfl⟩ w hw
    exact hN (n + N) (by omega) w (ball_subset_closedBall hw) 2
  · exact mem_ball_self hε

theorem isNormalAt_meromorphic_dilates_of_sector_mult_zero {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (a : Fin 3 → ℂ) (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult f (a j : Sphere) t = 0)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    IsNormalAt (range (fun n w => sphereGermValue f ((r n : ℂ) * w))) z₀ := by
  apply isNormalAt_dilates_of_sector_omission
    (sphereHolomorphicOn_sphereGermValue isOpen_univ hf.1) (fun j => (a j : OnePoint ℂ))
      (fun i j h => ha (OnePoint.coe_injective h)) ?_ hr hz₀
  intro δ hδ
  obtain ⟨R, hR⟩ := homit δ hδ
  refine ⟨R, fun t ht hsec j heq => ?_⟩
  have hpos := (mult_finite_pos_iff_sphereGermValue_eq
    (hf.meromorphic t) (hf.2 t (mem_univ t) (a j))).mpr heq
  rw [hR t ht hsec j] at hpos
  exact lt_irrefl (0 : ℕ) hpos

end ThreeIM
