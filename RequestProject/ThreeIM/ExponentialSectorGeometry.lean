module

public import RequestProject.ThreeIM.Basic

/-!
# A fixed polar rectangle in a right half-plane disk

The parameters are chosen from an arbitrary open disk whose centre has
positive real part.  In particular the angular interval has positive length;
its existence is a conclusion, rather than an assumption in the sector
integration argument.
-/

@[expose] public section

open Filter Set Topology Real Complex Metric

namespace ThreeIM

theorem exists_polar_point_in_ball {z : ℂ} (hz : 0 < z.re) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < 2 * π ∧
      circleMap 0 ρ θ ∈ ball z ε ∧ (circleMap 0 ρ θ).re = z.re := by
  have hs : 0 < ε / 4 := by positivity
  obtain ⟨w, hwr, hwi, hwball⟩ : ∃ w : ℂ,
      w.re = z.re ∧ w.im ≠ 0 ∧ w ∈ ball z ε := by
    by_cases hi : 0 ≤ z.im
    · refine ⟨z + (ε / 4 : ℝ) * I, ?_, ?_, ?_⟩
      · simp
      · simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
          mul_one, zero_mul, add_zero]
        linarith
      · rw [mem_ball, dist_eq_norm]
        have heq : z + (ε / 4 : ℝ) * I - z = (ε / 4 : ℝ) * I := by ring
        rw [heq, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos hs]
        linarith
    · refine ⟨z - (ε / 4 : ℝ) * I, ?_, ?_, ?_⟩
      · simp
      · simp only [sub_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
          mul_one, zero_mul, add_zero]
        linarith
      · rw [mem_ball, dist_eq_norm]
        have heq : z - (ε / 4 : ℝ) * I - z = -((ε / 4 : ℝ) * I) := by ring
        rw [heq, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos hs]
        linarith
  have hw : w ≠ 0 := by
    intro heq
    have := congrArg Complex.re heq
    simp only [zero_re] at this
    linarith
  have hρ : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have harg : arg w ≠ 0 := fun heq => hwi (arg_eq_zero_iff.mp heq).2
  have hpolar : circleMap 0 ‖w‖ (arg w) = w := by
    simpa only [circleMap, zero_add] using norm_mul_exp_arg_mul_I w
  by_cases ha : 0 < arg w
  · refine ⟨‖w‖, arg w, hρ, ha, ?_, ?_, ?_⟩
    · have := arg_le_pi w
      linarith [pi_pos]
    · simpa only [hpolar] using hwball
    · simpa only [hpolar] using hwr
  · have han : arg w < 0 := lt_of_le_of_ne (le_of_not_gt ha) harg
    have hp : circleMap 0 ‖w‖ (arg w + 2 * π) = w := by
      rw [(periodic_circleMap 0 ‖w‖) (arg w), hpolar]
    refine ⟨‖w‖, arg w + 2 * π, hρ, ?_, ?_, ?_, ?_⟩
    · linarith [neg_pi_lt_arg w, pi_pos]
    · linarith
    · simpa only [hp] using hwball
    · simpa only [hp] using hwr

theorem exists_annular_sector_in_ball {z : ℂ} (hz : 0 < z.re) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ α β u v : ℝ, 0 < α ∧ α < β ∧ 0 ≤ u ∧ u < v ∧ v ≤ 2 * π ∧
      ∀ ρ ∈ Icc α β, ∀ θ ∈ Icc u v,
        circleMap 0 ρ θ ∈ ball z ε ∧ z.re / 2 < (circleMap 0 ρ θ).re := by
  obtain ⟨ρ₀, θ₀, hρ₀, hθ₀, hθπ, hball, hre⟩ :=
    exists_polar_point_in_ball hz hε
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hnb : ∀ᶠ p : ℝ × ℝ in 𝓝 (ρ₀, θ₀),
      circleMap 0 p.1 p.2 ∈ ball z ε ∧ z.re / 2 < (circleMap 0 p.1 p.2).re := by
    refine (hc.continuousAt.eventually (isOpen_ball.mem_nhds hball)).and ?_
    have hr : z.re / 2 < (circleMap 0 ρ₀ θ₀).re := by rw [hre]; linarith
    exact (Complex.continuous_re.comp hc).continuousAt.eventually (eventually_gt_nhds hr)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnb
  let m : ℝ := min δ (min ρ₀ (min θ₀ (2 * π - θ₀)))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min hδ (lt_min hρ₀ (lt_min hθ₀ (sub_pos.mpr hθπ)))
  have hmδ : m ≤ δ := min_le_left _ _
  have hmρ : m ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hmθ : m ≤ θ₀ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmπ : m ≤ 2 * π - θ₀ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let η : ℝ := m / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := by dsimp [η]; linarith
  have hηρ : η < ρ₀ := by dsimp [η]; linarith
  have hηθ : η < θ₀ := by dsimp [η]; linarith
  have hηπ : η < 2 * π - θ₀ := by dsimp [η]; linarith
  refine ⟨ρ₀ - η, ρ₀ + η, θ₀ - η, θ₀ + η, by linarith,
    by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro ρ hρ θ hθ
  apply hδsub (a := (ρ, θ))
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  have hρabs : |ρ - ρ₀| ≤ η := abs_le.mpr ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  have hθabs : |θ - θ₀| ≤ η := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact ⟨hρabs.trans_lt hηδ, hθabs.trans_lt hηδ⟩

end ThreeIM
