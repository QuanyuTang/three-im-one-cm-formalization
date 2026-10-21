module

public import RequestProject.ThreeIM.SelectedRadiiParameter

/-! # The retained counting mass exceeds the polynomial exception budget

The logarithmic count includes its genuine origin term. Its fixed origin
gap changes the logarithmic error only by a constant factor. The density
and local exception estimates therefore force more actual support points
than any fixed multiple of the branch parameter to the power twenty-six.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Real Topology

namespace ThreeIM

theorem selected_log_origin_gap_bound {r rstar : ℝ} (hstar : 0 < rstar)
    (hr : Real.exp 1 ≤ r) (hrstar : rstar ≤ r) :
    0 ≤ Real.log (r / rstar) ∧
      Real.log (r / rstar) ≤ (1 + |Real.log rstar|) * Real.log r := by
  have hrpos : 0 < r := (Real.exp_pos 1).trans_le hr
  have hlog : 1 ≤ Real.log r := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hr
  refine ⟨Real.log_nonneg ((one_le_div hstar).mpr hrstar), ?_⟩
  rw [Real.log_div hrpos.ne' hstar.ne']
  have hscale := le_mul_of_one_le_right (abs_nonneg (Real.log rstar)) hlog
  nlinarith only [hscale, neg_le_abs (Real.log rstar)]

/-- This is a counting lemma, not an assumed branch selection. Its inputs
are the actual density inequality, the actual distinct-support bound, and
the already proved vanishing Nevanlinna and polynomial error terms. -/
theorem selected_counting_budget_eventually_lt
    {r B T L N card : ℕ → ℝ} {rstar α C K : ℝ}
    (hr : Tendsto r atTop atTop) (hstar : 0 < rstar) (hα : 0 < α) (hK : 0 ≤ K)
    (hB : ∀ n, 0 ≤ B n) (hT : ∀ᶠ n in atTop, 0 < T n)
    (hlocal : Tendsto (fun n => B n ^ 26 * Real.log (r n) / T n) atTop (𝓝 0))
    (hglobal : Tendsto (fun n => L n / T n) atTop (𝓝 0))
    (hdensity : ∀ᶠ n in atTop, α * T n ≤ N n + C * L n)
    (hcount : ∀ n, N n ≤ 3 * card n * Real.log (r n / rstar)) :
    ∀ᶠ n in atTop, K * B n ^ 26 < card n := by
  let A : ℝ := 3 * K * (1 + |Real.log rstar|)
  have hsmall : Tendsto (fun n => A * (B n ^ 26 * Real.log (r n) / T n) +
      C * (L n / T n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hlocal.const_mul A).add (hglobal.const_mul C)
  filter_upwards [hT, hdensity, hr.eventually_ge_atTop (max (Real.exp 1) rstar),
    hsmall.eventually (gt_mem_nhds hα)] with n hTn hd hn hs
  have hlog := selected_log_origin_gap_bound hstar
    ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  by_contra hnot
  have hc : card n ≤ K * B n ^ 26 := le_of_not_gt hnot
  have hN : N n ≤ A * (B n ^ 26 * Real.log (r n)) := by
    calc
      N n ≤ 3 * card n * Real.log (r n / rstar) := hcount n
      _ ≤ 3 * (K * B n ^ 26) * Real.log (r n / rstar) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc (by norm_num)) hlog.1
      _ ≤ 3 * (K * B n ^ 26) * ((1 + |Real.log rstar|) * Real.log (r n)) :=
        mul_le_mul_of_nonneg_left hlog.2 (by positivity)
      _ = A * (B n ^ 26 * Real.log (r n)) := by dsimp only [A]; ring
  have hnorm : α ≤ (A * (B n ^ 26 * Real.log (r n)) + C * L n) / T n := by
    apply (le_div_iff₀ hTn).mpr
    linarith only [hd, hN]
  have heq : (A * (B n ^ 26 * Real.log (r n)) + C * L n) / T n =
      A * (B n ^ 26 * Real.log (r n) / T n) + C * (L n / T n) := by ring
  rw [heq] at hnorm
  exact (not_le_of_gt hs) hnorm

end ThreeIM
