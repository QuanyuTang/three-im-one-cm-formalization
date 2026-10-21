module

public import RequestProject.ThreeIM.SelectedGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Growth dominates the polynomial and logarithmic selection parameters -/

@[expose] public section

open Filter Set MeasureTheory Topology

namespace ThreeIM

set_option autoImplicit false

theorem selected_log_bounds {r t : ℝ} (hr : 1 ≤ r) (hrt : r ≤ t)
    (ht : Real.exp 1 + 1 ≤ t) :
    1 ≤ Real.log (Real.exp 1 + r * t) ∧
      Real.log (Real.exp 1 + r * t) ≤ 3 * Real.log t := by
  have hr0 : 0 ≤ r := by linarith
  have ht1 : 1 ≤ t := hr.trans hrt
  have ht0 : 0 < t := by linarith
  have hs : 1 ≤ t ^ 2 := by nlinarith
  have he : Real.exp 1 ≤ Real.exp 1 * t ^ 2 :=
    le_mul_of_one_le_right (Real.exp_pos 1).le hs
  have hrt' : r * t ≤ t ^ 2 := by nlinarith
  have hbound : Real.exp 1 + r * t ≤ t ^ 3 := calc
    Real.exp 1 + r * t ≤ (Real.exp 1 + 1) * t ^ 2 := by nlinarith
    _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    _ = t ^ 3 := by ring
  have harg : 0 < Real.exp 1 + r * t := by positivity
  constructor
  · have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + r * t by linarith [mul_nonneg hr0 ht0.le])
    simpa only [Real.log_exp] using h
  · calc
      Real.log (Real.exp 1 + r * t) ≤ Real.log (t ^ 3) := Real.log_le_log harg hbound
      _ = 3 * Real.log t := by rw [Real.log_pow]; norm_num

theorem selected_growth_error_bound (p q : ℕ) {r t : ℝ} (hr : 1 ≤ r)
    (hgrowth : r ^ (2 * (p + 1)) ≤ t) (ht : Real.exp 1 + 1 ≤ t) :
    0 ≤ r ^ p * Real.log (Real.exp 1 + r * t) ^ q * Real.log r / t ∧
      r ^ p * Real.log (Real.exp 1 + r * t) ^ q * Real.log r / t ≤
        (3 : ℝ) ^ q * Real.log t ^ q / Real.sqrt t := by
  have hr0 : 0 < r := by linarith
  have hrt : r ≤ t := calc
    r = r ^ 1 := by simp
    _ ≤ r ^ (2 * (p + 1)) := pow_le_pow_right₀ hr (by omega)
    _ ≤ t := hgrowth
  have ht1 : 1 ≤ t := hr.trans hrt
  have ht0 : 0 < t := by linarith
  have hlogs := selected_log_bounds hr hrt ht
  have hroot : r ^ (p + 1) ≤ Real.sqrt t := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul]
    simpa only [Nat.mul_comm] using hgrowth
  have hfirst : r ^ p * Real.log r ≤ Real.sqrt t := calc
    r ^ p * Real.log r ≤ r ^ p * r :=
      mul_le_mul_of_nonneg_left (Real.log_le_self hr0.le) (pow_nonneg hr0.le _)
    _ = r ^ (p + 1) := by ring
    _ ≤ Real.sqrt t := hroot
  have hsecond : Real.log (Real.exp 1 + r * t) ^ q ≤ (3 : ℝ) ^ q * Real.log t ^ q := by
    calc
      Real.log (Real.exp 1 + r * t) ^ q ≤ (3 * Real.log t) ^ q := by
        gcongr <;> linarith [hlogs.1, hlogs.2]
      _ = (3 : ℝ) ^ q * Real.log t ^ q := mul_pow _ _ _
  have hnum : r ^ p * Real.log (Real.exp 1 + r * t) ^ q * Real.log r ≤
      Real.sqrt t * ((3 : ℝ) ^ q * Real.log t ^ q) := by
    calc
      r ^ p * Real.log (Real.exp 1 + r * t) ^ q * Real.log r =
          (r ^ p * Real.log r) * Real.log (Real.exp 1 + r * t) ^ q := by ring
      _ ≤ Real.sqrt t * ((3 : ℝ) ^ q * Real.log t ^ q) :=
        mul_le_mul hfirst hsecond (pow_nonneg (by linarith [hlogs.1]) _) (Real.sqrt_nonneg t)
  have hrootpos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hcancel : Real.sqrt t * ((3 : ℝ) ^ q * Real.log t ^ q) / t =
      (3 : ℝ) ^ q * Real.log t ^ q / Real.sqrt t := by
    apply (div_eq_div_iff ht0.ne' hrootpos.ne').2
    calc
      (Real.sqrt t * ((3 : ℝ) ^ q * Real.log t ^ q)) * Real.sqrt t =
          ((3 : ℝ) ^ q * Real.log t ^ q) * Real.sqrt t ^ 2 := by ring
      _ = ((3 : ℝ) ^ q * Real.log t ^ q) * t := by rw [Real.sq_sqrt ht0.le]
  exact ⟨div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr0.le _)
      (pow_nonneg (by linarith [hlogs.1]) _)) (Real.log_nonneg hr)) ht0.le,
    (div_le_div_of_nonneg_right hnum ht0.le).trans_eq hcancel⟩

theorem selected_growth_error_tendsto_zero (p q : ℕ) {r : ℕ → ℝ} {T : ℝ → ℝ}
    (hr : Tendsto r atTop atTop) (hr2 : ∀ n, 2 ≤ r n)
    (hgrowth : ∀ n, r n ^ (2 * (p + 1)) ≤ T (r n)) :
    Tendsto (fun n => r n ^ p * Real.log (Real.exp 1 + r n * T (r n)) ^ q *
      Real.log (r n) / T (r n)) atTop (𝓝 0) := by
  have hrt (n : ℕ) : r n ≤ T (r n) := calc
    r n = r n ^ 1 := by simp
    _ ≤ r n ^ (2 * (p + 1)) := pow_le_pow_right₀ (by linarith [hr2 n]) (by omega)
    _ ≤ T (r n) := hgrowth n
  have hT : Tendsto (fun n => T (r n)) atTop atTop := tendsto_atTop_mono hrt hr
  have hsmall : Tendsto (fun t : ℝ => Real.log t ^ q / Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (q : ℝ)
        (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun n => (3 : ℝ) ^ q * Real.log (T (r n)) ^ q /
      Real.sqrt (T (r n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, mul_div_assoc] using (hsmall.comp hT).const_mul ((3 : ℝ) ^ q)
  have hbound := (hT.eventually_ge_atTop (Real.exp 1 + 1)).mono fun n hn =>
    selected_growth_error_bound p q (by linarith [hr2 n]) (hgrowth n) hn
  exact squeeze_zero' (hbound.mono fun n hn => hn.1) (hbound.mono fun n hn => hn.2) hlim

theorem selected_growth_quotient_tendsto_atTop (p q : ℕ) {r : ℕ → ℝ} {T : ℝ → ℝ}
    (hr : Tendsto r atTop atTop) (hr2 : ∀ n, 2 ≤ r n)
    (hgrowth : ∀ n, r n ^ (2 * (p + 1)) ≤ T (r n)) :
    Tendsto (fun n => T (r n) / (r n ^ p * Real.log (Real.exp 1 + r n * T (r n)) ^ q *
      Real.log (r n))) atTop atTop := by
  have hsmall := selected_growth_error_tendsto_zero p q hr hr2 hgrowth
  have hpos : ∀ᶠ n in atTop,
      0 < r n ^ p * Real.log (Real.exp 1 + r n * T (r n)) ^ q * Real.log (r n) / T (r n) := by
    apply Eventually.of_forall
    intro n
    have hr0 : 0 < r n := by linarith [hr2 n]
    have hrt : r n ≤ T (r n) := calc
      r n = r n ^ 1 := by simp
      _ ≤ r n ^ (2 * (p + 1)) := pow_le_pow_right₀ (by linarith [hr2 n]) (by omega)
      _ ≤ T (r n) := hgrowth n
    have ht0 : 0 < T (r n) := hr0.trans_le hrt
    have hL : 0 < Real.log (Real.exp 1 + r n * T (r n)) := by
      have he := Real.add_one_le_exp (1 : ℝ)
      apply Real.log_pos
      nlinarith [mul_pos hr0 ht0]
    exact div_pos (mul_pos (mul_pos (pow_pos hr0 _) (pow_pos hL _))
      (Real.log_pos (by linarith [hr2 n]))) ht0
  have hwithin := tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hwithin

theorem selected_large_growth_radii {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hInf : InfiniteOrder f ∨ InfiniteOrder g) {E : Set ℝ} (hE : volume E < ⊤)
    (p q : ℕ) :
    ∃ r : ℕ → ℝ, (∀ n, 2 ≤ r n) ∧ Tendsto r atTop atTop ∧ (∀ n, r n ∉ E) ∧
      Tendsto (fun n => pairT f g (r n) /
        (r n ^ p * pairL f g (r n) ^ q * Real.log (r n))) atTop atTop := by
  obtain ⟨r, hr2, hr, hrE, hpow⟩ := power_radii_outside_finite_volume
    (pairT_monotoneOn_Ici_one hf hg) (pairT_frequently_ge_nat_power hInf) hE (2 * (p + 1))
  exact ⟨r, hr2, hr, hrE, by simpa only [pairL] using
    selected_growth_quotient_tendsto_atTop p q hr hr2 hpow⟩

end ThreeIM
