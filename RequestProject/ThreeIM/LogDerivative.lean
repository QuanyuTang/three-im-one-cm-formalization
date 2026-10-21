module

public import RequestProject.ThreeIM.LogDerivFactor
public import RequestProject.ThreeIM.NevanlinnaBasic

/-!
# The logarithmic derivative lemma (External theorem 2.3)

For a nonconstant meromorphic `h` on `ℂ` and `a ∈ ℂ`,
`m(r, h'/(h - a)) = O(log (e + r T(r, h)))` outside a set of finite linear measure.

The proof follows the classical route without the Poisson–Jensen formula: on a disk
`|z| ≤ ρ` write `F = h - a = ∏ (z - u)^{d u} · g` (`exists_factor_disk`), so that
`F'/F = ∑ d u/(z - u) + g'/g`.  The sum is controlled by `proximity_sum_div_sub_le`, the
number of terms by the counting functions at a larger radius (`sum_abs_order_mul_log_le`), and
`g'/g` by the Poisson-type bound and the Borel–Carathéodory estimate
(`norm_logDeriv_le_of_abs_log_le`).  A Borel-type growth lemma then chooses the radii.
-/

@[expose] public section

open Real MeasureTheory Set Filter Metric Topology ValueDistribution

namespace ThreeIM

/-- Weighted counting: `(∑_{z ∈ S} D z) log (R/ρ) ≤ N(R, D)` for `S` in `|z| ≤ ρ`, `1 ≤ ρ ≤ R`. -/
lemma logCounting_ge_weighted (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) {ρ R : ℝ}
    (hρ : 1 ≤ ρ) (hρR : ρ ≤ R) (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ ≤ ρ) :
    (∑ z ∈ S, (D z : ℝ)) * log (R / ρ) ≤ Function.locallyFinsuppWithin.logCounting D R := by
  have hR0 : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR0
  have hL : 0 ≤ log (R / ρ) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hLR : log (R / ρ) ≤ log R := Real.log_le_log (by positivity) (div_le_self hR0.le hρ)
  set T := D.toClosedBall R
  have hfin : T.support.Finite := T.finiteSupport (isCompact_closedBall 0 |R|)
  have hTz : ∀ z, ‖z‖ ≤ R → T z = D z := fun z hz =>
    Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by
      rw [mem_closedBall, dist_zero_right, habs]; exact hz)
  have hterm : ∀ z, 0 ≤ (T z : ℝ) * Real.log (R * ‖z‖⁻¹) := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) |R|
    · have hT : T z = D z := Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz
      rw [hT]
      apply mul_nonneg (by exact_mod_cast hD z)
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · apply Real.log_nonneg
        rw [mem_closedBall, dist_zero_right, habs] at hz
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 hz0)]; linarith
    · have : T z = 0 := by
        by_contra h
        exact hz (Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D h)
      simp [this]
  set S' := S.erase 0
  set W := hfin.toFinset ∪ S'
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset (s := W)]
  swap
  · intro z hz
    simp only [Function.mem_support] at hz
    simp only [W, Finset.coe_union, Finite.coe_toFinset, mem_union, Function.mem_support]
    left; intro h; apply hz
    rw [show (Function.locallyFinsuppWithin.toClosedBall R D) z = T z from rfl, h]; simp
  have h1 : ∑ z ∈ S', (D z : ℝ) * log (R / ρ) ≤ ∑ z ∈ W, (T z : ℝ) * log (R * ‖z‖⁻¹) := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun z _ _ => hterm z))
    refine Finset.sum_le_sum fun z hz => ?_
    have hz0 : z ≠ 0 := Finset.ne_of_mem_erase hz
    have hzS := hS z (Finset.mem_of_mem_erase hz)
    rw [hTz z (hzS.trans hρR)]
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hD z)
    rw [← div_eq_mul_inv]
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hR0.le
      (norm_pos_iff.2 hz0) hzS)
  have h0 : (∑ z ∈ S, (D z : ℝ)) * log (R / ρ) ≤
      ∑ z ∈ S', (D z : ℝ) * log (R / ρ) + (D 0 : ℝ) * log R := by
    rw [Finset.sum_mul]
    by_cases h0S : (0 : ℂ) ∈ S
    · rw [← Finset.add_sum_erase S _ h0S, add_comm]
      have := mul_le_mul_of_nonneg_left hLR (show (0 : ℝ) ≤ D 0 by exact_mod_cast hD 0)
      linarith
    · have hS' : S' = S := Finset.erase_eq_of_notMem h0S
      rw [hS']
      have := mul_nonneg (show (0 : ℝ) ≤ D 0 by exact_mod_cast hD 0) (hL.trans hLR)
      linarith
  linarith


/-- The zeros and poles in `|z| ≤ ρ`, counted with multiplicity, are controlled by the counting
functions at a larger radius: `n · log (R/ρ) ≤ N(R, 0; F) + N(R, ∞; F)`. -/
lemma sum_abs_order_mul_log_le {F : ℂ → ℂ} (hF : Meromorphic F) {ρ R : ℝ} (hρ : 1 ≤ ρ)
    (hρR : ρ ≤ R) (S : Finset ℂ) (d : ℂ → ℤ)
    (hS : ∀ u ∈ S, ‖u‖ ≤ ρ ∧ d u = (meromorphicOrderAt F u).untop₀) :
    (∑ u ∈ S, |(d u : ℝ)|) * log (R / ρ) ≤ logCounting F 0 R + logCounting F ⊤ R := by
  set D := MeromorphicOn.divisor F univ
  have hFU : MeromorphicOn F univ := fun z _ => hF z
  have hd : ∀ u ∈ S, d u = D u := fun u hu => by
    rw [(hS u hu).2, MeromorphicOn.divisor_apply hFU (mem_univ u)]
  have h1 := logCounting_ge_weighted D⁺ (posPart_nonneg _) hρ hρR S (fun u hu => (hS u hu).1)
  have h2 := logCounting_ge_weighted D⁻ (negPart_nonneg _) hρ hρR S (fun u hu => (hS u hu).1)
  rw [logCounting_zero, logCounting_top]
  have heq : ∑ u ∈ S, |(d u : ℝ)| = ∑ u ∈ S, ((D⁺ u : ℤ) : ℝ) + ∑ u ∈ S, ((D⁻ u : ℤ) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hd u hu, Function.locallyFinsuppWithin.posPart_apply,
      Function.locallyFinsuppWithin.negPart_apply]
    rw [← Int.cast_add, posPart_add_negPart, Int.cast_abs]
  rw [heq, add_mul]
  linarith


/-- **Logarithmic derivative lemma, fixed radii.**  For `1 ≤ r < ρ`, with `s = (r + ρ)/2`,
`n` the number of zeros and poles of `F` in `|z| ≤ ρ` and
`A = m(ρ, F) + m(ρ, 1/F)`:
`m(r, F'/F) ≤ 2 log (2n + 1) + 3 + log⁺ (8 s (2K + 5)/(s - r)²)` with
`K = (ρ + s)/(ρ - s) · (A + 2n (log ρ + 2))`. -/
theorem proximity_logDeriv_le_raw {F : ℂ → ℂ} (hF : ∀ z, MeromorphicAt F z)
    (hnz : ∀ z, meromorphicOrderAt F z ≠ ⊤) {r ρ : ℝ} (hr : 1 ≤ r) (hrρ : r < ρ) :
    ∃ n : ℝ, 0 ≤ n ∧ (∀ R, ρ ≤ R → n * log (R / ρ) ≤ logCounting F 0 R + logCounting F ⊤ R) ∧
      circleAverage (fun z => log⁺ ‖logDeriv F z‖) 0 r ≤ 2 * log (2 * n + 1) + 3 +
        log⁺ (8 * ((r + ρ) / 2) * (2 * ((ρ + (r + ρ) / 2) / (ρ - (r + ρ) / 2) *
          (circleAverage (fun z => log⁺ ‖F z‖) 0 ρ + circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ +
            2 * n * (log ρ + 2))) + 5) / ((r + ρ) / 2 - r) ^ 2) := by
  have hρ1 : 1 ≤ ρ := by linarith
  have hr0 : 0 < r := by linarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨S, d, g, hS, hg, hg0, hlog, hld⟩ := exists_factor_disk hF hnz ρ
  set n := ∑ u ∈ S, |(d u : ℝ)| with hn
  have hn0 : 0 ≤ n := Finset.sum_nonneg fun u _ => abs_nonneg _
  refine ⟨n, hn0, fun R hR => sum_abs_order_mul_log_le hF hρ1 hR S d hS, ?_⟩
  set s := (r + ρ) / 2 with hs
  have hrs : r < s := by rw [hs]; linarith
  have hsρ : s < ρ := by rw [hs]; linarith
  set A := circleAverage (fun z => log⁺ ‖F z‖) 0 ρ + circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ
  set K := (ρ + s) / (ρ - s) * (A + 2 * n * (log ρ + 2)) with hK
  have hP := proximity_factor_le hF hρ1 (fun u hu => (hS u hu).1) hg hlog
  have hG0 : 0 ≤ circleAverage (fun z => log⁺ ‖g z‖) 0 ρ +
      circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 ρ :=
    add_nonneg (circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg)
      (circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg)
  have hball : ball (0 : ℂ) s ⊆ closedBall 0 ρ :=
    (ball_subset_ball hsρ.le).trans ball_subset_closedBall
  have hKbound : ∀ w ∈ ball (0 : ℂ) s, |log ‖g w‖| ≤ K := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    have h1 := abs_log_norm_le_poisson hρ0 hg hg0 (hw.trans hsρ)
    refine h1.trans ?_
    have hq : (ρ + ‖w‖) / (ρ - ‖w‖) ≤ (ρ + s) / (ρ - s) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [norm_nonneg w]
    have hq0 : 0 ≤ (ρ + ‖w‖) / (ρ - ‖w‖) := div_nonneg (by positivity) (by linarith)
    calc _ ≤ (ρ + ‖w‖) / (ρ - ‖w‖) * (A + 2 * n * (log ρ + 2)) :=
          mul_le_mul_of_nonneg_left hP hq0
      _ ≤ K := mul_le_mul_of_nonneg_right hq (hG0.trans hP)
  have hgd : DifferentiableOn ℂ g (ball 0 s) := fun z hz =>
    (hg z (hball hz)).differentiableAt.differentiableWithinAt
  set B := 8 * s * (2 * K + 5) / (s - r) ^ 2 with hB
  have hgbound : ∀ z ∈ sphere (0 : ℂ) |r|, ‖logDeriv g z‖ ≤ B := by
    intro z hz
    rw [mem_sphere, dist_zero_right, abs_of_pos hr0] at hz
    exact norm_logDeriv_le_of_abs_log_le hgd (fun z hz => hg0 z (hball hz)) hKbound hr0.le hrs
      hz.le
  -- integrability
  have hmer : MeromorphicOn (logDeriv F) (sphere (0 : ℂ) |r|) := fun z _ =>
    (hF z).deriv.div (hF z)
  have i1 := circleIntegrable_posLog_norm_meromorphicOn hmer
  have hsumM : MeromorphicOn (fun z => ∑ u ∈ S, (d u : ℂ) / (z - u)) (sphere (0 : ℂ) |r|) :=
    by
      intro z _
      apply MeromorphicAt.fun_sum
      intro u _
      exact (MeromorphicAt.const _ z).div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have i2 := circleIntegrable_posLog_norm_meromorphicOn hsumM
  have i3 : CircleIntegrable (fun z => log⁺ ‖∑ u ∈ S, (d u : ℂ) / (z - u)‖ + (log⁺ B + log 2))
      0 r := i2.add (circleIntegrable_const _ _ _)
  have hsph : sphere (0 : ℂ) |r| ⊆ ball 0 ρ := by
    intro z hz; rw [mem_sphere, dist_zero_right, abs_of_pos hr0] at hz
    rw [mem_ball, dist_zero_right]; linarith
  have hld' := codiscreteWithin.mono hsph hld
  have hmono := circleAverage_mono_codiscrete hr0.ne' i1 i3 (by
    filter_upwards [hld', self_mem_codiscreteWithin (sphere (0 : ℂ) |r|)] with z hz hzs
    rw [hz]
    refine (posLog_norm_add_le _ _).trans ?_
    have := posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) (hgbound z hzs)
    linarith)
  rw [circleAverage_fun_add i2 (circleIntegrable_const _ _ _), circleAverage_const] at hmono
  have hsum := proximity_sum_div_sub_le S d hr
  have hl2 : log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  linarith


lemma ld_algebra {X n A q l s r δ R : ℝ} (hX1 : 1 ≤ X) (hn0 : 0 ≤ n) (hn : n ≤ 4 * X)
    (hA0 : 0 ≤ A) (hA : A ≤ 2 * X) (hq0 : 0 ≤ q) (hq : q ≤ 8 * X) (hl0 : 0 ≤ l)
    (hl : l + 2 ≤ 3 * X) (hs0 : 0 ≤ s) (hsR : s ≤ R) (hsr : s - r = δ / 4) (hδ0 : 0 < δ)
    (hR : R ≤ X ^ 2 * δ ^ 2) :
    8 * s * (2 * (q * (A + 2 * n * (l + 2))) + 5) / (s - r) ^ 2 ≤ 2 ^ 16 * X ^ 5 := by
  have hX0 : 0 ≤ X := by linarith
  have h1 : 2 * n * (l + 2) ≤ 2 * (4 * X) * (3 * X) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hl (by linarith) (by positivity)
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hI : A + 2 * n * (l + 2) ≤ 26 * X ^ 2 := by nlinarith
  have hI0 : 0 ≤ A + 2 * n * (l + 2) := by positivity
  have hK : q * (A + 2 * n * (l + 2)) ≤ 8 * X * (26 * X ^ 2) := mul_le_mul hq hI hI0 (by positivity)
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
  have h2K : 2 * (q * (A + 2 * n * (l + 2))) + 5 ≤ 421 * X ^ 3 := by nlinarith
  have hK0 : 0 ≤ 2 * (q * (A + 2 * n * (l + 2))) + 5 := by positivity
  rw [hsr, div_le_iff₀ (by positivity)]
  calc 8 * s * (2 * (q * (A + 2 * n * (l + 2))) + 5) ≤ 8 * R * (421 * X ^ 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsR (by norm_num)) h2K hK0 (by linarith)
    _ ≤ 8 * (X ^ 2 * δ ^ 2) * (421 * X ^ 3) := by gcongr
    _ ≤ 2 ^ 16 * X ^ 5 * (δ / 4) ^ 2 := by
      have : 0 ≤ X ^ 5 * δ ^ 2 := by positivity
      nlinarith

lemma ld_logs {X n B m : ℝ} (hX1 : 1 ≤ X) (hn0 : 0 ≤ n) (hn : n ≤ 4 * X)
    (hB0 : 0 ≤ B) (hB : B ≤ 2 ^ 16 * X ^ 5) (hm : m ≤ 2 * log (2 * n + 1) + 3 + log⁺ B) :
    m ≤ 7 * log X + 24 := by
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ log X := Real.log_nonneg hX1
  have hl2 := Real.log_two_lt_d9
  have hX5 : 1 ≤ X ^ 5 := one_le_pow₀ hX1
  have hlogB : log⁺ B ≤ 16 * log 2 + 5 * log X := by
    have h1 : log⁺ B ≤ log⁺ (2 ^ 16 * X ^ 5) := posLog_le_posLog ((by norm_num : (-1 : ℝ) ≤ 0).trans hB0) hB
    refine h1.trans (le_of_eq ?_)
    rw [posLog_eq_log (by rw [abs_of_pos (by positivity)]; nlinarith),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlogn : log (2 * n + 1) ≤ 4 * log 2 + log X := by
    have h1 : 2 * n + 1 ≤ 2 ^ 4 * X := by nlinarith
    calc log (2 * n + 1) ≤ log (2 ^ 4 * X) := Real.log_le_log (by positivity) h1
      _ = 4 * log 2 + log X := by
        rw [Real.log_mul (by positivity) hX0.ne', Real.log_pow]; push_cast; ring
  linarith


/-- First main theorem: `m(r, 1/F) ≤ T(r, F) + O(1)` for `r ≥ 1`. -/
lemma proximity_inv_le_charT {F : ℂ → ℂ} (hF : Meromorphic F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r →
      circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 r ≤ charT F r + K := by
  refine ⟨max |log ‖F 0‖| |log ‖meromorphicTrailingCoeffAt F 0‖|,
    (abs_nonneg _).trans (le_max_left _ _), fun r hr => ?_⟩
  have h2 := characteristic_sub_characteristic_inv_le (R := r) hF
  have h3 : circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 r ≤ characteristic F⁻¹ ⊤ r := by
    unfold characteristic
    simp only [Pi.add_apply, proximity_top]
    have := logCounting_nonneg (f := F⁻¹) (e := ⊤) hr
    simp only [Pi.inv_apply, norm_inv] at this ⊢
    linarith
  unfold charT
  rw [abs_le] at h2
  linarith [h2.1]


/-- **Logarithmic derivative lemma, clean fixed-radius form.**  There is `C ≥ 0` such that for
`1 ≤ r < R ≤ r + 1`, `m(r, F'/F) ≤ 7 log ((T(R, F) + C + 1) R/(R - r)) + 24`. -/
theorem proximity_logDeriv_le_fixed {F : ℂ → ℂ} (hF : Meromorphic F)
    (hnz : ∀ z, meromorphicOrderAt F z ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r R : ℝ, 1 ≤ r → r < R → R ≤ r + 1 →
      circleAverage (fun z => log⁺ ‖logDeriv F z‖) 0 r ≤
        7 * log ((charT F R + C + 1) * R / (R - r)) + 24 := by
  obtain ⟨K0, hK0⟩ := logCounting_zero_le_charT hF
  obtain ⟨K1, hK1nn, hK1⟩ := proximity_inv_le_charT hF
  refine ⟨|K0| + K1, by positivity, fun r R hr hrR hR1 => ?_⟩
  set C := |K0| + K1 with hC
  have hC0 : 0 ≤ C := by positivity
  set ρ := (r + R) / 2 with hρ
  have hrρ : r < ρ := by rw [hρ]; linarith
  have hρR : ρ ≤ R := by rw [hρ]; linarith
  have hR1' : 1 ≤ R := by linarith
  have hρ1 : 1 ≤ ρ := by linarith
  obtain ⟨n, hn0, hcount, hraw⟩ := proximity_logDeriv_le_raw (fun z => hF z) hnz hr hrρ
  set δ := R - r with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hNtop : logCounting F ⊤ R ≤ charT F R := by
    unfold charT characteristic
    simp only [Pi.add_apply]
    have := proximity_nonneg (f := F) (a := ⊤) R
    simp only [Pi.zero_apply] at this
    linarith
  have hN0 := hK0 R hR1'
  set T := charT F R with hT
  have hT0 : 0 ≤ T := characteristic_nonneg hR1'
  have hmero : MeromorphicOn F univ := fun z _ => hF z
  have hTρ : charT F ρ ≤ T := charT_mono hmero (by linarith) hρR
  set X := (T + C + 1) * R / δ with hX
  have hRδ : R ≤ R / δ := le_div_self (by linarith) hδ0 hδ1
  have hRδX : R / δ ≤ X := by
    rw [hX, mul_div_assoc]; nlinarith [div_nonneg (show (0:ℝ) ≤ R by linarith) hδ0.le]
  have hX1 : 1 ≤ X := by linarith
  have hRX : R ≤ X := hRδ.trans hRδX
  have hiδX : 1 / δ ≤ X := by
    have : 1 / δ ≤ R / δ := div_le_div_of_nonneg_right hR1' hδ0.le
    linarith
  -- counting
  have hN : logCounting F 0 R + logCounting F ⊤ R ≤ 2 * T + C := by
    have : K0 ≤ |K0| := le_abs_self K0
    linarith
  have hlogRρ : δ / (2 * R) ≤ log (R / ρ) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < R / ρ by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [inv_div]; field_simp; rw [hρ, hδ]; ring
  have hn : n ≤ 4 * X := by
    have h1 := hcount R hρR
    have h2 : n * (δ / (2 * R)) ≤ 2 * T + C := by
      have := mul_le_mul_of_nonneg_left hlogRρ hn0
      linarith
    have h3 : 4 * X * (δ / (2 * R)) = 2 * (T + C + 1) := by
      rw [hX]; field_simp; ring
    have hpos : 0 < δ / (2 * R) := by positivity
    by_contra hcon; push_neg at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    linarith
  -- proximity terms
  have hA : circleAverage (fun z => log⁺ ‖F z‖) 0 ρ + circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ
      ≤ 2 * X := by
    have h1 : circleAverage (fun z => log⁺ ‖F z‖) 0 ρ ≤ charT F ρ := by
      unfold charT characteristic
      simp only [Pi.add_apply, proximity_top]
      linarith [logCounting_nonneg (f := F) (e := ⊤) hρ1]
    have h2 := hK1 ρ hρ1
    have : K1 ≤ C := by rw [hC]; linarith [abs_nonneg K0]
    have h3 : 2 * T + C ≤ 2 * X := by
      have : T + C + 1 ≤ X := by
        rw [hX, mul_div_assoc]
        have h1' : 1 ≤ R / δ := le_trans hR1' hRδ
        nlinarith
      linarith
    linarith
  have hA0 : 0 ≤ circleAverage (fun z => log⁺ ‖F z‖) 0 ρ +
      circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ :=
    add_nonneg (circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg)
      (circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg)
  have hsr : (r + ρ) / 2 - r = δ / 4 := by rw [hρ, hδ]; ring
  have hρs : ρ - (r + ρ) / 2 = δ / 4 := by rw [hρ, hδ]; ring
  have hsR : (r + ρ) / 2 ≤ R := by linarith
  have hq0 : 0 ≤ (ρ + (r + ρ) / 2) / (ρ - (r + ρ) / 2) := div_nonneg (by linarith) (by linarith)
  have hqX : (ρ + (r + ρ) / 2) / (ρ - (r + ρ) / 2) ≤ 8 * X := by
    rw [hρs, div_le_iff₀ (by positivity)]
    have : 8 * (R / δ) * (δ / 4) = 2 * R := by field_simp; ring
    nlinarith
  have hlogρ : log ρ + 2 ≤ 3 * X := by
    have := Real.log_le_sub_one_of_pos (show 0 < ρ by linarith)
    linarith
  have hlogρ0 : 0 ≤ log ρ := Real.log_nonneg hρ1
  have hRle : R ≤ X ^ 2 * δ ^ 2 := by
    have h1 : R / δ ^ 2 = (R / δ) * (1 / δ) := by field_simp
    have h2 : R / δ ^ 2 ≤ X ^ 2 := by
      rw [h1, sq]; exact mul_le_mul hRδX hiδX (by positivity) (by linarith)
    rwa [div_le_iff₀ (by positivity)] at h2
  refine ld_logs hX1 hn0 hn ?_ ?_ hraw
  · apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg (by linarith)
    have := mul_nonneg hq0 (show 0 ≤ circleAverage (fun z => log⁺ ‖F z‖) 0 ρ +
      circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ + 2 * n * (log ρ + 2) by positivity)
    linarith
  · exact ld_algebra hX1 hn0 hn hA0 hA hq0 hqX hlogρ0 hlogρ (by linarith) hsR hsr hδ0 hRle

lemma ld_final_bound {m s sR r T M : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsR0 : 0 < sR)
    (hsR : sR ≤ 2 * s) (hT : 1 ≤ T) (hM : 1 ≤ M) (hsM : s ≤ M * T)
    (hm : m ≤ 7 * log (sR * (r + 1 / s) / (r + 1 / s - r)) + 24) :
    m ≤ (45 + 7 * log 4 + 14 * log M) * log (exp 1 + r * T) := by
  have hs0 : 0 < s := by linarith
  have hT0 : 0 < T := by linarith
  have hr0 : 0 < r := by linarith
  have hX : sR * (r + 1 / s) / (r + 1 / s - r) = sR * (r + 1 / s) * s := by
    field_simp; ring
  have h1s : 1 / s ≤ r := by
    rw [div_le_iff₀ hs0]; nlinarith
  have hXle : sR * (r + 1 / s) * s ≤ 4 * (r * s ^ 2) := by
    have : sR * (r + 1 / s) ≤ 2 * s * (2 * r) :=
      mul_le_mul hsR (by linarith) (by positivity) (by linarith)
    nlinarith
  have hlogX : log (sR * (r + 1 / s) * s) ≤ log 4 + log r + 2 * log s := by
    calc log (sR * (r + 1 / s) * s) ≤ log (4 * (r * s ^ 2)) :=
          Real.log_le_log (by positivity) hXle
      _ = log 4 + log r + 2 * log s := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hr0.ne' (by positivity),
            Real.log_pow]; push_cast; ring
  set L := log (exp 1 + r * T) with hL
  have hrT : r * T ≤ exp 1 + r * T := by linarith [exp_pos 1]
  have hL1 : 1 ≤ L := by
    have := Real.log_le_log (exp_pos 1) (show exp 1 ≤ exp 1 + r * T by nlinarith)
    rwa [Real.log_exp] at this
  have hlogr : log r ≤ L := by
    calc log r ≤ log (r * T) := Real.log_le_log hr0 (by nlinarith)
      _ ≤ L := Real.log_le_log (by positivity) hrT
  have hlogs : log s ≤ log M + L := by
    calc log s ≤ log (M * T) := Real.log_le_log hs0 hsM
      _ = log M + log T := Real.log_mul (by positivity) hT0.ne'
      _ ≤ log M + L := by
        have : log T ≤ L :=
          (Real.log_le_log hT0 (by nlinarith)).trans (Real.log_le_log (by positivity) hrT)
        linarith
  have hlM : 0 ≤ log M := Real.log_nonneg hM
  have hl4 : 0 ≤ log 4 := Real.log_nonneg (by norm_num)
  rw [hX] at hm
  have hm' : m ≤ 21 * L + (7 * log 4 + 14 * log M + 24) := by linarith
  have : (7 * log 4 + 14 * log M + 24) ≤ (7 * log 4 + 14 * log M + 24) * L :=
    le_mul_of_one_le_right (by positivity) hL1
  nlinarith

/-- **Borel's growth lemma.**  If `S ≥ 1` is nondecreasing on `[1, ∞)`, then
`S (r + 1/S(r)) ≤ 2 S(r)` for all `r ≥ 1` outside a measurable set of finite measure. -/
theorem borel_growth {S : ℝ → ℝ} (hS1 : ∀ r, 1 ≤ r → 1 ≤ S r)
    (hmono : ∀ r r', 1 ≤ r → r ≤ r' → S r ≤ S r') :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ⊤ ∧
      ∀ r, 1 ≤ r → r ∉ E → S (r + 1 / S r) ≤ 2 * S r := by
  classical
  let A : ℕ → Set ℝ := fun k =>
    {r | 1 ≤ r ∧ (2:ℝ) ^ k ≤ S r ∧ S r < 2 ^ (k + 1) ∧ 2 * S r < S (r + 1 / S r)}
  let a : ℕ → ℝ := fun k => if h : (A k).Nonempty then h.some else 0
  let E : Set ℝ := ⋃ k, Icc (a k - (1/2) ^ k) (a k + (1/2) ^ k)
  have key : ∀ k, ∀ r ∈ A k, ∀ r' ∈ A k, r ≤ r' → r' - r ≤ (1/2) ^ k := by
    intro k r hr r' hr' hle
    obtain ⟨hr1, hrk, hrk1, hrg⟩ := hr
    obtain ⟨hr'1, hr'k, hr'k1, -⟩ := hr'
    have hSpos : 0 < S r := by linarith [hS1 r hr1]
    by_contra hcon
    push_neg at hcon
    have h1 : 1 / S r ≤ (1/2) ^ k := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hrk
    have h2 : S (r + 1 / S r) ≤ S r' :=
      hmono _ _ (by have := one_div_pos.mpr hSpos; linarith) (by linarith)
    have : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    linarith
  refine ⟨E, MeasurableSet.iUnion fun k => measurableSet_Icc, ?_, ?_⟩
  · calc volume E ≤ ∑' k, volume (Icc (a k - (1/2) ^ k) (a k + (1/2) ^ k)) :=
          measure_iUnion_le _
      _ = ∑' k : ℕ, ENNReal.ofReal (2 * (1/2) ^ k) := by
          congr 1; ext k; rw [Real.volume_Icc]; ring_nf
      _ = ENNReal.ofReal (∑' k : ℕ, 2 * (1/2 : ℝ) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            ((summable_geometric_two).mul_left 2)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  · intro r hr hrE
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (hS1 r hr) (show (1:ℝ) < 2 by norm_num)
    have hrA : r ∈ A k := ⟨hr, hk1, hk2, hcon⟩
    have hne : (A k).Nonempty := ⟨r, hrA⟩
    have haA : a k ∈ A k := by
      simp only [a, dif_pos hne]; exact hne.some_mem
    apply hrE
    refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
    · rcases le_total (a k) r with h | h
      · have := pow_pos (show (0:ℝ) < 1/2 by norm_num) k
        linarith
      · linarith [key k r hrA (a k) haA h]
    · rcases le_total (a k) r with h | h
      · linarith [key k (a k) haA r hrA h]
      · have := pow_pos (show (0:ℝ) < 1/2 by norm_num) k
        linarith


/-- **Logarithmic derivative lemma** (External theorem 2.3): for a nonconstant meromorphic `h`
on `ℂ` and `a ∈ ℂ`, `m(r, h'/(h - a)) ≤ C log (e + r T(r, h))` for all large `r` outside a
measurable set of finite linear measure. -/
theorem log_derivative_lemma {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) (a : ℂ) :
    ∃ C : ℝ, ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ⊤ ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, r ∉ E →
      proximity (fun z => deriv h z / (h z - a)) ⊤ r ≤
        C * log (exp 1 + r * charT h r) := by
  have hm := hh.meromorphic
  set F : ℂ → ℂ := fun z => h z - a with hFdef
  have hFm : Meromorphic F := fun z => (hm z).sub (MeromorphicAt.const a z)
  have hnz : ∀ z, meromorphicOrderAt F z ≠ ⊤ := fun z => hh.2 z (mem_univ z) a
  have hlog : (fun z => deriv h z / (h z - a)) = logDeriv F := by
    funext z
    rw [logDeriv_apply, hFdef, deriv_sub_const]
  obtain ⟨C0, hC0, hfix⟩ := proximity_logDeriv_le_fixed hFm hnz
  have hFmero : MeromorphicOn F univ := fun z _ => hFm z
  set S : ℝ → ℝ := fun r => charT F r + C0 + 1 with hS
  have hS1 : ∀ r, 1 ≤ r → 1 ≤ S r := fun r hr => by
    have : 0 ≤ charT F r := characteristic_nonneg hr
    simp only [hS]; linarith
  have hSmono : ∀ r r', 1 ≤ r → r ≤ r' → S r ≤ S r' := fun r r' hr hrr' => by
    have := charT_mono hFmero (by linarith) hrr'
    simp only [hS]; linarith
  obtain ⟨E, hEm, hEv, hE⟩ := borel_growth hS1 hSmono
  obtain ⟨r₀, hr₀⟩ := one_le_charT_eventually hh
  set c := log⁺ ‖a‖ + log 2 with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have := posLog_nonneg (x := ‖a‖)
    linarith
  set M := c + C0 + 2 with hM
  refine ⟨45 + 7 * log 4 + 14 * log M, E, hEm, hEv, max r₀ 1, fun r hr hrE => ?_⟩
  have hr1 : 1 ≤ r := le_of_max_le_right hr
  have hT1 : 1 ≤ charT h r := hr₀ r (le_of_max_le_left hr)
  have hsr := hS1 r hr1
  have hspos : 0 < S r := by linarith
  have hδ : 0 < 1 / S r := one_div_pos.mpr hspos
  have hδ1 : 1 / S r ≤ 1 := by rw [div_le_one hspos]; exact hsr
  have hfix' := hfix r (r + 1 / S r) hr1 (by linarith) (by linarith)
  have hgrow := hE r hr1 hrE
  have hshift : charT F r ≤ charT h r + c := by
    have := abs_characteristic_sub_characteristic_shift_le (a₀ := a) (r := r) hm
    rw [abs_le] at this
    unfold charT; rw [hFdef]; linarith [this.1]
  have hsM : S r ≤ M * charT h r := by
    have h1 : S r ≤ charT h r + c + C0 + 1 := by simp only [hS]; linarith
    have h2 : charT h r + c + C0 + 1 ≤ M * charT h r := by
      rw [hM]; nlinarith
    linarith
  rw [hlog, proximity_top]
  exact ld_final_bound hr1 hsr (by linarith [hS1 (r + 1 / S r) (by linarith)]) hgrow hT1
    (by rw [hM]; linarith) hsM hfix'

end ThreeIM
