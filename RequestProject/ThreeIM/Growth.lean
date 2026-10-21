module

public import RequestProject.ThreeIM.Basic

/-!
# Growth from a vertical progression (Lemma 4.8, first part)

Using Mathlib's first main theorem of Nevanlinna theory we show that a meromorphic function
taking a fixed finite value along a vertical arithmetic progression `z₀ + iℓk` has
characteristic function of at least linear growth.
-/

@[expose] public section

open Filter Set Topology Real Function Metric

namespace ThreeIM

lemma logCounting_ge_sum (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r)
    (S : Finset ℂ) (hS : ∀ z ∈ S, 1 ≤ D z ∧ ‖z‖ ≤ r ∧ z ≠ 0) :
    ∑ z ∈ S, Real.log (r * ‖z‖⁻¹) ≤ Function.locallyFinsuppWithin.logCounting D r := by
  have hr0 : 0 < r := by linarith
  have habs : |r| = r := abs_of_pos hr0
  set T := D.toClosedBall r
  have hfin : T.support.Finite := T.finiteSupport (isCompact_closedBall 0 |r|)
  have hterm : ∀ z, 0 ≤ (T z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) |r|
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
  have hsub : (S : Set ℂ) ⊆ hfin.toFinset := by
    intro z hz
    obtain ⟨h1, h2, _⟩ := hS z hz
    have hzb : z ∈ closedBall (0 : ℂ) |r| := by
      rw [mem_closedBall, dist_zero_right, habs]; exact h2
    simp only [Finite.coe_toFinset, Function.mem_support]
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hzb]; omega
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · have h0 : 0 ≤ (D 0 : ℝ) * Real.log r :=
      mul_nonneg (by exact_mod_cast hD 0) (Real.log_nonneg hr)
    have : ∑ z ∈ S, Real.log (r * ‖z‖⁻¹) ≤ ∑ z ∈ S, (T z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨h1, h2, h3⟩ := hS z hz
      have hzb : z ∈ closedBall (0 : ℂ) |r| := by
        rw [mem_closedBall, dist_zero_right, habs]; exact h2
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hzb]
      have hl : 0 ≤ Real.log (r * ‖z‖⁻¹) := by
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 h3)]; linarith
      have : (1 : ℝ) ≤ D z := by exact_mod_cast h1
      nlinarith
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => (T z : ℝ) *
      Real.log (r * ‖z‖⁻¹)) (Finset.coe_subset.1 hsub)
      (fun z _ _ => hterm z)
    linarith
  · intro z hz
    simp only [Finite.coe_toFinset, Function.mem_support] at hz ⊢
    intro h; apply hz; simp [T] at h; simp [h]

lemma norm_progression_le (z₀ : ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℤ) :
    ‖z₀ + Complex.I * ℓ * k‖ ≤ ‖z₀‖ + ℓ * |(k : ℝ)| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  congr 1
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
    Real.norm_of_nonneg hℓ.le, one_mul]

lemma progression_injective (z₀ : ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.Injective (fun k : ℤ => z₀ + Complex.I * ℓ * k) := by
  intro k m hkm
  simp only [add_right_inj] at hkm
  have hne : Complex.I * (ℓ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hℓ.ne')
  have := mul_left_cancel₀ hne hkm
  exact_mod_cast this

/-- A divisor that is `≥ 1` along a vertical progression has logarithmic counting function of
at least linear growth. -/
lemma logCounting_progression (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) (z₀ : ℂ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hpts : ∀ k : ℤ, 1 ≤ D (z₀ + Complex.I * ℓ * k)) :
    ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ Function.locallyFinsuppWithin.logCounting D r := by
  set e := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  have he1 : 1 ≤ e := by rw [he]; exact Real.one_le_exp zero_le_one
  refine ⟨1 / (e * ℓ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (e * (2 * ‖z₀‖ + 4 * ℓ) + 1)] with r hr
  have hr1 : 1 ≤ r := by
    have : 0 ≤ e * (2 * ‖z₀‖ + 4 * ℓ) := by positivity
    linarith
  have hr0 : 0 < r := by linarith
  set K : ℕ := ⌊(r / e - ‖z₀‖) / ℓ⌋₊ with hK
  set zk : ℤ → ℂ := fun k => z₀ + Complex.I * ℓ * k with hzk
  set S := ((Finset.Icc (-(K : ℤ)) K).image zk).erase 0 with hS
  have hbound : ∀ k ∈ Finset.Icc (-(K : ℤ)) K, ‖zk k‖ ≤ r / e := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk' : |(k : ℝ)| ≤ K := by
      rw [abs_le]; constructor <;> [have := hk.1; have := hk.2] <;> exact_mod_cast (by omega)
    have hKle : (K : ℝ) ≤ (r / e - ‖z₀‖) / ℓ := by
      apply Nat.floor_le
      apply div_nonneg _ hℓ.le
      rw [sub_nonneg, le_div_iff₀ he0]; nlinarith [norm_nonneg z₀]
    have := norm_progression_le z₀ hℓ k
    have h2 : ℓ * |(k : ℝ)| ≤ r / e - ‖z₀‖ := by
      calc ℓ * |(k : ℝ)| ≤ ℓ * K := by gcongr
        _ ≤ ℓ * ((r / e - ‖z₀‖) / ℓ) := by gcongr
        _ = r / e - ‖z₀‖ := by field_simp
    simp only [hzk]; linarith
  have hsum := logCounting_ge_sum D hD hr1 S (by
    intro z hz
    rw [hS, Finset.mem_erase, Finset.mem_image] at hz
    obtain ⟨hz0, k, hk, rfl⟩ := hz
    refine ⟨hpts k, ?_, hz0⟩
    have := hbound k hk
    have : r / e ≤ r := div_le_self hr0.le he1
    linarith)
  have hterm : ∀ z ∈ S, (1 : ℝ) ≤ Real.log (r * ‖z‖⁻¹) := by
    intro z hz
    rw [hS, Finset.mem_erase, Finset.mem_image] at hz
    obtain ⟨hz0, k, hk, rfl⟩ := hz
    have hb := hbound k hk
    have hpos : 0 < ‖zk k‖ := norm_pos_iff.2 hz0
    rw [Real.le_log_iff_exp_le (by positivity), ← he, ← div_eq_mul_inv, le_div_iff₀ hpos]
    rw [le_div_iff₀ he0] at hb; linarith
  have hcard : 2 * (K : ℝ) ≤ S.card := by
    have h1 := Finset.pred_card_le_card_erase (s := (Finset.Icc (-(K : ℤ)) K).image zk) (a := 0)
    rw [Finset.card_image_of_injective _ (progression_injective z₀ hℓ), Int.card_Icc] at h1
    have : (↑K + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
    rw [this] at h1
    have : 2 * K ≤ S.card := by rw [hS]; omega
    exact_mod_cast this
  have hsum2 : (S.card : ℝ) ≤ ∑ z ∈ S, Real.log (r * ‖z‖⁻¹) := by
    simpa using Finset.card_nsmul_le_sum S _ 1 hterm
  have hKge : (r / e - ‖z₀‖) / ℓ - 1 ≤ K := (Nat.sub_one_lt_floor _).le
  have : 1 / (e * ℓ) * r ≤ 2 * ((r / e - ‖z₀‖) / ℓ - 1) := by
    rw [show 1 / (e * ℓ) * r = (r / e) / ℓ by field_simp]
    rw [show 2 * ((r / e - ‖z₀‖) / ℓ - 1) = (2 * (r / e) - 2 * ‖z₀‖ - 2 * ℓ) / ℓ by
      field_simp]
    apply div_le_div_of_nonneg_right _ hℓ.le
    have : e * (2 * ‖z₀‖ + 4 * ℓ) ≤ r := by linarith
    have : 2 * ‖z₀‖ + 4 * ℓ ≤ r / e := by rw [le_div_iff₀ he0]; linarith
    linarith
  linarith

/-- **Lemma 4.8** (first part, growth from a vertical progression).  If a nonconstant
meromorphic `h` takes a fixed finite value `a` at every point `z₀ + iℓk`, `k ∈ ℤ`, `ℓ > 0`, then
`T(r, h) ≥ c r` for some `c > 0` and all large `r`. -/
theorem linear_growth_of_progression {h : ℂ → ℂ} (hh : MeromorphicOn h univ) {a z₀ : ℂ}
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hpts : ∀ k : ℤ, 0 < mult h (a : Sphere) (z₀ + Complex.I * ℓ * k)) :
    ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ charT h r := by
  have hm : Meromorphic h := fun z => hh z (mem_univ z)
  set F : ℂ → ℂ := fun z => h z - a with hF
  have hFm : Meromorphic F := fun z => (hm z).sub (MeromorphicAt.const a z)
  set D := (MeromorphicOn.divisor F univ)⁺ with hD
  have hD0 : 0 ≤ D := by rw [hD]; exact posPart_nonneg _
  have hDk : ∀ k : ℤ, 1 ≤ D (z₀ + Complex.I * ℓ * k) := by
    intro k
    have := hpts k
    rw [mult_coe] at this
    rw [hD, Function.locallyFinsuppWithin.posPart_apply,
      MeromorphicOn.divisor_apply hFm.meromorphicOn (mem_univ _)]
    have h1 : 1 ≤ (meromorphicOrderAt F (z₀ + Complex.I * ℓ * k)).untop₀ := by
      simp only [hF]; omega
    exact h1.trans (le_posPart _)
  obtain ⟨c, hc, hev⟩ := logCounting_progression D hD0 z₀ hℓ hDk
  set C := (Real.posLog ‖a‖ + Real.log 2) + max |Real.log ‖F 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt F 0‖| with hC
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 * C / c)] with r hr hrC
  have h1 : |ValueDistribution.characteristic h ⊤ r - ValueDistribution.characteristic F ⊤ r| ≤
      Real.posLog ‖a‖ + Real.log 2 :=
    ValueDistribution.abs_characteristic_sub_characteristic_shift_le (a₀ := a) (r := r) hm
  have h2 := ValueDistribution.characteristic_sub_characteristic_inv_le (R := r) hFm
  have h3 : ValueDistribution.logCounting F⁻¹ ⊤ r ≤ ValueDistribution.characteristic F⁻¹ ⊤ r := by
    unfold ValueDistribution.characteristic
    simp only [Pi.add_apply]
    have := ValueDistribution.proximity_nonneg (f := F⁻¹) (a := ⊤) r
    simp only [Pi.zero_apply] at this
    linarith
  rw [ValueDistribution.logCounting_inv, ValueDistribution.logCounting_zero] at h3
  have hCr : 2 * C ≤ c * r := by rwa [div_le_iff₀' hc] at hrC
  unfold charT
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.1]

/-- **Lemma 4.8** (second part).  If `T(r) ≥ c r` for all large `r`, with `c > 0`, then
`L(r) = log(e + r T(r)) = o(T(r))`. -/
theorem log_isLittleO_of_linear_growth {T : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hT : ∀ᶠ r in atTop, c * r ≤ T r) :
    Tendsto (fun r => Real.log (Real.exp 1 + r * T r) / T r) atTop (𝓝 0) := by
  -- `log(e + rT) ≤ log(e + T²/c) ≤ 1 + 2 log(T) + log(1 + 1/c)` for large `r`
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono' atTop hT (tendsto_id.const_mul_atTop hc)
  have hlog : Tendsto (fun x : ℝ => (2 + Real.log (1 + c⁻¹) + 2 * Real.log x) / x)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (2 + Real.log (1 + c⁻¹)) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have := h1.add (h2.const_mul 2)
    simp only [add_zero, mul_zero] at this
    refine this.congr' (Eventually.of_forall fun x => ?_)
    ring
  have hlim := hlog.comp hTtop
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hTtop.eventually_ge_atTop 1, eventually_ge_atTop 0] with r hr hr0
    refine div_nonneg (Real.log_nonneg ?_) (by linarith)
    have : 0 ≤ r * T r := mul_nonneg hr0 (by linarith)
    linarith [Real.add_one_le_exp 1]
  · filter_upwards [hT, hTtop.eventually_ge_atTop 1, eventually_ge_atTop 0] with r hr hr1 hr0
    simp only [Function.comp]
    apply div_le_div_of_nonneg_right _ (by linarith)
    -- `e + r T ≤ e (1 + c⁻¹) T²`
    have hrT : r ≤ T r / c := by rw [le_div_iff₀ hc]; linarith
    have hT0 : 0 < T r := by linarith
    have hbound : Real.exp 1 + r * T r ≤ Real.exp 2 * (1 + c⁻¹) * T r ^ 2 := by
      have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
      have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have h1 : r * T r ≤ c⁻¹ * T r ^ 2 := by
        calc r * T r ≤ T r / c * T r := mul_le_mul_of_nonneg_right hrT hT0.le
          _ = c⁻¹ * T r ^ 2 := by ring
      have hT2 : 1 ≤ T r ^ 2 := by nlinarith
      have hc' : 0 < c⁻¹ := inv_pos.2 hc
      have a1 : Real.exp 1 ≤ Real.exp 2 * T r ^ 2 :=
        he.trans (le_mul_of_one_le_right (Real.exp_pos 2).le hT2)
      have he2 : 1 ≤ Real.exp 2 := by linarith
      have a2 : c⁻¹ * T r ^ 2 ≤ Real.exp 2 * (c⁻¹ * T r ^ 2) :=
        le_mul_of_one_le_left (by positivity) he2
      have : Real.exp 2 * (1 + c⁻¹) * T r ^ 2 =
          Real.exp 2 * T r ^ 2 + Real.exp 2 * (c⁻¹ * T r ^ 2) := by ring
      linarith
    have hpos : 0 < Real.exp 1 + r * T r := by
      have : 0 ≤ r * T r := mul_nonneg hr0 hT0.le
      linarith [Real.exp_pos 1]
    calc Real.log (Real.exp 1 + r * T r)
        ≤ Real.log (Real.exp 2 * (1 + c⁻¹) * T r ^ 2) := Real.log_le_log hpos hbound
      _ = 2 + Real.log (1 + c⁻¹) + 2 * Real.log (T r) := by
        have h1 : (0 : ℝ) < 1 + c⁻¹ := by positivity
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_exp, Real.log_pow]
        push_cast; ring

end ThreeIM
