module

public import RequestProject.ThreeIM.ExponentialData
public import RequestProject.ThreeIM.NevanlinnaAux
public import RequestProject.ThreeIM.External

/-!
# Growth of exponential pairs (Lemma 8.3)

Every exponential pair satisfies `T(r) = O(r)`.  As in the paper, the reduced counting function
of each finite shared value is split into the shared points with `max(m, n) ≤ 10`, which lie
over finitely many values `m/n` of `e^{2t}`, and those with `max(m, n) ≥ 11`, for which
`m + n ≥ 12` (since `min(m, n) = 1`, Lemma 8.2).  The three-value second main theorem
(External theorem 2.4) then gives `T(r) ≤ (1/2) T(r) + O(r) + O(log(e + r T(r)))` outside a set
of finite linear measure, and monotonicity of `T` removes the exceptional set.
-/

@[expose] public section

open Filter Set Topology Metric

namespace ThreeIM

/-- The reduced counting function of a fiber is the logarithmic counting function of the
indicator divisor of the fiber. -/
lemma reducedCounting_eq_logCounting {f : ℂ → ℂ} {b : Sphere} (D : Function.locallyFinsupp ℂ ℤ)
    (hD : ∀ z, D z = if 0 < mult f b z then 1 else 0) {r : ℝ} (hr : 0 ≤ r) :
    reducedCounting f b r = Function.locallyFinsuppWithin.logCounting D r := by
  unfold reducedCounting Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  · rw [finsum_mem_def]
    congr 1
    funext z
    by_cases hz : z ∈ closedBall (0:ℂ) |r|
    · rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ hz, hD z]
      rw [mem_closedBall, dist_zero_right, abs_of_nonneg hr] at hz
      by_cases hm : 0 < mult f b z
      · simp [hm, hz, indicator_of_mem]
      · simp [hm]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
      rw [mem_closedBall, dist_zero_right, abs_of_nonneg hr] at hz
      simp [hz]
  · rw [hD 0]; split_ifs <;> simp

/-- First main theorem: `N(r, c; h) ≤ T(r, h) + O(1)`. -/
lemma logCounting_fiber_le {h : ℂ → ℂ} (hh : MeromorphicOn h univ) (c : ℂ) :
    ∃ C : ℝ, ∀ r : ℝ, Function.locallyFinsuppWithin.logCounting
      (MeromorphicOn.divisor (fun w => h w - c) univ)⁺ r ≤ charT h r + C := by
  have hm : Meromorphic h := fun z => hh z (mem_univ z)
  set F : ℂ → ℂ := fun z => h z - c with hF
  have hFm : Meromorphic F := fun z => (hm z).sub (MeromorphicAt.const c z)
  refine ⟨(Real.posLog ‖c‖ + Real.log 2) + max |Real.log ‖F 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt F 0‖|, fun r => ?_⟩
  have h1 : |ValueDistribution.characteristic h ⊤ r - ValueDistribution.characteristic F ⊤ r| ≤
      Real.posLog ‖c‖ + Real.log 2 :=
    ValueDistribution.abs_characteristic_sub_characteristic_shift_le (a₀ := c) (r := r) hm
  have h2 := ValueDistribution.characteristic_sub_characteristic_inv_le (R := r) hFm
  have h3 : ValueDistribution.logCounting F⁻¹ ⊤ r ≤ ValueDistribution.characteristic F⁻¹ ⊤ r := by
    unfold ValueDistribution.characteristic
    simp only [Pi.add_apply]
    have := ValueDistribution.proximity_nonneg (f := F⁻¹) (a := ⊤) r
    simp only [Pi.zero_apply] at this
    linarith
  rw [ValueDistribution.logCounting_inv, ValueDistribution.logCounting_zero] at h3
  unfold charT
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.1]

/-- `T(r, e^{2t}) ≤ 2r`. -/
lemma charT_exp_two_mul_le {r : ℝ} (hr : 0 ≤ r) :
    charT (fun t => Complex.exp (2 * t)) r ≤ 2 * r := by
  have han : AnalyticOnNhd ℂ (fun t : ℂ => Complex.exp (2 * t)) univ := fun x _ => by fun_prop
  unfold charT ValueDistribution.characteristic
  simp only [Pi.add_apply]
  have hlc : ValueDistribution.logCounting (fun t => Complex.exp (2 * t)) ⊤ r = 0 := by
    rw [ValueDistribution.logCounting_top]
    have h0 : (MeromorphicOn.divisor (fun t => Complex.exp (2 * t)) univ)⁻ = 0 :=
      negPart_eq_zero.2 (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han)
    rw [h0, map_zero]; rfl
  rw [hlc, add_zero, ValueDistribution.proximity_top]
  apply Real.circleAverage_mono_on_of_le_circle
  · apply circleIntegrable_posLog_norm_meromorphicOn
    intro z _
    exact (han z (mem_univ z)).meromorphicAt
  · intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_nonneg hr] at hz
    rw [Complex.norm_exp, Real.posLog_apply, Real.log_exp]
    apply max_le (by positivity)
    have : (2 * z).re = 2 * z.re := by simp
    rw [this, ← hz]
    linarith [Complex.re_le_norm z]

/-- The value of the positive part of the divisor of `h - c` is the local degree over `c`. -/
lemma divisor_posPart_apply {h : ℂ → ℂ} (hh : MeromorphicOn h univ) (c : ℂ) (z : ℂ) :
    (MeromorphicOn.divisor (fun w => h w - c) univ)⁺ z = (mult h (c : Sphere) z : ℤ) := by
  have hm : MeromorphicOn (fun w => h w - c) univ := fun w _ =>
    (hh w (mem_univ w)).sub (MeromorphicAt.const c w)
  rw [Function.locallyFinsuppWithin.posPart_apply, MeromorphicOn.divisor_apply hm (mem_univ z),
    mult_coe, Int.toNat_eq_max]
  rfl

/-- Absorption of the logarithmic error term. -/
lemma absorb_log {T r α β γ : ℝ} (hr : 1 ≤ r) (hT : 0 ≤ T) (hγ : 0 ≤ γ)
    (h : T ≤ α * r + β + T / 2 + γ * Real.log (Real.exp 1 + r * T)) :
    T ≤ 4 * (|α| + |β| + 2 * γ + 1 + γ * Real.log (4 * γ + 1)) * r := by
  set e := Real.exp 1
  have he : 2 < e := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; norm_num at this; linarith
  have he3 : e < 3 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  set M := 4 * γ + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  -- `log (e + rT) ≤ log (e + r) + log (e + T)`
  have hsplit : Real.log (e + r * T) ≤ Real.log (e + r) + Real.log (e + T) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    apply Real.log_le_log (by nlinarith)
    nlinarith
  have hlr : Real.log (e + r) ≤ 2 * r := by
    have := Real.log_le_sub_one_of_pos (show 0 < (e + r) / e by positivity)
    rw [Real.log_div (by linarith) (by linarith), Real.log_exp] at this
    have h2 : (e + r) / e ≤ 1 + r := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlT : γ * Real.log (e + T) ≤ T / 4 + 1 + γ * Real.log M := by
    have := Real.log_le_sub_one_of_pos (show 0 < (e + T) / M by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at this
    have h1 : γ * Real.log (e + T) ≤ γ * ((e + T) / M) + γ * Real.log M := by
      have := mul_le_mul_of_nonneg_left this hγ
      nlinarith
    have h2 : γ * ((e + T) / M) ≤ T / 4 + 1 := by
      rw [mul_div_assoc', div_le_iff₀ hM0, hM]
      nlinarith
    linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have h3 : γ * Real.log (e + r * T) ≤ 2 * γ * r + T / 4 + 1 + γ * Real.log M := by
    have := mul_le_mul_of_nonneg_left hsplit hγ
    nlinarith
  have h4 : T / 4 ≤ α * r + β + 2 * γ * r + 1 + γ * Real.log M := by linarith
  have hα : α * r ≤ |α| * r := mul_le_mul_of_nonneg_right (le_abs_self α) (by linarith)
  have hβ : β ≤ |β| * r := (le_abs_self β).trans (le_mul_of_one_le_right (abs_nonneg _) hr)
  have h1r : (1 : ℝ) ≤ 1 * r := by linarith
  have hγr : γ * Real.log M ≤ γ * Real.log M * r :=
    le_mul_of_one_le_right (mul_nonneg hγ hlogM) hr
  nlinarith

lemma locallyFinsupp_sum_apply (s : Finset ℂ) (Z : ℂ → Function.locallyFinsupp ℂ ℤ) (z : ℂ) :
    (∑ c ∈ s, Z c) z = ∑ c ∈ s, Z c z := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, ih,
      Finset.sum_insert ha]

/-- The finitely many values `m/n`, `1 ≤ m, n ≤ 10`. -/
noncomputable def smallRatios : Finset ℂ :=
  (Finset.Icc 1 10 ×ˢ Finset.Icc 1 10).image (fun p : ℕ × ℕ => (p.1 : ℂ) / p.2)

/-- The counting step of Lemma 8.3 for one shared value: `N̄(r, a_j) ≤ O(r) + (N(r,a_j;f) +
N(r,a_j;g))/12 ≤ O(r) + (T(r,f) + T(r,g))/12`. -/
lemma ExponentialPair.reducedCounting_le {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (j : Fin 3) :
    ∃ A B : ℝ, ∀ r ≥ 1, reducedCounting f (a j : Sphere) r ≤
      A * r + B + (charT f r + charT g r) / 12 := by
  have hP := h.pair
  have hfm := hP.nonconst_f.1
  have hgm := hP.nonconst_g.1
  have hem : MeromorphicOn (fun t : ℂ => Complex.exp (2 * t)) univ := fun x _ =>
    (show AnalyticAt ℂ (fun t : ℂ => Complex.exp (2 * t)) x by fun_prop).meromorphicAt
  set Df := (MeromorphicOn.divisor (fun w => f w - a j) univ)⁺ with hDf
  set Dg := (MeromorphicOn.divisor (fun w => g w - a j) univ)⁺ with hDg
  set Z : ℂ → Function.locallyFinsupp ℂ ℤ := fun c =>
    (MeromorphicOn.divisor (fun t => Complex.exp (2 * t) - c) univ)⁺ with hZ
  set D := Df ⊓ Dg with hD
  have hDf' : ∀ z, Df z = (mult f (a j : Sphere) z : ℤ) := divisor_posPart_apply hfm (a j)
  have hDg' : ∀ z, Dg z = (mult g (a j : Sphere) z : ℤ) := divisor_posPart_apply hgm (a j)
  have hZ0 : ∀ c z, 0 ≤ Z c z := fun c z => posPart_nonneg _
  -- the local degrees at a point
  have hloc : ∀ z, 0 < mult f (a j : Sphere) z →
      0 < mult g (a j : Sphere) z ∧ min (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) = 1 ∧
      Complex.exp (2 * z) = (mult f (a j : Sphere) z : ℂ) / (mult g (a j : Sphere) z) :=
    fun z hz => ⟨(hP.im j z (mem_univ z)).1 hz, (h.shared_point hz).1, (h.shared_point hz).2⟩
  have hDapp : ∀ z, D z = if 0 < mult f (a j : Sphere) z then 1 else 0 := by
    intro z
    rw [hD, Function.locallyFinsuppWithin.min_apply, hDf', hDg']
    split_ifs with hz
    · obtain ⟨-, hmin, -⟩ := hloc z hz
      rw [← Nat.cast_min, hmin]; rfl
    · have : mult f (a j : Sphere) z = 0 := by omega
      rw [this]; simp
  -- the pointwise divisor inequality
  have hpt : 12 • D ≤ 12 • (∑ c ∈ smallRatios, Z c) + Df + Dg := by
    intro z
    have hL : (12 • D) z = 12 * D z := by
      rw [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]; norm_num
    have hR : (12 • (∑ c ∈ smallRatios, Z c) + Df + Dg) z =
        12 * (∑ c ∈ smallRatios, Z c z) + Df z + Dg z := by
      rw [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_add,
        Pi.add_apply, Pi.add_apply, Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
        locallyFinsupp_sum_apply, nsmul_eq_mul]; norm_num
    rw [hL, hR, hDapp z, hDf', hDg']
    have hsum0 : 0 ≤ ∑ c ∈ smallRatios, Z c z := Finset.sum_nonneg fun c _ => hZ0 c z
    split_ifs with hz
    · obtain ⟨hg, hmin, hexp⟩ := hloc z hz
      by_cases hsmall : mult f (a j : Sphere) z ≤ 10 ∧ mult g (a j : Sphere) z ≤ 10
      · set c : ℂ := (mult f (a j : Sphere) z : ℂ) / (mult g (a j : Sphere) z) with hc
        have hcmem : c ∈ smallRatios := by
          unfold smallRatios
          rw [Finset.mem_image]
          exact ⟨(mult f (a j : Sphere) z, mult g (a j : Sphere) z),
            Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hz, hsmall.1⟩,
              Finset.mem_Icc.2 ⟨hg, hsmall.2⟩⟩, rfl⟩
        have hZc : 1 ≤ Z c z := by
          have han : AnalyticAt ℂ (fun t : ℂ => Complex.exp (2 * t)) z := by fun_prop
          have hd : deriv (fun t : ℂ => Complex.exp (2 * t)) z ≠ 0 := by
            have hd : HasDerivAt (fun t : ℂ => Complex.exp (2 * t))
                (Complex.exp (2 * z) * (2 * 1)) z :=
              (Complex.hasDerivAt_exp (2 * z)).comp z ((hasDerivAt_id z).const_mul 2)
            rw [hd.deriv]; exact mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)
          have h1 := han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
          have hsa : AnalyticAt ℂ (fun t : ℂ => Complex.exp (2 * t) - c) z :=
            han.sub analyticAt_const
          have hord : meromorphicOrderAt (fun t : ℂ => Complex.exp (2 * t) - c) z = 1 := by
            have hfun : (fun t : ℂ => Complex.exp (2 * t) - c) =
                (fun t : ℂ => Complex.exp (2 * t) - Complex.exp (2 * z)) := by
              rw [hexp]
            rw [hsa.meromorphicOrderAt_eq, hfun, h1]; rfl
          have hm : MeromorphicOn (fun t : ℂ => Complex.exp (2 * t) - c) univ := fun w _ =>
            (hem w (mem_univ w)).sub (MeromorphicAt.const c w)
          simp only [hZ, Function.locallyFinsuppWithin.posPart_apply,
            MeromorphicOn.divisor_apply hm (mem_univ z), hord]
          rw [show (1 : WithTop ℤ) = ((1:ℤ) : WithTop ℤ) from rfl, WithTop.untop₀_coe]
          simp
        have := Finset.single_le_sum (f := fun c => Z c z) (fun c _ => hZ0 c z) hcmem
        have : (0:ℤ) ≤ mult f (a j : Sphere) z := Int.natCast_nonneg _
        have : (0:ℤ) ≤ mult g (a j : Sphere) z := Int.natCast_nonneg _
        linarith
      · have hbig : 12 ≤ mult f (a j : Sphere) z + mult g (a j : Sphere) z := by omega
        have : (12:ℤ) ≤ mult f (a j : Sphere) z + mult g (a j : Sphere) z := by exact_mod_cast hbig
        linarith
    · have : (0:ℤ) ≤ mult f (a j : Sphere) z := Int.natCast_nonneg _
      have : (0:ℤ) ≤ mult g (a j : Sphere) z := Int.natCast_nonneg _
      linarith
  -- constants
  choose Cz hCz using fun c => logCounting_fiber_le hem c
  obtain ⟨Cf, hCf⟩ := logCounting_fiber_le hfm (a j)
  obtain ⟨Cg, hCg⟩ := logCounting_fiber_le hgm (a j)
  refine ⟨2 * smallRatios.card, ∑ c ∈ smallRatios, Cz c + (Cf + Cg) / 12, fun r hr => ?_⟩
  have hred := reducedCounting_eq_logCounting (f := f) (b := (a j : Sphere)) D hDapp
    (by linarith : (0:ℝ) ≤ r)
  have hle := Function.locallyFinsuppWithin.logCounting_le hpt hr
  simp only [map_add, map_nsmul, map_sum, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply] at hle
  have hZb : ∀ c, Function.locallyFinsuppWithin.logCounting (Z c) r ≤ 2 * r + Cz c := fun c =>
    (hCz c r).trans (by linarith [charT_exp_two_mul_le (by linarith : (0:ℝ) ≤ r)])
  have hsumZ : ∑ c ∈ smallRatios, Function.locallyFinsuppWithin.logCounting (Z c) r ≤
      ∑ c ∈ smallRatios, (2 * r + Cz c) := Finset.sum_le_sum fun c _ => hZb c
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsumZ
  have h1 : Function.locallyFinsuppWithin.logCounting Df r ≤ charT f r + Cf := hCf r
  have h2 : Function.locallyFinsuppWithin.logCounting Dg r ≤ charT g r + Cg := hCg r
  rw [hred]
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  linarith

/-- **Lemma 8.3** (exponential growth).  Every exponential pair satisfies `T(r) = O(r)`. -/
theorem ExponentialPair.linear_growth {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) :
    ∃ K : ℝ, ∀ᶠ r in atTop, charT f r ≤ K * r ∧ charT g r ≤ K * r := by
  have hP := h.pair
  have hfm := hP.nonconst_f
  have hgm := hP.nonconst_g
  choose A B hAB using fun j => h.reducedCounting_le j
  have hred_g : ∀ j r, reducedCounting g (a j : Sphere) r = reducedCounting f (a j : Sphere) r := by
    intro j r
    unfold reducedCounting
    have hset : {z : ℂ | ‖z‖ ≤ r ∧ 0 < mult g (a j : Sphere) z} =
        {z : ℂ | ‖z‖ ≤ r ∧ 0 < mult f (a j : Sphere) z} := by
      ext z; simp only [mem_setOf_eq, (hP.im j z (mem_univ z)).symm]
    rw [hset]
    simp only [(hP.im j 0 (mem_univ 0)).symm]
  set b : Fin 3 → Sphere := fun j => (a j : Sphere) with hbdef
  have hb : Function.Injective b := fun i j hij => hP.injective (WithTop.coe_injective hij)
  obtain ⟨Cf, hSf⟩ := ext_second_main_theorem hfm (le_refl 3) b hb
  obtain ⟨Cg, hSg⟩ := ext_second_main_theorem hgm (le_refl 3) b hb
  set α := ∑ j, A j
  set β := ∑ j, B j
  set γ := max |Cf| |Cg|
  have hγ : 0 ≤ γ := le_max_of_le_left (abs_nonneg _)
  set K₀ := 4 * (|α| + |β| + 2 * γ + 1 + γ * Real.log (4 * γ + 1))
  have hmain : OutsideFiniteMeasure fun r => pairT f g r ≤ K₀ * r := by
    refine (hSf.and hSg).mono fun r hr1 ⟨h1, h2⟩ => ?_
    have hsum : ∀ F : ℂ → ℂ, (∀ j, reducedCounting F (a j : Sphere) r =
        reducedCounting f (a j : Sphere) r) →
        ∑ j, reducedCounting F (b j) r ≤ α * r + β + (charT f r + charT g r) / 4 := by
      intro F hF
      calc ∑ j, reducedCounting F (b j) r
          = ∑ j, reducedCounting f (a j : Sphere) r := Finset.sum_congr rfl fun j _ => hF j
        _ ≤ ∑ j, (A j * r + B j + (charT f r + charT g r) / 12) :=
          Finset.sum_le_sum fun j _ => hAB j r hr1
        _ = α * r + β + (charT f r + charT g r) / 4 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
          push_cast; ring
    have hsf := hsum f fun j => rfl
    have hsg := hsum g fun j => hred_g j r
    have hTf0 : 0 ≤ charT f r := ValueDistribution.characteristic_nonneg hr1
    have hTg0 : 0 ≤ charT g r := ValueDistribution.characteristic_nonneg hr1
    set T := pairT f g r with hT
    have hfT : charT f r ≤ T := le_max_left _ _
    have hgT : charT g r ≤ T := le_max_right _ _
    have hT0 : 0 ≤ T := hTf0.trans hfT
    have hlogf : Cf * Real.log (Real.exp 1 + r * charT f r) ≤
        γ * Real.log (Real.exp 1 + r * T) := by
      have hpos : 0 < Real.exp 1 + r * charT f r := by positivity
      have hl0 : 0 ≤ Real.log (Real.exp 1 + r * charT f r) :=
        Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1:ℝ)])
      calc Cf * Real.log (Real.exp 1 + r * charT f r)
          ≤ γ * Real.log (Real.exp 1 + r * charT f r) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) hl0
        _ ≤ γ * Real.log (Real.exp 1 + r * T) := by
            apply mul_le_mul_of_nonneg_left _ hγ
            apply Real.log_le_log hpos
            nlinarith
    have hlogg : Cg * Real.log (Real.exp 1 + r * charT g r) ≤
        γ * Real.log (Real.exp 1 + r * T) := by
      have hpos : 0 < Real.exp 1 + r * charT g r := by positivity
      have hl0 : 0 ≤ Real.log (Real.exp 1 + r * charT g r) :=
        Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1:ℝ)])
      calc Cg * Real.log (Real.exp 1 + r * charT g r)
          ≤ γ * Real.log (Real.exp 1 + r * charT g r) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) hl0
        _ ≤ γ * Real.log (Real.exp 1 + r * T) := by
            apply mul_le_mul_of_nonneg_left _ hγ
            apply Real.log_le_log hpos
            nlinarith
    norm_num at h1 h2
    have hTle : T ≤ α * r + β + T / 2 + γ * Real.log (Real.exp 1 + r * T) := by
      rcases le_total (charT f r) (charT g r) with hfg | hfg
      · have : T = charT g r := max_eq_right hfg
        rw [this] at hlogf hlogg ⊢
        linarith
      · have : T = charT f r := max_eq_left hfg
        rw [this] at hlogf hlogg ⊢
        linarith
    exact absorb_log hr1 hT0 hγ hTle
  obtain ⟨E, hEm, hEv, r₀, hr₀⟩ := hmain
  obtain ⟨r₁, hr₁⟩ := exists_not_mem_of_finite_measure hEm hEv
  refine ⟨2 * |K₀|, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max r₀ r₁) 1)] with r hr
  have hr0 : r₀ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr1' : r₁ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨R, hrR, hRr, hRE⟩ := hr₁ r hr1'
  have hTR := hr₀ R (hr0.trans hrR) hRE
  have hKR : K₀ * R ≤ 2 * |K₀| * r := by
    calc K₀ * R ≤ |K₀| * R := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |K₀| * (r + 1) := mul_le_mul_of_nonneg_left hRr (abs_nonneg _)
      _ ≤ 2 * |K₀| * r := by nlinarith [abs_nonneg K₀]
  constructor
  · calc charT f r ≤ charT f R := ext_charT_mono hfm.1 hr1 hrR
      _ ≤ pairT f g R := le_max_left _ _
      _ ≤ 2 * |K₀| * r := hTR.trans hKR
  · calc charT g r ≤ charT g R := ext_charT_mono hgm.1 hr1 hrR
      _ ≤ pairT f g R := le_max_right _ _
      _ ≤ 2 * |K₀| * r := hTR.trans hKR

end ThreeIM
