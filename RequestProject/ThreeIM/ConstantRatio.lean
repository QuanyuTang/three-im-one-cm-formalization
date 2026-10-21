module

public import RequestProject.ThreeIM.NevanlinnaAux
public import RequestProject.ThreeIM.PoleCount

/-!
# The constant auxiliary ratio (Lemma 4.10)

If `Φ = U/V` is constant for a normalized pair on `ℂ`, then all four values are shared CM.

The proof follows the paper.  If `Φ ≡ c`, then `c = m/n` at every finite shared point of type
`(m, n)` (Lemma 3.6), so `c = 1` gives CM sharing.  If `c ≠ 1` and there is a defect, we
precompose with `t ↦ z⋆ - 1 + e^t` to get linear growth of `T`, and then show:

* `m(r, 1/U) = O(L)`, since `U² = cΨ` and `T(r, Ψ) = O(L)` (Lemma 3.10);
* `m(r, σ) = O(L)` for `σ = f + g`, from `f'/(f-a) - c g'/(g-a) = U (σ - s₁ + a)`;
* `m(r, J) = O(L + log r)` for `J = σ'/V`, by the logarithmic derivative lemma;
* `c P(σ - g) + P(g) - (σ - 2g) J = 0`, a cubic in `g` with leading coefficient `1 - c`, so the
  root bound (Lemma 4.9) gives `m(r, g), m(r, f) = O(L + log r)`;
* hence `T = N_∞ + O(L + log r) ≤ (4/5) T + O(L + log r)` by the pole bound (Lemma 4.5),
  contradicting linear growth.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory

namespace ThreeIM

/-! ### The root bound for the cubic -/

/-- The root bound for the cubic `c P(σ - g) + P(g) - (σ - 2g) J = 0`, whose leading
coefficient in `g` is `1 - c ≠ 0`. -/
lemma posLog_le_of_cubic (a : Fin 3 → ℂ) {c : ℂ} (hc : c ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ J w : ℂ,
      c * cubicP a (σ - w) + cubicP a w - (σ - 2 * w) * J = 0 →
        log⁺ ‖w‖ ≤ K + 4 * log⁺ ‖σ‖ + 4 * log⁺ ‖J‖ := by
  set s1 := a 0 + a 1 + a 2
  set s2 := a 0 * a 1 + a 0 * a 2 + a 1 * a 2
  set s3 := a 0 * a 1 * a 2
  set d : ℂ := 1 - c with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  set A : ℝ := 1 + ‖c‖ + ‖s1‖ + ‖s2‖ + ‖s3‖ with hA
  have hA1 : 1 ≤ A := by
    have := norm_nonneg c; have := norm_nonneg s1; have := norm_nonneg s2
    have := norm_nonneg s3
    rw [hA]; linarith
  set K₀ : ℝ := 1 + 9 / ‖d‖ with hK₀
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ 9 / ‖d‖ := by positivity
    rw [hK₀]; linarith
  refine ⟨log⁺ K₀ + 4 * (log⁺ A + 2 * log 2), by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have := Real.posLog_nonneg (x := K₀); have := Real.posLog_nonneg (x := A)
    positivity, fun σ J w hE => ?_⟩
  set M : ℝ := 1 + ‖σ‖ + ‖J‖ with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith [norm_nonneg σ, norm_nonneg J]
  set N : ℝ := A * M with hN
  have hN1 : 1 ≤ N := one_le_mul_of_one_le_of_one_le hA1 hM1
  have hN0 : 0 ≤ N := by linarith
  have hAN : A ≤ N := le_mul_of_one_le_right (by linarith) hM1
  have hMN : M ≤ N := le_mul_of_one_le_left (by linarith) hA1
  have := norm_nonneg c; have := norm_nonneg s1; have := norm_nonneg s2
  have := norm_nonneg s3; have := norm_nonneg σ; have := norm_nonneg J
  have hcN : ‖c‖ ≤ N := by linarith
  have hs1N : ‖s1‖ ≤ N := by linarith
  have hs2N : ‖s2‖ ≤ N := by linarith
  have hs3N : ‖s3‖ ≤ N := by linarith
  have hσN : ‖σ‖ ≤ N := by linarith
  have hJN : ‖J‖ ≤ N := by linarith
  clear_value N M A
  -- the coefficients
  set e2 : ℂ := c * (3 * σ - s1) - s1 with he2d
  set e1 : ℂ := c * (-3 * σ ^ 2 + 2 * s1 * σ - s2) + s2 + 2 * J with he1d
  set e0 : ℂ := c * (σ ^ 3 - s1 * σ ^ 2 + s2 * σ - s3) - s3 - σ * J with he0d
  have hid : c * cubicP a (σ - w) + cubicP a w - (σ - 2 * w) * J =
      d * w ^ 3 + e2 * w ^ 2 + e1 * w + e0 := by
    simp only [cubicP, e2, e1, e0, s1, s2, s3, hd]; ring
  clear_value e0 e1 e2
  have hN2 : N ≤ N ^ 4 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN3 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have he2 : ‖e2‖ ≤ 9 * N ^ 4 := by
    have h1 : ‖e2‖ ≤ ‖c‖ * (3 * ‖σ‖ + ‖s1‖) + ‖s1‖ := by
      rw [he2d]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]; norm_num
    have h2 : ‖c‖ * (3 * ‖σ‖ + ‖s1‖) + ‖s1‖ ≤ N * (3 * N + N) + N := by gcongr
    have : N * (3 * N + N) + N = 4 * N ^ 2 + N := by ring
    linarith
  have he1 : ‖e1‖ ≤ 9 * N ^ 4 := by
    have h1 : ‖e1‖ ≤ ‖c‖ * (3 * ‖σ‖ ^ 2 + 2 * ‖s1‖ * ‖σ‖ + ‖s2‖) + ‖s2‖ + 2 * ‖J‖ := by
      rw [he1d]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) ?_
      · rw [norm_mul]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
        simp [norm_pow]
      · simp
    have h2 : ‖c‖ * (3 * ‖σ‖ ^ 2 + 2 * ‖s1‖ * ‖σ‖ + ‖s2‖) + ‖s2‖ + 2 * ‖J‖ ≤
        N * (3 * N ^ 2 + 2 * N * N + N) + N + 2 * N := by gcongr
    have : N * (3 * N ^ 2 + 2 * N * N + N) + N + 2 * N = 5 * N ^ 3 + N ^ 2 + 3 * N := by ring
    have hN4 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    linarith
  have he0 : ‖e0‖ ≤ 9 * N ^ 4 := by
    have h1 : ‖e0‖ ≤ ‖c‖ * (‖σ‖ ^ 3 + ‖s1‖ * ‖σ‖ ^ 2 + ‖s2‖ * ‖σ‖ + ‖s3‖) + ‖s3‖ +
        ‖σ‖ * ‖J‖ := by
      rw [he0d]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
      · rw [norm_mul]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
        refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
        · simp [norm_pow]
        · simp
      · simp
    have h2 : ‖c‖ * (‖σ‖ ^ 3 + ‖s1‖ * ‖σ‖ ^ 2 + ‖s2‖ * ‖σ‖ + ‖s3‖) + ‖s3‖ + ‖σ‖ * ‖J‖ ≤
        N * (N ^ 3 + N * N ^ 2 + N * N + N) + N + N * N := by gcongr
    have : N * (N ^ 3 + N * N ^ 2 + N * N + N) + N + N * N = 2 * N ^ 4 + N ^ 3 + 2 * N ^ 2 + N := by
      ring
    have hN4 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    linarith
  -- the monic root bound
  set b : ℕ → ℂ := fun j => if j = 0 then e0 / d else if j = 1 then e1 / d else e2 / d with hb
  have hmon : w ^ 3 + ∑ j ∈ Finset.range 3, b j * w ^ j = 0 := by
    have h0 : d * w ^ 3 + e2 * w ^ 2 + e1 * w + e0 = 0 := hid ▸ hE
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hb]
    norm_num
    field_simp
    linear_combination h0
  have hbB : ∀ j < 3, ‖b j‖ ≤ 9 * N ^ 4 / ‖d‖ := by
    intro j hj
    interval_cases j <;> simp [hb] <;> gcongr
  have hw := norm_le_of_monic_root (by norm_num) hbB hmon
  have hw' : ‖w‖ ≤ K₀ * N ^ 4 := by
    rw [hK₀, add_mul, one_mul, div_mul_eq_mul_div]
    have : 9 * N ^ 4 / ‖d‖ = 9 / ‖d‖ * N ^ 4 := by ring
    have h1 : (1 : ℝ) ≤ N ^ 4 := one_le_pow₀ hN1
    linarith
  -- logarithms
  have hlogM : log⁺ M ≤ 2 * log 2 + log⁺ ‖σ‖ + log⁺ ‖J‖ := by
    have e1 := Real.posLog_add (x := 1 + ‖σ‖) (y := ‖J‖)
    have e2 := Real.posLog_add (x := 1) (y := ‖σ‖)
    rw [Real.posLog_one] at e2
    rw [hM]; linarith
  calc log⁺ ‖w‖ ≤ log⁺ (K₀ * N ^ 4) := Real.posLog_le_posLog ((by norm_num : (-1 : ℝ) ≤ 0).trans (norm_nonneg _)) hw'
    _ ≤ log⁺ K₀ + log⁺ (N ^ 4) := Real.posLog_mul
    _ = log⁺ K₀ + 4 * log⁺ N := by rw [Real.posLog_pow]; norm_num
    _ ≤ log⁺ K₀ + 4 * (log⁺ A + log⁺ M) := by
        gcongr; rw [hN]; exact Real.posLog_mul
    _ ≤ _ := by linarith

/-! ### The pair with constant ratio -/

section Pair

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

/-- If `Φ - c` vanishes identically near one point, then `Φ = c` near every point. -/
lemma auxPhi_eventually_eq (hp : NormalizedPair univ f g a) {c z : ℂ}
    (hc : meromorphicOrderAt (fun w => auxPhi a f g w - c) z = ⊤) (x : ℂ) :
    ∀ᶠ w in 𝓝[≠] x, auxPhi a f g w = c := by
  have hQm : MeromorphicOn (fun w => auxPhi a f g w - c) univ := fun x _ =>
    (hp.meromorphic_auxPhi x).sub (MeromorphicAt.const c x)
  have htop : meromorphicOrderAt (fun w => auxPhi a f g w - c) x = ⊤ := by
    by_contra hne
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hQm isPreconnected_univ
      (mem_univ x) (mem_univ z) hne hc
  exact (meromorphicOrderAt_eq_top_iff.1 htop).mono fun w hw => sub_eq_zero.1 hw

/-- If `Φ - c` vanishes identically near one point, then `U = c V` off a discrete set. -/
lemma auxU_eq_const_mul_auxV (hp : NormalizedPair univ f g a) {c z : ℂ}
    (hc : meromorphicOrderAt (fun w => auxPhi a f g w - c) z = ⊤) :
    ∀ᶠ w in codiscrete ℂ, auxU a f g w = c * auxV a f g w := by
  have hQm : MeromorphicOn (fun w => auxPhi a f g w - c) univ := fun x _ =>
    (hp.meromorphic_auxPhi x).sub (MeromorphicAt.const c x)
  have htop : ∀ x, meromorphicOrderAt (fun w => auxPhi a f g w - c) x = ⊤ := by
    intro x
    by_contra hne
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hQm isPreconnected_univ
      (mem_univ x) (mem_univ z) hne hc
  have hΦ : ∀ᶠ w in codiscrete ℂ, auxPhi a f g w = c :=
    codiscrete_iff_nhdsNE.2 fun x =>
      (meromorphicOrderAt_eq_top_iff.1 (htop x)).mono fun w hw => sub_eq_zero.1 hw
  filter_upwards [hΦ, hp.eventually_auxV_ne_zero] with w h1 h2
  rw [← h1, auxPhi, div_mul_cancel₀ _ h2]

/-- The identity `U = c V` is preserved by a precomposition with nonvanishing derivative. -/
lemma auxU_eq_const_mul_auxV_comp (hp : NormalizedPair univ f g a) {c : ℂ}
    (hUV : ∀ᶠ w in codiscrete ℂ, auxU a f g w = c * auxV a f g w) {h : ℂ → ℂ}
    (hh : ∀ z, AnalyticAt ℂ h z) (hh' : ∀ z, deriv h z ≠ 0) :
    ∀ᶠ t in codiscrete ℂ, auxU a (f ∘ h) (g ∘ h) t = c * auxV a (f ∘ h) (g ∘ h) t := by
  have hP : ∀ᶠ w in codiscrete ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      auxU a f g w = c * auxV a f g w :=
    (eventually_analyticAt_of_meromorphic hp.nonconst_f.meromorphic).and
      ((eventually_analyticAt_of_meromorphic hp.nonconst_g.meromorphic).and hUV)
  have hnc : ∀ x ∈ (univ : Set ℂ), ¬ EventuallyConst h (𝓝 x) := by
    intro x _ hx
    obtain ⟨b, hb⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hx
    apply hh' x
    rw [hb.deriv_eq]; simp
  have hpre := AnalyticOnNhd.preimage_mem_codiscreteWithin (U := univ)
    (fun x _ => hh x) hnc (codiscreteWithin.mono (subset_univ _) hP)
  have hpre' : ∀ᶠ t in codiscrete ℂ, AnalyticAt ℂ f (h t) ∧ AnalyticAt ℂ g (h t) ∧
      auxU a f g (h t) = c * auxV a f g (h t) := hpre
  filter_upwards [hpre'] with t ⟨h1, h2, h3⟩
  rw [auxU_comp h1.differentiableAt (hh t).differentiableAt,
    auxV_comp h2.differentiableAt (hh t).differentiableAt, h3]
  ring

/-- Pointwise identity behind `m(r, σ) = O(L)`: if `U = c V`, then
`f + g = (f'/(f - a₀) - c g'/(g - a₀)) / U + a₁ + a₂`. -/
lemma sigma_identity_pt {a : Fin 3 → ℂ} {F G F' G' c : ℂ} (f0 : F ≠ a 0) (f1 : F ≠ a 1)
    (f2 : F ≠ a 2) (g0 : G ≠ a 0) (g1 : G ≠ a 1) (g2 : G ≠ a 2) (hfg : F ≠ G)
    (hU : (F - G) * F' / cubicP a F ≠ 0)
    (hUV : (F - G) * F' / cubicP a F = c * ((F - G) * G' / cubicP a G)) :
    F + G = (F' / (F - a 0) + (-c) * (G' / (G - a 0))) * ((F - G) * F' / cubicP a F)⁻¹ +
      (a 1 + a 2) := by
  have f0' := sub_ne_zero.2 f0; have f1' := sub_ne_zero.2 f1; have f2' := sub_ne_zero.2 f2
  have g0' := sub_ne_zero.2 g0; have g1' := sub_ne_zero.2 g1; have g2' := sub_ne_zero.2 g2
  have hfg' := sub_ne_zero.2 hfg
  have hF' : F' ≠ 0 := by rintro rfl; simp at hU
  unfold cubicP at hU hUV ⊢
  field_simp at hUV ⊢
  linear_combination (-1 : ℂ) * hUV

variable (hp : NormalizedPair univ f g a) {c : ℂ} (hc1 : c ≠ 1)
  (hUV : ∀ᶠ w in codiscrete ℂ, auxU a f g w = c * auxV a f g w)
include hp hUV

/-- The constant is nonzero. -/
lemma const_ne_zero_of_auxU_eq : c ≠ 0 := by
  rintro rfl
  have h := codiscrete_iff_nhdsNE.1 (hUV.and hp.eventually_auxU_ne_zero) 0
  obtain ⟨w, h1, h2⟩ := h.exists
  exact h2 (by rw [h1, zero_mul])

/-- `m(r, 1/U) = O(L)`. -/
lemma proximity_inv_auxU_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => (auxU a f g z)⁻¹) ⊤ r ≤ C * pairL f g r := by
  have hc0 := const_ne_zero_of_auxU_eq hp hUV
  obtain ⟨K, hK⟩ := proximity_inv_auxPsi_le hp
  obtain ⟨C, hC⟩ := mues_estimate hp
  have hΨi : Meromorphic (fun z => (auxPsi a f g z)⁻¹) := fun x => (hp.meromorphic_auxPsi x).inv
  have hsq : (fun z => (auxU a f g z)⁻¹ ^ 2) =ᶠ[codiscrete ℂ]
      fun z => c⁻¹ * (auxPsi a f g z)⁻¹ := by
    filter_upwards [hUV] with z hz
    simp only [auxPsi, hz]
    rw [mul_inv, mul_inv, mul_inv]; ring
  refine ⟨(log⁺ ‖c⁻¹‖ + |K| + |C|) / 2, hC.mono fun r hr hCr => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have e1 := proximity_sq (fun z => (auxU a f g z)⁻¹) r
  rw [proximity_congr_codiscrete hsq (by linarith)] at e1
  have e2 := proximity_const_mul_le c⁻¹ hΨi r
  have e3 := hK r hr
  have hlc : 0 ≤ log⁺ ‖c⁻¹‖ := Real.posLog_nonneg
  have h4 : log⁺ ‖c⁻¹‖ ≤ log⁺ ‖c⁻¹‖ * pairL f g r := le_mul_of_one_le_right hlc hL
  have h5 : K ≤ |K| * pairL f g r := (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  have h6 : C * pairL f g r ≤ |C| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have : (log⁺ ‖c⁻¹‖ + |K| + |C|) / 2 * pairL f g r =
      (log⁺ ‖c⁻¹‖ * pairL f g r + |K| * pairL f g r + |C| * pairL f g r) / 2 := by ring
  rw [this]
  linarith

/-- `m(r, σ) = O(L)` for `σ = f + g`. -/
lemma proximity_sigma_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => f z + g z) ⊤ r ≤ C * pairL f g r := by
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  set Df : ℂ → ℂ := fun z => deriv f z / (f z - a 0) with hDf
  set Dg : ℂ → ℂ := fun z => deriv g z / (g z - a 0) with hDg
  have hDfm : Meromorphic Df := meromorphic_logDeriv_sub hfm (a 0)
  have hDgm : Meromorphic Dg := meromorphic_logDeriv_sub hgm (a 0)
  have hUi : Meromorphic (fun z => (auxU a f g z)⁻¹) := fun x => (hp.meromorphic_auxU x).inv
  set D : ℂ → ℂ := fun z => Df z + (-c) * Dg z with hD
  have hDm : Meromorphic D := fun x => (hDfm x).add ((MeromorphicAt.const _ x).mul (hDgm x))
  have hDU : Meromorphic (fun z => D z * (auxU a f g z)⁻¹) := fun x => (hDm x).mul (hUi x)
  have hid : (fun z => f z + g z) =ᶠ[codiscrete ℂ]
      fun z => D z * (auxU a f g z)⁻¹ + (a 1 + a 2) := by
    have hfa : ∀ i, ∀ᶠ z in codiscrete ℂ, f z ≠ a i := fun i => hp.nonconst_f.eventually_ne _
    have hga : ∀ i, ∀ᶠ z in codiscrete ℂ, g z ≠ a i := fun i => hp.nonconst_g.eventually_ne _
    filter_upwards [hfa 0, hfa 1, hfa 2, hga 0, hga 1, hga 2, hp.eventually_ne,
      hp.eventually_auxU_ne_zero, hUV] with z f0 f1 f2 g0 g1 g2 hfg hU hUVz
    show f z + g z = (deriv f z / (f z - a 0) + (-c) * (deriv g z / (g z - a 0))) *
      (auxU a f g z)⁻¹ + (a 1 + a 2)
    simp only [auxU, auxV] at hU hUVz ⊢
    exact sigma_identity_pt f0 f1 f2 g0 g1 g2 hfg hU hUVz
  obtain ⟨C₁, hC₁⟩ := proximity_inv_auxU_le hp hUV
  obtain ⟨C₂, hC₂⟩ := proximity_logDeriv_le_pairL hp (a 0)
  refine ⟨|C₁| + 2 * |C₂| + log⁺ ‖a 1 + a 2‖ + log⁺ ‖-c‖ + 2 * log 2,
    (hC₁.and hC₂).mono fun r hr ⟨h1, h2, h3⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  rw [proximity_congr_codiscrete hid (by linarith)]
  have e1 := proximity_add_top_le hDU (fun x => MeromorphicAt.const (a 1 + a 2) x) r
  have hconst : proximity (fun _ : ℂ => a 1 + a 2) ⊤ r = log⁺ ‖a 1 + a 2‖ := by simp
  simp only [Pi.add_apply] at e1
  have e2 := proximity_mul_top_le hDm hUi r
  simp only [Pi.add_apply] at e2
  have e3 := proximity_add_top_le hDfm (fun x => (MeromorphicAt.const (-c) x).mul (hDgm x)) r
  simp only [Pi.add_apply] at e3
  have e4 := proximity_const_mul_le (-c) hDgm r
  have hl2 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have hp1 : 0 ≤ log⁺ ‖a 1 + a 2‖ := Real.posLog_nonneg
  have hp2 : 0 ≤ log⁺ ‖-c‖ := Real.posLog_nonneg
  have k1 : C₁ * pairL f g r ≤ |C₁| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k2 : C₂ * pairL f g r ≤ |C₂| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k3 : log⁺ ‖a 1 + a 2‖ ≤ log⁺ ‖a 1 + a 2‖ * pairL f g r := le_mul_of_one_le_right hp1 hL
  have k4 : log⁺ ‖-c‖ ≤ log⁺ ‖-c‖ * pairL f g r := le_mul_of_one_le_right hp2 hL
  have k5 : log 2 ≤ log 2 * pairL f g r := le_mul_of_one_le_right hl2 hL
  have q1 : proximity (D * fun z => (auxU a f g z)⁻¹) ⊤ r =
      proximity (fun z => D z * (auxU a f g z)⁻¹) ⊤ r := rfl
  have q2 : proximity (Df + (fun x => -c) * Dg) ⊤ r = proximity D ⊤ r := rfl
  have q3 : proximity ((fun x => -c) * Dg) ⊤ r = proximity (fun z => -c * Dg z) ⊤ r := rfl
  have q4 : proximity Df ⊤ r = proximity (fun z => deriv f z / (f z - a 0)) ⊤ r := rfl
  have q5 : proximity Dg ⊤ r = proximity (fun z => deriv g z / (g z - a 0)) ⊤ r := rfl
  have : (|C₁| + 2 * |C₂| + log⁺ ‖a 1 + a 2‖ + log⁺ ‖-c‖ + 2 * log 2) * pairL f g r =
      |C₁| * pairL f g r + 2 * (|C₂| * pairL f g r) + log⁺ ‖a 1 + a 2‖ * pairL f g r +
        log⁺ ‖-c‖ * pairL f g r + 2 * (log 2 * pairL f g r) := by ring
  rw [this]
  show proximity ((fun z => D z * (auxU a f g z)⁻¹) + fun _ => a 1 + a 2) ⊤ r ≤ _
  rw [hconst] at e1
  linarith

/-- `m(r, σ') = O(L + log r)` for `σ = f + g`. -/
lemma proximity_deriv_sigma_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (deriv (fun w => f w + g w)) ⊤ r ≤ C * (pairL f g r + log r) := by
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  set σ : ℂ → ℂ := fun w => f w + g w with hσ
  have hσm : Meromorphic σ := fun x => (hfm x).add (hgm x)
  by_cases hconst : ∃ z c₀, meromorphicOrderAt (fun w => σ w - c₀) z = ⊤
  · -- `σ` is constant, so `σ' = 0` off a discrete set
    obtain ⟨z, c₀, hz⟩ := hconst
    have hQm : MeromorphicOn (fun w => σ w - c₀) univ := fun x _ =>
      (hσm x).sub (MeromorphicAt.const c₀ x)
    have htop : ∀ x, meromorphicOrderAt (fun w => σ w - c₀) x = ⊤ := by
      intro x
      by_contra hne
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hQm isPreconnected_univ
        (mem_univ x) (mem_univ z) hne hz
    have hd : deriv σ =ᶠ[codiscrete ℂ] fun _ => (0 : ℂ) :=
      codiscrete_iff_nhdsNE.2 fun x => deriv_eventually_zero_of_eventually_const
        ((meromorphicOrderAt_eq_top_iff.1 (htop x)).mono fun w hw => sub_eq_zero.1 hw)
    refine ⟨0, ⟨∅, MeasurableSet.empty, by simp, 1, fun r hr _ => ?_⟩⟩
    show proximity (deriv σ) ⊤ r ≤ 0 * (pairL f g r + log r)
    rw [proximity_congr_codiscrete hd (by linarith)]
    simp
  · push_neg at hconst
    have hσnc : IsNonconstMeroOn σ univ := ⟨fun x _ => hσm x, fun z _ c₀ => hconst z c₀⟩
    obtain ⟨C₀, hC₀⟩ := ext_log_derivative hσnc 0
    obtain ⟨C₁, hC₁⟩ := proximity_sigma_le hp hUV
    have hσ0 := hσnc.eventually_ne 0
    have hσ'm : Meromorphic (deriv σ) := fun x => (hσm x).deriv
    have hLm : Meromorphic (fun z => deriv σ z / (σ z - 0)) := meromorphic_logDeriv_sub hσm 0
    have hid : deriv σ =ᶠ[codiscrete ℂ] fun z => σ z * (deriv σ z / (σ z - 0)) := by
      filter_upwards [hσ0] with z hz
      rw [sub_zero, mul_div_cancel₀ _ hz]
    refine ⟨|C₁| + |C₀| * (1 + log 3), (hC₀.and hC₁).mono fun r hr ⟨h0, h1⟩ => ?_⟩
    have hL := one_le_pairL (f := f) (g := g) hr
    have hlr : 0 ≤ log r := Real.log_nonneg hr
    have hl3 : 0 ≤ log 3 := Real.log_nonneg (by norm_num)
    rw [proximity_congr_codiscrete hid (by linarith)]
    have e1 := proximity_mul_top_le hσm hLm r
    simp only [Pi.add_apply] at e1
    -- the error term of the logarithmic derivative lemma
    have hTσ : charT σ r ≤ 2 * pairT f g r + 1 := by
      have := characteristic_add_top_le hfm hgm hr (E := ℂ)
      have h2 : log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have h3 : charT f r ≤ pairT f g r := le_max_left _ _
      have h4 : charT g r ≤ pairT f g r := le_max_right _ _
      show characteristic (f + g) ⊤ r ≤ _
      unfold charT at h3 h4
      linarith
    have hlog := log_le_of_le_two_mul_add_one hr (le_max_of_le_left (charT_nonneg hr))
      (charT_nonneg (h := σ) hr) hTσ
    have hLσ0 : 0 ≤ Real.log (Real.exp 1 + r * charT σ r) :=
      Real.log_nonneg (by nlinarith [charT_nonneg (h := σ) hr, Real.add_one_le_exp 1])
    have k0 : C₀ * Real.log (Real.exp 1 + r * charT σ r) ≤
        |C₀| * (pairL f g r + log 3 + log r) := by
      calc _ ≤ |C₀| * Real.log (Real.exp 1 + r * charT σ r) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hLσ0
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    have k1 : C₁ * pairL f g r ≤ |C₁| * (pairL f g r + log r) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
    have k2 : |C₀| * (pairL f g r + log 3 + log r) ≤
        |C₀| * (1 + log 3) * (pairL f g r + log r) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith
    have e2 : proximity (σ * fun z => deriv σ z / (σ z - 0)) ⊤ r =
        proximity (fun z => σ z * (deriv σ z / (σ z - 0))) ⊤ r := rfl
    have e3 : proximity σ ⊤ r = proximity (fun z => f z + g z) ⊤ r := rfl
    rw [add_mul]
    linarith

/-- `m(r, J) = O(L + log r)` for `J = σ'/V`. -/
lemma proximity_J_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => deriv (fun w => f w + g w) z / auxV a f g z) ⊤ r ≤
        C * (pairL f g r + log r) := by
  have hc0 := const_ne_zero_of_auxU_eq hp hUV
  obtain ⟨C₁, hC₁⟩ := proximity_inv_auxU_le hp hUV
  obtain ⟨C₂, hC₂⟩ := proximity_deriv_sigma_le hp hUV
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  set σ : ℂ → ℂ := fun w => f w + g w with hσ
  have hσ'm : Meromorphic (deriv σ) := fun x => ((hfm x).add (hgm x)).deriv
  have hUi : Meromorphic (fun z => (auxU a f g z)⁻¹) := fun x => (hp.meromorphic_auxU x).inv
  have hcU : Meromorphic (fun z => c * (auxU a f g z)⁻¹) := fun x =>
    (MeromorphicAt.const c x).mul (hUi x)
  have hid : (fun z => deriv σ z / auxV a f g z) =ᶠ[codiscrete ℂ]
      fun z => deriv σ z * (c * (auxU a f g z)⁻¹) := by
    filter_upwards [hUV] with z hz
    rw [hz, mul_inv, div_eq_mul_inv]
    field_simp
  refine ⟨|C₂| + log⁺ ‖c‖ + |C₁|, (hC₁.and hC₂).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hlr : 0 ≤ log r := Real.log_nonneg hr
  rw [proximity_congr_codiscrete hid (by linarith)]
  have e1 := proximity_mul_top_le hσ'm hcU r
  simp only [Pi.add_apply] at e1
  have e2 := proximity_const_mul_le c hUi r
  have e3 : proximity (deriv σ * fun z => c * (auxU a f g z)⁻¹) ⊤ r =
      proximity (fun z => deriv σ z * (c * (auxU a f g z)⁻¹)) ⊤ r := rfl
  have hpc : 0 ≤ log⁺ ‖c‖ := Real.posLog_nonneg
  have k1 : C₁ * pairL f g r ≤ |C₁| * (pairL f g r + log r) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have k2 : C₂ * (pairL f g r + log r) ≤ |C₂| * (pairL f g r + log r) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k3 : log⁺ ‖c‖ ≤ log⁺ ‖c‖ * (pairL f g r + log r) :=
    le_mul_of_one_le_right hpc (by linarith)
  rw [add_mul, add_mul]
  linarith

/-- The cubic identity `c P(σ - g) + P(g) - (σ - 2g) J = 0`, off a discrete set. -/
lemma cubic_identity :
    ∀ᶠ z in codiscrete ℂ,
      c * cubicP a ((f z + g z) - g z) + cubicP a (g z) -
        ((f z + g z) - 2 * g z) * (deriv (fun w => f w + g w) z / auxV a f g z) = 0 := by
  have hfa : ∀ i, ∀ᶠ z in codiscrete ℂ, f z ≠ a i := fun i => hp.nonconst_f.eventually_ne _
  have hga : ∀ i, ∀ᶠ z in codiscrete ℂ, g z ≠ a i := fun i => hp.nonconst_g.eventually_ne _
  filter_upwards [hfa 0, hfa 1, hfa 2, hga 0, hga 1, hga 2, hp.eventually_ne,
    hp.eventually_auxV_ne_zero, hUV,
    eventually_analyticAt_of_meromorphic hp.nonconst_f.meromorphic,
    eventually_analyticAt_of_meromorphic hp.nonconst_g.meromorphic]
    with z f0 f1 f2 g0 g1 g2 hfg hV hUVz hfa' hga'
  have hd : deriv (fun w => f w + g w) z = deriv f z + deriv g z :=
    deriv_add hfa'.differentiableAt hga'.differentiableAt
  rw [hd]
  have hPf : cubicP a (f z) ≠ 0 := by
    unfold cubicP
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 f0) (sub_ne_zero.2 f1)) (sub_ne_zero.2 f2)
  have hPg : cubicP a (g z) ≠ 0 := by
    unfold cubicP
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 g0) (sub_ne_zero.2 g1)) (sub_ne_zero.2 g2)
  have hfg' := sub_ne_zero.2 hfg
  simp only [auxU, auxV] at hV hUVz ⊢
  have hG' : deriv g z ≠ 0 := by rintro h; rw [h] at hV; simp at hV
  rw [show f z + g z - g z = f z by ring, show f z + g z - 2 * g z = f z - g z by ring]
  field_simp at hUVz ⊢
  linear_combination (-1 : ℂ) * hUVz

include hc1 in
/-- `m(r, g) = O(L + log r)`. -/
lemma proximity_g_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => proximity g ⊤ r ≤ C * (pairL f g r + log r) := by
  obtain ⟨K, hK0, hK⟩ := posLog_le_of_cubic a hc1
  obtain ⟨C₁, hC₁⟩ := proximity_sigma_le hp hUV
  obtain ⟨C₂, hC₂⟩ := proximity_J_le hp hUV
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  have hσm : Meromorphic (fun z => f z + g z) := fun x => (hfm x).add (hgm x)
  have hJm : Meromorphic (fun z => deriv (fun w => f w + g w) z / auxV a f g z) := fun x =>
    (hσm x).deriv.div (hp.meromorphic_auxV x)
  have hpt : ∀ᶠ z in codiscrete ℂ, log⁺ ‖g z‖ ≤ K + 4 * log⁺ ‖f z + g z‖ +
      4 * log⁺ ‖deriv (fun w => f w + g w) z / auxV a f g z‖ :=
    (cubic_identity hp hUV).mono fun z hz => hK _ _ _ hz
  refine ⟨K + 4 * |C₁| + 4 * |C₂|, (hC₁.and hC₂).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hlr : 0 ≤ log r := Real.log_nonneg hr
  have e := proximity_le_of_eventually hgm hσm hJm hK0 (by norm_num) (by norm_num) hpt
    (r := r) (by linarith)
  have k0 : K ≤ K * (pairL f g r + log r) := le_mul_of_one_le_right hK0 (by linarith)
  have k1 : C₁ * pairL f g r ≤ |C₁| * (pairL f g r + log r) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have k2 : C₂ * (pairL f g r + log r) ≤ |C₂| * (pairL f g r + log r) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  rw [add_mul, add_mul, mul_assoc, mul_assoc]
  linarith

include hc1 in
/-- `m(r, f) = O(L + log r)`. -/
lemma proximity_f_le :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => proximity f ⊤ r ≤ C * (pairL f g r + log r) := by
  obtain ⟨C₁, hC₁⟩ := proximity_sigma_le hp hUV
  obtain ⟨C₂, hC₂⟩ := proximity_g_le hp hc1 hUV
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  have hσm : Meromorphic (fun z => f z + g z) := fun x => (hfm x).add (hgm x)
  have hng : Meromorphic (fun z => (-1 : ℂ) * g z) := fun x =>
    (MeromorphicAt.const _ x).mul (hgm x)
  refine ⟨|C₁| + |C₂| + log 2, (hC₁.and hC₂).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hlr : 0 ≤ log r := Real.log_nonneg hr
  have hl2 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have hf : f = (fun z => f z + g z) + fun z => (-1 : ℂ) * g z := by ext z; simp
  have e1 := proximity_add_top_le hσm hng r
  simp only [Pi.add_apply] at e1
  have e2 := proximity_const_mul_le (-1 : ℂ) hgm r
  simp only [norm_neg, norm_one, Real.posLog_one, zero_add] at e2
  have hf' : proximity f ⊤ r =
      proximity ((fun z => f z + g z) + fun z => (-1 : ℂ) * g z) ⊤ r :=
    congrArg (fun F => proximity F ⊤ r) hf
  have k1 : C₁ * pairL f g r ≤ |C₁| * (pairL f g r + log r) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have k2 : C₂ * (pairL f g r + log r) ≤ |C₂| * (pairL f g r + log r) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k3 : log 2 ≤ log 2 * (pairL f g r + log r) := le_mul_of_one_le_right hl2 (by linarith)
  rw [add_mul, add_mul]
  linarith

include hc1 in
/-- Core of **Lemma 4.10**: with `U = c V`, `c ≠ 1`, and a defect, `T = O(L + log r)`. -/
theorem pairT_le_of_constant_ratio (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => pairT f g r ≤ C * (pairL f g r + log r) := by
  have hnot' : ¬ ∀ j, SharesCMOn univ g f (a j : Sphere) := fun h =>
    hnot fun j z hz => (h j z hz).symm
  obtain ⟨Cf, hCf⟩ := pole_count hp hnot
  obtain ⟨Cg, hCg⟩ := pole_count hp.symm hnot'
  obtain ⟨Df, hDf⟩ := proximity_f_le hp hc1 hUV
  obtain ⟨Dg, hDg⟩ := proximity_g_le hp hc1 hUV
  refine ⟨5 * (|Cf| + |Cg| + |Df| + |Dg|),
    (((hCf.and hCg).and hDf).and hDg).mono fun r hr ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hlr : 0 ≤ log r := Real.log_nonneg hr
  have hTs : pairT g f r = pairT f g r := max_comm _ _
  have hLs : pairL g f r = pairL f g r := by simp only [pairL, hTs]
  rw [hTs, hLs] at h2
  have hTf : charT f r = proximity f ⊤ r + logCounting f ⊤ r := rfl
  have hTg : charT g r = proximity g ⊤ r + logCounting g ⊤ r := rfl
  set X := pairL f g r + log r
  have hX : 0 ≤ X := by linarith
  have k1 : Cf * pairL f g r ≤ |Cf| * X :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have k2 : Cg * pairL f g r ≤ |Cg| * X :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have k3 : Df * X ≤ |Df| * X := mul_le_mul_of_nonneg_right (le_abs_self _) hX
  have k4 : Dg * X ≤ |Dg| * X := mul_le_mul_of_nonneg_right (le_abs_self _) hX
  have k5 : 0 ≤ |Cf| * X := mul_nonneg (abs_nonneg _) hX
  have k6 : 0 ≤ |Cg| * X := mul_nonneg (abs_nonneg _) hX
  have k7 : 0 ≤ |Df| * X := mul_nonneg (abs_nonneg _) hX
  have k8 : 0 ≤ |Dg| * X := mul_nonneg (abs_nonneg _) hX
  have hf : charT f r ≤ 4 / 5 * pairT f g r + (|Cf| + |Cg| + |Df| + |Dg|) * X := by
    rw [hTf]; nlinarith
  have hg : charT g r ≤ 4 / 5 * pairT f g r + (|Cf| + |Cg| + |Df| + |Dg|) * X := by
    rw [hTg]; nlinarith
  have hmax : pairT f g r ≤ 4 / 5 * pairT f g r + (|Cf| + |Cg| + |Df| + |Dg|) * X :=
    max_le hf hg
  have : 5 * (|Cf| + |Cg| + |Df| + |Dg|) * X = 5 * ((|Cf| + |Cg| + |Df| + |Dg|) * X) := by ring
  rw [this]
  linarith

end Pair

/-- **Lemma 4.10** (constant auxiliary ratio).  If `Φ` is constant for a normalized pair on `ℂ`,
then all four values are shared CM. -/
theorem constant_ratio {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (h : NormalizedPair univ f g a)
    (hc : ∃ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z = ⊤) :
    ∀ j, SharesCMOn univ f g (a j : Sphere) := by
  by_contra hnot
  obtain ⟨c, z, hcz⟩ := hc
  have hUV := auxU_eq_const_mul_auxV h hcz
  obtain ⟨zs, hd⟩ := h.exists_defect hnot 0
  by_cases hc1 : c = 1
  · -- `Φ ≡ 1` forces equal multiplicities at every shared point (Lemma 3.6)
    obtain ⟨hm, hn, hmn⟩ := hd
    have hlim := tendsto_auxPhi_at_shared (h.nonconst_f.1 zs (mem_univ _))
      (h.nonconst_g.1 zs (mem_univ _)) h.injective (j := 0) hm hn
      (order_sub_eq_mult hm) (order_sub_eq_mult hn) (h.distinct zs (mem_univ _))
    have hlim' : Tendsto (auxPhi a f g) (𝓝[≠] zs) (𝓝 c) :=
      tendsto_const_nhds.congr' ((auxPhi_eventually_eq h hcz zs).mono fun w hw => hw.symm)
    have heq := tendsto_nhds_unique hlim hlim'
    rw [hc1] at heq
    have hn0 : ((mult g (a 0 : Sphere) zs : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_eq_one_iff_eq hn0] at heq
    exact hmn (by exact_mod_cast heq)
  · -- `c ≠ 1`: pass to the exponential precomposition, which has linear growth
    have hh := expShift_analyticAt zs
    have hh' : ∀ t, deriv (expShift zs) t ≠ 0 := fun t => by
      rw [deriv_expShift]; exact Complex.exp_ne_zero t
    obtain ⟨hp, -, -, hdk⟩ := h.comp_expShift hd
    have hUV₁ := auxU_eq_const_mul_auxV_comp h hUV hh hh'
    have hnot₁ : ¬ ∀ j, SharesCMOn univ (f ∘ expShift zs) (g ∘ expShift zs) (a j : Sphere) :=
      fun hall => (hdk 0).2.2 (hall 0 _ (mem_univ _))
    obtain ⟨C, hC⟩ := pairT_le_of_constant_ratio hp hc1 hUV₁ hnot₁
    obtain ⟨c', hc', hev⟩ := linear_growth_of_progression hp.nonconst_f.1 (a := a 0) (z₀ := 0)
      (ℓ := 2 * Real.pi) (by positivity) (fun k => by
        have := (hdk k).1
        convert this using 2
        push_cast; ring)
    exact false_of_linear_growth hc' (hev.mono fun r hr => hr.trans (le_max_left _ _)) hC

end ThreeIM
