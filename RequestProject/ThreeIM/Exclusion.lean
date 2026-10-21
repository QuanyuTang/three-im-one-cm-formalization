module

public import RequestProject.ThreeIM.ExclusionAux
public import RequestProject.ThreeIM.LimitExtraction
public import RequestProject.ThreeIM.ConstantRatio
public import RequestProject.ThreeIM.Transport

/-!
# Exclusion of the selected configurations (Section 10)
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

namespace SelectedConfiguration

/-- Passing to a subsequence of a selected configuration gives a selected configuration. -/
noncomputable def comp (S : SelectedConfiguration) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    SelectedConfiguration where
  a := S.a
  j := S.j
  m := S.m
  two_le_m := S.two_le_m
  m_le_thirty := S.m_le_thirty
  B := S.B ∘ φ
  B_pos n := S.B_pos (φ n)
  tendsto_B := S.tendsto_B.comp hφ.tendsto_atTop
  F := S.F ∘ φ
  G := S.G ∘ φ
  k := S.k ∘ φ
  pair n := S.pair (φ n)
  marked_F n := S.marked_F (φ n)
  marked_G n := S.marked_G (φ n)
  k_holo n := S.k_holo (φ n)
  k_ne_zero n := S.k_ne_zero (φ n)
  coeff_U n := S.coeff_U (φ n)
  coeff_V n := S.coeff_V (φ n)
  control_center n := S.control_center (φ n)
  control_log n := S.control_log (φ n)

@[simp] lemma comp_c (S : SelectedConfiguration) (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.comp φ hφ).c n = S.c (φ n) := rfl

/-- **Lemma 10.4** (exclusion of a coefficient tending to zero). -/
lemma c_ne_zero (S : SelectedConfiguration) (n : ℕ) : S.c n ≠ 0 :=
  S.k_ne_zero n 0 (by simp [S.B_pos n])

lemma m_pos (S : SelectedConfiguration) : (0 : ℝ) < S.m := by
  have := S.two_le_m; positivity

lemma sqrt_q_ne_zero (S : SelectedConfiguration) : (Real.sqrt (1 / S.m) : ℂ) ≠ 0 := by
  have := S.m_pos
  exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'

lemma sqrt_q_ne_inv (S : SelectedConfiguration) :
    (Real.sqrt (1 / S.m) : ℂ) ≠ (Real.sqrt (1 / S.m) : ℂ)⁻¹ := by
  have hm := S.m_pos
  have h2 : (2 : ℝ) ≤ S.m := by exact_mod_cast S.two_le_m
  intro h
  have h' : (Real.sqrt (1 / S.m)) * Real.sqrt (1 / S.m) = 1 := by
    have := congrArg (fun z => z * (Real.sqrt (1 / S.m) : ℂ)) h
    simp only [inv_mul_cancel₀ S.sqrt_q_ne_zero] at this
    exact_mod_cast this
  rw [Real.mul_self_sqrt (by positivity)] at h'
  field_simp at h'
  linarith

lemma tendsto_radius (S : SelectedConfiguration) :
    Tendsto (fun n => S.B n ^ 6 / 2) atTop atTop :=
  ((tendsto_pow_atTop (by norm_num)).comp S.tendsto_B).atTop_div_const two_pos

theorem not_tendsto_zero (S : SelectedConfiguration) :
    ¬ Tendsto S.c atTop (𝓝 0) := by
  intro hlim
  have hc0 := S.c_ne_zero
  set sq : ℂ := (Real.sqrt (1 / S.m) : ℂ) with hsq_def
  have hsq : sq ≠ 0 := S.sqrt_q_ne_zero
  -- the rescaled radii `B_n^6 / (2 |c_n|)` tend to infinity
  set r : ℕ → ℝ := fun n => (S.B n ^ 6 / 2) / ‖S.c n‖ with hr_def
  have hr : Tendsto r atTop atTop := by
    have hle : ∀ᶠ n in atTop, S.B n ^ 6 / 2 ≤ r n := by
      have h1 : ∀ᶠ n in atTop, ‖S.c n‖ ≤ 1 := by
        have := hlim.norm
        rw [norm_zero] at this
        exact this.eventually (ge_mem_nhds one_pos)
      filter_upwards [h1] with n hn
      exact le_div_self (by have := S.B_pos n; positivity) (norm_pos_iff.2 (hc0 n)) hn
    exact tendsto_atTop_mono' _ hle S.tendsto_radius
  -- the rescaled pairs `F_n(c_n ζ), G_n(c_n ζ)`
  have hderiv : ∀ n z, deriv (fun ζ => S.c n * ζ) z = S.c n := fun n z =>
    (hasDerivAt_const_mul' _ _).deriv
  have hmarked : ∀ (H : ℂ → ℂ) n b, mult (H ∘ fun ζ => S.c n * ζ) b 0 = mult H b 0 := by
    intro H n b
    rw [mult_comp_of_deriv_ne_zero (by fun_prop) (by rw [hderiv]; exact hc0 n), mul_zero]
  set uₙ : ℕ → ℂ → ℂ := fun n ζ =>
    S.c n * (sq * Complex.exp (S.c n * ζ / 2) / S.k n (S.c n * ζ)) with huₙ_def
  set vₙ : ℕ → ℂ → ℂ := fun n ζ =>
    S.c n * (sq⁻¹ * Complex.exp (-(S.c n * ζ) / 2) / S.k n (S.c n * ζ)) with hvₙ_def
  have hk : ∀ n, ∀ ζ ∈ ball (0 : ℂ) (r n), S.k n (S.c n * ζ) ≠ 0 := fun n ζ hζ =>
    S.k_ne_zero n _ (mapsTo_mul_ball (hc0 n) _ hζ)
  have hkd : ∀ n, DifferentiableOn ℂ (fun ζ => S.k n (S.c n * ζ)) (ball 0 (r n)) := fun n =>
    (S.k_holo n).comp (by fun_prop) (mapsTo_mul_ball (hc0 n) _)
  have hT : ∀ n, ∀ x ∈ ball (0 : ℂ) (r n),
      Tendsto (fun ζ => S.c n * ζ) (𝓝[≠] x) (𝓝[≠] (S.c n * x)) := fun n x _ => by
    simpa using tendsto_affine_nhdsNE (hc0 n) 0 x
  -- uniform convergence of the rescaled coefficients
  have hw : ∀ K, IsCompact K → ∀ δ > 0, ∀ᶠ n in atTop, ∀ ζ ∈ K, ζ ∈ ball (0 : ℂ) (r n) ∧
      ‖S.c n / S.k n (S.c n * ζ) * Complex.exp (S.c n * ζ / 2) - 1‖ ≤ δ ∧
      ‖S.c n / S.k n (S.c n * ζ) * Complex.exp (-(S.c n * ζ) / 2) - 1‖ ≤ δ := by
    intro K hK δ hδ
    obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    set δ' := min 1 (δ / 3) with hδ'_def
    have hδ' : 0 < δ' := by positivity
    have h3 : 3 * δ' ≤ δ := by
      have := min_le_right 1 (δ / 3); linarith
    have hcM : ∀ᶠ n in atTop, ‖S.c n‖ * max M 1 ≤ δ' := by
      have := (hlim.norm.mul_const (max M 1))
      rw [norm_zero, zero_mul] at this
      exact this.eventually (ge_mem_nhds hδ')
    filter_upwards [hcM, S.uniform.1 δ' hδ', hr.eventually_gt_atTop M] with n hn1 hn2 hn3 ζ hζ
    have hζb : ζ ∈ ball (0 : ℂ) (r n) := by
      simpa using (hM ζ hζ).trans_lt hn3
    have hsmall : ‖S.c n * ζ / 2‖ ≤ 1 := by
      rw [norm_div, norm_mul, Complex.norm_two]
      have : ‖S.c n‖ * ‖ζ‖ ≤ ‖S.c n‖ * max M 1 :=
        mul_le_mul_of_nonneg_left ((hM ζ hζ).trans (le_max_left _ _)) (norm_nonneg _)
      have : δ' ≤ 1 := min_le_left _ _
      linarith
    have hexp : ∀ σ : ℂ, ‖σ‖ = ‖S.c n * ζ / 2‖ → ‖Complex.exp σ - 1‖ ≤ δ' := by
      intro σ hσ
      refine (Complex.norm_exp_sub_one_le (hσ ▸ hsmall)).trans ?_
      rw [hσ, norm_div, norm_mul, Complex.norm_two]
      have : ‖S.c n‖ * ‖ζ‖ ≤ ‖S.c n‖ * max M 1 :=
        mul_le_mul_of_nonneg_left ((hM ζ hζ).trans (le_max_left _ _)) (norm_nonneg _)
      linarith
    have hk1 := (hn2 _ (mapsTo_mul_ball (hc0 n) _ hζb)).2
    refine ⟨hζb, ?_, ?_⟩
    · exact (norm_mul_sub_one_le hk1 (hexp _ rfl) (min_le_left _ _)).trans h3
    · refine (norm_mul_sub_one_le hk1 (hexp _ ?_) (min_le_left _ _)).trans h3
      rw [neg_div, norm_neg]
  obtain ⟨f, g, hP, hfU, hgV, hdef⟩ := limit_extraction (u := fun _ => sq) (v := fun _ => sq⁻¹)
    S.two_le_m hr (fun n => (S.pair n).comp_mul_ball (hc0 n))
    (fun n => (hmarked _ n _).trans (S.marked_F n)) (fun n => (hmarked _ n _).trans (S.marked_G n))
    (uₙ := uₙ) (vₙ := vₙ)
    (fun n => ((by fun_prop : Differentiable ℂ fun ζ => sq * Complex.exp (S.c n * ζ / 2))
      |>.differentiableOn.div (hkd n) (hk n)).const_mul _)
    (fun n => ((by fun_prop : Differentiable ℂ fun ζ => sq⁻¹ * Complex.exp (-(S.c n * ζ) / 2))
      |>.differentiableOn.div (hkd n) (hk n)).const_mul _)
    (fun n ζ hζ => by
      simp only [huₙ_def]
      exact mul_ne_zero (hc0 n) (div_ne_zero (mul_ne_zero hsq (Complex.exp_ne_zero _))
        (hk n ζ hζ)))
    (fun n ζ hζ => by
      simp only [hvₙ_def]
      exact mul_ne_zero (hc0 n) (div_ne_zero (mul_ne_zero (inv_ne_zero hsq)
        (Complex.exp_ne_zero _)) (hk n ζ hζ)))
    (fun n => by
      filter_upwards [codiscreteWithin_comp ((S.coeff_U n).and
        (MeromorphicOn.eventually_codiscreteWithin_analyticAt _ (S.pair n).nonconst_f.1))
        (mapsTo_mul_ball (hc0 n) _) (hT n)] with ζ hζ
      rw [auxU_comp (h := fun ζ => S.c n * ζ) hζ.2.differentiableAt (by fun_prop), hderiv,
        hζ.1])
    (fun n => by
      filter_upwards [codiscreteWithin_comp ((S.coeff_V n).and
        (MeromorphicOn.eventually_codiscreteWithin_analyticAt _ (S.pair n).nonconst_g.1))
        (mapsTo_mul_ball (hc0 n) _) (hT n)] with ζ hζ
      rw [auxV_comp (h := fun ζ => S.c n * ζ) hζ.2.differentiableAt (by fun_prop), hderiv,
        hζ.1])
    (differentiable_const _) (differentiable_const _) (fun _ => hsq) (fun _ => inv_ne_zero hsq)
    (tendstoLocallyUniformly_of_mul_one continuous_const fun K hK δ hδ => by
      filter_upwards [hw K hK δ hδ] with n hn ζ hζ
      obtain ⟨-, h1, -⟩ := hn ζ hζ
      exact ⟨by simp only [huₙ_def]; ring, h1⟩)
    (tendstoLocallyUniformly_of_mul_one continuous_const fun K hK δ hδ => by
      filter_upwards [hw K hK δ hδ] with n hn ζ hζ
      obtain ⟨-, -, h2⟩ := hn ζ hζ
      exact ⟨by simp only [hvₙ_def]; ring, h2⟩)
    (fun s hs => absurd hs S.sqrt_q_ne_inv)
  -- the limit pair has constant auxiliary ratio, contradicting Lemma 4.10
  have hΦ : meromorphicOrderAt (fun w => auxPhi S.a f g w - sq / sq⁻¹) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [eventually_nhdsNE_of_codiscrete (hfU.and hgV) 0] with w hw
    simp only [auxPhi, hw.1, hw.2, sub_self]
  exact hdef.2.2 (constant_ratio hP ⟨_, 0, hΦ⟩ S.j 0 (mem_univ 0))

/-- **Lemma 10.5** (exclusion of a finite nonzero coefficient limit). -/
theorem not_tendsto_ne_zero (S : SelectedConfiguration) {c : ℂ} (hc : c ≠ 0) :
    ¬ Tendsto S.c atTop (𝓝 c) := by
  intro hlim
  have hc0 := S.c_ne_zero
  set q : ℝ := 1 / S.m with hq_def
  have hq : 0 < q := by have := S.m_pos; positivity
  set sq : ℂ := (Real.sqrt q : ℂ) with hsq_def
  have hsq : sq ≠ 0 := S.sqrt_q_ne_zero
  set r : ℕ → ℝ := fun n => S.B n ^ 6 / 2 with hr_def
  set uₙ : ℕ → ℂ → ℂ := fun n s => sq * Complex.exp (s / 2) / S.k n s with huₙ_def
  set vₙ : ℕ → ℂ → ℂ := fun n s => sq⁻¹ * Complex.exp (-s / 2) / S.k n s with hvₙ_def
  set u : ℂ → ℂ := fun s => c⁻¹ * sq * Complex.exp (s / 2) with hu_def
  set v : ℂ → ℂ := fun s => c⁻¹ * sq⁻¹ * Complex.exp (-s / 2) with hv_def
  -- uniform convergence of `w_n(s) = (c / c_n) (c_n / k_n(s))` to `1`
  have hw : ∀ K, IsCompact K → ∀ δ > 0, ∀ᶠ n in atTop, ∀ s ∈ K, s ∈ ball (0 : ℂ) (r n) ∧
      ‖c / S.c n * (S.c n / S.k n s) - 1‖ ≤ δ := by
    intro K hK δ hδ
    obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    set δ' := min 1 (δ / 3) with hδ'_def
    have hδ' : 0 < δ' := by positivity
    have h3 : 3 * δ' ≤ δ := by
      have := min_le_right 1 (δ / 3); linarith
    have h1 : ∀ᶠ n in atTop, ‖c / S.c n - 1‖ ≤ δ' := by
      have h := (((tendsto_const_nhds (x := c)).div hlim hc).sub_const 1).norm
      rw [div_self hc, sub_self, norm_zero] at h
      exact h.eventually (ge_mem_nhds hδ')
    filter_upwards [h1, S.uniform.1 δ' hδ', S.tendsto_radius.eventually_gt_atTop M]
      with n hn1 hn2 hn3 s hs
    have hsb : s ∈ ball (0 : ℂ) (r n) := by
      simpa using (hM s hs).trans_lt hn3
    exact ⟨hsb, (norm_mul_sub_one_le hn1 (hn2 s hsb).2 (min_le_left _ _)).trans h3⟩
  have hφ : (fun w => u w / v w) = fun w => (q : ℂ) * Complex.exp w := by
    funext w
    have hsq2 : sq * sq = q := by
      rw [hsq_def, ← Complex.ofReal_mul, Real.mul_self_sqrt hq.le]
    have he : Complex.exp (w / 2) * Complex.exp (w / 2) = Complex.exp w := by
      rw [← Complex.exp_add]; ring_nf
    have hne : Complex.exp (w / 2) ≠ 0 := Complex.exp_ne_zero _
    simp only [hu_def, hv_def, neg_div, Complex.exp_neg]
    rw [← he, ← hsq2]
    field_simp
  obtain ⟨f, g, hP, hfU, hgV, hdef⟩ := limit_extraction (u := u) (v := v)
    S.two_le_m S.tendsto_radius S.pair S.marked_F S.marked_G (uₙ := uₙ) (vₙ := vₙ)
    (fun n => (by fun_prop : Differentiable ℂ fun s => sq * Complex.exp (s / 2))
      |>.differentiableOn.div (S.k_holo n) (S.k_ne_zero n))
    (fun n => (by fun_prop : Differentiable ℂ fun s => sq⁻¹ * Complex.exp (-s / 2))
      |>.differentiableOn.div (S.k_holo n) (S.k_ne_zero n))
    (fun n s hs => div_ne_zero (mul_ne_zero hsq (Complex.exp_ne_zero _)) (S.k_ne_zero n s hs))
    (fun n s hs => div_ne_zero (mul_ne_zero (inv_ne_zero hsq) (Complex.exp_ne_zero _))
      (S.k_ne_zero n s hs))
    S.coeff_U S.coeff_V (by fun_prop) (by fun_prop)
    (fun s => by simp [hu_def, hc, hsq, Complex.exp_ne_zero])
    (fun s => by simp [hv_def, hc, hsq, Complex.exp_ne_zero])
    (tendstoLocallyUniformly_of_mul_one (by fun_prop) fun K hK δ hδ => by
      filter_upwards [hw K hK δ hδ] with n hn s hs
      obtain ⟨hsb, h1⟩ := hn s hs
      refine ⟨?_, h1⟩
      have := S.k_ne_zero n s hsb
      simp only [huₙ_def, hu_def]
      field_simp [hc0 n])
    (tendstoLocallyUniformly_of_mul_one (by fun_prop) fun K hK δ hδ => by
      filter_upwards [hw K hK δ hδ] with n hn s hs
      obtain ⟨hsb, h1⟩ := hn s hs
      refine ⟨?_, h1⟩
      have := S.k_ne_zero n s hsb
      simp only [hvₙ_def, hv_def]
      field_simp [hc0 n])
    (fun s _ => by
      rw [hφ, ((Complex.hasDerivAt_exp s).const_mul (q : ℂ)).deriv]
      exact mul_ne_zero (by exact_mod_cast hq.ne') (Complex.exp_ne_zero _))
  exact hP.not_isDefect_of_aux hc hq hfU hgV S.j 0 hdef

/-- **Lemma 10.6**, after the choice of a convergent phase: if `|c_n| → ∞` and
`|c_n| / c_n → ω`, the selected configuration contradicts Lemma 7.14. -/
theorem not_tendsto_infty_of_phase (S : SelectedConfiguration)
    (hlim : Tendsto (fun n => ‖S.c n‖) atTop atTop) {ω : ℂ} (hω : ω ≠ 0)
    (hphase : Tendsto (fun n => (‖S.c n‖ : ℂ) / S.c n) atTop (𝓝 ω)) : False := by
  have hc0 := S.c_ne_zero
  set sq : ℂ := (Real.sqrt (1 / S.m) : ℂ) with hsq_def
  have hsq : sq ≠ 0 := S.sqrt_q_ne_zero
  set ε : ℕ → ℝ := fun n => ‖S.c n‖⁻¹ with hε_def
  have hε_pos : ∀ n, 0 < ε n := fun n => inv_pos.2 (norm_pos_iff.2 (hc0 n))
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlim
  set Ω : ℕ → Set ℂ := fun n => Metric.ball 0 (S.B n ^ 6 / 2) with hΩ_def
  set uₙ : ℕ → ℂ → ℂ := fun n s => sq * Complex.exp (s / 2) / S.k n s with huₙ_def
  set vₙ : ℕ → ℂ → ℂ := fun n s => sq⁻¹ * Complex.exp (-s / 2) / S.k n s with hvₙ_def
  -- the rectangles lie in the disks
  have hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n := by
    intro R hR
    have h1 : ∀ᶠ n in atTop, 1 ≤ ‖S.c n‖ := hlim.eventually_ge_atTop 1
    have h2 : ∀ᶠ n in atTop, 1 ≤ S.B n := S.tendsto_B.eventually_ge_atTop 1
    have h3 : ∀ᶠ n in atTop, 4 * R + 40 ≤ S.B n ^ 4 :=
      ((tendsto_pow_atTop (by norm_num)).comp S.tendsto_B).eventually_ge_atTop _
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3 z hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hlog : Real.log (1 / ε n) ≤ 9 * S.B n ^ 2 := by
      simp only [hε_def, one_div, inv_inv]
      exact (le_abs_self _).trans (S.uniform.2 n)
    have hlog0 : 0 ≤ Real.log (1 / ε n) := by
      simp only [hε_def, one_div, inv_inv]
      exact Real.log_nonneg hn1
    have hre : |z.re| ≤ 2 * Real.log (1 / ε n) + R := by
      rw [abs_le]; constructor <;> linarith
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    simp only [hΩ_def, Metric.mem_ball, dist_zero_right]
    have hB2 : 1 ≤ S.B n ^ 2 := one_le_pow₀ hn2
    have : S.B n ^ 6 / 2 = S.B n ^ 2 * S.B n ^ 4 / 2 := by ring
    nlinarith
  -- uniform control of `(ω_n / ω) (c_n / k_n)`
  have hw : ∀ δ > 0, ∀ᶠ n in atTop, ∀ s ∈ Ω n,
      ‖(‖S.c n‖ : ℂ) / S.c n / ω * (S.c n / S.k n s) - 1‖ ≤ δ := by
    intro δ hδ
    set δ' := min 1 (δ / 3) with hδ'_def
    have hδ' : 0 < δ' := by positivity
    have h3 : 3 * δ' ≤ δ := by
      have := min_le_right 1 (δ / 3); linarith
    have h1 : ∀ᶠ n in atTop, ‖(‖S.c n‖ : ℂ) / S.c n / ω - 1‖ ≤ δ' := by
      have h := ((hphase.div_const ω).sub_const 1).norm
      rw [div_self hω, sub_self, norm_zero] at h
      exact h.eventually (ge_mem_nhds hδ')
    filter_upwards [h1, S.uniform.1 δ' hδ'] with n hn1 hn2 s hs
    exact (norm_mul_sub_one_le hn1 (hn2 s hs).2 (min_le_left _ _)).trans h3
  have hprof : ∀ (A : ℂ) (σ : ℂ → ℂ), A ≠ 0 → (∀ s, σ s ≠ 0) → ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ s ∈ Ω n, ‖A * σ s / S.k n s / (ε n * (ω * A) * σ s) - 1‖ ≤ δ := by
    intro A σ hA hσ δ hδ
    filter_upwards [hw δ hδ] with n hn s hs
    convert hn s hs using 2
    have hk := S.k_ne_zero n s hs
    have hcn : (‖S.c n‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 (hc0 n)).ne'
    simp only [hε_def, Complex.ofReal_inv]
    field_simp [hσ s, hc0 n]
  have hAB : (ω * sq) / (ω * sq⁻¹) = 1 / (S.m : ℂ) := by
    have hm : (S.m : ℂ) ≠ 0 := by exact_mod_cast (by have := S.two_le_m; omega : S.m ≠ 0)
    have hsq2 : sq * sq = 1 / (S.m : ℂ) := by
      rw [hsq_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (by have := S.m_pos; positivity)]
      push_cast; ring
    rw [← hsq2]; field_simp
  refine transport (Ω := Ω) (ε := ε) (A₀ := ω * sq) (B₀ := ω * sq⁻¹) (uₙ := uₙ) (vₙ := vₙ)
    S.two_le_m (fun n => Metric.isOpen_ball) S.pair S.marked_F S.marked_G hε_pos hε
    (mul_ne_zero hω hsq) (mul_ne_zero hω (inv_ne_zero hsq)) hAB
    (fun n => (by fun_prop : Differentiable ℂ fun s => sq * Complex.exp (s / 2))
      |>.differentiableOn.div (S.k_holo n) (S.k_ne_zero n))
    (fun n => (by fun_prop : Differentiable ℂ fun s => sq⁻¹ * Complex.exp (-s / 2))
      |>.differentiableOn.div (S.k_holo n) (S.k_ne_zero n))
    S.coeff_U S.coeff_V hrect ?_ ?_
  · intro R hR δ hδ
    filter_upwards [hrect R hR, hprof sq (fun z => Complex.exp (z / 2)) hsq
      (fun _ => Complex.exp_ne_zero _) δ hδ] with n hn1 hn2 z hz
    simpa [huₙ_def, mul_assoc] using hn2 z (hn1 hz)
  · intro R hR δ hδ
    filter_upwards [hrect R hR, hprof sq⁻¹ (fun z => Complex.exp (-z / 2)) (inv_ne_zero hsq)
      (fun _ => Complex.exp_ne_zero _) δ hδ] with n hn1 hn2 z hz
    simpa [hvₙ_def, mul_assoc] using hn2 z (hn1 hz)

/-- **Lemma 10.6** (exclusion of an unbounded coefficient). -/
theorem not_tendsto_infty (S : SelectedConfiguration) :
    ¬ Tendsto (fun n => ‖S.c n‖) atTop atTop := by
  intro hlim
  have hc0 := S.c_ne_zero
  -- a convergent subsequence of the phases `|c_n| / c_n` on the unit circle
  have hnorm : ∀ n, ‖(‖S.c n‖ : ℂ) / S.c n‖ = 1 := fun n => by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hc0 n))]
  obtain ⟨ω, -, φ, hφ, hphase⟩ := tendsto_subseq_of_bounded
    (x := fun n => (‖S.c n‖ : ℂ) / S.c n) (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1))
    (fun n => Metric.mem_closedBall.2 (by rw [dist_zero_right, hnorm n]))
  have hω : ‖ω‖ = 1 := by
    have h := hphase.norm
    simp only [Function.comp_def, hnorm] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  exact (S.comp φ hφ).not_tendsto_infty_of_phase (hlim.comp hφ.tendsto_atTop)
    (norm_ne_zero_iff.1 (by rw [hω]; norm_num)) hphase

/-- No selected configuration exists: the sequence `c_n` has a convergent subsequence in the
Riemann sphere, and its three possible kinds of limits are excluded by Lemmas 10.4–10.6. -/
theorem false (S : SelectedConfiguration) : False := by
  by_cases hb : ∃ C, ∀ n, ‖S.c n‖ ≤ C
  · obtain ⟨C, hC⟩ := hb
    obtain ⟨c, -, φ, hφ, hlim⟩ :=
      tendsto_subseq_of_bounded (x := S.c) (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := C))
        (fun n => by simpa using hC n)
    by_cases hc : c = 0
    · subst hc
      exact (S.comp φ hφ).not_tendsto_zero hlim
    · exact (S.comp φ hφ).not_tendsto_ne_zero hc hlim
  · push_neg at hb
    -- extract a subsequence with `‖c_{φ n}‖ → ∞`
    have hfreq : ∀ C : ℝ, ∃ᶠ n in atTop, C ≤ ‖S.c n‖ := by
      intro C
      rw [Filter.frequently_atTop]
      intro N
      by_contra hcon
      push_neg at hcon
      obtain ⟨n, hn⟩ := hb (max C (Finset.sup' (Finset.range (N + 1)) (by simp)
        (fun n => ‖S.c n‖)))
      rcases lt_or_ge n N with h | h
      · have : ‖S.c n‖ ≤ Finset.sup' (Finset.range (N + 1)) (by simp) (fun n => ‖S.c n‖) :=
          Finset.le_sup' (fun n => ‖S.c n‖) (Finset.mem_range.2 (by omega))
        linarith [le_max_right C (Finset.sup' (Finset.range (N + 1)) (by simp)
          (fun n => ‖S.c n‖))]
      · linarith [hcon n h, le_max_left C (Finset.sup' (Finset.range (N + 1)) (by simp)
          (fun n => ‖S.c n‖))]
    have hlim : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => ‖S.c (φ n)‖) atTop atTop := by
      have : ∀ k : ℕ, ∃ᶠ n in atTop, (k : ℝ) ≤ ‖S.c n‖ := fun k => hfreq k
      obtain ⟨φ, hφ, hφk⟩ := Filter.extraction_forall_of_frequently this
      refine ⟨φ, hφ, ?_⟩
      refine tendsto_atTop.2 fun C => ?_
      obtain ⟨k, hk⟩ := exists_nat_ge C
      filter_upwards [eventually_ge_atTop k] with n hn
      exact hk.trans ((Nat.cast_le.2 hn).trans (hφk n))
    obtain ⟨φ, hφ, hl⟩ := hlim
    exact (S.comp φ hφ).not_tendsto_infty hl

end SelectedConfiguration

end ThreeIM
