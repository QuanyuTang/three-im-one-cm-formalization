module

/-
Copyright (c) 2026 Yixin He, Quanyu Tang, Jun Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original source authors: Yixin He, Quanyu Tang, Jun Wang
Project authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/
public import RequestProject.ThreeIM.Basic

/-!
# Persistence of common zero multiplicities

Holomorphic pairs with equal finite zero orders retain that equality under
locally uniform convergence, provided both limit germs are finite and nonzero.
Normal-form quotients are analytic units. Compact circle bounds pass inside
by the maximum modulus principle, then exclude poles of both limiting ratios.
No Rouché or argument-principle theorem is assumed.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem mero_order_div_eq_zero {f g : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z)
    (heq : meromorphicOrderAt f z = meromorphicOrderAt g z)
    (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    meromorphicOrderAt (fun w => f w / g w) z = 0 := by
  have hdiv : (fun w => f w / g w) = f * g⁻¹ := by
    funext w
    exact div_eq_mul_inv _ _
  rw [hdiv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, ← heq]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfinite
  rw [← hn]
  simp

/-- Equal finite meromorphic orders make the normal-form quotient an
analytic unit, including at common zeros. -/
theorem analytic_unit_nf_quotient {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : MeromorphicOn f Ω) (hg : MeromorphicOn g Ω)
    (heq : ∀ z ∈ Ω, meromorphicOrderAt f z = meromorphicOrderAt g z)
    (hfinite : ∀ z ∈ Ω, meromorphicOrderAt f z ≠ ⊤) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (fun w => f w / g w) Ω) Ω ∧
      ∀ z ∈ Ω, toMeromorphicNFOn (fun w => f w / g w) Ω z ≠ 0 := by
  have hfg : MeromorphicOn (fun w => f w / g w) Ω := hf.div hg
  have horder : ∀ z ∈ Ω,
      meromorphicOrderAt (toMeromorphicNFOn (fun w => f w / g w) Ω) z = 0 := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hfg hz]
    exact mero_order_div_eq_zero (hf z hz) (hg z hz) (heq z hz) (hfinite z hz)
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun w => f w / g w) Ω
  constructor
  · intro z hz
    exact (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 (by rw [horder z hz])
  · intro z hz
    exact (hnf hz).meromorphicOrderAt_eq_zero_iff.1 (horder z hz)

theorem nf_quotient_eq_at_of_ne_zero {f g : ℂ → ℂ} {Ω : Set ℂ} {z : ℂ}
    (hfg : MeromorphicOn (fun w => f w / g w) Ω) (hz : z ∈ Ω)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    toMeromorphicNFOn (fun w => f w / g w) Ω z = f z / g z := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hfg hz]
  have ha : AnalyticAt ℂ (fun w => f w / g w) z := hf.div hg hgz
  have heq : toMeromorphicNFAt (fun w => f w / g w) z = (fun w => f w / g w) :=
    toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt
  exact congrFun heq z

/-- A meromorphic germ bounded on a punctured neighborhood cannot be a pole. -/
theorem mero_order_nonneg_of_eventually_norm_le {f : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (hb : ∀ᶠ w in 𝓝[≠] z, ‖f w‖ ≤ C) : 0 ≤ meromorphicOrderAt f z := by
  by_contra hnot
  have hneg : meromorphicOrderAt f z < 0 := lt_of_not_ge hnot
  have htop : Tendsto (fun w => ‖f w‖) (𝓝[≠] z) atTop :=
    tendsto_norm_atTop_iff_cobounded.2 (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)
  obtain ⟨w, hle, hgt⟩ := (hb.and (htop.eventually (eventually_gt_atTop C))).exists
  exact (not_lt_of_ge hle) hgt

/-- Bounded quotients in both directions force equality of finite orders. -/
theorem mero_order_eq_of_bounded_ratios {f g : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z)
    (hff : meromorphicOrderAt f z ≠ ⊤) (hgf : meromorphicOrderAt g z ≠ ⊤)
    {C D : ℝ} (hC : ∀ᶠ w in 𝓝[≠] z, ‖f w / g w‖ ≤ C)
    (hD : ∀ᶠ w in 𝓝[≠] z, ‖g w / f w‖ ≤ D) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hff
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hgf
  have hdiv : (fun w => f w / g w) = f * g⁻¹ := by
    funext w
    exact div_eq_mul_inv _ _
  have hrev : (fun w => g w / f w) = g * f⁻¹ := by
    funext w
    exact div_eq_mul_inv _ _
  have h₁ := mero_order_nonneg_of_eventually_norm_le hC
  have h₂ := mero_order_nonneg_of_eventually_norm_le hD
  rw [hdiv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, ← ha, ← hb] at h₁
  rw [hrev, meromorphicOrderAt_mul hg hf.inv, meromorphicOrderAt_inv, ← ha, ← hb] at h₂
  have h₁' : (0 : ℤ) ≤ a - b := by exact_mod_cast h₁
  have h₂' : (0 : ℤ) ≤ b - a := by exact_mod_cast h₂
  have hab : a = b := by omega
  rw [← ha, ← hb, hab]

/-- The maximum modulus principle transfers an actual boundary ratio bound
to the normal-form quotient at every point inside the circle. -/
theorem nf_quotient_norm_le_of_boundary {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (heq : ∀ w ∈ Ω, meromorphicOrderAt f w = meromorphicOrderAt g w)
    (hfinite : ∀ w ∈ Ω, meromorphicOrderAt f w ≠ ⊤)
    (hsub : closedBall z r ⊆ Ω)
    (hboundary : ∀ w ∈ sphere z r, g w ≠ 0 ∧ ‖f w / g w‖ ≤ C) :
    ∀ w ∈ closedBall z r, ‖toMeromorphicNFOn (fun v => f v / g v) Ω w‖ ≤ C := by
  have hfg : MeromorphicOn (fun w => f w / g w) Ω := hf.meromorphicOn.div hg.meromorphicOn
  have hQ := (analytic_unit_nf_quotient hf.meromorphicOn hg.meromorphicOn heq hfinite).1
  have hDiff : DiffContOnCl ℂ (toMeromorphicNFOn (fun v => f v / g v) Ω) (ball z r) := by
    refine ⟨?_, ?_⟩
    · exact hQ.differentiableOn.mono (ball_subset_closedBall.trans hsub)
    · rw [closure_ball z hr.ne']
      exact hQ.continuousOn.mono hsub
  intro w hw
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hDiff
  · intro v hv
    have hvs : v ∈ sphere z r := by simpa only [frontier_ball z hr.ne'] using hv
    have hvΩ := hsub (sphere_subset_closedBall hvs)
    rw [nf_quotient_eq_at_of_ne_zero hfg hvΩ (hf v hvΩ) (hg v hvΩ) (hboundary v hvs).1]
    exact (hboundary v hvs).2
  · simpa only [closure_ball z hr.ne'] using hw

/-- Uniform convergence bounds ratios on a compact set where the limiting
denominator does not vanish. The numerator may vanish. -/
theorem uniform_ratio_bound_of_compact {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hgnz : ∀ w ∈ K, g w ≠ 0)
    (hF : TendstoUniformlyOn F f atTop K) (hG : TendstoUniformlyOn G g atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ w ∈ K, G n w ≠ 0 ∧ ‖F n w / G n w‖ ≤ C := by
  obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn hKn hg.norm
  obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn hKn hf.norm
  let δ : ℝ := ‖g x‖ / 2
  let B : ℝ := ‖f y‖ + 1
  have hδ : 0 < δ := half_pos (norm_pos_iff.2 (hgnz x hx))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B / δ, div_nonneg hB hδ.le, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF 1 zero_lt_one,
    Metric.tendstoUniformlyOn_iff.mp hG δ hδ] with n hFn hGn w hw
  have hFclose := hFn w hw
  have hGclose := hGn w hw
  rw [dist_eq_norm] at hFclose hGclose
  have hFbound : ‖F n w‖ ≤ B := by
    have htriangle := norm_sub_norm_le (F n w) (f w)
    have hmax : ‖f w‖ ≤ ‖f y‖ := hymax hw
    dsimp only [B]
    linarith [norm_sub_rev (F n w) (f w)]
  have hGlower : δ ≤ ‖G n w‖ := by
    have htriangle := norm_sub_norm_le (g w) (G n w)
    have hmin : ‖g x‖ ≤ ‖g w‖ := hxmin hw
    dsimp only [δ] at *
    linarith [norm_sub_rev (G n w) (g w)]
  have hGpos : 0 < ‖G n w‖ := hδ.trans_le hGlower
  refine ⟨norm_pos_iff.1 hGpos, ?_⟩
  rw [norm_div]
  apply (div_le_iff₀ hGpos).2
  apply hFbound.trans
  calc
    B = (B / δ) * δ := by field_simp [hδ.ne']
    _ ≤ (B / δ) * ‖G n w‖ :=
      mul_le_mul_of_nonneg_left hGlower (div_nonneg hB hδ.le)

/-- Bounds for the unit normal-form quotients pass to their pointwise limit
at all points where the limiting denominator is nonzero. -/
theorem ratio_limit_bound_from_boundary {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    {Ω : Set ℂ} {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hseq : ∀ᶠ n in atTop, AnalyticOnNhd ℂ (F n) Ω ∧ AnalyticOnNhd ℂ (G n) Ω ∧
      (∀ w ∈ Ω, meromorphicOrderAt (F n) w = meromorphicOrderAt (G n) w) ∧
      ∀ w ∈ Ω, meromorphicOrderAt (F n) w ≠ ⊤)
    (hsub : closedBall z r ⊆ Ω)
    (hF : TendstoUniformlyOn F f atTop (closedBall z r))
    (hG : TendstoUniformlyOn G g atTop (closedBall z r))
    (hcircle : ∀ᶠ n in atTop, ∀ w ∈ sphere z r,
      G n w ≠ 0 ∧ ‖F n w / G n w‖ ≤ C) :
    ∀ w ∈ closedBall z r, g w ≠ 0 → ‖f w / g w‖ ≤ C := by
  have hinside : ∀ᶠ n in atTop, ∀ w ∈ closedBall z r,
      ‖toMeromorphicNFOn (fun v => F n v / G n v) Ω w‖ ≤ C := by
    filter_upwards [hseq, hcircle] with n hn hc
    exact nf_quotient_norm_le_of_boundary hr hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 hsub hc
  intro w hw hgw
  have hGn : ∀ᶠ n in atTop, G n w ≠ 0 :=
    (hG.tendsto_at hw).eventually (eventually_ne_nhds hgw)
  have hbound : ∀ᶠ n in atTop, ‖F n w / G n w‖ ≤ C := by
    filter_upwards [hseq, hinside, hGn] with n hn hq hgn
    have hwΩ := hsub hw
    have heq := nf_quotient_eq_at_of_ne_zero
      (hn.1.meromorphicOn.div hn.2.1.meromorphicOn) hwΩ (hn.1 w hwΩ) (hn.2.1 w hwΩ) hgn
    have hqw := hq w hw
    rw [heq] at hqw
    exact hqw
  exact le_of_tendsto ((hF.tendsto_at hw).div (hG.tendsto_at hw) hgw).norm hbound

/-- Equal finite zero orders persist under holomorphic convergence. A
closed disk is used only to express the compact uniform bounds explicitly. -/
theorem orders_eq_of_uniform_cm {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hseq : ∀ᶠ n in atTop,
      AnalyticOnNhd ℂ (F n) (closedBall z R) ∧
      AnalyticOnNhd ℂ (G n) (closedBall z R) ∧
      (∀ w ∈ closedBall z R, meromorphicOrderAt (F n) w = meromorphicOrderAt (G n) w) ∧
      ∀ w ∈ closedBall z R, meromorphicOrderAt (F n) w ≠ ⊤)
    (hF : TendstoUniformlyOn F f atTop (closedBall z R))
    (hG : TendstoUniformlyOn G g atTop (closedBall z R))
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hff : meromorphicOrderAt f z ≠ ⊤) (hgf : meromorphicOrderAt g z ≠ ⊤) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  have hnzf : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf.meromorphicAt).1 hff
  have hnzg : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hg.meromorphicAt).1 hgf
  obtain ⟨ρf, hρf, hρfa, hρfnz⟩ : ∃ ρ > 0,
      AnalyticOnNhd ℂ f (closedBall z ρ) ∧
        ∀ w ∈ closedBall z ρ, w ≠ z → f w ≠ 0 := by
    obtain ⟨ρ, hρ, hball⟩ := nhds_basis_closedBall.mem_iff.mp
      (hf.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp hnzf))
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro w hw
      exact (hball hw).1
    · intro w hw hwz
      exact (hball hw).2 (by simpa only [mem_compl_iff, mem_singleton_iff] using hwz)
  obtain ⟨ρg, hρg, hρga, hρgnz⟩ : ∃ ρ > 0,
      AnalyticOnNhd ℂ g (closedBall z ρ) ∧
        ∀ w ∈ closedBall z ρ, w ≠ z → g w ≠ 0 := by
    obtain ⟨ρ, hρ, hball⟩ := nhds_basis_closedBall.mem_iff.mp
      (hg.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp hnzg))
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro w hw
      exact (hball hw).1
    · intro w hw hwz
      exact (hball hw).2 (by simpa only [mem_compl_iff, mem_singleton_iff] using hwz)
  let r : ℝ := min ρf (min ρg R)
  have hr : 0 < r := lt_min hρf (lt_min hρg hR)
  have hrf : closedBall z r ⊆ closedBall z ρf :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hrg : closedBall z r ⊆ closedBall z ρg :=
    closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : closedBall z r ⊆ closedBall z R :=
    closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _))
  have hcircle : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hfc : ContinuousOn f (sphere z r) :=
    hρfa.continuousOn.mono (sphere_subset_closedBall.trans hrf)
  have hgc : ContinuousOn g (sphere z r) :=
    hρga.continuousOn.mono (sphere_subset_closedBall.trans hrg)
  have hfcnz : ∀ w ∈ sphere z r, f w ≠ 0 := fun w hw =>
    hρfnz w (hrf (sphere_subset_closedBall hw)) (ne_of_mem_sphere hw hr.ne')
  have hgcnz : ∀ w ∈ sphere z r, g w ≠ 0 := fun w hw =>
    hρgnz w (hrg (sphere_subset_closedBall hw)) (ne_of_mem_sphere hw hr.ne')
  obtain ⟨C, _, hC⟩ := uniform_ratio_bound_of_compact (isCompact_sphere z r) hcircle
    hfc hgc hgcnz (hF.mono (sphere_subset_closedBall.trans hrR))
      (hG.mono (sphere_subset_closedBall.trans hrR))
  obtain ⟨D, _, hD⟩ := uniform_ratio_bound_of_compact (isCompact_sphere z r) hcircle
    hgc hfc hfcnz (hG.mono (sphere_subset_closedBall.trans hrR))
      (hF.mono (sphere_subset_closedBall.trans hrR))
  have hseqrev : ∀ᶠ n in atTop,
      AnalyticOnNhd ℂ (G n) (closedBall z R) ∧
      AnalyticOnNhd ℂ (F n) (closedBall z R) ∧
      (∀ w ∈ closedBall z R, meromorphicOrderAt (G n) w = meromorphicOrderAt (F n) w) ∧
      ∀ w ∈ closedBall z R, meromorphicOrderAt (G n) w ≠ ⊤ := by
    filter_upwards [hseq] with n hn
    refine ⟨hn.2.1, hn.1, fun w hw => (hn.2.2.1 w hw).symm, fun w hw => ?_⟩
    rw [← hn.2.2.1 w hw]
    exact hn.2.2.2 w hw
  have hCin := ratio_limit_bound_from_boundary hr hseq hrR (hF.mono hrR) (hG.mono hrR) hC
  have hDin := ratio_limit_bound_from_boundary hr hseqrev hrR (hG.mono hrR) (hF.mono hrR) hD
  have hCb : ∀ᶠ w in 𝓝[≠] z, ‖f w / g w‖ ≤ C := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [ball_mem_nhds z hr] with w hw
    intro hne
    have hwne : w ≠ z := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    exact hCin w (ball_subset_closedBall hw) (hρgnz w (hrg (ball_subset_closedBall hw)) hwne)
  have hDb : ∀ᶠ w in 𝓝[≠] z, ‖g w / f w‖ ≤ D := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [ball_mem_nhds z hr] with w hw
    intro hne
    have hwne : w ≠ z := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    exact hDin w (ball_subset_closedBall hw) (hρfnz w (hrf (ball_subset_closedBall hw)) hwne)
  exact mero_order_eq_of_bounded_ratios hf.meromorphicAt hg.meromorphicAt hff hgf hCb hDb

/-- Open-disk, locally uniform form of CM zero-order persistence. All
sequence hypotheses are eventual, as is natural after changing charts. -/
theorem orders_eq_of_locally_uniform_cm {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hseq : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (F n) (ball z R) ∧
      DifferentiableOn ℂ (G n) (ball z R) ∧
      (∀ w ∈ ball z R, meromorphicOrderAt (F n) w = meromorphicOrderAt (G n) w) ∧
      ∀ w ∈ ball z R, meromorphicOrderAt (F n) w ≠ ⊤)
    (hF : TendstoLocallyUniformlyOn F f atTop (ball z R))
    (hG : TendstoLocallyUniformlyOn G g atTop (ball z R))
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hff : meromorphicOrderAt f z ≠ ⊤) (hgf : meromorphicOrderAt g z ≠ ⊤) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  let ρ : ℝ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hsub : closedBall z ρ ⊆ ball z R := closedBall_subset_ball (half_lt_self hR)
  have hcompact : IsCompact (closedBall z ρ) := isCompact_closedBall z ρ
  apply orders_eq_of_uniform_cm (F := F) (G := G) (f := f) (g := g) hρ
  · filter_upwards [hseq] with n hn
    refine ⟨?_, ?_, fun w hw => hn.2.2.1 w (hsub hw), fun w hw => hn.2.2.2 w (hsub hw)⟩
    · intro w hw
      exact hn.1.analyticAt (isOpen_ball.mem_nhds (hsub hw))
    · intro w hw
      exact hn.2.1.analyticAt (isOpen_ball.mem_nhds (hsub hw))
  · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcompact).1 (hF.mono hsub)
  · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcompact).1 (hG.mono hsub)
  · exact hf
  · exact hg
  · exact hff
  · exact hgf

theorem order_eq_of_analytic_zero_mult_eq {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hff : meromorphicOrderAt f z ≠ ⊤) (hgf : meromorphicOrderAt g z ≠ ⊤)
    (hm : mult f ((0 : ℂ) : Sphere) z = mult g ((0 : ℂ) : Sphere) z) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hff
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hgf
  have ha0 : 0 ≤ a := by
    have h := hf.meromorphicOrderAt_nonneg
    rw [← ha] at h
    exact_mod_cast h
  have hb0 : 0 ≤ b := by
    have h := hg.meromorphicOrderAt_nonneg
    rw [← hb] at h
    exact_mod_cast h
  have hm' : (meromorphicOrderAt f z).untop₀.toNat =
      (meromorphicOrderAt g z).untop₀.toNat := by
    change (meromorphicOrderAt (fun w => f w - 0) z).untop₀.toNat =
      (meromorphicOrderAt (fun w => g w - 0) z).untop₀.toNat at hm
    simpa only [sub_zero] using hm
  rw [← ha, ← hb] at hm'
  have hnat : a.toNat = b.toNat := by simpa only [WithTop.untop₀_coe] using hm'
  have hab := congrArg (fun k : ℕ => (k : ℤ)) hnat
  change (a.toNat : ℤ) = (b.toNat : ℤ) at hab
  rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] at hab
  rw [← ha, ← hb, hab]

/-- The same persistence theorem with the project's natural-number zero
multiplicity predicate. Finiteness of both sequence germs is explicit. -/
theorem orders_eq_of_locally_uniform_zero_mult {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hseq : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (F n) (ball z R) ∧
      DifferentiableOn ℂ (G n) (ball z R) ∧
      (∀ w ∈ ball z R, mult (F n) ((0 : ℂ) : Sphere) w = mult (G n) ((0 : ℂ) : Sphere) w) ∧
      ∀ w ∈ ball z R, meromorphicOrderAt (F n) w ≠ ⊤ ∧ meromorphicOrderAt (G n) w ≠ ⊤)
    (hF : TendstoLocallyUniformlyOn F f atTop (ball z R))
    (hG : TendstoLocallyUniformlyOn G g atTop (ball z R))
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hff : meromorphicOrderAt f z ≠ ⊤) (hgf : meromorphicOrderAt g z ≠ ⊤) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  apply orders_eq_of_locally_uniform_cm (F := F) (G := G) hR ?_ hF hG hf hg hff hgf
  filter_upwards [hseq] with n hn
  refine ⟨hn.1, hn.2.1, ?_, fun w hw => (hn.2.2.2 w hw).1⟩
  intro w hw
  exact order_eq_of_analytic_zero_mult_eq
    (hn.1.analyticAt (isOpen_ball.mem_nhds hw))
    (hn.2.1.analyticAt (isOpen_ball.mem_nhds hw))
    (hn.2.2.2 w hw).1 (hn.2.2.2 w hw).2 (hn.2.2.1 w hw)

end ThreeIM
