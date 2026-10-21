module

public import RequestProject.ThreeIM.TwoCMMixedEtaLocal
public import RequestProject.ThreeIM.TwoCMChiCounting

/-! # The mixed auxiliary at a simple CM point and its counting estimates -/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

private lemma mixedEta_cubicP_cyclic (a : Fin 3 → ℂ) (j : Fin 3) (w : ℂ) :
    cubicP a w = (w - a j) * (w - a (j + 1)) * (w - a (j + 2)) := by
  fin_cases j <;> simp [cubicP] <;> ring

private lemma mixedEta_simple_models {h : ℂ → ℂ} {z₀ c : ℂ}
    (hh : MeromorphicAt h z₀)
    (ho : meromorphicOrderAt (fun w => h w - c) z₀ = (1 : ℤ)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ F z₀ ≠ 0 ∧
      h =ᶠ[𝓝[≠] z₀] (fun w => c + (w - z₀) * F w) ∧
      deriv h =ᶠ[𝓝[≠] z₀] (fun w => F w + (w - z₀) * deriv F w) := by
  obtain ⟨F, hFa, hF0, heq⟩ := local_rep hh (m := 1) (by decide) ho
  refine ⟨F, hFa, hF0, ?_, ?_⟩
  · exact heq.mono fun w hw => by simpa only [pow_one] using hw.1
  · exact heq.mono fun w hw => by
      simpa only [Nat.sub_self, pow_zero, Nat.cast_one, one_mul] using hw.2

private lemma mixedEta_simple_limits {h F : ℂ → ℂ} {z₀ c : ℂ}
    (hFa : AnalyticAt ℂ F z₀)
    (hh : h =ᶠ[𝓝[≠] z₀] (fun w => c + (w - z₀) * F w))
    (hd : deriv h =ᶠ[𝓝[≠] z₀] (fun w => F w + (w - z₀) * deriv F w)) :
    Tendsto h (𝓝[≠] z₀) (𝓝 c) ∧ Tendsto (deriv h) (𝓝[≠] z₀) (𝓝 (F z₀)) := by
  have hs : ContinuousAt (fun w : ℂ => w - z₀) z₀ := by fun_prop
  have ht : Tendsto (fun w : ℂ => w - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using hs.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
  have hF : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) :=
    hFa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFd : Tendsto (deriv F) (𝓝[≠] z₀) (𝓝 (deriv F z₀)) :=
    hFa.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun _ : ℂ => c) (𝓝[≠] z₀) (𝓝 c) := tendsto_const_nhds
  constructor
  · simpa using (hC.add (ht.mul hF)).congr' hh.symm
  · simpa using (hF.add (ht.mul hFd)).congr' hd.symm

/-- Both mixed functions vanish at a common simple point over the marked
CM target. The extra target may be any different finite value. -/
theorem twoCM_mixed_tendsto_shared_simple {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) (hab : a j ≠ b)
    {z₀ : ℂ} (hf1 : meromorphicOrderAt (fun w => f w - a j) z₀ = (1 : ℤ))
    (hg1 : meromorphicOrderAt (fun w => g w - a j) z₀ = (1 : ℤ)) :
    Tendsto (twoCMMixedEta a j b f g) (𝓝[≠] z₀) (𝓝 0) ∧
      Tendsto (twoCMMixedTheta a j b f g) (𝓝[≠] z₀) (𝓝 0) := by
  obtain ⟨F, hFa, hF0, hF, hFd⟩ := mixedEta_simple_models (hp.nonconst_f.meromorphic z₀) hf1
  obtain ⟨G, hGa, hG0, hG, hGd⟩ := mixedEta_simple_models (hp.nonconst_g.meromorphic z₀) hg1
  obtain ⟨hflim, hfdlim⟩ := mixedEta_simple_limits hFa hF hFd
  obtain ⟨hglim, hgdlim⟩ := mixedEta_simple_limits hGa hG hGd
  have hjb : j ≠ j + 1 := by fin_cases j <;> decide
  have hjc : j ≠ j + 2 := by fin_cases j <;> decide
  let K : ℂ := (a j - a (j + 1)) * (a j - a (j + 2))
  have hK : K ≠ 0 := mul_ne_zero (sub_ne_zero.2 (hp.injective.ne hjb))
    (sub_ne_zero.2 (hp.injective.ne hjc))
  have hFt : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hFa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGt : Tendsto G (𝓝[≠] z₀) (𝓝 (G z₀)) := hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFne : ∀ᶠ w in 𝓝[≠] z₀, F w ≠ 0 :=
    nhdsWithin_le_nhds (hFa.continuousAt.eventually_ne hF0)
  have hGne : ∀ᶠ w in 𝓝[≠] z₀, G w ≠ 0 :=
    nhdsWithin_le_nhds (hGa.continuousAt.eventually_ne hG0)
  have hratioF : (fun w => (f w - g w) / (f w - a j)) =ᶠ[𝓝[≠] z₀]
      (fun w => (F w - G w) / F w) := by
    filter_upwards [hF, hG, hFne, self_mem_nhdsWithin] with w hwf hwg hfn hwz
    rw [hwf, hwg]
    field_simp [hfn, sub_ne_zero.2 hwz]
    ring
  have hratioG : (fun w => (f w - g w) / (g w - a j)) =ᶠ[𝓝[≠] z₀]
      (fun w => (F w - G w) / G w) := by
    filter_upwards [hF, hG, hGne, self_mem_nhdsWithin] with w hwf hwg hgn hwz
    rw [hwf, hwg]
    field_simp [hgn, sub_ne_zero.2 hwz]
    ring
  have hrFlim := ((hFt.sub hGt).div hFt hF0).congr' hratioF.symm
  have hrGlim := ((hFt.sub hGt).div hGt hG0).congr' hratioG.symm
  have hUf (w : ℂ) : auxU a f g w = (f w - g w) / (f w - a j) * deriv f w /
      ((f w - a (j + 1)) * (f w - a (j + 2))) := by
    simp only [auxU, mixedEta_cubicP_cyclic a j, div_eq_mul_inv, mul_inv_rev]
    ring
  have hVg (w : ℂ) : auxV a f g w = (f w - g w) / (g w - a j) * deriv g w /
      ((g w - a (j + 1)) * (g w - a (j + 2))) := by
    simp only [auxV, mixedEta_cubicP_cyclic a j, div_eq_mul_inv, mul_inv_rev]
    ring
  have hUlim : Tendsto (auxU a f g) (𝓝[≠] z₀) (𝓝 ((F z₀ - G z₀) / K)) := by
    have h := ((hrFlim.mul hfdlim).div
      ((hflim.sub_const (a (j + 1))).mul (hflim.sub_const (a (j + 2)))) hK).congr'
        (Eventually.of_forall fun w => (hUf w).symm)
    convert h using 1
    congr 1
    dsimp [K]
    field_simp [hF0, hK]
  have hVlim : Tendsto (auxV a f g) (𝓝[≠] z₀) (𝓝 ((F z₀ - G z₀) / K)) := by
    have h := ((hrGlim.mul hgdlim).div
      ((hglim.sub_const (a (j + 1))).mul (hglim.sub_const (a (j + 2)))) hK).congr'
        (Eventually.of_forall fun w => (hVg w).symm)
    convert h using 1
    congr 1
    dsimp [K]
    field_simp [hG0, hK]
  have hΨlim : Tendsto (auxPsi a f g) (𝓝[≠] z₀) (𝓝 (((F z₀ - G z₀) / K) ^ 2)) := by
    have hfun : auxPsi a f g = (fun w => auxU a f g w * auxV a f g w) := by
      funext w
      rfl
    rw [hfun]
    simpa only [pow_two] using hUlim.mul hVlim
  have hRF : Tendsto (twoCMRegularTerm a j f) (𝓝[≠] z₀)
      (𝓝 (F z₀ * cAux a j / K)) := by
    have h := (hfdlim.mul ((((hflim.const_mul 3).sub_const (a j)).sub_const (a (j + 1))).sub_const (a (j + 2)))).div
        ((hflim.sub_const (a (j + 1))).mul (hflim.sub_const (a (j + 2)))) hK
    convert h using 1
    congr 1
    dsimp [K, cAux]
    ring
  have hRG : Tendsto (twoCMRegularTerm a j g) (𝓝[≠] z₀)
      (𝓝 (G z₀ * cAux a j / K)) := by
    have h := (hgdlim.mul ((((hglim.const_mul 3).sub_const (a j)).sub_const (a (j + 1))).sub_const (a (j + 2)))).div
        ((hglim.sub_const (a (j + 1))).mul (hglim.sub_const (a (j + 2)))) hK
    convert h using 1
    congr 1
    dsimp [K, cAux]
    ring
  have hEpos : 0 < meromorphicOrderAt (EAux a j f g) z₀ :=
    lt_of_lt_of_le (by decide : (0 : WithTop ℤ) < 1)
      (EAux_order_ge_one_at_shared_simple (hp.nonconst_f.meromorphic z₀)
        (hp.nonconst_g.meromorphic z₀) hp.injective j hf1 hg1)
  have hElim := (tendsto_zero_iff_meromorphicOrderAt_pos
    (meromorphicAt_EAux (hp.nonconst_f.meromorphic z₀) (hp.nonconst_g.meromorphic z₀) a j)).2 hEpos
  have hχlim : Tendsto (twoCMChi a j f g) (𝓝[≠] z₀)
      (𝓝 (-(F z₀ - G z₀) * cAux a j / K)) := by
    have heqχ : twoCMChi a j f g =ᶠ[𝓝[≠] z₀]
        (fun z => EAux a j f g z - (twoCMRegularTerm a j f z - twoCMRegularTerm a j g z)) :=
      codiscrete_iff_nhdsNE.1 (twoCM_chi_eq_EAux_sub_regular hp j) z₀
    have h := (hElim.sub (hRF.sub hRG)).congr' heqχ.symm
    convert h using 1 <;> ring
  have hAb : a j - b ≠ 0 := sub_ne_zero.mpr hab
  constructor
  · have h := hχlim.add (((hUlim.const_mul (cAux a j)).mul
      (hflim.sub_const b)).div (hglim.sub_const b) hAb)
    convert h using 1
    · funext w
      simp only [twoCMMixedEta, Pi.div_apply]
    · congr 1
      field_simp [hAb, hK] <;> ring
  · have h := hχlim.add (((hVlim.const_mul (cAux a j)).mul
      (hglim.sub_const b)).div (hflim.sub_const b) hAb)
    convert h using 1
    · funext w
      simp only [twoCMMixedTheta, Pi.div_apply]
    · congr 1
      field_simp [hAb, hK] <;> ring

theorem twoCM_order_mixedEta_ne_top {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ)
    (hH : ∃ w, meromorphicOrderAt (twoCMMixedEta a j b f g) w ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (twoCMMixedEta a j b f g) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hH
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => twoCM_meromorphic_mixedEta hp j b y) isPreconnected_univ
      (mem_univ w) (mem_univ z) hw

theorem twoCM_finiteFiberDivisor_le_mixedEta {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) (hab : a j ≠ b)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMMixedEta a j b f g) w ≠ ⊤) :
    fiberDivisor f (a j : Sphere) ≤ (MeromorphicOn.divisor (twoCMMixedEta a j b f g) univ)⁺ +
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [fiberDivisor_apply hp.nonconst_f.1,
    MeromorphicOn.divisor_apply (fun x _ => twoCM_meromorphic_mixedEta hp j b x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.meromorphic_auxPsi x) (mem_univ z)]
  have hW0 := posPart_nonneg (meromorphicOrderAt (twoCMMixedEta a j b f g) z).untop₀
  have hΨ0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  by_cases hpos : 0 < mult f (a j : Sphere) z
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | h2
    · have hf1 : meromorphicOrderAt (fun w => f w - a j) z = (1 : ℤ) := by
        simpa only [← h1, Nat.cast_succ, Nat.cast_zero, zero_add] using order_sub_eq_mult hpos
      have hg1 : meromorphicOrderAt (fun w => g w - a j) z = (1 : ℤ) :=
        (twoCM_order_shift_eq hp j hcm z).symm.trans hf1
      have hWpos := (tendsto_zero_iff_meromorphicOrderAt_pos (twoCM_meromorphic_mixedEta hp j b z)).1
        (twoCM_mixed_tendsto_shared_simple hp j b hab hf1 hg1).1
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (twoCM_order_mixedEta_ne_top hp j b hW z)
      rw [← hn] at hWpos ⊢
      have hnpos : (0 : ℤ) < n := by exact_mod_cast hWpos
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hnpos.le]
      omega
    · have hΨ := twoCM_order_psi_at_finite_CM hp j hcm hpos
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
      rw [← hn] at hΨ ⊢
      have hle : 2 * (mult f (a j : Sphere) z : ℤ) - 2 ≤ n := by exact_mod_cast hΨ
      have hn0 : (0 : ℤ) ≤ n := by omega
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hn0]
      omega
  · have hm0 : mult f (a j : Sphere) z = 0 := by omega
    rw [hm0, Nat.cast_zero]
    exact add_nonneg hW0 hΨ0

theorem twoCM_logCounting_finite_le_mixedEta {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) (hab : a j ≠ b)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMMixedEta a j b f g) w ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting f (a j : Sphere) r ≤ logCounting (twoCMMixedEta a j b f g) 0 r + logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (twoCM_finiteFiberDivisor_le_mixedEta hp j b hab hcm hW) hr
  rw [map_add, fiberDivisor_logCounting] at h
  simpa only [Pi.add_apply, ← logCounting_zero] using h

theorem twoCM_order_mixedTheta_ne_top {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ)
    (hH : ∃ w, meromorphicOrderAt (twoCMMixedTheta a j b f g) w ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (twoCMMixedTheta a j b f g) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hH
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => twoCM_meromorphic_mixedTheta hp j b y) isPreconnected_univ
      (mem_univ w) (mem_univ z) hw

theorem twoCM_finiteFiberDivisor_le_mixedTheta {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) (hab : a j ≠ b)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMMixedTheta a j b f g) w ≠ ⊤) :
    fiberDivisor f (a j : Sphere) ≤ (MeromorphicOn.divisor (twoCMMixedTheta a j b f g) univ)⁺ +
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [fiberDivisor_apply hp.nonconst_f.1,
    MeromorphicOn.divisor_apply (fun x _ => twoCM_meromorphic_mixedTheta hp j b x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.meromorphic_auxPsi x) (mem_univ z)]
  have hW0 := posPart_nonneg (meromorphicOrderAt (twoCMMixedTheta a j b f g) z).untop₀
  have hΨ0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  by_cases hpos : 0 < mult f (a j : Sphere) z
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | h2
    · have hf1 : meromorphicOrderAt (fun w => f w - a j) z = (1 : ℤ) := by
        simpa only [← h1, Nat.cast_succ, Nat.cast_zero, zero_add] using order_sub_eq_mult hpos
      have hg1 : meromorphicOrderAt (fun w => g w - a j) z = (1 : ℤ) :=
        (twoCM_order_shift_eq hp j hcm z).symm.trans hf1
      have hWpos := (tendsto_zero_iff_meromorphicOrderAt_pos (twoCM_meromorphic_mixedTheta hp j b z)).1
        (twoCM_mixed_tendsto_shared_simple hp j b hab hf1 hg1).2
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (twoCM_order_mixedTheta_ne_top hp j b hW z)
      rw [← hn] at hWpos ⊢
      have hnpos : (0 : ℤ) < n := by exact_mod_cast hWpos
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hnpos.le]
      omega
    · have hΨ := twoCM_order_psi_at_finite_CM hp j hcm hpos
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
      rw [← hn] at hΨ ⊢
      have hle : 2 * (mult f (a j : Sphere) z : ℤ) - 2 ≤ n := by exact_mod_cast hΨ
      have hn0 : (0 : ℤ) ≤ n := by omega
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hn0]
      omega
  · have hm0 : mult f (a j : Sphere) z = 0 := by omega
    rw [hm0, Nat.cast_zero]
    exact add_nonneg hW0 hΨ0

theorem twoCM_logCounting_finite_le_mixedTheta {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) (hab : a j ≠ b)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMMixedTheta a j b f g) w ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting f (a j : Sphere) r ≤ logCounting (twoCMMixedTheta a j b f g) 0 r + logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (twoCM_finiteFiberDivisor_le_mixedTheta hp j b hab hcm hW) hr
  rw [map_add, fiberDivisor_logCounting] at h
  simpa only [Pi.add_apply, ← logCounting_zero] using h


theorem twoCM_order_shift_eq_off_fiber {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (i : Fin 3) (z : ℂ)
    (hgzero : mult g (a i : Sphere) z = 0) :
    meromorphicOrderAt (fun w => f w - a i) z =
      meromorphicOrderAt (fun w => g w - a i) z := by
  have hfzero : mult f (a i : Sphere) z = 0 := by
    have h := hp.im i z (mem_univ z)
    omega
  by_cases hpole : 0 < mult f ⊤ z
  · have hpoleg : 0 < mult g ⊤ z := by rwa [← hp.cm_top z (mem_univ z)]
    have hf := order_eq_neg_mult_top hpole
    have hg := order_eq_neg_mult_top hpoleg
    have hfneg : meromorphicOrderAt f z < 0 := by
      rw [hf]; exact_mod_cast (by omega : -(mult f ⊤ z : ℤ) < 0)
    have hgneg : meromorphicOrderAt g z < 0 := by
      rw [hg]; exact_mod_cast (by omega : -(mult g ⊤ z : ℤ) < 0)
    rw [order_sub_const_of_neg hfneg, order_sub_const_of_neg hgneg,
      hf, hg, hp.cm_top z (mem_univ z)]
  · have hf0 : mult f ⊤ z = 0 := by omega
    have hg0 : mult g ⊤ z = 0 := by rw [← hp.cm_top z (mem_univ z)]; exact hf0
    have hfnn := order_nonneg_of_mult_top_eq_zero hf0
      (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z))
    have hgnn := order_nonneg_of_mult_top_eq_zero hg0
      (order_ne_top_of_nonconst hp.nonconst_g (mem_univ z))
    rw [order_sub_const_eq_zero_generic hp.nonconst_f (mem_univ z) hfnn hfzero,
      order_sub_const_eq_zero_generic hp.nonconst_g (mem_univ z) hgnn hgzero]

/-- At an IM fiber the quotient has a pole of order at most n-1. Off that
fiber its order is zero, including common poles of the original pair. -/
theorem twoCM_mixed_ratio_order_lower {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (i : Fin 3) (z : ℂ) :
    ((if 0 < mult g (a i : Sphere) z then 1 - (mult g (a i : Sphere) z : ℤ)
      else 0 : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun w => (f w - a i) / (g w - a i)) z := by
  have hfm : MeromorphicAt (fun w => f w - a i) z :=
    (hp.nonconst_f.meromorphic z).sub (MeromorphicAt.const (a i) z)
  have hgm : MeromorphicAt (fun w => g w - a i) z :=
    (hp.nonconst_g.meromorphic z).sub (MeromorphicAt.const (a i) z)
  have heq : (fun w => (f w - a i) / (g w - a i)) =
      (fun w => f w - a i) * (fun w => g w - a i)⁻¹ := by
    ext w
    simp [div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul hfm hgm.inv, meromorphicOrderAt_inv]
  by_cases hgpos : 0 < mult g (a i : Sphere) z
  · have hfpos := (hp.im i z (mem_univ z)).mpr hgpos
    rw [if_pos hgpos, order_sub_eq_mult hfpos, order_sub_eq_mult hgpos,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    exact_mod_cast (by omega : (1 : ℤ) - mult g (a i : Sphere) z ≤
      (mult f (a i : Sphere) z : ℤ) + -(mult g (a i : Sphere) z : ℤ))
  · have hgzero : mult g (a i : Sphere) z = 0 := by omega
    rw [if_neg hgpos, twoCM_order_shift_eq_off_fiber hp i z hgzero]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.nonconst_g.2 z (mem_univ z) (a i))
    rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
      add_neg_cancel]

theorem twoCM_mixedEta_order_lower {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) (z : ℂ) :
    ((if 0 < mult g (a i : Sphere) z then 1 - (mult g (a i : Sphere) z : ℤ)
      else 0 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (twoCMMixedEta a j (a i) f g) z := by
  let B : ℂ → ℂ := fun w => cAux a j * auxU a f g w
  let R : ℂ → ℂ := fun w => (f w - a i) / (g w - a i)
  let n : ℤ := if 0 < mult g (a i : Sphere) z then 1 - (mult g (a i : Sphere) z : ℤ) else 0
  have hn : n ≤ 0 := by dsimp [n]; split_ifs <;> omega
  have hB : MeromorphicAt B z := (MeromorphicAt.const _ z).mul (hp.meromorphic_auxU z)
  have hR : MeromorphicAt R z :=
    ((hp.nonconst_f.meromorphic z).sub (MeromorphicAt.const _ z)).div
      ((hp.nonconst_g.meromorphic z).sub (MeromorphicAt.const _ z))
  have hBnn : 0 ≤ meromorphicOrderAt B z := by
    change 0 ≤ meromorphicOrderAt ((fun _ : ℂ => cAux a j) * auxU a f g) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const _ z) (hp.meromorphic_auxU z)]
    exact add_nonneg analyticAt_const.meromorphicOrderAt_nonneg (hp.order_aux (mem_univ z)).1.1
  have hχ := twoCM_meromorphic_chi hp j z
  have hlowχ : (n : WithTop ℤ) ≤ meromorphicOrderAt (twoCMChi a j f g) z :=
    (show (n : WithTop ℤ) ≤ 0 by exact_mod_cast hn).trans
      (twoCM_chi_order_nonneg_of_WChi_zero hp j hW z)
  have hlowBR : (n : WithTop ℤ) ≤ meromorphicOrderAt (B * R) z := by
    rw [meromorphicOrderAt_mul hB hR]
    calc
      (n : WithTop ℤ) ≤ meromorphicOrderAt R z := twoCM_mixed_ratio_order_lower hp i z
      _ ≤ meromorphicOrderAt B z + meromorphicOrderAt R z := le_add_of_nonneg_left hBnn
  have heq : twoCMMixedEta a j (a i) f g = twoCMChi a j f g + B * R := by
    ext w
    dsimp [twoCMMixedEta, B, R]
    ring
  rw [heq]
  exact (le_min hlowχ hlowBR).trans (meromorphicOrderAt_add hχ (hB.mul hR))

theorem twoCM_negPart_mixedEta_le_fiber_sub_reduced {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    (MeromorphicOn.divisor (twoCMMixedEta a j (a i) f g) univ)⁻ ≤
      fiberDivisor g (a i : Sphere) - reducedFiberDivisor g (a i : Sphere) := by
  intro z
  rw [Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply (fun w _ => twoCM_meromorphic_mixedEta hp j (a i) w) (mem_univ z)]
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
  rw [fiberDivisor_apply hp.nonconst_g.1, reducedFiberDivisor_apply hp.nonconst_g.1]
  have ho := twoCM_mixedEta_order_lower hp j i hW z
  induction he : meromorphicOrderAt (twoCMMixedEta a j (a i) f g) z using WithTop.recTopCoe with
  | top =>
    simp only [WithTop.untop₀_top, negPart_zero]
    split_ifs <;> omega
  | coe n =>
    rw [he] at ho
    simp only [WithTop.untop₀_coe]
    have hn : (if 0 < mult g (a i : Sphere) z then 1 - (mult g (a i : Sphere) z : ℤ)
        else 0) ≤ n := by exact_mod_cast ho
    rw [negPart_def]
    split_ifs at hn ⊢ <;> omega

theorem twoCM_logCounting_mixedEta_poles_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (twoCMMixedEta a j (a i) f g) ⊤ r ≤
      logCounting g (a i : Sphere) r - reducedCounting g (a i : Sphere) r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (twoCM_negPart_mixedEta_le_fiber_sub_reduced hp j i hW) hr
  rw [map_sub, fiberDivisor_logCounting] at h
  simpa only [Pi.sub_apply, ← logCounting_top,
    ← reducedCounting_eq_reducedFiberDivisor hp.nonconst_g.1 (a i : Sphere) (le_trans zero_le_one hr)] using h

theorem twoCM_mixedTheta_order_lower {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) (z : ℂ) :
    ((if 0 < mult f (a i : Sphere) z then 1 - (mult f (a i : Sphere) z : ℤ)
      else 0 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (twoCMMixedTheta a j (a i) f g) z := by
  have hWs : ∀ w, meromorphicOrderAt (twoCMWChi a j g f) w = ⊤ := by
    intro w
    rw [twoCM_WChi_swap]
    exact hW w
  have h := twoCM_mixedEta_order_lower hp.symm j i hWs z
  rw [twoCM_mixedEta_swap, order_neg_eq] at h
  exact h

theorem twoCM_negPart_mixedTheta_le_fiber_sub_reduced {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    (MeromorphicOn.divisor (twoCMMixedTheta a j (a i) f g) univ)⁻ ≤
      fiberDivisor f (a i : Sphere) - reducedFiberDivisor f (a i : Sphere) := by
  intro z
  rw [Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply (fun w _ => twoCM_meromorphic_mixedTheta hp j (a i) w) (mem_univ z)]
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
  rw [fiberDivisor_apply hp.nonconst_f.1, reducedFiberDivisor_apply hp.nonconst_f.1]
  have ho := twoCM_mixedTheta_order_lower hp j i hW z
  induction he : meromorphicOrderAt (twoCMMixedTheta a j (a i) f g) z using WithTop.recTopCoe with
  | top =>
    simp only [WithTop.untop₀_top, negPart_zero]
    split_ifs <;> omega
  | coe n =>
    rw [he] at ho
    simp only [WithTop.untop₀_coe]
    have hn : (if 0 < mult f (a i : Sphere) z then 1 - (mult f (a i : Sphere) z : ℤ)
        else 0) ≤ n := by exact_mod_cast ho
    rw [negPart_def]
    split_ifs at hn ⊢ <;> omega

theorem twoCM_logCounting_mixedTheta_poles_le {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (twoCMMixedTheta a j (a i) f g) ⊤ r ≤
      logCounting f (a i : Sphere) r - reducedCounting f (a i : Sphere) r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (twoCM_negPart_mixedTheta_le_fiber_sub_reduced hp j i hW) hr
  rw [map_sub, fiberDivisor_logCounting] at h
  simpa only [Pi.sub_apply, ← logCounting_top,
    ← reducedCounting_eq_reducedFiberDivisor hp.nonconst_f.1 (a i : Sphere) (le_trans zero_le_one hr)] using h

end ThreeIM
