module

public import RequestProject.ThreeIM.RationalAux

/-!
# The zero fiber is empty (Lemma 9.27)

We first compute the value of the auxiliary function `U = (f - g) f'/P(f)` at a finite common
point where `f` is simple, and then prove Lemma 9.27 under the endpoint normalization
(`P(w) = w (w - 1) (w - c)` with `c < 0`, `U = κ t^{-1}`, `V = κ t` with `κ > 0`) and the
derivative signs of Lemma 9.26.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- Value of `U` at a common `a_j`-point where `f` is simple: `U → (f' - g')/P'(a_j)`. -/
theorem tendsto_auxU_simple {f g : ℂ → ℂ} {t₀ : ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    {j : Fin 3} (hf : AnalyticAt ℂ f t₀) (hg : AnalyticAt ℂ g t₀) (hf0 : f t₀ = a j)
    (hg0 : g t₀ = a j) (hf' : deriv f t₀ ≠ 0) :
    Tendsto (auxU a f g) (𝓝[≠] t₀)
      (𝓝 ((deriv f t₀ - deriv g t₀) / ∏ i ∈ Finset.univ.erase j, (a j - a i))) := by
  set F := dslope f t₀
  set G := dslope g t₀
  set Q : ℂ → ℂ := fun x => ∏ i ∈ Finset.univ.erase j, (x - a i) with hQ
  have hQc : Continuous Q := by simp only [hQ]; fun_prop
  have hQ0 : Q (a j) ≠ 0 := prod_erase_ne_zero ha j
  have hFc : ContinuousAt F t₀ := continuousAt_dslope_same.2 hf.differentiableAt
  have hGc : ContinuousAt G t₀ := continuousAt_dslope_same.2 hg.differentiableAt
  have hF0 : F t₀ = deriv f t₀ := dslope_same f t₀
  have hG0 : G t₀ = deriv g t₀ := dslope_same g t₀
  have hd : ContinuousAt (deriv f) t₀ := hf.deriv.continuousAt
  have hQf : ContinuousAt (fun w => Q (f w)) t₀ := hQc.continuousAt.comp hf.continuousAt
  set Λ : ℂ → ℂ := fun w => (F w - G w) * deriv f w / (F w * Q (f w)) with hΛ
  have hΛc : ContinuousAt Λ t₀ := by
    refine ((hFc.sub hGc).mul hd).div (hFc.mul hQf) ?_
    simp only [hF0, hf0]
    exact mul_ne_zero hf' hQ0
  have hΛ0 : Λ t₀ = (deriv f t₀ - deriv g t₀) / Q (a j) := by
    simp only [hΛ, hF0, hG0, hf0]
    field_simp
  have hev : ∀ᶠ w in 𝓝[≠] t₀, F w ≠ 0 ∧ Q (f w) ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [hFc.eventually_ne (by rw [hF0]; exact hf'),
      hQf.eventually_ne (by rw [hf0]; exact hQ0)] with w h1 h2
    exact ⟨h1, h2⟩
  have heq : auxU a f g =ᶠ[𝓝[≠] t₀] Λ := by
    filter_upwards [hev, self_mem_nhdsWithin] with w hw hwt
    have hw' : w - t₀ ≠ 0 := sub_ne_zero.2 hwt
    have e1 : f w - a j = (w - t₀) * F w := by
      rw [← hf0, ← smul_eq_mul, sub_smul_dslope]
    have e2 : g w - a j = (w - t₀) * G w := by
      rw [← hg0, ← smul_eq_mul, sub_smul_dslope]
    have e3 : f w - g w = (w - t₀) * (F w - G w) := by
      linear_combination e1 - e2
    simp only [auxU, hΛ]
    rw [cubicP_eq_mul a j (f w), e1, e3]
    simp only [hQ] at hw ⊢
    field_simp
  exact ((hΛc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm).trans (by rw [hΛ0])

/-! ### Auxiliary facts -/

/-- An analytic function vanishes at `t` iff its order at `t` is positive. -/
lemma analyticAt_eq_zero_iff_order_pos {F : ℂ → ℂ} {t : ℂ} (hF : AnalyticAt ℂ F t) :
    F t = 0 ↔ 0 < meromorphicOrderAt F t := by
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos hF.meromorphicAt]
  have hc : Tendsto F (𝓝[≠] t) (𝓝 (F t)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro h0; rwa [h0] at hc
  · intro h0; exact tendsto_nhds_unique hc h0

/-- A complex number whose square is a nonnegative real number is real. -/
lemma exists_real_of_sq_eq {t : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : t ^ 2 = r) :
    ∃ s : ℝ, t = s ∧ s ^ 2 = r := by
  have hs := Real.sq_sqrt hr
  have hs' : ((Real.sqrt r : ℝ) : ℂ) ^ 2 = r := by exact_mod_cast hs
  have : (t - Real.sqrt r) * (t + Real.sqrt r) = 0 := by linear_combination h - hs'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ⟨Real.sqrt r, by linear_combination h1, hs⟩
  · exact ⟨-Real.sqrt r, by push_cast; linear_combination h1, by rw [neg_sq, hs]⟩

/-- If `t F(t) = G(t)` off a finite set, with `G` continuous at `t₀ ≠ 0`, then
`F → G(t₀)/t₀` at `t₀`. -/
lemma tendsto_of_mul_eventually {F G : ℂ → ℂ} {t₀ : ℂ} (ht₀ : t₀ ≠ 0) (hG : ContinuousAt G t₀)
    (h : ∀ᶠ t in cofinite, t * F t = G t) : Tendsto F (𝓝[≠] t₀) (𝓝 (G t₀ / t₀)) := by
  have heq : F =ᶠ[𝓝[≠] t₀] fun t => G t / t := by
    filter_upwards [eventually_nhdsNE_of_cofinite h t₀,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t h1 ht
    rw [← h1]; field_simp
  have hc : ContinuousAt (fun t => G t / t) t₀ := hG.div continuousAt_id ht₀
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-! ### Lemma 9.27 -/

/-- **Lemma 9.27** (the zero fiber is empty).  Let `f, g` form a normalized pair on `ℂ*` for the
values `0, 1, c` with `c < 0` (so `P(w) = w (w - 1) (w - c)`), with auxiliary functions
`U = t (f - g) f'/P(f) = κ t^{-1}` and `V = t (f - g) g'/P(g) = κ t` (off a finite set), `κ > 0`.
Assume that `f, g` are analytic at their finite points of `ℂ*` and satisfy the derivative signs
of Lemma 9.26: `f' > 0` on the real points with `|t| ≥ 1`, and `g' < 0` on the real points with
`0 < |t| ≤ 1` (real parts, at finite points).  Then `f, g` have no common zero in `ℂ*`. -/
theorem zero_fiber_empty {f g : ℂ → ℂ} {c κ : ℝ} (hc : c < 0) (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ f g ![0, 1, (c : ℂ)])
    (hU : ∀ᶠ t in cofinite, t * auxU ![0, 1, (c : ℂ)] f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV ![0, 1, (c : ℂ)] f g t = κ * t ^ (1 : ℤ))
    (hfreg : ∀ t : ℂ, t ≠ 0 → mult f ⊤ t = 0 → AnalyticAt ℂ f t)
    (hgreg : ∀ t : ℂ, t ≠ 0 → mult g ⊤ t = 0 → AnalyticAt ℂ g t)
    (hsignR : ∀ t : ℝ, 1 ≤ |t| → mult f ⊤ t = 0 → 0 < (deriv f t).re)
    (hsignS : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → mult g ⊤ t = 0 → (deriv g t).re < 0) :
    ∀ t₀ : ℂ, t₀ ≠ 0 → mult f ((0 : ℂ) : Sphere) t₀ = 0 := by
  set a : Fin 3 → ℂ := ![0, 1, (c : ℂ)] with ha
  have ha0 : a 0 = 0 := rfl
  have hQ : ∏ i ∈ Finset.univ.erase (0 : Fin 3), (a 0 - a i) = c := by
    rw [show Finset.univ.erase (0 : Fin 3) = {1, 2} from by decide]
    simp [ha]
  intro t₀ ht₀
  by_contra hm0
  have hm : 0 < mult f (a 0 : Sphere) t₀ := Nat.pos_of_ne_zero hm0
  have hn : 0 < mult g (a 0 : Sphere) t₀ := (hpair.im 0 t₀ ht₀).1 hm
  have hfm := hpair.nonconst_f.1 t₀ ht₀
  have hgm := hpair.nonconst_g.1 t₀ ht₀
  have hordf : meromorphicOrderAt f t₀ = ((mult f (a 0 : Sphere) t₀ : ℕ) : ℤ) := by
    have := order_sub_eq_mult hm; simpa [ha0] using this
  have hordg : meromorphicOrderAt g t₀ = ((mult g (a 0 : Sphere) t₀ : ℕ) : ℤ) := by
    have := order_sub_eq_mult hn; simpa [ha0] using this
  have hfp : mult f ⊤ t₀ = 0 := by
    simp only [mult_top, hordf]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    omega
  have hgp : mult g ⊤ t₀ = 0 := by
    simp only [mult_top, hordg]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    omega
  have hfa := hfreg t₀ ht₀ hfp
  have hga := hgreg t₀ ht₀ hgp
  have hf0 : f t₀ = a 0 := by
    rw [ha0, analyticAt_eq_zero_iff_order_pos hfa, hordf]; exact_mod_cast hm
  have hg0 : g t₀ = a 0 := by
    rw [ha0, analyticAt_eq_zero_iff_order_pos hga, hordg]; exact_mod_cast hn
  have hdf : deriv f t₀ = 0 ↔ 2 ≤ mult f (a 0 : Sphere) t₀ := by
    rw [analyticAt_eq_zero_iff_order_pos hfa.deriv,
      order_deriv_of_order_sub hfm hm (order_sub_eq_mult hm),
      show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    omega
  have hdg : deriv g t₀ = 0 ↔ 2 ≤ mult g (a 0 : Sphere) t₀ := by
    rw [analyticAt_eq_zero_iff_order_pos hga.deriv,
      order_deriv_of_order_sub hgm hn (order_sub_eq_mult hn),
      show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    omega
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  -- `Ψ = κ² / t²` has order zero, so `min(m, n) = 1`
  have hpsi : meromorphicOrderAt (auxPsi a f g) t₀ = 0 := by
    have heq : auxPsi a f g =ᶠ[𝓝[≠] t₀] fun t => (κ : ℂ) ^ 2 / t ^ 2 := by
      filter_upwards [eventually_nhdsNE_of_cofinite hU t₀, eventually_nhdsNE_of_cofinite hV t₀,
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t h1 h2 ht
      have e1 : auxU a f g t = κ * t ^ (-1 : ℤ) / t := by rw [← h1]; field_simp
      have e2 : auxV a f g t = κ * t ^ (1 : ℤ) / t := by rw [← h2]; field_simp
      simp only [auxPsi]
      rw [e1, e2, zpow_neg_one, zpow_one]
      field_simp
    have hA : AnalyticAt ℂ (fun t : ℂ => (κ : ℂ) ^ 2 / t ^ 2) t₀ :=
      analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 ht₀)
    rw [meromorphicOrderAt_congr heq]
    have hne : ¬ (fun t : ℂ => (κ : ℂ) ^ 2 / t ^ 2) t₀ = 0 := by simp [ht₀, hκ']
    rw [analyticAt_eq_zero_iff_order_pos hA, not_lt] at hne
    exact le_antisymm hne hA.meromorphicOrderAt_nonneg
  have hmin := hpair.min_mult_eq_one_of_psi ht₀ hm hpsi
  -- the ratio identity `n = t₀² m`
  have hratio : (mult g (a 0 : Sphere) t₀ : ℂ) = t₀ ^ 2 * mult f (a 0 : Sphere) t₀ := by
    have h := rational_aux_ratio hpair hκ' hU hV ht₀ hm
    rw [zpow_neg_one, zpow_one] at h
    have := congrArg (· * (t₀ / κ)) h
    field_simp at this
    linear_combination this
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne
  have hn0 : (0 : ℝ) < mult g (a 0 : Sphere) t₀ := by exact_mod_cast hn
  by_cases hm1 : mult f (a 0 : Sphere) t₀ = 1
  · -- `f` is simple at `t₀`: `f'(t₀) - g'(t₀) = κ c / t₀²` and `t₀² = n`
    have hf' : deriv f t₀ ≠ 0 := fun h => by have := hdf.1 h; omega
    have L1 := tendsto_auxU_simple hpair.injective hfa hga hf0 hg0 hf'
    rw [hQ] at L1
    have hGc : ContinuousAt (fun t : ℂ => (κ : ℂ) * t ^ (-1 : ℤ)) t₀ :=
      (continuousAt_zpow₀ t₀ (-1) (Or.inl ht₀)).const_mul _
    have hval := tendsto_nhds_unique L1 (tendsto_of_mul_eventually ht₀ hGc hU)
    have hsq : t₀ ^ 2 = ((mult g (a 0 : Sphere) t₀ : ℕ) : ℝ) := by
      rw [hm1] at hratio; push_cast; linear_combination -hratio
    obtain ⟨s, rfl, hs2⟩ := exists_real_of_sq_eq (Nat.cast_nonneg _) hsq
    have hs0 : s ≠ 0 := by rintro rfl; exact ht₀ (by simp)
    have hs2' : ((s : ℂ)) ^ 2 = ((mult g (a 0 : Sphere) (s : ℂ) : ℕ) : ℂ) := by
      exact_mod_cast hs2
    have hdiff : deriv f s - deriv g s =
        ((κ * c / (mult g (a 0 : Sphere) (s : ℂ) : ℕ) : ℝ) : ℂ) := by
      rw [div_eq_iff hc'] at hval
      rw [hval, zpow_neg_one]
      push_cast
      rw [← hs2']
      have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
      field_simp
    have hre := congrArg Complex.re hdiff
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    have hneg : κ * c / (mult g (a 0 : Sphere) (s : ℂ) : ℕ) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hκ hc) hn0
    by_cases hn1 : mult g (a 0 : Sphere) (s : ℂ) = 1
    · rw [hn1] at hs2
      push_cast at hs2
      have habs : |s| ^ 2 = 1 := by rw [sq_abs]; exact hs2
      have h1 : 1 ≤ |s| := by nlinarith [abs_nonneg s]
      have h2 : |s| ≤ 1 := by nlinarith [abs_nonneg s]
      have := hsignR s h1 hfp
      have := hsignS s hs0 h2 hgp
      linarith
    · have hg'0 : deriv g s = 0 := hdg.2 (by omega)
      rw [hg'0, Complex.zero_re, sub_zero] at hre
      have h2 : (2 : ℝ) ≤ (mult g (a 0 : Sphere) (s : ℂ) : ℕ) := by
        exact_mod_cast (by omega : 2 ≤ mult g (a 0 : Sphere) (s : ℂ))
      have habs : |s| ^ 2 = (mult g (a 0 : Sphere) (s : ℂ) : ℕ) := by rw [sq_abs]; exact hs2
      have h1 : 1 ≤ |s| := by nlinarith [abs_nonneg s]
      have := hsignR s h1 hfp
      linarith
  · -- `g` is simple at `t₀`: `g'(t₀) = -κ c` and `t₀² = 1/m`
    have hn1 : mult g (a 0 : Sphere) t₀ = 1 := by
      rcases min_eq_iff.1 hmin with h | h
      · exact absurd h.1 hm1
      · exact h.1
    have hm2 : 2 ≤ mult f (a 0 : Sphere) t₀ := by omega
    have hg' : deriv g t₀ ≠ 0 := fun h => by have := hdg.1 h; omega
    have hf'0 : deriv f t₀ = 0 := hdf.2 hm2
    have L1 := tendsto_auxU_simple hpair.injective hga hfa hg0 hf0 hg'
    rw [hQ, hf'0, sub_zero] at L1
    have hVeq : auxV a f g = fun w => -auxU a g f w := by
      ext w; simp only [auxV, auxU]; ring
    have L1' : Tendsto (auxV a f g) (𝓝[≠] t₀) (𝓝 (-(deriv g t₀ / c))) := by
      rw [hVeq]; exact L1.neg
    have hGc : ContinuousAt (fun t : ℂ => (κ : ℂ) * t ^ (1 : ℤ)) t₀ :=
      (continuousAt_zpow₀ t₀ 1 (Or.inl ht₀)).const_mul _
    have hval := tendsto_nhds_unique L1' (tendsto_of_mul_eventually ht₀ hGc hV)
    have hgval : deriv g t₀ = ((-(κ * c) : ℝ) : ℂ) := by
      rw [zpow_one, mul_div_assoc, div_self ht₀, mul_one] at hval
      push_cast
      field_simp at hval
      linear_combination -hval
    have hsq : t₀ ^ 2 = ((1 / (mult f (a 0 : Sphere) t₀ : ℝ) : ℝ) : ℂ) := by
      rw [hn1] at hratio
      push_cast
      have : ((mult f (a 0 : Sphere) t₀ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      linear_combination -hratio
    obtain ⟨s, rfl, hs2⟩ := exists_real_of_sq_eq (div_nonneg zero_le_one (Nat.cast_nonneg _)) hsq
    have hs0 : s ≠ 0 := by rintro rfl; exact ht₀ (by simp)
    have h2 : (2 : ℝ) ≤ (mult f (a 0 : Sphere) (s : ℂ) : ℕ) := by exact_mod_cast hm2
    have habs : |s| ^ 2 * (mult f (a 0 : Sphere) (s : ℂ) : ℕ) = 1 := by
      rw [sq_abs, hs2]; field_simp
    have h1 : |s| ≤ 1 := by nlinarith [abs_nonneg s]
    have := hsignS s hs0 h1 hgp
    rw [hgval, Complex.ofReal_re] at this
    nlinarith

end ThreeIM
