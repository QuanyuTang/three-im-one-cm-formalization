module

public import RequestProject.ThreeIM.ThetaProximity
public import RequestProject.ThreeIM.SharedValueCounting

/-!
# The small theta auxiliary function at a CM value

This is the first analytic dichotomy in the independent two-CM argument:
the squared theta identity holds as a germ everywhere, or the common pole
count is bounded by the logarithmic error. No sharing theorem is imported.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory Function

namespace ThreeIM

private lemma twoCM_charT_const (c : ℂ) (r : ℝ) : charT (fun _ => c) r = log⁺ ‖c‖ := by
  simp [charT, characteristic]

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

lemma twoCM_meromorphic_thetaAux (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (thetaAux a j f g) := fun x => by
  have hf := hp.nonconst_f.meromorphic x
  have hg := hp.nonconst_g.meromorphic x
  have hf' := hf.deriv; have hg' := hg.deriv
  have hf'' := hf'.deriv; have hg'' := hg'.deriv
  unfold thetaAux ThetaFun
  fun_prop

lemma twoCM_meromorphic_WAux (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (WAux a j f g) := fun x => by
  have h1 := twoCM_meromorphic_thetaAux hp j x
  have h2 := hp.meromorphic_auxPsi x
  unfold WAux
  fun_prop

/-- `T(W_a) ≤ 2 T(θ_a) + T(Ψ) + O(1)`. -/
lemma twoCM_charT_WAux_le_general (hp : NormalizedPair univ f g a) (j : Fin 3) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      charT (WAux a j f g) r ≤ 2 * charT (thetaAux a j f g) r + charT (auxPsi a f g) r + K := by
  have hθ := twoCM_meromorphic_thetaAux hp j
  have hΨ := hp.meromorphic_auxPsi
  set c : ℂ := -(cAux a j ^ 2)
  refine ⟨log 2 + log⁺ ‖c‖, fun r hr => ?_⟩
  have hθ2 : Meromorphic (thetaAux a j f g ^ 2) := fun x => (hθ x).pow 2
  have hcΨ : Meromorphic ((fun _ => c) * auxPsi a f g) := fun x =>
    (MeromorphicAt.const c x).mul (hΨ x)
  have hW : WAux a j f g = thetaAux a j f g ^ 2 + (fun _ => c) * auxPsi a f g := by
    ext z; simp [WAux, c]; ring
  have e1 := characteristic_add_top_le hθ2 hcΨ hr
  have e2 : characteristic (thetaAux a j f g ^ 2) ⊤ r = 2 * charT (thetaAux a j f g) r := by
    rw [characteristic_pow_top hθ]; simp [charT]
  have hΨ0 : 0 ≤ charT (auxPsi a f g) r := charT_nonneg hr
  have e3 : characteristic ((fun _ => c) * auxPsi a f g) ⊤ r ≤
      log⁺ ‖c‖ + charT (auxPsi a f g) r := by
    by_cases hc : c = 0
    · have : (fun _ => c) * auxPsi a f g = fun _ => (0 : ℂ) := by ext z; simp [hc]
      rw [this]
      have := twoCM_charT_const 0 r
      simp only [norm_zero, Real.posLog_zero] at this
      unfold charT at this
      rw [this]; have := Real.posLog_nonneg (x := ‖c‖); linarith
    · have h := characteristic_mul_top_le hr (fun x => MeromorphicAt.const c x)
        (fun z => by rw [order_const_eq c hc]; exact WithTop.zero_ne_top) hΨ
        (fun z => (hp.order_aux (mem_univ z)).2.2.2)
      simp only [Pi.add_apply] at h
      have := twoCM_charT_const c r
      unfold charT at this ⊢
      rw [this] at h
      exact h
  rw [hW]
  unfold charT at e2 e3 hΨ0 ⊢
  linarith

/-- Nonvanishing of `W` at one germ propagates over the plane. -/
theorem twoCM_order_WAux_ne_top (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hW : ∃ w, meromorphicOrderAt (WAux a j f g) w ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (WAux a j f g) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hW
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => twoCM_meromorphic_WAux hp j y) isPreconnected_univ
    (mem_univ w) (mem_univ z) hw

/-- Pointwise: `(poles of f) ≤ (zeros of W_a) + (zeros of Ψ)`. -/
lemma twoCM_negPart_divisor_le_W (hp : NormalizedPair univ f g a)
    (j : Fin 3) (hW : ∃ w, meromorphicOrderAt (WAux a j f g) w ≠ ⊤) :
    (MeromorphicOn.divisor f univ)⁻ ≤
      (MeromorphicOn.divisor (WAux a j f g) univ)⁺ +
        (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  have hfm := hp.nonconst_f.meromorphic
  have hWm := twoCM_meromorphic_WAux hp j
  have hΨm := hp.meromorphic_auxPsi
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [MeromorphicOn.divisor_apply (fun x _ => hfm x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hWm x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hΨm x) (mem_univ z)]
  have hW0 : 0 ≤ (meromorphicOrderAt (WAux a j f g) z).untop₀⁺ := posPart_nonneg _
  have hΨ0 : 0 ≤ (meromorphicOrderAt (auxPsi a f g) z).untop₀⁺ := posPart_nonneg _
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z))
  rw [← hn, WithTop.untop₀_coe]
  rcases le_or_gt 0 n with h0 | h0
  · rw [negPart_eq_zero.2 h0]; positivity
  rcases eq_or_lt_of_le (show n ≤ -1 by omega) with h1 | h1
  · -- simple pole
    subst h1
    have hlim := tendsto_WAux_simple_pole hp j (z₀ := z) (by rw [← hn]; rfl)
    have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos (hWm z)).1 hlim
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (twoCM_order_WAux_ne_top hp j hW z)
    rw [← hm] at hpos ⊢
    have : (0 : ℤ) < m := by exact_mod_cast hpos
    rw [WithTop.untop₀_coe, posPart_eq_self.2 this.le]
    simp only [negPart_def]
    omega
  · -- pole of order `k ≥ 2`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hΨ := order_auxPsi_at_pole hp (z₀ := z) (k := k) (by omega) (by rw [← hn, hk]; rfl)
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
    rw [← hm] at hΨ ⊢
    have : 2 * (k : ℤ) - 2 ≤ m := by exact_mod_cast hΨ
    rw [WithTop.untop₀_coe, posPart_eq_self.2 (show (0 : ℤ) ≤ m by omega)]
    simp only [negPart_def]
    omega

/-- At a CM target the poles of theta are charged only to zeros of Ψ. -/
theorem twoCM_negPart_theta_le_psi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    (MeromorphicOn.divisor (thetaAux a j f g) univ)⁻ ≤
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  simp only [Function.locallyFinsuppWithin.negPart_apply,
    Function.locallyFinsuppWithin.posPart_apply]
  rw [MeromorphicOn.divisor_apply (fun x _ => twoCM_meromorphic_thetaAux hp j x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.meromorphic_auxPsi x) (mem_univ z)]
  obtain ⟨hord, hsupp, -⟩ := thetaAux_order hp j z
  have hP0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  induction hθ : meromorphicOrderAt (thetaAux a j f g) z using WithTop.recTopCoe with
  | top => simpa using hP0
  | coe n =>
    rw [hθ] at hord hsupp
    have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 hord
    simp only [WithTop.untop₀_coe, negPart_def]
    by_cases hn0 : 0 ≤ n
    · omega
    · have hnneg : n < 0 := by omega
      have hneg : ((n : ℤ) : WithTop ℤ) < 0 := by exact_mod_cast hnneg
      rcases hsupp hneg with hd | hpsi
      · exact (hd.2.2 (hcm z (mem_univ z))).elim
      · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
        rw [← hm] at hpsi ⊢
        have hmpos : (0 : ℤ) < m := by exact_mod_cast hpsi
        rw [WithTop.untop₀_coe, posPart_eq_self.2 hmpos.le]
        omega

/-- The integrated pole count of theta at a CM target. -/
theorem twoCM_logCounting_theta_le_psi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (thetaAux a j f g) ⊤ r ≤ logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (twoCM_negPart_theta_le_psi hp j hcm) hr
  simpa only [← logCounting_top, ← logCounting_zero] using h

/-- Theta has logarithmically small characteristic at every finite CM target. -/
theorem twoCM_charT_theta_le_pairL (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT (thetaAux a j f g) r ≤ C * pairL f g r := by
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨Cθ, hCθ⟩ := proximity_thetaAux_le hp
  refine ⟨Cθ + CP, (hCθ.and hCP).mono fun r hr ⟨hθ, hP⟩ => ?_⟩
  have hN := twoCM_logCounting_theta_le_psi hp j hcm hr
  have hθj := hθ j
  change proximity (thetaAux a j f g) ⊤ r + logCounting (thetaAux a j f g) ⊤ r ≤ _
  rw [add_mul]
  linarith

/-- The squared theta remainder at a CM target is logarithmically small. -/
theorem twoCM_charT_WAux_le_pairL (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT (WAux a j f g) r ≤ C * pairL f g r := by
  obtain ⟨Cθ, hθ⟩ := twoCM_charT_theta_le_pairL hp j hcm
  obtain ⟨CΨ, hΨ⟩ := charT_auxPsi_le hp
  obtain ⟨K, hK⟩ := twoCM_charT_WAux_le_general hp j
  refine ⟨2 * Cθ + CΨ + |K|, (hθ.and hΨ).mono fun r hr ⟨hθr, hΨr⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  have := hK r hr
  rw [add_mul, add_mul]
  linarith

/-- If the squared theta remainder is not the zero germ, the full common
pole count is logarithmically small. -/
theorem twoCM_logCounting_top_le_pairL_of_W_nonzero (hp : NormalizedPair univ f g a)
    (j : Fin 3) (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (WAux a j f g) w ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r := by
  obtain ⟨CW, hCW⟩ := twoCM_charT_WAux_le_pairL hp j hcm
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT (twoCM_meromorphic_WAux hp j)
  refine ⟨CW + CP + |K|, (hCW.and hCP).mono fun r hr ⟨hWr, hP⟩ => ?_⟩
  have hN := Function.locallyFinsuppWithin.logCounting_le (twoCM_negPart_divisor_le_W hp j hW) hr
  rw [map_add] at hN
  simp only [Pi.add_apply, ← logCounting_top, ← logCounting_zero] at hN
  have hzero := hK r hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K)
      (one_le_pairL (f := f) (g := g) hr))
  rw [add_mul, add_mul]
  linarith

/-- The zero-germ branch is exactly the squared-theta identity, with no
claim about arbitrary representative values at exceptional points. -/
theorem twoCM_theta_identity_of_W_zero (j : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) (z : ℂ) :
    (fun w => thetaAux a j f g w ^ 2) =ᶠ[𝓝[≠] z]
      (fun w => cAux a j ^ 2 * auxPsi a f g w) := by
  have h := meromorphicOrderAt_eq_top_iff.1 (hW z)
  exact h.mono fun w hw => sub_eq_zero.1 hw

/-- The first genuine two-CM dichotomy: a global squared-theta identity,
or logarithmically few common poles. -/
theorem twoCM_theta_dichotomy (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    (∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∨
      ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r := by
  by_cases hW : ∃ w, meromorphicOrderAt (WAux a j f g) w ≠ ⊤
  · exact Or.inr (twoCM_logCounting_top_le_pairL_of_W_nonzero hp j hcm hW)
  · exact Or.inl (by simpa only [not_exists, not_not] using hW)

end ThreeIM
