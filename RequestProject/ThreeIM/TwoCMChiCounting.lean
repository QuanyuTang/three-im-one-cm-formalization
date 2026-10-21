module

public import RequestProject.ThreeIM.TwoCMFiniteFiber

/-!
# The second counting dichotomy and explicit remaining two-CM cases
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

private lemma twoCM_chiCounting_charT_const (c : ℂ) (r : ℝ) :
    charT (fun _ => c) r = log⁺ ‖c‖ := by
  simp [charT, characteristic]

lemma twoCM_charT_WChi_le_general (hp : NormalizedPair univ f g a) (j : Fin 3) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      charT (twoCMWChi a j f g) r ≤ 2 * charT (twoCMChi a j f g) r + charT (auxPsi a f g) r + K := by
  have hθ := twoCM_meromorphic_chi hp j
  have hΨ := hp.meromorphic_auxPsi
  set c : ℂ := -(cAux a j ^ 2)
  refine ⟨log 2 + log⁺ ‖c‖, fun r hr => ?_⟩
  have hθ2 : Meromorphic (twoCMChi a j f g ^ 2) := fun x => (hθ x).pow 2
  have hcΨ : Meromorphic ((fun _ => c) * auxPsi a f g) := fun x =>
    (MeromorphicAt.const c x).mul (hΨ x)
  have hW : twoCMWChi a j f g = twoCMChi a j f g ^ 2 + (fun _ => c) * auxPsi a f g := by
    ext z; simp [twoCMWChi, c]; ring
  have e1 := characteristic_add_top_le hθ2 hcΨ hr
  have e2 : characteristic (twoCMChi a j f g ^ 2) ⊤ r = 2 * charT (twoCMChi a j f g) r := by
    rw [characteristic_pow_top hθ]; simp [charT]
  have hΨ0 : 0 ≤ charT (auxPsi a f g) r := charT_nonneg hr
  have e3 : characteristic ((fun _ => c) * auxPsi a f g) ⊤ r ≤
      log⁺ ‖c‖ + charT (auxPsi a f g) r := by
    by_cases hc : c = 0
    · have : (fun _ => c) * auxPsi a f g = fun _ => (0 : ℂ) := by ext z; simp [hc]
      rw [this]
      have := twoCM_chiCounting_charT_const 0 r
      simp only [norm_zero, Real.posLog_zero] at this
      unfold charT at this
      rw [this]; have := Real.posLog_nonneg (x := ‖c‖); linarith
    · have h := characteristic_mul_top_le hr (fun x => MeromorphicAt.const c x)
        (fun z => by rw [order_const_eq c hc]; exact WithTop.zero_ne_top) hΨ
        (fun z => (hp.order_aux (mem_univ z)).2.2.2)
      simp only [Pi.add_apply] at h
      have := twoCM_chiCounting_charT_const c r
      unfold charT at this ⊢
      rw [this] at h
      exact h
  rw [hW]
  unfold charT at e2 e3 hΨ0 ⊢
  linarith

theorem twoCM_charT_WChi_le_pairL (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT (twoCMWChi a j f g) r ≤ C * pairL f g r := by
  obtain ⟨Cχ, hχ⟩ := twoCM_charT_chi_le_pairL hp j hcm
  obtain ⟨CΨ, hΨ⟩ := charT_auxPsi_le hp
  obtain ⟨K, hK⟩ := twoCM_charT_WChi_le_general hp j
  refine ⟨2 * Cχ + CΨ + |K|, (hχ.and hΨ).mono fun r hr ⟨hχr, hΨr⟩ => ?_⟩
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) (one_le_pairL (f := f) (g := g) hr))
  have := hK r hr
  rw [add_mul, add_mul]
  linarith

/-- A finite CM multiplicity m forces at least 2m-2 zeros of Ψ. -/
theorem twoCM_order_psi_at_finite_CM (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) {z : ℂ}
    (hpos : 0 < mult f (a j : Sphere) z) :
    ((2 * (mult f (a j : Sphere) z : ℤ) - 2 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (auxPsi a f g) z := by
  have hposg : 0 < mult g (a j : Sphere) z := by rwa [← hcm z (mem_univ z)]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z (mem_univ z))
  have hΨ := (order_aux_at_shared (hp.nonconst_f.meromorphic z)
    (hp.nonconst_g.meromorphic z) hp.injective hpos hposg
    (order_sub_eq_mult hpos) (order_sub_eq_mult hposg) hd.symm).2.2
  have hle := min_mult_le_order_sub (hp.nonconst_f.meromorphic z)
    (hp.nonconst_g.meromorphic z) hpos hposg
  rw [← hcm z (mem_univ z), min_self, ← hd] at hle
  have hmd : (mult f (a j : Sphere) z : ℤ) ≤ d := by exact_mod_cast hle
  rw [hΨ]
  exact_mod_cast (by omega : 2 * (mult f (a j : Sphere) z : ℤ) - 2 ≤ 2 * d - 2)

theorem twoCM_order_WChi_ne_top (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hW : ∃ w, meromorphicOrderAt (twoCMWChi a j f g) w ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (twoCMWChi a j f g) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hW
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => twoCM_meromorphic_WChi hp j y) isPreconnected_univ (mem_univ w) (mem_univ z) hw

/-- Full finite-fiber multiplicities are charged to the two zero divisors.
The nonzero-germ condition is explicit and essential. -/
theorem twoCM_finiteFiberDivisor_le_WChi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMWChi a j f g) w ≠ ⊤) :
    fiberDivisor f (a j : Sphere) ≤ (MeromorphicOn.divisor (twoCMWChi a j f g) univ)⁺ +
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [fiberDivisor_apply hp.nonconst_f.1,
    MeromorphicOn.divisor_apply (fun x _ => twoCM_meromorphic_WChi hp j x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.meromorphic_auxPsi x) (mem_univ z)]
  have hW0 := posPart_nonneg (meromorphicOrderAt (twoCMWChi a j f g) z).untop₀
  have hΨ0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  by_cases hpos : 0 < mult f (a j : Sphere) z
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | h2
    · have hf1 : meromorphicOrderAt (fun w => f w - a j) z = (1 : ℤ) := by
        simpa only [← h1, Nat.cast_succ, Nat.cast_zero, zero_add] using order_sub_eq_mult hpos
      have hg1 : meromorphicOrderAt (fun w => g w - a j) z = (1 : ℤ) :=
        (twoCM_order_shift_eq hp j hcm z).symm.trans hf1
      have hWpos := (tendsto_zero_iff_meromorphicOrderAt_pos (twoCM_meromorphic_WChi hp j z)).1
        (twoCM_tendsto_WChi_shared_simple hp j hf1 hg1)
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (twoCM_order_WChi_ne_top hp j hW z)
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

theorem twoCM_logCounting_finite_le_WChi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMWChi a j f g) w ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting f (a j : Sphere) r ≤ logCounting (twoCMWChi a j f g) 0 r + logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (twoCM_finiteFiberDivisor_le_WChi hp j hcm hW) hr
  rw [map_add, fiberDivisor_logCounting] at h
  simpa only [Pi.add_apply, ← logCounting_zero] using h

/-- The second nonzero auxiliary bounds the full finite CM counting function. -/
theorem twoCM_logCounting_finite_le_pairL_of_WChi_nonzero (hp : NormalizedPair univ f g a)
    (j : Fin 3) (hcm : SharesCMOn univ f g (a j : Sphere))
    (hW : ∃ w, meromorphicOrderAt (twoCMWChi a j f g) w ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r := by
  obtain ⟨CW, hCW⟩ := twoCM_charT_WChi_le_pairL hp j hcm
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT (twoCM_meromorphic_WChi hp j)
  refine ⟨CW + CP + |K|, (hCW.and hCP).mono fun r hr ⟨hWr, hP⟩ => ?_⟩
  have hN := twoCM_logCounting_finite_le_WChi hp j hcm hW hr
  have hzero := hK r hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) (one_le_pairL (f := f) (g := g) hr))
  rw [add_mul, add_mul]
  linarith

/-- The finite CM fiber is logarithmically small unless the squared-chi
identity holds as a germ everywhere. -/
theorem twoCM_chi_dichotomy (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) ∨
      ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r := by
  by_cases hW : ∃ w, meromorphicOrderAt (twoCMWChi a j f g) w ≠ ⊤
  · exact Or.inr (twoCM_logCounting_finite_le_pairL_of_WChi_nonzero hp j hcm hW)
  · exact Or.inl (by simpa only [not_exists, not_not] using hW)

/-- Explicit remaining cases, with same-sign squared identities discharged.
This is a reduction; none of these cases is assumed to be impossible. -/
theorem twoCM_four_cases (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    ((∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)) ∨
    ((∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤)) ∨
    ((∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f (a j : Sphere) r ≤ C * pairL f g r)) ∨
    ((∀ b : Sphere, SharesIMOn univ f g b → SharesCMOn univ f g b) ∨
      ((∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤) ∧
       (∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) ∧
       thetaAux a j f g =ᶠ[codiscrete ℂ] (fun z => -twoCMChi a j f g z))) := by
  rcases twoCM_theta_dichotomy hp j hcm with hθ | hPole
  · rcases twoCM_chi_dichotomy hp j hcm with hχ | hfinite
    · rcases twoCM_both_squared_identities_case hp j hcm hθ hχ with hCM | hopp
      · exact Or.inr (Or.inr (Or.inr (Or.inl hCM)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hθ, hχ, hopp⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hθ, hfinite⟩))
  · rcases twoCM_chi_dichotomy hp j hcm with hχ | hfinite
    · exact Or.inr (Or.inl ⟨hPole, hχ⟩)
    · exact Or.inl ⟨hPole, hfinite⟩

end ThreeIM
