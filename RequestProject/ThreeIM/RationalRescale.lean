module

public import RequestProject.ThreeIM.RationalEndpointCoeff
public import RequestProject.ThreeIM.Pullback

/-!
# Rescaling a rational function

For `c ≠ 0` we define `ratScale c R`, the rational function `t ↦ R(c t)`, and show that it
evaluates pointwise as expected.  This is used to normalise the endpoint constants of Lemma 9.5.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- For coprime `p, q`, the normalised numerator and denominator of `p / q` are `p, q` up to a
common nonzero constant. -/
lemma num_denom_div_of_coprime {p q : ℂ[X]} (hq : q ≠ 0) (hpq : IsCoprime p q) :
    ∃ u : ℂ, u ≠ 0 ∧
      (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).num = p * C u ∧
      (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).denom = q * C u := by
  set H := algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q with hH
  have hq' : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hd' : algebraMap ℂ[X] (RatFunc ℂ) H.denom ≠ 0 := RatFunc.algebraMap_ne_zero H.denom_ne_zero
  have key : H.num * q = p * H.denom := by
    apply RatFunc.algebraMap_injective ℂ
    have : algebraMap ℂ[X] (RatFunc ℂ) H.num / algebraMap ℂ[X] (RatFunc ℂ) H.denom =
        algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q := RatFunc.num_div_denom H
    rw [div_eq_div_iff hd' hq'] at this
    rw [map_mul, map_mul, this]
  have h1 : q ∣ H.denom := hpq.symm.dvd_of_dvd_mul_left ⟨H.num, by rw [← key, mul_comm]⟩
  have h2 : H.denom ∣ q :=
    (RatFunc.isCoprime_num_denom H).symm.dvd_of_dvd_mul_left ⟨p, by rw [key, mul_comm]⟩
  obtain ⟨r, hr⟩ := h1
  have hnum : H.num = p * r := by
    apply mul_right_cancel₀ hq
    rw [key, hr]; ring
  have hru : IsUnit r := by
    rw [hr] at h2
    have : q * r ∣ q * 1 := by simpa using h2
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hq).1 this)
  obtain ⟨u, hu1, hu2⟩ := Polynomial.isUnit_iff.1 hru
  exact ⟨u, hu1.ne_zero, by rw [hnum, hu2], by rw [hr, hu2]⟩

/-- A quotient of coprime polynomials evaluates to the quotient of their values everywhere. -/
lemma ratEval_div_of_coprime {p q : ℂ[X]} (hq : q ≠ 0) (hpq : IsCoprime p q) (t : ℂ) :
    ratEval (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) t =
      p.eval t / q.eval t := by
  obtain ⟨u, hu, hn, hd⟩ := num_denom_div_of_coprime hq hpq
  rw [ratEval_eq, hn, hd, eval_mul, eval_mul, eval_C, mul_div_mul_right _ _ hu]

/-- The rescaled rational function `t ↦ R(c t)`. -/
noncomputable def ratScale (c : ℂ) (R : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (R.num.comp (C c * X)) /
    algebraMap ℂ[X] (RatFunc ℂ) (R.denom.comp (C c * X))

lemma comp_C_mul_X_ne_zero {c : ℂ} (hc : c ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    p.comp (C c * X) ≠ 0 := by
  rw [Ne, comp_eq_zero_iff]
  rintro (h | ⟨-, h⟩)
  · exact hp h
  · have := congrArg (fun p => p.coeff 1) h
    simp [coeff_C] at this
    exact hc this

lemma isCoprime_comp_num_denom (c : ℂ) (R : RatFunc ℂ) :
    IsCoprime (R.num.comp (C c * X)) (R.denom.comp (C c * X)) :=
  (RatFunc.isCoprime_num_denom R).map (compRingHom (C c * X))

lemma ratEval_ratScale {c : ℂ} (hc : c ≠ 0) (R : RatFunc ℂ) (t : ℂ) :
    ratEval (ratScale c R) t = ratEval R (c * t) := by
  unfold ratScale
  rw [ratEval_div_of_coprime (comp_C_mul_X_ne_zero hc R.denom_ne_zero)
    (isCoprime_comp_num_denom c R), ratEval_eq, eval_comp, eval_comp]
  simp

/-- The denominator of `ratScale c R` does not vanish at `0` iff that of `R` does not. -/
lemma denom_ratScale_eval_zero {c : ℂ} (hc : c ≠ 0) (R : RatFunc ℂ) :
    (ratScale c R).denom.eval 0 ≠ 0 ↔ R.denom.eval 0 ≠ 0 := by
  obtain ⟨u, hu, -, hd⟩ := num_denom_div_of_coprime (comp_C_mul_X_ne_zero hc R.denom_ne_zero)
    (isCoprime_comp_num_denom c R)
  unfold ratScale
  rw [hd]
  simp [eval_comp, hu]

lemma ratEval_ratScale_fun {c : ℂ} (hc : c ≠ 0) (R : RatFunc ℂ) :
    ratEval (ratScale c R) = fun t => ratEval R (c * t) :=
  funext (ratEval_ratScale hc R)

lemma mul_auxU_ratScale {c : ℂ} (a : Fin 3 → ℂ) (R S : RatFunc ℂ) (t : ℂ) :
    t * auxU a (fun x => ratEval R (c * x)) (fun x => ratEval S (c * x)) t =
      (c * t) * auxU a (ratEval R) (ratEval S) (c * t) := by
  simp only [auxU]
  rw [show deriv (fun x => ratEval R (c * x)) t = c • deriv (ratEval R) (c * t) from
    deriv_comp_mul_left (f := ratEval R) c t, smul_eq_mul]
  ring

lemma mul_auxV_ratScale {c : ℂ} (a : Fin 3 → ℂ) (R S : RatFunc ℂ) (t : ℂ) :
    t * auxV a (fun x => ratEval R (c * x)) (fun x => ratEval S (c * x)) t =
      (c * t) * auxV a (ratEval R) (ratEval S) (c * t) := by
  simp only [auxV]
  rw [show deriv (fun x => ratEval S (c * x)) t = c • deriv (ratEval S) (c * t) from
    deriv_comp_mul_left (f := ratEval S) c t, smul_eq_mul]
  ring

lemma meromorphicOrderAt_comp_mul {c : ℂ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    meromorphicOrderAt (fun t => f (c * t)) 0 = meromorphicOrderAt f 0 := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun t => c * t) (x := 0)
    (analyticAt_const.mul analyticAt_id) (by rw [deriv_const_mul_field']; simpa using hc)
  simpa [Function.comp_def] using h

/-- Rescaling the variable preserves the opposite-endpoint configuration, multiplying the
constants by `c^{-ρ}` and `c^{ρ}` respectively. -/
theorem OppositeData.ratScale {j k : Fin 3} {ρ : ℕ} {α β : ℂ} {R S : RatFunc ℂ}
    {a : Fin 3 → ℂ} (h : OppositeData a R S j k ρ α β) {c : ℂ} (hc : c ≠ 0) :
    OppositeData a (ratScale c R) (ratScale c S) j k ρ (α * c ^ (-(ρ : ℤ)))
      (β * c ^ (ρ : ℤ)) := by
  have hT : Tendsto (fun t : ℂ => c * t) cofinite cofinite :=
    (mul_right_injective₀ hc).tendsto_cofinite
  refine ⟨h.rho_pos, mul_ne_zero h.alpha_ne (zpow_ne_zero _ hc),
    mul_ne_zero h.beta_ne (zpow_ne_zero _ hc), (denom_ratScale_eval_zero hc R).2 h.denom_zero,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ratEval_ratScale hc, mul_zero]; exact h.value_zero
  · rw [ratEval_ratScale_fun hc S, meromorphicOrderAt_comp_mul hc]; exact h.order_zero
  · rw [ratEval_ratScale_fun hc R]
    have : (fun t => ratEval R (c * t⁻¹)) = fun t => (fun s => ratEval R s⁻¹) (c⁻¹ * t) := by
      funext t; simp only [mul_inv, inv_inv, mul_comm]
    rw [this, meromorphicOrderAt_comp_mul (inv_ne_zero hc) (fun s => ratEval R s⁻¹)]
    exact h.order_infty
  · rw [ratEval_ratScale_fun hc S]
    exact h.tendsto_infty.comp (Filter.tendsto_cocompact_mul_left₀ hc)
  · rw [ratEval_ratScale_fun hc R, ratEval_ratScale_fun hc S]
    filter_upwards [hT.eventually h.aux_U] with t ht
    rw [mul_auxU_ratScale, ht, mul_zpow]; ring
  · rw [ratEval_ratScale_fun hc R, ratEval_ratScale_fun hc S]
    filter_upwards [hT.eventually h.aux_V] with t ht
    rw [mul_auxV_ratScale, ht, mul_zpow]; ring

/-- After rescaling the variable, the two endpoint constants of Lemma 9.5 can be taken equal. -/
theorem OppositeData.exists_ratScale_balanced {j k : Fin 3} {ρ : ℕ} {α β : ℂ} {R S : RatFunc ℂ}
    {a : Fin 3 → ℂ} (h : OppositeData a R S j k ρ α β) :
    ∃ c γ : ℂ, c ≠ 0 ∧
      OppositeData a (ThreeIM.ratScale c R) (ThreeIM.ratScale c S) j k ρ γ γ := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (α / β) (by have := h.rho_pos; omega :
    0 < 2 * ρ)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := h.rho_pos; omega)] at hc
    exact div_ne_zero h.alpha_ne h.beta_ne hc.symm
  refine ⟨c, α * c ^ (-(ρ : ℤ)), hc0, ?_⟩
  have heq : α * c ^ (-(ρ : ℤ)) = β * c ^ (ρ : ℤ) := by
    have hcρ : c ^ (ρ : ℤ) ≠ 0 := zpow_ne_zero _ hc0
    rw [zpow_neg, zpow_natCast] at *
    have h2 : c ^ ρ * c ^ ρ = α / β := by rw [← pow_add, ← two_mul, hc]
    field_simp
    rw [sq, h2]; field_simp [h.beta_ne]
  have := h.ratScale hc0
  rwa [← heq] at this

lemma image_mul_compl_zero {c : ℂ} (hc : c ≠ 0) :
    (fun t : ℂ => c * t) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
  ext w
  simp only [mem_image, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact mul_ne_zero hc ht
  · intro hw; exact ⟨c⁻¹ * w, by simp [hc, hw], by field_simp⟩

/-- Rescaling the variable preserves normalized pairs on `ℂ*`. -/
theorem NormalizedPair.ratScale {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) {c : ℂ} (hc : c ≠ 0) :
    NormalizedPair {0}ᶜ (ratEval (ThreeIM.ratScale c R)) (ratEval (ThreeIM.ratScale c S)) a := by
  have hh : ∀ z ∈ ({0}ᶜ : Set ℂ), AnalyticAt ℂ (fun t : ℂ => c * t) z :=
    fun z _ => analyticAt_const.mul analyticAt_id
  have hh' : ∀ z ∈ ({0}ᶜ : Set ℂ), deriv (fun t : ℂ => c * t) z ≠ 0 := fun z _ => by
    rw [deriv_const_mul_field']; simpa using hc
  have himg := image_mul_compl_zero hc
  have hR : ratEval (ThreeIM.ratScale c R) = ratEval R ∘ fun t => c * t :=
    ratEval_ratScale_fun hc R
  have hS : ratEval (ThreeIM.ratScale c S) = ratEval S ∘ fun t => c * t :=
    ratEval_ratScale_fun hc S
  have hmaps : MapsTo (fun t : ℂ => c * t) ({0}ᶜ : Set ℂ) {0}ᶜ := fun z hz =>
    himg ▸ mem_image_of_mem _ hz
  rw [hR, hS]
  refine ⟨h.nonconst_f.comp hh hh' hmaps,
    h.nonconst_g.comp hh hh' hmaps, fun z hz => ?_, h.injective,
    fun j => (sharesIMOn_iff_comp hh hh' himg).1 (h.im j),
    (sharesCMOn_iff_comp hh hh' himg).1 h.cm_top⟩
  have : (fun w => (ratEval R ∘ fun t => c * t) w - (ratEval S ∘ fun t => c * t) w) =
      (fun w => ratEval R w - ratEval S w) ∘ fun t => c * t := rfl
  rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
  exact h.distinct _ (hmaps hz)

/-- **Lemma 9.5, normalised form.**  If the opposite-endpoint configuration holds for `(R, S)`,
then after a rescaling `t ↦ c t` of the variable the pair is still a normalized pair on `ℂ*` and
the configuration holds with equal constants, `U = γ t^{-ρ - 1}` and `V = γ t^{ρ - 1}`. -/
theorem OppositeEndpoints.exists_balanced {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) (h : OppositeEndpoints a R S) :
    ∃ c : ℂ, c ≠ 0 ∧
      NormalizedPair {0}ᶜ (ratEval (ratScale c R)) (ratEval (ratScale c S)) a ∧
      ∃ (j k : Fin 3) (ρ : ℕ) (γ : ℂ), OppositeData a (ratScale c R) (ratScale c S) j k ρ γ γ := by
  obtain ⟨j, k, ρ, α, β, hd⟩ := h
  obtain ⟨c, γ, hc, hγ⟩ := hd.exists_ratScale_balanced
  exact ⟨c, hc, hpair.ratScale hc, j, k, ρ, γ, hγ⟩

end ThreeIM
