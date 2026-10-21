module

public import RequestProject.ThreeIM.Covariance
public import RequestProject.ThreeIM.External
public import RequestProject.ThreeIM.Rational
public import RequestProject.ThreeIM.Rotation

/-!
# Pullback of sharing conditions (Lemma 9.7)

* General principle: precomposition with a holomorphic map `h : Ω → Ω'` which is onto and has
  nowhere vanishing derivative transports IM and CM sharing in both directions.
* Lemma 9.7, first part: sharing on `ℂ*` is equivalent to sharing of the pullbacks by
  `z ↦ e^z` on `ℂ`.
* Lemma 9.7, second part: in a sharing datum on `ℂ*` (three finite values IM, `∞` CM) with a
  defect, every finite shared value has a defect.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

section General

variable {Ω Ω' : Set ℂ} {h : ℂ → ℂ}

/-- Precomposition with a map `h`, holomorphic with nonvanishing derivative on `Ω` and mapping
`Ω` onto `Ω'`, preserves and reflects IM sharing. -/
theorem sharesIMOn_iff_comp (hh : ∀ z ∈ Ω, AnalyticAt ℂ h z) (hh' : ∀ z ∈ Ω, deriv h z ≠ 0)
    (himg : h '' Ω = Ω') {f g : ℂ → ℂ} {b : Sphere} :
    SharesIMOn Ω' f g b ↔ SharesIMOn Ω (f ∘ h) (g ∘ h) b := by
  constructor
  · intro H z hz
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact H (h z) (himg ▸ mem_image_of_mem h hz)
  · intro H w hw
    rw [← himg] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have := H z hz
    rwa [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)] at this

/-- Precomposition with a map `h`, holomorphic with nonvanishing derivative on `Ω` and mapping
`Ω` onto `Ω'`, preserves and reflects CM sharing. -/
theorem sharesCMOn_iff_comp (hh : ∀ z ∈ Ω, AnalyticAt ℂ h z) (hh' : ∀ z ∈ Ω, deriv h z ≠ 0)
    (himg : h '' Ω = Ω') {f g : ℂ → ℂ} {b : Sphere} :
    SharesCMOn Ω' f g b ↔ SharesCMOn Ω (f ∘ h) (g ∘ h) b := by
  constructor
  · intro H z hz
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact H (h z) (himg ▸ mem_image_of_mem h hz)
  · intro H w hw
    rw [← himg] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have := H z hz
    rwa [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)] at this

/-- Precomposition with a holomorphic map `h` with nonvanishing derivative on `Ω`, mapping `Ω`
into `Ω'`, preserves nonconstant meromorphy. -/
theorem IsNonconstMeroOn.comp (hh : ∀ z ∈ Ω, AnalyticAt ℂ h z) (hh' : ∀ z ∈ Ω, deriv h z ≠ 0)
    (hmaps : MapsTo h Ω Ω') {f : ℂ → ℂ} (hf : IsNonconstMeroOn f Ω') :
    IsNonconstMeroOn (f ∘ h) Ω := by
  refine ⟨fun z hz => (hf.1 (h z) (hmaps hz)).comp_analyticAt (hh z hz), fun z hz c => ?_⟩
  have : (fun w => (f ∘ h) w - c) = (fun w => f w - c) ∘ h := rfl
  rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
  exact hf.2 (h z) (hmaps hz) c

end General

/-! ### The exponential map -/

lemma exp_image_univ : Complex.exp '' univ = {0}ᶜ := by
  ext w
  simp only [mem_image, mem_univ, true_and, mem_compl_iff, mem_singleton_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ Complex.exp_ne_zero z, fun hw => ⟨Complex.log w, Complex.exp_log hw⟩⟩

lemma analyticAt_exp' (z : ℂ) : AnalyticAt ℂ Complex.exp z :=
  analyticAt_cexp

lemma deriv_exp_ne_zero (z : ℂ) : deriv Complex.exp z ≠ 0 := by
  rw [Complex.deriv_exp]; exact Complex.exp_ne_zero z

lemma image_pow_punctured {ρ : ℕ} (hρ : 0 < ρ) : (fun t : ℂ => t ^ ρ) '' {0}ᶜ = {0}ᶜ := by
  ext w
  simp only [mem_image, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact pow_ne_zero _ ht
  · intro hw
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq w hρ
    exact ⟨t, fun h => hw (by rw [← ht, h, zero_pow hρ.ne']), ht⟩

lemma analyticAt_exp_div {q : ℂ} (z : ℂ) : AnalyticAt ℂ (fun t => Complex.exp (t / q)) z :=
  analyticAt_cexp.comp (analyticAt_id.div_const)

lemma deriv_exp_div_ne_zero {q : ℂ} (hq : q ≠ 0) (z : ℂ) :
    deriv (fun t => Complex.exp (t / q)) z ≠ 0 := by
  have : HasDerivAt (fun t => Complex.exp (t / q)) (Complex.exp (z / q) * (1 / q)) z :=
    ((hasDerivAt_id z).div_const q).cexp
  rw [this.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (one_div_ne_zero hq)

lemma image_exp_div {q : ℂ} (hq : q ≠ 0) : (fun t => Complex.exp (t / q)) '' univ = {0}ᶜ := by
  ext w
  simp only [mem_image, mem_univ, true_and, mem_compl_iff, mem_singleton_iff]
  refine ⟨fun ⟨z, hz⟩ => hz ▸ Complex.exp_ne_zero _, fun hw => ⟨q * Complex.log w, ?_⟩⟩
  rw [mul_div_cancel_left₀ _ hq, Complex.exp_log hw]

/-- **Lemma 9.7** (IM part).  Sharing a value IM on `ℂ*` is equivalent to sharing it IM on `ℂ`
after pullback by `z ↦ e^z`. -/
theorem sharesIMOn_punctured_iff_comp_exp {f g : ℂ → ℂ} {b : Sphere} :
    SharesIMOn {0}ᶜ f g b ↔ SharesIMOn univ (f ∘ Complex.exp) (g ∘ Complex.exp) b :=
  sharesIMOn_iff_comp (fun z _ => analyticAt_exp' z) (fun z _ => deriv_exp_ne_zero z)
    exp_image_univ

/-- **Lemma 9.7** (CM part).  Sharing a value CM on `ℂ*` is equivalent to sharing it CM on `ℂ`
after pullback by `z ↦ e^z`. -/
theorem sharesCMOn_punctured_iff_comp_exp {f g : ℂ → ℂ} {b : Sphere} :
    SharesCMOn {0}ᶜ f g b ↔ SharesCMOn univ (f ∘ Complex.exp) (g ∘ Complex.exp) b :=
  sharesCMOn_iff_comp (fun z _ => analyticAt_exp' z) (fun z _ => deriv_exp_ne_zero z)
    exp_image_univ

/-- Pullback by `z ↦ e^z` of a nonconstant meromorphic function on `ℂ*`. -/
theorem IsNonconstMeroOn.comp_exp {f : ℂ → ℂ} (hf : IsNonconstMeroOn f {0}ᶜ) :
    IsNonconstMeroOn (f ∘ Complex.exp) univ :=
  hf.comp (fun z _ => analyticAt_exp' z) (fun z _ => deriv_exp_ne_zero z)
    (fun z _ => Complex.exp_ne_zero z)

/-- **Lemma 9.7** (second part).  Let `f, g` be nonconstant meromorphic functions on `ℂ*`
sharing four distinct values on `ℂ*`, all IM, and two of them CM.  Then all four values are
shared CM on `ℂ*`.  Equivalently: if a sharing datum on `ℂ*` (three finite values IM and `∞`
CM) has a defect, then every finite shared value has a defect. -/
theorem punctured_two_cm {f g : ℂ → ℂ} (hf : IsNonconstMeroOn f {0}ᶜ)
    (hg : IsNonconstMeroOn g {0}ᶜ) (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i, SharesIMOn {0}ᶜ f g (a i)) {i₁ i₂ : Fin 4} (hi : i₁ ≠ i₂)
    (hcm₁ : SharesCMOn {0}ᶜ f g (a i₁)) (hcm₂ : SharesCMOn {0}ᶜ f g (a i₂)) :
    ∀ i, SharesCMOn {0}ᶜ f g (a i) := by
  intro i
  rw [sharesCMOn_punctured_iff_comp_exp]
  exact ext_two_cm hf.comp_exp hg.comp_exp a ha
    (fun i => sharesIMOn_punctured_iff_comp_exp.1 (him i)) hi
    (sharesCMOn_punctured_iff_comp_exp.1 hcm₁) (sharesCMOn_punctured_iff_comp_exp.1 hcm₂) i

/-- **Lemma 9.7** (defect form).  In a sharing datum on `ℂ*` (three distinct finite values
shared IM, `∞` shared CM), if some finite shared value has a defect, then every finite shared value has a
defect. -/
theorem defect_at_every_value {f g : ℂ → ℂ} (hf : IsNonconstMeroOn f {0}ᶜ)
    (hg : IsNonconstMeroOn g {0}ᶜ) (a : Fin 3 → ℂ) (ha : Function.Injective a)
    (him : ∀ j, SharesIMOn {0}ᶜ f g (a j : Sphere)) (hcm : SharesCMOn {0}ᶜ f g ⊤)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect f g (a k : Sphere) z) :
    ∀ j, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect f g (a j : Sphere) z := by
  intro j
  by_contra hnd
  push_neg at hnd
  -- the value `a j` is then shared CM
  have hcmj : SharesCMOn {0}ᶜ f g (a j : Sphere) := by
    intro z hz
    by_contra hne
    by_cases h0 : 0 < mult f (a j : Sphere) z
    · exact hnd z hz ⟨h0, (him j z hz).1 h0, hne⟩
    · have h1 : ¬ 0 < mult g (a j : Sphere) z := fun h => h0 ((him j z hz).2 h)
      omega
  -- the four values `a 0, a 1, a 2, ∞`
  let b : Fin 4 → Sphere := fun i => if h : (i : ℕ) < 3 then (a ⟨i, h⟩ : Sphere) else ⊤
  have hb : Function.Injective b := by
    intro i i' hii'
    simp only [b] at hii'
    split_ifs at hii' with h1 h2 h2
    · have := ha (WithTop.coe_injective hii')
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · exact (WithTop.coe_ne_top hii').elim
    · exact (WithTop.coe_ne_top hii'.symm).elim
    · exact Fin.ext (by omega)
  have him' : ∀ i, SharesIMOn {0}ᶜ f g (b i) := by
    intro i
    simp only [b]
    split_ifs
    · exact him _
    · exact hcm.sharesIMOn
  have hbj : b ⟨j, by omega⟩ = (a j : Sphere) := by simp [b]
  have hb3 : b 3 = ⊤ := by simp [b]
  have hne : (⟨j, by omega⟩ : Fin 4) ≠ 3 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hall := punctured_two_cm hf hg b hb him' hne (hbj ▸ hcmj) (hb3 ▸ hcm)
  obtain ⟨k, z, hz, hd⟩ := hdef
  have := hall ⟨k, by omega⟩
  simp only [b, Fin.is_lt, ↓reduceDIte] at this
  exact hd.2.2 (this z hz)

/-! ### Rational functions are nonconstant meromorphic functions -/

lemma polynomial_eventually_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (x : ℂ) :
    ∀ᶠ z in 𝓝[≠] x, p.eval z ≠ 0 := by
  have hfin : ({z | p.eval z = 0} \ {x} : Set ℂ).Finite :=
    (p.finite_setOf_isRoot hp).subset (fun z hz => hz.1)
  have hmem : ({z | p.eval z = 0} \ {x} : Set ℂ)ᶜ ∈ 𝓝 x :=
    hfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with z hz hzx h
  exact hz ⟨h, hzx⟩

lemma ratEval_eq (R : RatFunc ℂ) (t : ℂ) : ratEval R t = R.num.eval t / R.denom.eval t := by
  simp [ratEval, RatFunc.eval]

lemma meromorphicAt_ratEval (R : RatFunc ℂ) (x : ℂ) : MeromorphicAt (ratEval R) x := by
  have : ratEval R = fun t => R.num.eval t / R.denom.eval t := funext (ratEval_eq R)
  rw [this]
  exact (R.num.differentiable.analyticAt x).meromorphicAt.div
    (R.denom.differentiable.analyticAt x).meromorphicAt

lemma order_ratEval_sub_ne_top {R : RatFunc ℂ} {c : ℂ} (hR : R ≠ RatFunc.C c) (x : ℂ) :
    meromorphicOrderAt (fun t => ratEval R t - c) x ≠ ⊤ := by
  have hne : R.num - Polynomial.C c * R.denom ≠ 0 := by
    intro h
    apply hR
    rw [sub_eq_zero] at h
    have hd : (algebraMap (Polynomial ℂ) (RatFunc ℂ) R.denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero R.denom_ne_zero
    rw [← RatFunc.num_div_denom R, h, map_mul, mul_div_assoc, div_self hd, mul_one]
    simp [RatFunc.algebraMap_C]
  intro htop
  rw [meromorphicOrderAt_eq_top_iff] at htop
  obtain ⟨z, hz, h1, h2⟩ := (htop.and ((polynomial_eventually_ne_zero hne x).and
    (polynomial_eventually_ne_zero R.denom_ne_zero x))).exists
  rw [ratEval_eq, div_sub' h2, div_eq_zero_iff] at hz
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at h1
  rcases hz with hz | hz
  · exact h1 (by rw [← hz]; ring)
  · exact h2 hz

/-- A nonconstant rational function is a nonconstant meromorphic function on every set. -/
theorem isNonconstMeroOn_ratEval {R : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c) (Ω : Set ℂ) :
    IsNonconstMeroOn (ratEval R) Ω :=
  ⟨fun x _ => meromorphicAt_ratEval R x, fun x _ c => order_ratEval_sub_ne_top (hR c) x⟩

/-- **Lemma 9.7** for rational functions.  If nonconstant rational functions share three
distinct finite values IM and `∞` CM on `ℂ*`, and one of the finite values has a defect, then
every finite shared value has a defect. -/
theorem ratEval_defect_at_every_value {R S : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c)
    (hS : ∀ c : ℂ, S ≠ RatFunc.C c) (a : Fin 3 → ℂ) (ha : Function.Injective a)
    (him : ∀ j, SharesIMOn {0}ᶜ (ratEval R) (ratEval S) (a j : Sphere))
    (hcm : SharesCMOn {0}ᶜ (ratEval R) (ratEval S) ⊤)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z) :
    ∀ j, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a j : Sphere) z :=
  defect_at_every_value (isNonconstMeroOn_ratEval hR _) (isNonconstMeroOn_ratEval hS _) a ha
    him hcm hdef

/-! ### Lemma 9.3, final step, in terms of orders -/

lemma order_poly_eq_zero_iff (p : Polynomial ℂ) (t : ℂ) :
    meromorphicOrderAt (fun z => p.eval z) t = 0 ↔ p.eval t ≠ 0 := by
  have ha : AnalyticAt ℂ (fun z => p.eval z) t := p.differentiable.analyticAt t
  rw [ha.meromorphicOrderAt_eq, ← ha.analyticOrderAt_eq_zero]
  constructor
  · intro h
    cases hx : analyticOrderAt (fun z => p.eval z) t with
    | top => simp [hx] at h
    | coe n => simp [hx] at h ⊢; exact_mod_cast h
  · intro h; simp [h]

/-- If a rational function has order zero at `t` (no zero or pole there), its reduced numerator
and denominator do not vanish at `t`. -/
lemma eval_num_denom_ne_zero_of_order {H : RatFunc ℂ} {t : ℂ}
    (h : meromorphicOrderAt (ratEval H) t = 0) : H.num.eval t ≠ 0 ∧ H.denom.eval t ≠ 0 := by
  obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom H
  have hab' := congrArg (fun r => r.eval t) hab
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at hab'
  have hmer := meromorphicAt_ratEval H t
  have hpm : MeromorphicAt (fun z => H.num.eval z) t :=
    (H.num.differentiable.analyticAt t).meromorphicAt
  have hqm : MeromorphicAt (fun z => H.denom.eval z) t :=
    (H.denom.differentiable.analyticAt t).meromorphicAt
  by_cases hq : H.denom.eval t = 0
  · exfalso
    have hp : H.num.eval t ≠ 0 := by intro hp; rw [hp, hq] at hab'; simp at hab'
    have hev : ∀ᶠ z in 𝓝 t, H.num.eval z ≠ 0 :=
      (H.num.differentiable.continuous.continuousAt (x := t)).eventually_ne hp
    have heq : (fun z => H.denom.eval z) =ᶠ[𝓝[≠] t] (ratEval H)⁻¹ * fun z => H.num.eval z := by
      filter_upwards [nhdsWithin_le_nhds hev] with z hz
      simp only [Pi.mul_apply, Pi.inv_apply, ratEval_eq]
      field_simp
    have h0 : meromorphicOrderAt (fun z => H.denom.eval z) t = 0 := by
      rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul hmer.inv hpm,
        meromorphicOrderAt_inv, h, (order_poly_eq_zero_iff _ _).2 hp]
      simp
    exact (order_poly_eq_zero_iff _ _).1 h0 hq
  · refine ⟨?_, hq⟩
    have hev : ∀ᶠ z in 𝓝 t, H.denom.eval z ≠ 0 :=
      (H.denom.differentiable.continuous.continuousAt (x := t)).eventually_ne hq
    have heq : (fun z => H.num.eval z) =ᶠ[𝓝[≠] t] ratEval H * fun z => H.denom.eval z := by
      filter_upwards [nhdsWithin_le_nhds hev] with z hz
      simp only [Pi.mul_apply, ratEval_eq]
      field_simp
    have h0 : meromorphicOrderAt (fun z => H.num.eval z) t = 0 := by
      rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul hmer hqm, h,
        (order_poly_eq_zero_iff _ _).2 hq]
      simp
    exact (order_poly_eq_zero_iff _ _).1 h0

/-- **Lemma 9.3, final step** (order form).  A rational function with neither zeros nor poles
on `ℂ*` (order zero at every `t ≠ 0`) is `α t^u` with `α ≠ 0` and `u ∈ ℤ`. -/
theorem ratFunc_eq_monomial_of_order {H : RatFunc ℂ}
    (h : ∀ t : ℂ, t ≠ 0 → meromorphicOrderAt (ratEval H) t = 0) :
    ∃ α : ℂ, α ≠ 0 ∧ ∃ u : ℤ, H = RatFunc.C α * RatFunc.X ^ u := by
  have hH : H ≠ 0 := by
    rintro rfl
    have := h 1 one_ne_zero
    have h0 : ratEval 0 = fun _ => (0 : ℂ) := funext fun t => by simp [ratEval_eq]
    rw [h0, meromorphicOrderAt_const] at this
    simp at this
  exact ratFunc_eq_monomial hH (fun t ht => (eval_num_denom_ne_zero_of_order (h t ht)).1)
    (fun t ht => (eval_num_denom_ne_zero_of_order (h t ht)).2)

/-! ### Other pullbacks used in Sections 9 and 10 -/

/-- Pullback by `t ↦ t^ρ` (used in Lemma 9.25): sharing IM on `ℂ*` is equivalent for
`f, g` and for `f(t^ρ), g(t^ρ)`. -/
theorem sharesIMOn_punctured_iff_comp_pow {ρ : ℕ} (hρ : 0 < ρ) {f g : ℂ → ℂ} {b : Sphere} :
    SharesIMOn {0}ᶜ f g b ↔ SharesIMOn {0}ᶜ (f ∘ fun t => t ^ ρ) (g ∘ fun t => t ^ ρ) b := by
  apply sharesIMOn_iff_comp (fun z _ => (differentiable_pow ρ).analyticAt z)
  · intro z hz
    simp only [deriv_pow_field, ne_eq, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff', not_or]
    exact ⟨hρ.ne', fun h => hz h.1⟩
  · exact image_pow_punctured hρ

/-- Pullback by `t ↦ t^ρ` (used in Lemma 9.25): sharing CM on `ℂ*` is equivalent for
`f, g` and for `f(t^ρ), g(t^ρ)`. -/
theorem sharesCMOn_punctured_iff_comp_pow {ρ : ℕ} (hρ : 0 < ρ) {f g : ℂ → ℂ} {b : Sphere} :
    SharesCMOn {0}ᶜ f g b ↔ SharesCMOn {0}ᶜ (f ∘ fun t => t ^ ρ) (g ∘ fun t => t ^ ρ) b := by
  apply sharesCMOn_iff_comp (fun z _ => (differentiable_pow ρ).analyticAt z)
  · intro z hz
    simp only [deriv_pow_field, ne_eq, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff', not_or]
    exact ⟨hρ.ne', fun h => hz h.1⟩
  · exact image_pow_punctured hρ

/-- Pullback by `t ↦ e^{t/q}` (used in Lemma 10.5): sharing IM on `ℂ*` is equivalent to
sharing IM on `ℂ` after this pullback. -/
theorem sharesIMOn_punctured_iff_comp_exp_div {q : ℂ} (hq : q ≠ 0) {f g : ℂ → ℂ} {b : Sphere} :
    SharesIMOn {0}ᶜ f g b ↔
      SharesIMOn univ (f ∘ fun t => Complex.exp (t / q)) (g ∘ fun t => Complex.exp (t / q)) b :=
  sharesIMOn_iff_comp (fun z _ => analyticAt_exp_div z) (fun z _ => deriv_exp_div_ne_zero hq z)
    (image_exp_div hq)

/-- Pullback by `t ↦ e^{t/q}` (used in Lemma 10.5): sharing CM on `ℂ*` is equivalent to
sharing CM on `ℂ` after this pullback. -/
theorem sharesCMOn_punctured_iff_comp_exp_div {q : ℂ} (hq : q ≠ 0) {f g : ℂ → ℂ} {b : Sphere} :
    SharesCMOn {0}ᶜ f g b ↔
      SharesCMOn univ (f ∘ fun t => Complex.exp (t / q)) (g ∘ fun t => Complex.exp (t / q)) b :=
  sharesCMOn_iff_comp (fun z _ => analyticAt_exp_div z) (fun z _ => deriv_exp_div_ne_zero hq z)
    (image_exp_div hq)

end ThreeIM
