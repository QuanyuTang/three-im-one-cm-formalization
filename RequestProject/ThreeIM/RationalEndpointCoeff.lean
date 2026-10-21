module

public import RequestProject.ThreeIM.RationalOpposite

/-!
# Endpoint coefficient identities (Lemma 9.5, second part)

In the endpoint configuration of Lemma 9.5 (`OppositeEndpoints a R S`, with `U = α t^{-ρ}` and
`V = β t^ρ`), the leading Laurent coefficients of `R, S` at the endpoints are determined by
`α, β`.  Writing `B` for the leading coefficient of `S` at `0` (`S(t) ∼ B t^{-ρ}`), `A` for that
of `R` at `∞` (`R(t) ∼ A t^ρ`), `σ = ord₀(R - a j)` and `τ = ord_∞(S - a k)`:

* `β = ρ / B` and `α = ρ / A` (the paper's `R ∼ (ρ/κ) t^ρ`, `S ∼ (ρ/κ) t^{-ρ}`);
* `α = -σ B / P'(a j)` and `β = -τ A / P'(a k)`, hence
  `α β = -ρσ / P'(a j) = -ρτ / P'(a k)` (the paper's `κ² = -ρσ/P'(a) = -ρτ/P'(b)`).

The computations use Mathlib's trailing coefficients `meromorphicTrailingCoeffAt` (the leading
Laurent coefficient), which are multiplicative.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- `P'(a j) = ∏_{i ≠ j} (a j - a i)`. -/
noncomputable def cubicPDeriv (a : Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (a j - a i)

/-! ### Trailing coefficients -/

/-- The trailing coefficient of the derivative at a point of order `n ≠ 0`. -/
theorem tc_deriv_of_order_eq {f : ℂ → ℂ} {z₀ a : ℂ} (hf : MeromorphicAt f z₀) {n : ℤ}
    (hn0 : n ≠ 0) (hn : meromorphicOrderAt (fun w => f w - a) z₀ = n) :
    meromorphicTrailingCoeffAt (deriv f) z₀ =
      n * meromorphicTrailingCoeffAt (fun w => f w - a) z₀ := by
  obtain ⟨g, hga, hg0, hfg⟩ :=
    (meromorphicOrderAt_eq_int_iff (hf.sub (MeromorphicAt.const a z₀))).1 hn
  set F : ℂ → ℂ := fun w => (w - z₀) ^ n * g w with hF
  have hfF : (fun w => f w - a) =ᶠ[𝓝[≠] z₀] F :=
    hfg.mono fun w hw => by simpa [hF] using hw
  have hderiv : deriv (fun w => f w - a) =ᶠ[𝓝[≠] z₀] deriv F := hfF.nhdsNE_deriv
  have hderiv' : deriv f =ᶠ[𝓝[≠] z₀] deriv F := by
    have : deriv (fun w => f w - a) = deriv f := funext fun w => deriv_sub_const a
    rwa [this] at hderiv
  set G : ℂ → ℂ := fun w => (n : ℂ) * g w + (w - z₀) * deriv g w with hG
  have hGa : AnalyticAt ℂ G z₀ := by
    have := hga.deriv
    simp only [hG]
    fun_prop
  have hG0 : G z₀ ≠ 0 := by
    simp only [hG, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast hn0) hg0
  have hFG : ∀ᶠ w in 𝓝[≠] z₀, deriv F w = (w - z₀) ^ (n - 1) * G w := by
    filter_upwards [nhdsWithin_le_nhds hga.eventually_analyticAt, self_mem_nhdsWithin]
      with w hw hwz
    have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
    have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ n) w :=
      ((differentiableAt_zpow).2 (Or.inl hwz')).comp w (differentiableAt_id.sub_const z₀)
    rw [hF, deriv_fun_mul hd hw.differentiableAt]
    have : deriv (fun w => (w - z₀) ^ n) w = (n : ℂ) * (w - z₀) ^ (n - 1) := by
      rw [deriv_comp_sub_const (f := fun x : ℂ => x ^ n)]
      simp [deriv_zpow]
    rw [this, hG]
    have : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
      rw [← zpow_add_one₀ hwz', sub_add_cancel]
    rw [this]
    ring
  have htc : meromorphicTrailingCoeffAt (fun w => f w - a) z₀ = g z₀ :=
    hga.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg0 hfg
  rw [htc, hGa.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hG0
    (by filter_upwards [hderiv', hFG] with w h1 h2; rw [h1, h2, smul_eq_mul])]
  simp [hG]

lemma tc_id_zero : meromorphicTrailingCoeffAt (fun t : ℂ => t) 0 = 1 := by
  have := meromorphicTrailingCoeffAt_id_sub_const (x := (0 : ℂ)) (y := 0)
  simpa using this

lemma tc_cubicP_comp {f : ℂ → ℂ} {x : ℂ} (a : Fin 3 → ℂ) (hf : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (fun w => cubicP a (f w)) x =
      ∏ i, meromorphicTrailingCoeffAt (fun w => f w - a i) x := by
  have hm : ∀ c : ℂ, MeromorphicAt (fun w => f w - c) x :=
    fun c => hf.sub (MeromorphicAt.const c x)
  have e : (fun w => cubicP a (f w)) =
      (fun w => f w - a 0) * (fun w => f w - a 1) * (fun w => f w - a 2) := by
    ext w; simp [cubicP]
  rw [e, ((hm _).mul (hm _)).meromorphicTrailingCoeffAt_mul (hm _),
    (hm _).meromorphicTrailingCoeffAt_mul (hm _), Fin.prod_univ_three]

/-- If `f - a` has positive order at `x`, then `f - c` has trailing coefficient `a - c` for
`c ≠ a`. -/
lemma tc_sub_of_order_pos {f : ℂ → ℂ} {x a c : ℂ} (hf : MeromorphicAt f x)
    (h : 0 < meromorphicOrderAt (fun w => f w - a) x) (hc : c ≠ a) :
    meromorphicTrailingCoeffAt (fun w => f w - c) x = a - c := by
  have e : (fun w => f w - c) = (fun _ => a - c) + (fun w => f w - a) := by
    ext w; simp
  have hac : a - c ≠ 0 := sub_ne_zero.2 hc.symm
  have hm : MeromorphicAt (fun w => f w - a) x := hf.sub (MeromorphicAt.const a x)
  have hlt : meromorphicOrderAt (fun _ : ℂ => a - c) x <
      meromorphicOrderAt (fun w => f w - a) x := by
    rw [meromorphicOrderAt_const]
    simpa [hac] using h
  rw [e, hm.meromorphicTrailingCoeffAt_add_eq_left_of_lt hlt, meromorphicTrailingCoeffAt_const]

/-- At a pole, `f - c` has the trailing coefficient of `f`. -/
lemma tc_sub_of_pole {f : ℂ → ℂ} {x : ℂ} (c : ℂ)
    (h : meromorphicOrderAt f x < 0) :
    meromorphicTrailingCoeffAt (fun w => f w - c) x = meromorphicTrailingCoeffAt f x := by
  have e : (fun w => f w - c) = f + (fun _ => -c) := by
    ext w; simp [sub_eq_add_neg]
  rw [e, (MeromorphicAt.const (-c) x).meromorphicTrailingCoeffAt_add_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  split_ifs
  · exact lt_of_lt_of_le h le_top
  · exact h

/-- The trailing coefficient of `t · U(t)` at `0`. -/
lemma tc_mul_auxU {f g : ℂ → ℂ} (a : Fin 3 → ℂ) (hf : MeromorphicAt f 0)
    (hg : MeromorphicAt g 0) :
    meromorphicTrailingCoeffAt (fun t => t * auxU a f g t) 0 =
      meromorphicTrailingCoeffAt (fun w => f w - g w) 0 * meromorphicTrailingCoeffAt (deriv f) 0 /
        ∏ i, meromorphicTrailingCoeffAt (fun w => f w - a i) 0 := by
  have hP : MeromorphicAt (fun w => cubicP a (f w)) 0 := by unfold cubicP; fun_prop
  have hfg : MeromorphicAt (fun w => f w - g w) 0 := hf.sub hg
  have hid : MeromorphicAt (fun t : ℂ => t) 0 := analyticAt_id.meromorphicAt
  have e : (fun t => t * auxU a f g t) =
      (fun t : ℂ => t) * (fun w => f w - g w) * deriv f * (fun w => cubicP a (f w))⁻¹ := by
    ext t; simp [auxU, div_eq_mul_inv, mul_assoc]
  rw [e, ((hid.mul hfg).mul hf.deriv).meromorphicTrailingCoeffAt_mul hP.inv,
    (hid.mul hfg).meromorphicTrailingCoeffAt_mul hf.deriv,
    hid.meromorphicTrailingCoeffAt_mul hfg, meromorphicTrailingCoeffAt_inv,
    tc_cubicP_comp a hf, tc_id_zero]
  ring

/-- The trailing coefficient at `0` of `α t^u`. -/
lemma tc_monomial (α : ℂ) (u : ℤ) :
    meromorphicTrailingCoeffAt (fun t : ℂ => α * t ^ u) 0 = α := by
  have hid : MeromorphicAt (fun t : ℂ => t) 0 := analyticAt_id.meromorphicAt
  have e : (fun t : ℂ => α * t ^ u) = (fun _ => α) * (fun t : ℂ => t) ^ u := by
    ext t; simp
  rw [e, (MeromorphicAt.const α 0).meromorphicTrailingCoeffAt_mul (hid.zpow u),
    hid.meromorphicTrailingCoeffAt_zpow, tc_id_zero, meromorphicTrailingCoeffAt_const]
  simp


lemma tc_neg {F : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x) :
    meromorphicTrailingCoeffAt (fun w => -F w) x = -meromorphicTrailingCoeffAt F x := by
  have e : (fun w => -F w) = (fun _ => (-1 : ℂ)) * F := by ext w; simp
  rw [e, (MeromorphicAt.const (-1 : ℂ) x).meromorphicTrailingCoeffAt_mul hF,
    meromorphicTrailingCoeffAt_const]
  ring

/-- The local coefficient identities at an endpoint where `f` is finite with `f(0) = a j`
(`ord₀(f - a j) = σ`) and `g` has a pole of order `ρ`:
`tc(t U_{f,g}) = -σ B / P'(a j)` and `tc(t U_{g,f}) = -ρ / B`, where `B` is the leading
coefficient of `g`. -/
theorem endpoint_coeff_identities {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (hf : AnalyticAt ℂ f 0) {j : Fin 3} {σ : ℕ} (hσ : 0 < σ)
    (hfo : meromorphicOrderAt (fun w => f w - a j) 0 = ((σ : ℤ) : WithTop ℤ))
    (hg : MeromorphicAt g 0) {ρ : ℕ} (hρ : 0 < ρ)
    (hgo : meromorphicOrderAt g 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ)) :
    meromorphicTrailingCoeffAt (fun t => t * auxU a f g t) 0 =
        -(σ : ℂ) * meromorphicTrailingCoeffAt g 0 / cubicPDeriv a j ∧
      meromorphicTrailingCoeffAt (fun t => t * auxU a g f t) 0 =
        -(ρ : ℂ) / meromorphicTrailingCoeffAt g 0 := by
  have hfm := hf.meromorphicAt
  have hfnn := hf.meromorphicOrderAt_nonneg
  have hfa : MeromorphicAt (fun w => f w - a j) 0 := hfm.sub (MeromorphicAt.const _ 0)
  have hC : meromorphicTrailingCoeffAt (fun w => f w - a j) 0 ≠ 0 :=
    hfa.meromorphicTrailingCoeffAt_ne_zero (by rw [hfo]; exact WithTop.coe_ne_top)
  have hB : meromorphicTrailingCoeffAt g 0 ≠ 0 :=
    hg.meromorphicTrailingCoeffAt_ne_zero (by rw [hgo]; exact WithTop.coe_ne_top)
  have hgneg : meromorphicOrderAt g 0 < 0 := by
    rw [hgo]; exact_mod_cast (by omega : -(ρ : ℤ) < 0)
  have hfpos : 0 < meromorphicOrderAt (fun w => f w - a j) 0 := by
    rw [hfo]; exact_mod_cast hσ
  -- `f - g`
  have h1 : meromorphicTrailingCoeffAt (fun w => f w - g w) 0 =
      -meromorphicTrailingCoeffAt g 0 := by
    have e : (fun w => f w - g w) = (fun w => -g w) + f := by
      ext w; simp [sub_eq_add_neg, add_comm]
    have hlt : meromorphicOrderAt (fun w => -g w) 0 < meromorphicOrderAt f 0 := by
      rw [order_neg_eq]; exact lt_of_lt_of_le hgneg hfnn
    rw [e, hfm.meromorphicTrailingCoeffAt_add_eq_left_of_lt hlt, tc_neg hg]
  -- `g - f`
  have h1' : meromorphicTrailingCoeffAt (fun w => g w - f w) 0 =
      meromorphicTrailingCoeffAt g 0 := by
    have e : (fun w => g w - f w) = g + (fun w => -f w) := by ext w; simp [sub_eq_add_neg]
    have hlt : meromorphicOrderAt g 0 < meromorphicOrderAt (fun w => -f w) 0 := by
      rw [order_neg_eq]; exact lt_of_lt_of_le hgneg hfnn
    have hfn : MeromorphicAt (fun w => -f w) 0 := hfm.neg
    rw [e, hfn.meromorphicTrailingCoeffAt_add_eq_left_of_lt hlt]
  -- derivatives
  have h2 : meromorphicTrailingCoeffAt (deriv f) 0 =
      (σ : ℂ) * meromorphicTrailingCoeffAt (fun w => f w - a j) 0 := by
    rw [tc_deriv_of_order_eq hfm (n := (σ : ℤ)) (by exact_mod_cast hσ.ne') hfo]
    push_cast; ring
  have h2' : meromorphicTrailingCoeffAt (deriv g) 0 =
      -(ρ : ℂ) * meromorphicTrailingCoeffAt g 0 := by
    have hgo' : meromorphicOrderAt (fun w => g w - 0) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ) := by
      simpa using hgo
    rw [tc_deriv_of_order_eq hg (by omega) hgo']
    simp
  -- products
  have h3 : ∏ i, meromorphicTrailingCoeffAt (fun w => f w - a i) 0 =
      meromorphicTrailingCoeffAt (fun w => f w - a j) 0 * cubicPDeriv a j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), cubicPDeriv]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    exact tc_sub_of_order_pos hfm hfpos (ha.ne (Finset.ne_of_mem_erase hi))
  have h3' : ∏ i, meromorphicTrailingCoeffAt (fun w => g w - a i) 0 =
      meromorphicTrailingCoeffAt g 0 ^ 3 := by
    rw [Fin.prod_univ_three, tc_sub_of_pole _ hgneg, tc_sub_of_pole _ hgneg,
      tc_sub_of_pole _ hgneg]
    ring
  have hP : cubicPDeriv a j ≠ 0 := by
    rw [cubicPDeriv]
    exact Finset.prod_ne_zero_iff.2 fun i hi =>
      sub_ne_zero.2 (ha.ne (Finset.ne_of_mem_erase hi)).symm
  refine ⟨?_, ?_⟩
  · rw [tc_mul_auxU a hfm hg, h1, h2, h3]
    field_simp
  · rw [tc_mul_auxU a hg hfm, h1', h2', h3']
    field_simp

variable {R S : RatFunc ℂ} {a : Fin 3 → ℂ}

/-- If `f` is analytic at `0` with `f(0) = c` and `f - c` is not locally zero, then `f - c` has a
positive integer order at `0`. -/
lemma exists_order_sub_pos {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f 0) (hfc : f 0 = c)
    (hne : meromorphicOrderAt (fun w => f w - c) 0 ≠ ⊤) :
    ∃ σ : ℕ, 0 < σ ∧ meromorphicOrderAt (fun w => f w - c) 0 = ((σ : ℤ) : WithTop ℤ) := by
  have hfa : AnalyticAt ℂ (fun w => f w - c) 0 := hf.sub analyticAt_const
  obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderAt (fun w => f w - c) 0 = m := by
    rw [hfa.meromorphicOrderAt_eq] at hne
    cases h : analyticOrderAt (fun w => f w - c) 0 with
    | top => simp [h] at hne
    | coe m => exact ⟨m, rfl⟩
  refine ⟨m, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.cast_zero, hfa.analyticOrderAt_eq_zero] at hm
      exact absurd (by simp [hfc]) hm
    · exact h0
  · rw [hfa.meromorphicOrderAt_eq, hm]; rfl

/-- **Lemma 9.5**, endpoint coefficient identities.  In the endpoint configuration
`OppositeEndpoints a R S` (with data `j, k, ρ, α, β`), let `B` be the leading Laurent coefficient
of `S` at `0` and `A` that of `R` at `∞` (of `s ↦ R(1/s)` at `0`).  Then, with
`σ = ord₀(R - a j) ≥ 1` and `τ = ord_∞(S - a k) ≥ 1`:
`β B = ρ`, `α A = ρ`, `α P'(a j) = -σ B`, `β P'(a k) = -τ A`, and hence
`α β P'(a j) = -ρσ` and `α β P'(a k) = -ρτ`. -/
theorem opposite_endpoint_coefficients (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    {j k : Fin 3} {ρ : ℕ} {α β : ℂ} (hρ : 0 < ρ) (hR0 : R.denom.eval 0 ≠ 0)
    (hRj : ratEval R 0 = a j)
    (hSo : meromorphicOrderAt (ratEval S) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ))
    (hRo : meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ))
    (hSk : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k)))
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ (ρ : ℤ)) :
    ∃ σ τ : ℕ, 0 < σ ∧ 0 < τ ∧
      meromorphicOrderAt (fun t => ratEval R t - a j) 0 = ((σ : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt (fun s => ratEval S s⁻¹ - a k) 0 = ((τ : ℤ) : WithTop ℤ) ∧
      β * meromorphicTrailingCoeffAt (ratEval S) 0 = ρ ∧
      α * meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 = ρ ∧
      α * cubicPDeriv a j = -(σ : ℂ) * meromorphicTrailingCoeffAt (ratEval S) 0 ∧
      β * cubicPDeriv a k = -(τ : ℂ) * meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 ∧
      α * β * cubicPDeriv a j = -((ρ : ℂ) * σ) ∧ α * β * cubicPDeriv a k = -((ρ : ℂ) * τ) := by
  have ha := hpair.injective
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  -- the endpoint `0`
  have hRa : AnalyticAt ℂ (ratEval R) 0 := by
    rw [funext (ratEval_eq R)]
    exact (R.num.differentiable.analyticAt 0).div (R.denom.differentiable.analyticAt 0) hR0
  obtain ⟨σ, hσ, hσo⟩ := exists_order_sub_pos hRa hRj (order_ratEval_sub_ne_top (hRnc _) 0)
  obtain ⟨e1, e2⟩ := endpoint_coeff_identities ha hRa hσ hσo (meromorphicAt_ratEval S 0) hρ hSo
  have tU : meromorphicTrailingCoeffAt (fun t => t * auxU a (ratEval R) (ratEval S) t) 0 = α := by
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE (eventually_nhdsNE_of_cofinite hU 0),
      tc_monomial]
  have tV : meromorphicTrailingCoeffAt (fun t => t * auxU a (ratEval S) (ratEval R) t) 0 =
      -β := by
    have hev : (fun t => t * auxU a (ratEval S) (ratEval R) t) =ᶠ[𝓝[≠] 0]
        fun t => (-β) * t ^ (ρ : ℤ) := by
      filter_upwards [eventually_nhdsNE_of_cofinite hV 0] with t ht
      have := congrFun (mul_auxV_eq_neg a (ratEval R) (ratEval S)) t
      rw [neg_mul, ← ht, this, neg_neg]
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE hev, tc_monomial]
  rw [tU] at e1
  rw [tV] at e2
  -- the endpoint `∞`
  obtain ⟨hQ0, hGa, hG0⟩ := ratInvFun_of_tendsto hSk
  have hFo : meromorphicOrderAt (ratInvFun R) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ) := by
    rw [order_ratInvFun]; exact hRo
  obtain ⟨τ, hτ, hτo⟩ := exists_order_sub_pos hGa hG0 (order_ratInvFun_sub_ne_top (hSnc _) hQ0)
  obtain ⟨f1, f2⟩ := endpoint_coeff_identities ha hGa hτ hτo (meromorphicAt_ratInvFun R) hρ hFo
  have tU' : meromorphicTrailingCoeffAt
      (fun s => s * auxU a (ratInvFun R) (ratInvFun S) s) 0 = -α := by
    have hev : (fun s => s * auxU a (ratInvFun R) (ratInvFun S) s) =ᶠ[𝓝[≠] 0]
        fun s => (-α) * s ^ (-(-(ρ : ℤ))) :=
      Filter.EventuallyEq.trans (mul_auxU_ratInvFun a R S) (inv_monomial_eventually hU)
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE hev, tc_monomial]
  have tV' : meromorphicTrailingCoeffAt
      (fun s => s * auxU a (ratInvFun S) (ratInvFun R) s) 0 = β := by
    have hev : (fun s => s * auxU a (ratInvFun S) (ratInvFun R) s) =ᶠ[𝓝[≠] 0]
        fun s => β * s ^ (-(ρ : ℤ)) := by
      filter_upwards [mul_auxV_ratInvFun a R S, inv_monomial_eventually hV] with s h1 h2
      have := congrFun (mul_auxV_eq_neg a (ratInvFun R) (ratInvFun S)) s
      rw [← neg_neg (s * auxU a (ratInvFun S) (ratInvFun R) s), ← this, h1, h2]
      ring
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE hev, tc_monomial]
  rw [tV'] at f1
  rw [tU'] at f2
  have hA : meromorphicTrailingCoeffAt (ratInvFun R) 0 =
      meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 := by
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ratInvFun_eq R hs
  have hτo' : meromorphicOrderAt (fun s => ratEval S s⁻¹ - a k) 0 = ((τ : ℤ) : WithTop ℤ) := by
    rw [← hτo]
    apply meromorphicOrderAt_congr
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [ratInvFun_eq S hs]
  rw [hA] at f1 f2
  set B := meromorphicTrailingCoeffAt (ratEval S) 0
  set A := meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0
  have hB : B ≠ 0 := (meromorphicAt_ratEval S 0).meromorphicTrailingCoeffAt_ne_zero
    (by rw [hSo]; exact WithTop.coe_ne_top)
  have hA0 : A ≠ 0 := by
    rw [← hA]
    exact (meromorphicAt_ratInvFun R).meromorphicTrailingCoeffAt_ne_zero
      (by rw [hFo]; exact WithTop.coe_ne_top)
  have hPj : cubicPDeriv a j ≠ 0 := by
    rw [cubicPDeriv]
    exact Finset.prod_ne_zero_iff.2 fun i hi =>
      sub_ne_zero.2 (ha.ne (Finset.ne_of_mem_erase hi)).symm
  have hPk : cubicPDeriv a k ≠ 0 := by
    rw [cubicPDeriv]
    exact Finset.prod_ne_zero_iff.2 fun i hi =>
      sub_ne_zero.2 (ha.ne (Finset.ne_of_mem_erase hi)).symm
  have g1 : β * B = ρ := by field_simp at e2; linear_combination -e2
  have g2 : α * A = ρ := by field_simp at f2; linear_combination -f2
  have g3 : α * cubicPDeriv a j = -(σ : ℂ) * B := by field_simp at e1; linear_combination e1
  have g4 : β * cubicPDeriv a k = -(τ : ℂ) * A := by field_simp at f1; linear_combination f1
  refine ⟨σ, τ, hσ, hτ, hσo, hτo', g1, g2, g3, g4, ?_, ?_⟩
  · linear_combination β * g3 - (σ : ℂ) * g1
  · linear_combination α * g4 - (τ : ℂ) * g2

end ThreeIM
