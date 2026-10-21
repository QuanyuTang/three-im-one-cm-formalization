module

public import RequestProject.ThreeIM.RationalFiniteEndpointInfty

/-!
# Opposite endpoint poles: the exponents of `U` and `V` (Lemma 9.5, first part)

Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` with the conclusions of Lemma 9.2, so that
`U = (R - S) DR/P(R) = α t^u` and `V = (R - S) DS/P(S) = β t^v` (Lemma 9.3).  At an endpoint where
one map has a pole of order `k` and the other has a finite value in `{a 0, a 1, a 2}`, the
exponents of `U` and `V` are determined by `k` (the paper's computations
`U ∼ k/R`, `V ∼ -τ R/P'(b)` at `∞` and `U ∼ -σ S/P'(a)`, `V ∼ s/S` at `0`).  Consequently:

* if `R(0) ∈ {a j}`, `S` has a pole of order `s` at `0`, `R` has a pole of order `r` at `∞` and
  `S(∞) ∈ {a j}`, then `r = s =: ρ`, `U = α t^{-ρ}` and `V = β t^ρ`;
* the same map cannot be infinite at both endpoints while the other is finite at both.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-! ### Local orders at an endpoint -/

/-- At a point where `f` is analytic with `f(0) = a j`, `t · U(t)` has the order of `f - g`. -/
lemma order_mul_auxU_of_analytic {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (hf : AnalyticAt ℂ f 0) {j : Fin 3} (hfj : f 0 = a j)
    (hne : meromorphicOrderAt (fun w => f w - a j) 0 ≠ ⊤) (hg : MeromorphicAt g 0) {d : ℤ}
    (hd : meromorphicOrderAt (fun w => f w - g w) 0 = d) :
    meromorphicOrderAt (fun t => t * auxU a f g t) 0 = d := by
  have hfa : AnalyticAt ℂ (fun w => f w - a j) 0 := hf.sub analyticAt_const
  obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderAt (fun w => f w - a j) 0 = m := by
    rw [hfa.meromorphicOrderAt_eq] at hne
    cases h : analyticOrderAt (fun w => f w - a j) 0 with
    | top => simp [h] at hne
    | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.cast_zero, hfa.analyticOrderAt_eq_zero] at hm
      exact absurd (by simp [hfj]) hm
    · exact h0
  have hmo : meromorphicOrderAt (fun w => f w - a j) 0 = (m : ℤ) := by
    rw [hfa.meromorphicOrderAt_eq, hm]; rfl
  have hfm := hf.meromorphicAt
  have hid : meromorphicOrderAt (fun t : ℂ => t) 0 = ((1 : ℤ) : WithTop ℤ) := by
    have := order_monomial_zero (one_ne_zero (α := ℂ)) 1
    simpa using this
  have hP : MeromorphicAt (fun w => cubicP a (f w)) 0 := by unfold cubicP; fun_prop
  have hfgm : MeromorphicAt (fun w => f w - g w) 0 := hfm.sub hg
  have hfun : (fun t => t * auxU a f g t) =
      (fun t : ℂ => t) * (((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹) := by
    ext t; simp [auxU, div_eq_mul_inv, mul_assoc]
  rw [hfun, meromorphicOrderAt_mul
    (show MeromorphicAt (fun t : ℂ => t) 0 from analyticAt_id.meromorphicAt)
    ((hfgm.mul hfm.deriv).mul hP.inv),
    meromorphicOrderAt_mul (hfgm.mul hfm.deriv) hP.inv,
    meromorphicOrderAt_mul hfgm hfm.deriv, meromorphicOrderAt_inv,
    order_cubicP_comp hfm ha hm1 hmo, order_deriv_of_order_sub hfm hm1 hmo, hd, hid]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add,
    ← WithTop.coe_add]
  congr 1
  ring

/-- At a pole of order `s` of `f`, `t · U(t)` has order `ord(f - g) + 2s`. -/
lemma order_mul_auxU_of_pole {f g : ℂ → ℂ} (a : Fin 3 → ℂ) (hf : MeromorphicAt f 0) {s : ℕ}
    (hs : 0 < s) (hfo : meromorphicOrderAt f 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ))
    (hg : MeromorphicAt g 0) {d : ℤ} (hd : meromorphicOrderAt (fun w => f w - g w) 0 = d) :
    meromorphicOrderAt (fun t => t * auxU a f g t) 0 = ((d + 2 * s : ℤ) : WithTop ℤ) := by
  have hneg : -(s : ℤ) < 0 := by omega
  have hid : meromorphicOrderAt (fun t : ℂ => t) 0 = ((1 : ℤ) : WithTop ℤ) := by
    have := order_monomial_zero (one_ne_zero (α := ℂ)) 1
    simpa using this
  have hP : MeromorphicAt (fun w => cubicP a (f w)) 0 := by unfold cubicP; fun_prop
  have hfgm : MeromorphicAt (fun w => f w - g w) 0 := hf.sub hg
  have hder : meromorphicOrderAt (deriv f) 0 = ((-(s : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    have : meromorphicOrderAt (fun w => f w - 0) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ) := by
      simpa using hfo
    exact order_deriv_of_order_eq hf hneg.ne this
  have hfun : (fun t => t * auxU a f g t) =
      (fun t : ℂ => t) * (((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹) := by
    ext t; simp [auxU, div_eq_mul_inv, mul_assoc]
  rw [hfun, meromorphicOrderAt_mul
    (show MeromorphicAt (fun t : ℂ => t) 0 from analyticAt_id.meromorphicAt)
    ((hfgm.mul hf.deriv).mul hP.inv),
    meromorphicOrderAt_mul (hfgm.mul hf.deriv) hP.inv,
    meromorphicOrderAt_mul hfgm hf.deriv, meromorphicOrderAt_inv,
    order_cubicP_comp_of_neg hf a hneg hfo, hder, hd, hid]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add,
    ← WithTop.coe_add]
  congr 1
  ring

/-- If `f` is analytic and `g` has a pole of order `s` at `0`, then `f - g` has a pole of order
`s` there. -/
lemma order_sub_of_pole {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : MeromorphicAt g 0) {s : ℕ}
    (hs : 0 < s) (hgo : meromorphicOrderAt g 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt (fun w => f w - g w) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ) := by
  have hng : meromorphicOrderAt (fun w => -g w) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ) := by
    rw [order_neg_eq]; exact hgo
  have hfnn := hf.meromorphicOrderAt_nonneg
  have hlt : meromorphicOrderAt (fun w => -g w) 0 < meromorphicOrderAt f 0 := by
    rw [hng]
    exact lt_of_lt_of_le (by exact_mod_cast (by omega : -(s : ℤ) < 0)) hfnn
  have e : (fun w => f w - g w) = f + fun w => -g w := by ext w; simp [sub_eq_add_neg]
  rw [e, meromorphicOrderAt_add_of_ne hf.meromorphicAt
    (show MeromorphicAt (fun w => -g w) 0 from hg.neg) hlt.ne', min_eq_right hlt.le, hng]

lemma order_sub_of_pole' {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : MeromorphicAt g 0) {s : ℕ}
    (hs : 0 < s) (hgo : meromorphicOrderAt g 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt (fun w => g w - f w) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ) := by
  have e : (fun w => g w - f w) = fun w => -(f w - g w) := by ext w; ring
  rw [e, order_neg_eq]
  exact order_sub_of_pole hf hg hs hgo

/-- `V` for `(f, g)` is `-U` for `(g, f)`. -/
lemma mul_auxV_eq_neg (a : Fin 3 → ℂ) (f g : ℂ → ℂ) :
    (fun t => t * auxV a f g t) = fun t => -(t * auxU a g f t) := by
  ext t; simp only [auxV, auxU]; ring

/-! ### The exponents at the endpoint `0` -/

/-- **Lemma 9.5, exponents at `0`.**  If `R` is finite at `0` with `R(0) = a j` and `S` has a pole
of order `s ≥ 1` at `0`, then the monomials `U = α t^u`, `V = β t^v` of Lemma 9.3 have
`u = -s` and `v = s`. -/
theorem exponents_at_zero_of_pole_right {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (ha : Function.Injective a) (hRnc : ∀ c : ℂ, R ≠ RatFunc.C c)
    (hR0 : R.denom.eval 0 ≠ 0) {j : Fin 3} (hRj : ratEval R 0 = a j)
    {s : ℕ} (hs : 0 < s) (hSo : meromorphicOrderAt (ratEval S) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ))
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {u v : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u)
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) :
    u = -s ∧ v = s := by
  have hRa : AnalyticAt ℂ (ratEval R) 0 := by
    rw [funext (ratEval_eq R)]
    exact (R.num.differentiable.analyticAt 0).div (R.denom.differentiable.analyticAt 0) hR0
  have hSm := meromorphicAt_ratEval S 0
  constructor
  · have h1 := order_mul_auxU_of_analytic ha hRa hRj (order_ratEval_sub_ne_top (hRnc _) 0) hSm
      (order_sub_of_pole hRa hSm hs hSo)
    rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite hU 0),
      order_monomial_zero hα] at h1
    exact_mod_cast h1
  · have h1 := order_mul_auxU_of_pole a hSm hs hSo hRa.meromorphicAt
      (order_sub_of_pole' hRa hSm hs hSo)
    have e : (fun t => t * auxU a (ratEval S) (ratEval R) t) =
        fun t => -(t * auxV a (ratEval R) (ratEval S) t) := by
      ext t; simp only [auxV, auxU]; ring
    rw [e, order_neg_eq, meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite hV 0),
      order_monomial_zero hβ] at h1
    have : v = -(s : ℤ) + 2 * s := by exact_mod_cast h1
    omega

/-- **Lemma 9.5, exponents at `0`**, with the roles exchanged: if `R` has a pole of order `s ≥ 1`
at `0` and `S(0) = a k`, then `u = s` and `v = -s`. -/
theorem exponents_at_zero_of_pole_left {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (ha : Function.Injective a) (hSnc : ∀ c : ℂ, S ≠ RatFunc.C c)
    (hS0 : S.denom.eval 0 ≠ 0) {k : Fin 3} (hSk : ratEval S 0 = a k)
    {s : ℕ} (hs : 0 < s) (hRo : meromorphicOrderAt (ratEval R) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ))
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {u v : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u)
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) :
    u = s ∧ v = -s := by
  have hU' : ∀ᶠ t in cofinite, t * auxU a (ratEval S) (ratEval R) t = (-β) * t ^ v := by
    filter_upwards [hV] with t ht
    have := congrFun (mul_auxV_eq_neg a (ratEval R) (ratEval S)) t
    rw [neg_mul, ← ht, this, neg_neg]
  have hV' : ∀ᶠ t in cofinite, t * auxV a (ratEval S) (ratEval R) t = (-α) * t ^ u := by
    filter_upwards [hU] with t ht
    have := congrFun (mul_auxV_eq_neg a (ratEval S) (ratEval R)) t
    rw [neg_mul, ← ht, this]
  obtain ⟨h1, h2⟩ := exponents_at_zero_of_pole_right ha hSnc hS0 hSk hs hRo
    (neg_ne_zero.2 hβ) (neg_ne_zero.2 hα) hU' hV'
  exact ⟨h2, h1⟩

/-! ### The exponents at the endpoint `∞` -/

lemma mul_auxV_ratInvFun (a : Fin 3 → ℂ) (R S : RatFunc ℂ) :
    ∀ᶠ s in 𝓝[≠] 0, s * auxV a (ratInvFun R) (ratInvFun S) s =
      -(s⁻¹ * auxV a (ratEval R) (ratEval S) s⁻¹) := by
  filter_upwards [mul_auxU_ratInvFun a S R] with s hs
  have h1 := congrFun (mul_auxV_eq_neg a (ratInvFun R) (ratInvFun S)) s
  have h2 := congrFun (mul_auxV_eq_neg a (ratEval R) (ratEval S)) s⁻¹
  rw [h1, h2, hs]

lemma meromorphicAt_ratInvFun (R : RatFunc ℂ) : MeromorphicAt (ratInvFun R) 0 :=
  ((reflect (ratDeg R) R.num).differentiable.analyticAt 0).meromorphicAt.div
    ((reflect (ratDeg R) R.denom).differentiable.analyticAt 0).meromorphicAt

lemma order_ratInvFun (R : RatFunc ℂ) :
    meromorphicOrderAt (ratInvFun R) 0 = meromorphicOrderAt (fun s => ratEval R s⁻¹) 0 := by
  apply meromorphicOrderAt_congr
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ratInvFun_eq R hs

/-- **Lemma 9.5, exponents at `∞`.**  If `R` has a pole of order `r ≥ 1` at `∞` (that is,
`s ↦ R(1/s)` has a pole of order `r` at `0`) and `S(t) → a k` as `t → ∞`, then `u = -r` and
`v = r`. -/
theorem exponents_at_infty_of_pole_left {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (ha : Function.Injective a) (hSnc : ∀ c : ℂ, S ≠ RatFunc.C c)
    {r : ℕ} (hr : 0 < r)
    (hRo : meromorphicOrderAt (fun s => ratEval R s⁻¹) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ))
    {k : Fin 3} (hSk : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k)))
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {u v : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u)
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) :
    u = -r ∧ v = r := by
  obtain ⟨hQ0, hGa, hG0⟩ := ratInvFun_of_tendsto hSk
  have hFm := meromorphicAt_ratInvFun R
  have hFo : meromorphicOrderAt (ratInvFun R) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ) := by
    rw [order_ratInvFun, hRo]
  constructor
  · have h1 := order_mul_auxU_of_pole a hFm hr hFo hGa.meromorphicAt
      (order_sub_of_pole' hGa hFm hr hFo)
    rw [meromorphicOrderAt_congr (mul_auxU_ratInvFun a R S),
      meromorphicOrderAt_congr (inv_monomial_eventually hU), order_monomial_zero (neg_ne_zero.2 hα)]
      at h1
    have : -u = -(r : ℤ) + 2 * r := by exact_mod_cast h1
    omega
  · have h1 := order_mul_auxU_of_analytic ha hGa hG0 (order_ratInvFun_sub_ne_top (hSnc _) hQ0)
      hFm (order_sub_of_pole hGa hFm hr hFo)
    have e : (fun t => t * auxU a (ratInvFun S) (ratInvFun R) t) =
        fun t => -(t * auxV a (ratInvFun R) (ratInvFun S) t) := by
      ext t; simp only [auxV, auxU]; ring
    rw [e, order_neg_eq, meromorphicOrderAt_congr (mul_auxV_ratInvFun a R S),
      meromorphicOrderAt_congr (inv_monomial_eventually hV),
      order_monomial_zero (neg_ne_zero.2 hβ)] at h1
    have : -v = -(r : ℤ) := by exact_mod_cast h1
    omega

/-! ### Lemma 9.5, first part -/

/-- **Lemma 9.5, first part** (opposite endpoint poles), assuming the conclusions of Lemma 9.2.
Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` with coincidence multiplicity one on `ℂ*` and
no other coincidences or critical points there.  Suppose `R(0) = a j` is finite, `S` has a pole
of order `s ≥ 1` at `0`, `R` has a pole of order `r ≥ 1` at `∞`, and `S(t) → a k` as `t → ∞`.
Then `r = s =: ρ` and the auxiliary functions are `U = α t^{-ρ}`, `V = β t^ρ` with
`α, β ≠ 0`. -/
theorem rational_endpoint_exponents {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t)
    (hR0 : R.denom.eval 0 ≠ 0) {j : Fin 3} (hRj : ratEval R 0 = a j)
    {s : ℕ} (hs : 0 < s) (hSo : meromorphicOrderAt (ratEval S) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ))
    {r : ℕ} (hr : 0 < r)
    (hRo : meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ))
    {k : Fin 3} (hSk : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k))) :
    r = s ∧ ∃ α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧
      (∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ (-(s : ℤ))) ∧
      (∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ (s : ℤ)) := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨α, β, hα, hβ, u, v, hU, hV, -⟩ := rational_monomials hpair hco
  obtain ⟨hu0, hv0⟩ := exponents_at_zero_of_pole_right hpair.injective hRnc hR0 hRj hs hSo
    hα hβ hU hV
  obtain ⟨hu1, -⟩ := exponents_at_infty_of_pole_left hpair.injective hSnc hr hRo hSk hα hβ hU hV
  refine ⟨by omega, α, β, hα, hβ, ?_, ?_⟩
  · rwa [← hu0]
  · rwa [← hv0]

/-- **Lemma 9.5**, first step: the same map cannot be infinite at both endpoints while the other
one is finite at both (with values in `{a 0, a 1, a 2}`), since `U` would then vanish at both
endpoints, which is impossible for a monomial `α t^u`. -/
theorem rational_not_pole_both_endpoints {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t)
    {s : ℕ} (hs : 0 < s) (hRo : meromorphicOrderAt (ratEval R) 0 = ((-(s : ℤ) : ℤ) : WithTop ℤ))
    (hS0 : S.denom.eval 0 ≠ 0) {k : Fin 3} (hSk : ratEval S 0 = a k)
    {r : ℕ} (hr : 0 < r)
    (hRo' : meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ))
    {k' : Fin 3} (hSk' : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k'))) : False := by
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨α, β, hα, hβ, u, v, hU, hV, -⟩ := rational_monomials hpair hco
  obtain ⟨hu0, -⟩ := exponents_at_zero_of_pole_left hpair.injective hSnc hS0 hSk hs hRo
    hα hβ hU hV
  obtain ⟨hu1, -⟩ := exponents_at_infty_of_pole_left hpair.injective hSnc hr hRo' hSk'
    hα hβ hU hV
  omega

end ThreeIM
