module

public import RequestProject.ThreeIM.Pullback

/-!
# Rational auxiliary functions (Lemma 9.3)

For a rational sharing datum `R, S` (three finite values shared IM and `∞` shared CM on `ℂ*`),
Lemma 9.2 (saturation of the degree bounds) shows:

* at a finite common point the coincidence multiplicity `ord (R - S)` is one;
* every common pole in `ℂ*` is simple, with different residues, i.e. `ord (R - S) = -1`;
* away from the four fibers neither map is critical and the maps do not coincide.

We record these local conclusions in the predicate `SaturatedAt`.  Under them we prove
**Lemma 9.3**: the auxiliary functions `U = (R - S) DR / P(R)` and `V = (R - S) DS / P(S)`
(with `D = t d/dt`) have neither zeros nor poles on `ℂ*`, hence are monomials `α t^u`, `β t^v`;
and at a finite common point `U/V = m/n`.

In Lean, `auxU` is `(f - g) f' / P(f)`, so the paper's `U` is `t ↦ t * auxU t`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- The local conclusions of **Lemma 9.2** (saturation of the degree bounds) at a point `z`:
coincidence multiplicity one at finite common points, simple common poles with different
residues (`ord (f - g) = -1`), and, outside the four fibers, no coincidence and no critical
point of either map. -/
structure SaturatedAt (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (z : ℂ) : Prop where
  shared : ∀ j, 0 < mult f (a j : Sphere) z →
    meromorphicOrderAt (fun w => f w - g w) z = ((1 : ℤ) : WithTop ℤ)
  pole : 0 < mult f ⊤ z →
    mult f ⊤ z = 1 ∧ meromorphicOrderAt (fun w => f w - g w) z = ((-1 : ℤ) : WithTop ℤ)
  generic : (∀ j, mult f (a j : Sphere) z = 0) → mult f ⊤ z = 0 →
    meromorphicOrderAt (fun w => f w - g w) z = 0 ∧ meromorphicOrderAt (deriv f) z = 0 ∧
      meromorphicOrderAt (deriv g) z = 0

variable {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {z : ℂ}

/-- The saturation conditions are symmetric in the two members of a normalized pair. -/
lemma SaturatedAt.symm (h : NormalizedPair Ω f g a) (hz : z ∈ Ω) (hs : SaturatedAt a f g z) :
    SaturatedAt a g f z := by
  have e : (fun w => g w - f w) = fun w => -(f w - g w) := by ext; ring
  refine ⟨fun j hj => ?_, fun hp => ?_, fun hj hp => ?_⟩
  · rw [e, order_neg_eq]; exact hs.shared j ((h.im j z hz).2 hj)
  · rw [← h.cm_top z hz] at hp ⊢
    rw [e, order_neg_eq]; exact hs.pole hp
  · have hj' : ∀ j, mult f (a j : Sphere) z = 0 := fun j => by
      have := (h.im j z hz).not; simp only [not_lt, nonpos_iff_eq_zero] at this
      exact this.2 (hj j)
    obtain ⟨h1, h2, h3⟩ := hs.generic hj' (by rw [h.cm_top z hz]; exact hp)
    rw [e, order_neg_eq]; exact ⟨h1, h3, h2⟩

/-- The conclusions of **Lemma 9.2** at a point, in the paper's formulation: the coincidence
multiplicity (the order of `χ ∘ f - χ ∘ g` for a local coordinate `χ` at the common value, here
`χ(w) = w - c` at a finite value and `χ(w) = 1/w` at `∞`) is one at every common point of the
four fibers, and outside these fibers there is neither a coincidence nor a critical point. -/
structure CoincidenceSimpleAt (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (z : ℂ) : Prop where
  shared : ∀ j, 0 < mult f (a j : Sphere) z →
    meromorphicOrderAt (fun w => f w - g w) z = ((1 : ℤ) : WithTop ℤ)
  pole : 0 < mult f ⊤ z →
    meromorphicOrderAt (fun w => (f w)⁻¹ - (g w)⁻¹) z = ((1 : ℤ) : WithTop ℤ)
  generic : (∀ j, mult f (a j : Sphere) z = 0) → mult f ⊤ z = 0 →
    meromorphicOrderAt (fun w => f w - g w) z = 0 ∧ meromorphicOrderAt (deriv f) z = 0 ∧
      meromorphicOrderAt (deriv g) z = 0

/-- At a common pole with coincidence multiplicity one (for the coordinate `1/w`), the pole is
simple for both maps and `ord (f - g) = -1`, i.e. the residues differ (last part of
Lemma 9.2). -/
lemma NormalizedPair.pole_of_coincidence (h : NormalizedPair Ω f g a) (hz : z ∈ Ω)
    (hp : 0 < mult f ⊤ z)
    (hc : meromorphicOrderAt (fun w => (f w)⁻¹ - (g w)⁻¹) z = ((1 : ℤ) : WithTop ℤ)) :
    mult f ⊤ z = 1 ∧ meromorphicOrderAt (fun w => f w - g w) z = ((-1 : ℤ) : WithTop ℤ) := by
  have hfm := h.nonconst_f.1 z hz
  have hgm := h.nonconst_g.1 z hz
  have hp' : 0 < mult g ⊤ z := by rw [← h.cm_top z hz]; exact hp
  have hof := order_eq_neg_mult_top hp
  have hog := order_eq_neg_mult_top hp'
  rw [← h.cm_top z hz] at hog
  set k := mult f ⊤ z with hk
  have hif : meromorphicOrderAt (fun w => (f w)⁻¹) z = ((k : ℤ) : WithTop ℤ) := by
    rw [show (fun w => (f w)⁻¹) = f⁻¹ from rfl, meromorphicOrderAt_inv, hof,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg]
  have hig : meromorphicOrderAt (fun w => -(g w)⁻¹) z = ((k : ℤ) : WithTop ℤ) := by
    rw [order_neg_eq, show (fun w => (g w)⁻¹) = g⁻¹ from rfl, meromorphicOrderAt_inv, hog,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg]
  have hmin : min (meromorphicOrderAt (fun w => (f w)⁻¹) z)
      (meromorphicOrderAt (fun w => -(g w)⁻¹) z) ≤
      meromorphicOrderAt (fun w => (f w)⁻¹ - (g w)⁻¹) z := by
    have : (fun w => (f w)⁻¹ - (g w)⁻¹) = (fun w => (f w)⁻¹) + fun w => -(g w)⁻¹ := by
      ext w; simp [sub_eq_add_neg]
    rw [this]
    exact meromorphicOrderAt_add hfm.inv hgm.inv.neg
  rw [hif, hig, min_self, hc] at hmin
  have hk1 : k = 1 := by
    have : (k : ℤ) ≤ 1 := by exact_mod_cast hmin
    omega
  refine ⟨hk1, ?_⟩
  have hfne : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hfm).1 (by rw [hof]; simp)
  have hgne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hgm).1 (by rw [hog]; simp)
  have heq : (fun w => f w - g w) =ᶠ[𝓝[≠] z]
      ((fun w => -((f w)⁻¹ - (g w)⁻¹)) * f) * g := by
    filter_upwards [hfne, hgne] with w h1 h2
    simp only [Pi.mul_apply]
    field_simp
    ring
  have hd : MeromorphicAt (fun w => -((f w)⁻¹ - (g w)⁻¹)) z := (hfm.inv.sub hgm.inv).neg
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul (hd.mul hfm) hgm,
    meromorphicOrderAt_mul hd hfm, order_neg_eq, hc, hof, hog, hk1]
  rw [← WithTop.coe_add, ← WithTop.coe_add]
  norm_num

/-- The paper's formulation of the conclusions of Lemma 9.2 implies the saturation conditions
used below. -/
lemma NormalizedPair.saturatedAt_of_coincidenceSimpleAt (h : NormalizedPair Ω f g a)
    (hz : z ∈ Ω) (hc : CoincidenceSimpleAt a f g z) : SaturatedAt a f g z :=
  ⟨hc.shared, fun hp => h.pole_of_coincidence hz hp (hc.pole hp), hc.generic⟩

/-- **Lemma 9.3**, local part, for `U`: under the saturation conditions of Lemma 9.2, the
auxiliary function `U` of a normalized pair has order zero (neither zero nor pole). -/
theorem NormalizedPair.order_auxU_eq_zero (h : NormalizedPair Ω f g a) (hz : z ∈ Ω)
    (hs : SaturatedAt a f g z) : meromorphicOrderAt (auxU a f g) z = 0 := by
  have hfm := h.nonconst_f.1 z hz
  have hgm := h.nonconst_g.1 z hz
  have hfg : MeromorphicAt (fun w => f w - g w) z := hfm.sub hgm
  have hPf : MeromorphicAt (fun w => cubicP a (f w)) z := by unfold cubicP; fun_prop
  have hU : auxU a f g = ((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹ := by
    ext w; simp [auxU, div_eq_mul_inv]
  by_cases hpole : 0 < mult f ⊤ z
  · obtain ⟨h1, hd⟩ := hs.pole hpole
    have hof := order_eq_neg_mult_top hpole
    rw [h1] at hof
    have h2 : meromorphicOrderAt (deriv f) z = ((-((1 : ℕ) : ℤ) - 1 : ℤ) : WithTop ℤ) := by
      have : meromorphicOrderAt (fun w => f w - 0) z = ((-((1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
        rw [show (fun w => f w - 0) = f by ext; simp]; exact hof
      exact order_deriv_of_order_eq hfm (by norm_num) this
    have h3 := order_cubicP_comp_of_neg hfm a (by norm_num : -((1 : ℕ) : ℤ) < 0) hof
    rw [hU, meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPf.inv,
      meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv, h2, h3, hd]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
    norm_num
  · by_cases hshared : ∃ j, 0 < mult f (a j : Sphere) z
    · obtain ⟨j, hj⟩ := hshared
      have hj' := (h.im j z hz).1 hj
      rw [(order_aux_at_shared hfm hgm h.injective hj hj' (order_sub_eq_mult hj)
        (order_sub_eq_mult hj') (hs.shared j hj)).1]
      simp
    · push_neg at hshared
      have hj0 : ∀ j, mult f (a j : Sphere) z = 0 := fun j => by have := hshared j; omega
      have hp0 : mult f ⊤ z = 0 := by omega
      obtain ⟨hd, hD, -⟩ := hs.generic hj0 hp0
      have hfnn := order_nonneg_of_mult_top_eq_zero hp0 (order_ne_top_of_nonconst h.nonconst_f hz)
      have hzero : ∀ i, meromorphicOrderAt (fun w => f w - a i) z = 0 := fun i =>
        le_antisymm (order_sub_nonpos_of_mult_eq_zero (hj0 i) (h.nonconst_f.2 z hz (a i)))
          (order_sub_const_nonneg hfm hfnn (a i))
      have h3 := order_cubicP_comp_eq_zero hfm a hzero
      rw [hU, meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPf.inv,
        meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv, h3, hd, hD]
      simp

/-- **Lemma 9.3**, local part, for `V`. -/
theorem NormalizedPair.order_auxV_eq_zero (h : NormalizedPair Ω f g a) (hz : z ∈ Ω)
    (hs : SaturatedAt a f g z) : meromorphicOrderAt (auxV a f g) z = 0 := by
  have hVeq : auxV a f g = fun w => -auxU a g f w := by
    ext w; simp only [auxV, auxU]; ring
  rw [hVeq, order_neg_eq]
  exact h.symm.order_auxU_eq_zero hz (hs.symm h hz)

/-! ### Rational functions with neither zeros nor poles on `ℂ*` -/

lemma eventually_nhdsNE_of_cofinite {p : ℂ → Prop} (h : ∀ᶠ t in cofinite, p t) (x : ℂ) :
    ∀ᶠ t in 𝓝[≠] x, p t := by
  have hfin : ({t | ¬ p t} \ {x} : Set ℂ).Finite :=
    (Filter.eventually_cofinite.1 h).subset diff_subset
  have hmem : ({t | ¬ p t} \ {x} : Set ℂ)ᶜ ∈ 𝓝 x :=
    hfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t ht htx
  by_contra hp
  exact ht ⟨hp, htx⟩

/-- The rational function `p / q` evaluates to `p(t) / q(t)` off a finite set. -/
lemma ratEval_div_eventually (p q : ℂ[X]) (hq : q ≠ 0) :
    ∀ᶠ t in cofinite, ratEval (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) t =
      p.eval t / q.eval t := by
  set H := algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q with hH
  have hq' : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hd' : algebraMap ℂ[X] (RatFunc ℂ) H.denom ≠ 0 := RatFunc.algebraMap_ne_zero H.denom_ne_zero
  have key : H.num * q = p * H.denom := by
    apply RatFunc.algebraMap_injective ℂ
    have : algebraMap ℂ[X] (RatFunc ℂ) H.num / algebraMap ℂ[X] (RatFunc ℂ) H.denom =
        algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q := RatFunc.num_div_denom H
    rw [div_eq_div_iff hd' hq'] at this
    rw [map_mul, map_mul, this]
  have hfin : ({t | q.eval t = 0} ∪ {t | H.denom.eval t = 0} : Set ℂ).Finite :=
    (q.finite_setOf_isRoot hq).union (H.denom.finite_setOf_isRoot H.denom_ne_zero)
  filter_upwards [hfin.compl_mem_cofinite] with t ht
  simp only [mem_compl_iff, mem_union, mem_setOf_eq, not_or] at ht
  rw [ratEval_eq, div_eq_div_iff ht.2 ht.1]
  have := congrArg (Polynomial.eval t) key
  simpa only [eval_mul] using this

/-- A monomial `α X^u` evaluates to `α t^u` off a finite set. -/
lemma ratEval_monomial_eventually (α : ℂ) (u : ℤ) :
    ∀ᶠ t in cofinite, ratEval (RatFunc.C α * RatFunc.X ^ u) t = α * t ^ u := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg u
  · have : RatFunc.C α * RatFunc.X ^ (n : ℤ) =
        algebraMap ℂ[X] (RatFunc ℂ) (C α * X ^ n) / algebraMap ℂ[X] (RatFunc ℂ) 1 := by
      simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    filter_upwards [ratEval_div_eventually (C α * X ^ n) 1 one_ne_zero] with t ht
    rw [this, ht]; simp
  · have : RatFunc.C α * RatFunc.X ^ (-(n : ℤ)) =
        algebraMap ℂ[X] (RatFunc ℂ) (C α) / algebraMap ℂ[X] (RatFunc ℂ) (X ^ n) := by
      rw [zpow_neg, zpow_natCast]
      simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X, div_eq_mul_inv]
    filter_upwards [ratEval_div_eventually (C α) (X ^ n) (pow_ne_zero _ X_ne_zero)] with t ht
    rw [this, ht]; simp [zpow_neg, div_eq_mul_inv]

/-- A function which agrees with a quotient of polynomials off a finite set, and which has
neither zeros nor poles on `ℂ*`, agrees with a monomial `α t^u` off a finite set. -/
theorem eventually_eq_monomial_of_order {F : ℂ → ℂ} {p q : ℂ[X]}
    (hF : ∀ᶠ t in cofinite, F t = p.eval t / q.eval t)
    (hord : ∀ t : ℂ, t ≠ 0 → meromorphicOrderAt F t = 0) :
    ∃ α : ℂ, α ≠ 0 ∧ ∃ u : ℤ, ∀ᶠ t in cofinite, F t = α * t ^ u := by
  by_cases hq : q = 0
  · exfalso
    have h0 : F =ᶠ[𝓝[≠] 1] fun _ => (0 : ℂ) :=
      eventually_nhdsNE_of_cofinite (hF.mono fun t ht => by simp [ht, hq]) 1
    have := hord 1 one_ne_zero
    rw [meromorphicOrderAt_congr h0, meromorphicOrderAt_const] at this
    simp at this
  set H := algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q
  have hHF : ∀ᶠ t in cofinite, ratEval H t = F t := by
    filter_upwards [ratEval_div_eventually p q hq, hF] with t h1 h2
    rw [h1, h2]
  have hordH : ∀ t : ℂ, t ≠ 0 → meromorphicOrderAt (ratEval H) t = 0 := fun t ht => by
    rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite hHF t), hord t ht]
  obtain ⟨α, hα, u, hu⟩ := ratFunc_eq_monomial_of_order hordH
  refine ⟨α, hα, u, ?_⟩
  filter_upwards [hHF, ratEval_monomial_eventually α u] with t h1 h2
  rw [← h1, hu, h2]

/-! ### The auxiliary functions of two rational functions are rational -/

/-- Numerator of `t · U` for `f = A/B`, `g = C/E`. -/
noncomputable def auxUNum (A B C E : ℂ[X]) : ℂ[X] :=
  X * (A * E - C * B) * (derivative A * B - A * derivative B)

/-- Denominator of `t · U` for `f = A/B`, `g = C/E`. -/
noncomputable def auxUDen (a : Fin 3 → ℂ) (A B E : ℂ[X]) : ℂ[X] :=
  E * ((A - Polynomial.C (a 0) * B) * (A - Polynomial.C (a 1) * B) * (A - Polynomial.C (a 2) * B))

/-- For `f = A/B` and `g = C/E` with polynomials, `t · U(t)` is the quotient of the
polynomials `auxUNum`, `auxUDen` at every `t` with `B(t) E(t) ≠ 0`. -/
lemma mul_auxU_poly_eq (a : Fin 3 → ℂ) (A B C E : ℂ[X]) {t : ℂ} (hB : B.eval t ≠ 0)
    (hE : E.eval t ≠ 0) :
    t * auxU a (fun x => A.eval x / B.eval x) (fun x => C.eval x / E.eval x) t =
      (auxUNum A B C E).eval t / (auxUDen a A B E).eval t := by
  have hd : deriv (fun x => A.eval x / B.eval x) t =
      ((derivative A).eval t * B.eval t - A.eval t * (derivative B).eval t) / B.eval t ^ 2 :=
    ((A.hasDerivAt t).div (B.hasDerivAt t) hB).deriv
  simp only [auxU, hd, auxUNum, auxUDen, cubicP, eval_mul, eval_sub, eval_X, eval_C]
  set Q := (A.eval t - a 0 * B.eval t) * (A.eval t - a 1 * B.eval t) *
    (A.eval t - a 2 * B.eval t) with hQ
  have hP : (A.eval t / B.eval t - a 0) * (A.eval t / B.eval t - a 1) *
      (A.eval t / B.eval t - a 2) = Q / B.eval t ^ 3 := by
    rw [hQ]; field_simp
  rw [hP]
  rcases eq_or_ne Q 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

/-- `t · U` for two rational functions agrees with a quotient of polynomials off a finite set. -/
lemma mul_auxU_ratEval_eventually (a : Fin 3 → ℂ) (R S : RatFunc ℂ) :
    ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t =
      (auxUNum R.num R.denom S.num S.denom).eval t / (auxUDen a R.num R.denom S.denom).eval t := by
  have hfin : ({t | R.denom.eval t = 0} ∪ {t | S.denom.eval t = 0} : Set ℂ).Finite :=
    (R.denom.finite_setOf_isRoot R.denom_ne_zero).union
      (S.denom.finite_setOf_isRoot S.denom_ne_zero)
  filter_upwards [hfin.compl_mem_cofinite] with t ht
  simp only [mem_compl_iff, mem_union, mem_setOf_eq, not_or] at ht
  rw [show ratEval R = fun x => R.num.eval x / R.denom.eval x from funext (ratEval_eq R),
    show ratEval S = fun x => S.num.eval x / S.denom.eval x from funext (ratEval_eq S)]
  exact mul_auxU_poly_eq a _ _ _ _ ht.1 ht.2

lemma order_mul_id_eq {F : ℂ → ℂ} {t : ℂ} (ht : t ≠ 0) (hF : MeromorphicAt F t) :
    meromorphicOrderAt (fun x => x * F x) t = meromorphicOrderAt F t := by
  have hid : meromorphicOrderAt (fun x : ℂ => x) t = 0 := by
    have := (order_poly_eq_zero_iff (X : ℂ[X]) t).2 (by simpa using ht)
    simpa using this
  have hm : MeromorphicAt (fun x : ℂ => x) t := analyticAt_id.meromorphicAt
  rw [show (fun x => x * F x) = (fun x : ℂ => x) * F from rfl,
    meromorphicOrderAt_mul hm hF, hid, zero_add]

lemma meromorphicAt_auxU_ratEval (a : Fin 3 → ℂ) (R S : RatFunc ℂ) (t : ℂ) :
    MeromorphicAt (auxU a (ratEval R) (ratEval S)) t := by
  have hR := meromorphicAt_ratEval R t
  have hS := meromorphicAt_ratEval S t
  have hR' := hR.deriv
  unfold auxU cubicP
  fun_prop

/-- **Lemma 9.3** (rational auxiliary functions), assuming the conclusions of Lemma 9.2.
Let `R, S` be rational functions forming a normalized pair on `ℂ*` (distinct, nonconstant,
sharing three distinct finite values IM and `∞` CM there), which satisfy the saturation
conditions of Lemma 9.2 at every point of `ℂ*`.  Then the auxiliary functions
`U = (R - S) t R'/P(R)` and `V = (R - S) t S'/P(S)` are monomials:
`U = α t^u` and `V = β t^v` (off a finite set), with `α, β ≠ 0`. -/
theorem rational_aux_monomial {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hsat : ∀ t : ℂ, t ≠ 0 → SaturatedAt a (ratEval R) (ratEval S) t) :
    (∃ α : ℂ, α ≠ 0 ∧ ∃ u : ℤ,
      ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u) ∧
    (∃ β : ℂ, β ≠ 0 ∧ ∃ v : ℤ,
      ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) := by
  constructor
  · refine eventually_eq_monomial_of_order (mul_auxU_ratEval_eventually a R S) fun t ht => ?_
    rw [order_mul_id_eq ht (meromorphicAt_auxU_ratEval a R S t)]
    exact hpair.order_auxU_eq_zero ht (hsat t ht)
  · have hVeq : auxV a (ratEval R) (ratEval S) = fun w => -auxU a (ratEval S) (ratEval R) w := by
      ext w; simp only [auxV, auxU]; ring
    refine eventually_eq_monomial_of_order (p := -auxUNum S.num S.denom R.num R.denom)
      (q := auxUDen a S.num S.denom R.denom) ?_ fun t ht => ?_
    · filter_upwards [mul_auxU_ratEval_eventually a S R] with t h
      rw [hVeq, eval_neg, neg_div, ← h]; ring
    · rw [order_mul_id_eq ht, hVeq, order_neg_eq]
      · exact hpair.symm.order_auxU_eq_zero ht ((hsat t ht).symm hpair ht)
      · rw [hVeq]; exact (meromorphicAt_auxU_ratEval a S R t).neg

/-- **Lemma 9.3**, ratio at finite common points (stated for any normalized pair on `ℂ*`):
if `U = α t^u` and `V = β t^v` (off a finite
set), then at every finite common point `t₀ ∈ ℂ*` with multiplicities `m, n`,
`U(t₀)/V(t₀) = m/n`, i.e. `α t₀^u · n = β t₀^v · m`. -/
theorem rational_aux_ratio {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ f g a) {α β : ℂ} (hβ : β ≠ 0) {u v : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ u)
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ v)
    {t₀ : ℂ} (ht₀ : t₀ ≠ 0) {j : Fin 3} (hj : 0 < mult f (a j : Sphere) t₀) :
    α * t₀ ^ u * (mult g (a j : Sphere) t₀ : ℂ) =
      β * t₀ ^ v * (mult f (a j : Sphere) t₀ : ℂ) := by
  have hj' := (hpair.im j t₀ ht₀).1 hj
  have hlim := tendsto_auxPhi_at_shared (hpair.nonconst_f.1 t₀ ht₀)
    (hpair.nonconst_g.1 t₀ ht₀)
    hpair.injective hj hj' (order_sub_eq_mult hj) (order_sub_eq_mult hj') (hpair.distinct t₀ ht₀)
  have heq : auxPhi a f g =ᶠ[𝓝[≠] t₀]
      fun t => α * t ^ u / (β * t ^ v) := by
    filter_upwards [eventually_nhdsNE_of_cofinite hU t₀, eventually_nhdsNE_of_cofinite hV t₀,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t h1 h2 ht
    simp only [auxPhi]
    rw [← h1, ← h2, mul_div_mul_left _ _ ht]
  have hcont : Tendsto (fun t => α * t ^ u / (β * t ^ v)) (𝓝[≠] t₀)
      (𝓝 (α * t₀ ^ u / (β * t₀ ^ v))) :=
    ((((continuousAt_zpow₀ t₀ u (Or.inl ht₀)).const_mul α).div
      ((continuousAt_zpow₀ t₀ v (Or.inl ht₀)).const_mul β)
      (mul_ne_zero hβ (zpow_ne_zero v ht₀)))).mono_left nhdsWithin_le_nhds
  have hval := tendsto_nhds_unique (hcont.congr' heq.symm) hlim
  have hm0 : (mult g (a j : Sphere) t₀ : ℂ) ≠ 0 := by exact_mod_cast hj'.ne'
  rw [div_eq_div_iff (mul_ne_zero hβ (zpow_ne_zero v ht₀)) hm0] at hval
  linear_combination hval

/-- **Lemma 9.3** (rational auxiliary functions), full statement, assuming the conclusions of
Lemma 9.2 in the paper's formulation (coincidence multiplicity one at the common points of the
four fibers in `ℂ*`; no other coincidences or critical points in `ℂ*`).  For rational `R, S`
forming a normalized pair on `ℂ*`, the auxiliary functions `U = (R - S) DR/P(R)` and
`V = (R - S) DS/P(S)` (`D = t d/dt`) are `α t^u` and `β t^v` with `α, β ≠ 0` (off a finite set),
and `U(t₀)/V(t₀) = m(t₀)/n(t₀)` at each finite common point `t₀ ∈ ℂ*`. -/
theorem rational_monomials {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t) :
    ∃ α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧ ∃ u v : ℤ,
      (∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u) ∧
      (∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) ∧
      ∀ t₀ : ℂ, t₀ ≠ 0 → ∀ j : Fin 3, 0 < mult (ratEval R) (a j : Sphere) t₀ →
        α * t₀ ^ u * (mult (ratEval S) (a j : Sphere) t₀ : ℂ) =
          β * t₀ ^ v * (mult (ratEval R) (a j : Sphere) t₀ : ℂ) := by
  obtain ⟨⟨α, hα, u, hU⟩, ⟨β, hβ, v, hV⟩⟩ := rational_aux_monomial hpair
    (fun t ht => hpair.saturatedAt_of_coincidenceSimpleAt ht (hco t ht))
  exact ⟨α, β, hα, hβ, u, v, hU, hV, fun t₀ ht₀ j hj =>
    rational_aux_ratio hpair hβ hU hV ht₀ hj⟩

end ThreeIM
