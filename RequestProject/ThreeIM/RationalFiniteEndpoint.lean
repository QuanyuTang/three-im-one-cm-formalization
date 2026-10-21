module

public import RequestProject.ThreeIM.RationalReality

/-!
# The finite endpoint case (Lemma 9.4)

For a rational sharing datum `R, S` (three finite values `a 0, a 1, a 2` shared IM and `∞`
shared CM on `ℂ*`), assume the conclusions of Lemma 9.2: coincidence multiplicity one at the
common points in `ℂ*` and no other coincidences or critical points there, equal degrees, and,
if both maps are finite at the endpoint `0`, distinct values `R(0), S(0)` in `{a 0, a 1, a 2}`.
Then all four values are shared CM on `ℂ*` (**Lemma 9.4**, endpoint `0`).

The proof follows the paper: the auxiliary functions `U, V` have order zero at `0`, so the
monomials of Lemma 9.3 are constants `α, β`; at a finite common point `α n = β m`.  Counting
multiplicities of a value omitted by `S` (resp. `R`) at the endpoints, using that a rational
function of degree `d` takes every value, except possibly one, exactly `d` times on `ℂ`,
gives `α = β`, hence `m = n` at every finite common point.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-! ### Multiplicities of a rational function and root multiplicities -/

/-- Order of a polynomial quotient at a point where the denominator does not vanish. -/
lemma order_polyQuot_of_denom_ne_zero {P Q : ℂ[X]} (hP : P ≠ 0) {z : ℂ} (hQ : Q.eval z ≠ 0) :
    meromorphicOrderAt (fun w => P.eval w / Q.eval w) z =
      (((P.rootMultiplicity z : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP z
  have hrz : r.eval z ≠ 0 := fun h => hdvd (dvd_iff_isRoot.2 h)
  have hf : MeromorphicAt (fun w => P.eval w / Q.eval w) z :=
    (P.differentiable.analyticAt z).meromorphicAt.div (Q.differentiable.analyticAt z).meromorphicAt
  rw [meromorphicOrderAt_eq_int_iff hf]
  refine ⟨fun w => r.eval w / Q.eval w,
    (r.differentiable.analyticAt z).div (Q.differentiable.analyticAt z) hQ, by simp [hQ, hrz], ?_⟩
  filter_upwards with w
  conv_lhs => rw [hr]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul, zpow_natCast]
  ring

/-- The `b`-multiplicity of a rational function at `t` is the root multiplicity of
`num - b · denom` at `t`. -/
lemma mult_ratEval_eq_rootMultiplicity (R : RatFunc ℂ) {b : ℂ}
    (hb : R.num - Polynomial.C b * R.denom ≠ 0) (t : ℂ) :
    mult (ratEval R) (b : Sphere) t = (R.num - Polynomial.C b * R.denom).rootMultiplicity t := by
  rw [mult_coe]
  set N := R.num - Polynomial.C b * R.denom with hN
  have heq : (fun w => ratEval R w - b) =ᶠ[𝓝[≠] t] fun w => N.eval w / R.denom.eval w := by
    filter_upwards [polynomial_eventually_ne_zero R.denom_ne_zero t] with w hw
    rw [ratEval_eq, hN]
    simp only [eval_sub, eval_mul, eval_C]
    field_simp
  rw [meromorphicOrderAt_congr heq]
  by_cases hd : R.denom.eval t = 0
  · have hn : R.num.eval t ≠ 0 := by
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom R
      intro h0
      have := congrArg (eval t) huv
      simp only [eval_add, eval_mul, h0, hd, mul_zero, add_zero, eval_one] at this
      exact zero_ne_one this
    have hNt : N.eval t ≠ 0 := by simp [hN, hd, hn]
    rw [rootMultiplicity_eq_zero hNt, order_polyQuot R.denom_ne_zero hNt, WithTop.untop₀_coe]
    simp
  · rw [order_polyQuot_of_denom_ne_zero hb hd, WithTop.untop₀_coe]
    simp

/-- The root multiplicities of a polynomial over `ℂ`, summed over any finite set, are at most
its degree. -/
lemma sum_rootMultiplicity_le (N : ℂ[X]) (A : Finset ℂ) :
    ∑ t ∈ A, N.rootMultiplicity t ≤ N.natDegree := by
  classical
  calc ∑ t ∈ A, N.rootMultiplicity t = ∑ t ∈ A, N.roots.count t := by simp [count_roots]
    _ ≤ ∑ t ∈ A ∪ N.roots.toFinset, N.roots.count t :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ t ∈ N.roots.toFinset, N.roots.count t :=
      (Finset.sum_subset Finset.subset_union_right
        (fun x _ hx => Multiset.count_eq_zero.2 (by simpa using hx))).symm
    _ = Multiset.card N.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ N.natDegree := card_roots' N

/-- For a polynomial over `ℂ`, the root multiplicities summed over the nonzero roots equal the
degree minus the multiplicity of `0`. -/
lemma sum_rootMultiplicity_nonzero (N : ℂ[X]) :
    ∑ t ∈ N.roots.toFinset.erase 0, N.rootMultiplicity t + N.rootMultiplicity 0 =
      N.natDegree := by
  classical
  have hcard : ∑ t ∈ N.roots.toFinset, N.rootMultiplicity t = N.natDegree := by
    rw [← IsAlgClosed.card_roots_eq_natDegree, ← Multiset.toFinset_sum_count_eq]
    simp [count_roots]
  by_cases h0 : (0 : ℂ) ∈ N.roots.toFinset
  · rw [Finset.sum_erase_add _ _ h0, hcard]
  · have : N.rootMultiplicity 0 = 0 := by
      rw [← count_roots]; exact Multiset.count_eq_zero.2 (by simpa using h0)
    rw [Finset.erase_eq_of_notMem h0, this, add_zero, hcard]

/-- `num - b · denom` has degree at most `max (deg num) (deg denom)`, with equality for all `b`
except at most one. -/
lemma natDegree_num_sub_le (R : RatFunc ℂ) (b : ℂ) :
    (R.num - Polynomial.C b * R.denom).natDegree ≤ max R.num.natDegree R.denom.natDegree := by
  exact (natDegree_sub_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le _ _))

lemma exists_natDegree_num_sub_eq (R : RatFunc ℂ) :
    ∃ e : ℂ, ∀ b : ℂ, b ≠ e →
      (R.num - Polynomial.C b * R.denom).natDegree = max R.num.natDegree R.denom.natDegree := by
  rcases lt_trichotomy R.num.natDegree R.denom.natDegree with h | h | h
  · refine ⟨0, fun b hb => ?_⟩
    rw [max_eq_right h.le, natDegree_sub_eq_right_of_natDegree_lt (by rwa [natDegree_C_mul hb]),
      natDegree_C_mul hb]
  · refine ⟨R.num.leadingCoeff / R.denom.leadingCoeff, fun b hb => ?_⟩
    rw [← h, max_self]
    apply le_antisymm ((natDegree_num_sub_le R b).trans (by rw [h, max_self]))
    apply le_natDegree_of_ne_zero
    rw [coeff_sub, coeff_C_mul]
    have hD : R.denom.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 R.denom_ne_zero
    intro h0
    apply hb
    rw [eq_div_iff hD]
    have e1 : R.num.coeff R.num.natDegree = R.num.leadingCoeff := rfl
    have e2 : R.denom.coeff R.num.natDegree = R.denom.leadingCoeff := by rw [h]; rfl
    rw [e1, e2] at h0
    linear_combination -h0
  · refine ⟨0, fun b _ => ?_⟩
    rw [max_eq_left h.le]
    exact natDegree_sub_eq_left_of_natDegree_lt (lt_of_le_of_lt (natDegree_C_mul_le _ _) h)

/-- A rational function whose function `ratEval` is nonconstant on a punctured set is not a
constant rational function. -/
lemma ne_C_of_nonconst {R : RatFunc ℂ} (h : IsNonconstMeroOn (ratEval R) {0}ᶜ) (c : ℂ) :
    R ≠ RatFunc.C c := by
  intro hc
  apply h.2 1 (by norm_num) c
  have : (fun w => ratEval R w - c) = fun _ => (0 : ℂ) := by
    funext w; simp [ratEval, hc, RatFunc.eval_C]
  rw [this, meromorphicOrderAt_const]
  simp

lemma num_sub_ne_zero {R : RatFunc ℂ} {c : ℂ} (h : R ≠ RatFunc.C c) :
    R.num - Polynomial.C c * R.denom ≠ 0 := by
  intro h0
  apply h
  rw [sub_eq_zero] at h0
  have hd : (algebraMap (Polynomial ℂ) (RatFunc ℂ) R.denom) ≠ 0 :=
    RatFunc.algebraMap_ne_zero R.denom_ne_zero
  rw [← RatFunc.num_div_denom R, h0, map_mul, mul_div_assoc, div_self hd, mul_one]
  simp [RatFunc.algebraMap_C]

/-- A nonconstant rational function has positive degree. -/
lemma max_natDegree_pos {R : RatFunc ℂ} (h : ∀ c : ℂ, R ≠ RatFunc.C c) :
    0 < max R.num.natDegree R.denom.natDegree := by
  by_contra hle
  push_neg at hle
  have h1 : R.num.natDegree = 0 := by omega
  have h2 : R.denom.natDegree = 0 := by omega
  apply h (R.num.coeff 0)
  have hd : R.denom = 1 := Polynomial.eq_one_of_monic_natDegree_zero R.monic_denom h2
  conv_lhs => rw [← RatFunc.num_div_denom R]
  rw [hd, eq_C_of_natDegree_eq_zero h1]
  simp [RatFunc.algebraMap_C]

/-! ### The auxiliary functions at a finite endpoint -/

/-- The order at `0` of a monomial `α t^u` with `α ≠ 0` is `u`. -/
lemma order_monomial_zero {α : ℂ} (hα : α ≠ 0) (u : ℤ) :
    meromorphicOrderAt (fun t : ℂ => α * t ^ u) 0 = (u : WithTop ℤ) := by
  have hm : MeromorphicAt (fun t : ℂ => α * t ^ u) 0 :=
    (MeromorphicAt.const α 0).mul
      ((show MeromorphicAt (fun t : ℂ => t) 0 from analyticAt_id.meromorphicAt).zpow u)
  rw [meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun _ => α, analyticAt_const, hα, ?_⟩
  filter_upwards with t
  simp [smul_eq_mul, mul_comm]

/-- If `f, g` are analytic at `z₀` with distinct values `f(z₀) = a j`, `g(z₀) ≠ a j`, and
`f - a j` has finite order there, then `t · U(t)` has order `ord_{z₀}(t)` at `z₀`; in particular
order zero at `z₀ = 0` after multiplying by `t`. -/
lemma order_mul_auxU_endpoint {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) {j : Fin 3} (hfj : f 0 = a j)
    (hfg : f 0 ≠ g 0) (hne : meromorphicOrderAt (fun w => f w - a j) 0 ≠ ⊤) :
    meromorphicOrderAt (fun t => t * auxU a f g t) 0 = 0 := by
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
  have hfg0 : meromorphicOrderAt (fun w => f w - g w) 0 = 0 := by
    have hfga : AnalyticAt ℂ (fun w => f w - g w) 0 := hf.sub hg
    rw [hfga.meromorphicOrderAt_eq, hfga.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hfg)]
    rfl
  have hid : meromorphicOrderAt (fun t : ℂ => t) 0 = ((1 : ℤ) : WithTop ℤ) := by
    have := order_monomial_zero (one_ne_zero (α := ℂ)) 1
    simpa using this
  have hP : MeromorphicAt (fun w => cubicP a (f w)) 0 := by unfold cubicP; fun_prop
  have hfgm : MeromorphicAt (fun w => f w - g w) 0 := hfm.sub hg.meromorphicAt
  have hfun : (fun t => t * auxU a f g t) =
      (fun t : ℂ => t) * (((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹) := by
    ext t; simp [auxU, div_eq_mul_inv, mul_assoc]
  rw [hfun, meromorphicOrderAt_mul
    (show MeromorphicAt (fun t : ℂ => t) 0 from analyticAt_id.meromorphicAt) ((hfgm.mul hfm.deriv).mul hP.inv),
    meromorphicOrderAt_mul (hfgm.mul hfm.deriv) hP.inv,
    meromorphicOrderAt_mul hfgm hfm.deriv, meromorphicOrderAt_inv,
    order_cubicP_comp hfm ha hm1 hmo, order_deriv_of_order_sub hfm hm1 hmo, hfg0, hid]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, zero_add, ← WithTop.coe_add, ← WithTop.coe_add]
  rw [show (1 : ℤ) + ((m : ℤ) - 1 + -(m : ℤ)) = 0 by ring]
  rfl

lemma exists_index_ne {a : Fin 3 → ℂ} (ha : Function.Injective a) (e₁ e₂ : ℂ) :
    ∃ i, a i ≠ e₁ ∧ a i ≠ e₂ := by
  by_contra hcon
  push_neg at hcon
  have h : ∀ i, a i = e₁ ∨ a i = e₂ := fun i => by
    by_cases h1 : a i = e₁
    · exact Or.inl h1
    · exact Or.inr (hcon i h1)
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h 2 with h2 | h2 <;>
    first
    | exact absurd (ha (h0.trans h1.symm)) (by decide)
    | exact absurd (ha (h0.trans h2.symm)) (by decide)
    | exact absurd (ha (h1.trans h2.symm)) (by decide)

/-- `num - b · denom` does not vanish at `0`, except for at most one value of `b` (the value of
the rational function at `0`). -/
lemma exists_rootMultiplicity_zero_eq_zero (R : RatFunc ℂ) :
    ∃ e : ℂ, ∀ b : ℂ, b ≠ e → (R.num - Polynomial.C b * R.denom).rootMultiplicity 0 = 0 := by
  refine ⟨R.num.eval 0 / R.denom.eval 0, fun b hb => rootMultiplicity_eq_zero ?_⟩
  simp only [IsRoot, eval_sub, eval_mul, eval_C]
  by_cases hd : R.denom.eval 0 = 0
  · obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom R
    intro h0
    rw [hd, mul_zero, sub_zero] at h0
    have := congrArg (eval 0) huv
    simp only [eval_add, eval_mul, h0, hd, mul_zero, add_zero, eval_one] at this
    exact zero_ne_one this
  · intro h0
    apply hb
    rw [eq_div_iff hd]
    linear_combination -h0

/-- **Core of Lemma 9.4.**  Let `R, S ∈ ℂ(t)` of the same degree form a normalized pair on `ℂ*`.
If the monomials `U = α t^u` and `V = β t^u` of Lemma 9.3 have the same exponent (so that `U/V`
is a constant `q = α/β`), then `q = 1` and `R, S` share all four values `a 0, a 1, a 2, ∞` CM on
`ℂ*`.  The proof counts the multiplicities of a finite value which is taken neither at `0` nor
at `∞` by `S` (resp. `R`). -/
theorem cm_of_same_exponent {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hdeg : max R.num.natDegree R.denom.natDegree = max S.num.natDegree S.denom.natDegree)
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {u : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u)
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ u) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] i) := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  have hr : ∀ t : ℂ, t ≠ 0 → ∀ l : Fin 3, 0 < mult (ratEval R) (a l : Sphere) t →
      α * (mult (ratEval S) (a l : Sphere) t : ℂ) =
        β * (mult (ratEval R) (a l : Sphere) t : ℂ) := by
    intro t ht l hl
    have h := rational_aux_ratio hpair hβ hU hV ht hl
    have htu : t ^ u ≠ 0 := zpow_ne_zero u ht
    apply mul_left_cancel₀ htu
    linear_combination h
  set d := max R.num.natDegree R.denom.natDegree with hd
  have hdpos : 0 < d := max_natDegree_pos hRnc
  -- a value taken by `S` neither at `0` nor at `∞`
  obtain ⟨eS, heS⟩ := exists_natDegree_num_sub_eq S
  obtain ⟨eS0, heS0⟩ := exists_rootMultiplicity_zero_eq_zero S
  obtain ⟨i, hie0, hie⟩ := exists_index_ne hpair.injective eS0 eS
  set NS := S.num - Polynomial.C (a i) * S.denom with hNSdef
  have hNS : NS ≠ 0 := num_sub_ne_zero (hSnc _)
  have hdegNS : NS.natDegree = d := (heS _ hie).trans hdeg.symm
  have hNS0 : NS.rootMultiplicity 0 = 0 := heS0 _ hie0
  set Z := NS.roots.toFinset.erase 0 with hZdef
  have hsumS : ∑ t ∈ Z, mult (ratEval S) (a i : Sphere) t = d := by
    rw [Finset.sum_congr rfl (fun t _ => mult_ratEval_eq_rootMultiplicity S hNS t)]
    have := sum_rootMultiplicity_nonzero NS
    rw [← hZdef] at this
    rw [← hNSdef]
    omega
  have hsumR : ∑ t ∈ Z, mult (ratEval R) (a i : Sphere) t ≤ d := by
    rw [Finset.sum_congr rfl
      (fun t _ => mult_ratEval_eq_rootMultiplicity R (num_sub_ne_zero (hRnc (a i))) t)]
    exact (sum_rootMultiplicity_le _ Z).trans (natDegree_num_sub_le R _)
  have hZ : ∀ t ∈ Z, α * (mult (ratEval S) (a i : Sphere) t : ℂ) =
      β * (mult (ratEval R) (a i : Sphere) t : ℂ) := by
    intro t ht
    rw [hZdef, Finset.mem_erase, Multiset.mem_toFinset, mem_roots hNS] at ht
    have hpos : 0 < mult (ratEval S) (a i : Sphere) t := by
      rw [mult_ratEval_eq_rootMultiplicity S hNS t]
      exact (rootMultiplicity_pos hNS).2 ht.2
    exact hr t ht.1 i ((hpair.im i t ht.1).2 hpos)
  have h1 : α * (d : ℂ) = β * ((∑ t ∈ Z, mult (ratEval R) (a i : Sphere) t : ℕ) : ℂ) := by
    rw [← hsumS]; push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hZ
  -- a value taken by `R` neither at `0` nor at `∞`
  obtain ⟨eR, heR⟩ := exists_natDegree_num_sub_eq R
  obtain ⟨eR0, heR0⟩ := exists_rootMultiplicity_zero_eq_zero R
  obtain ⟨i', hie0', hie'⟩ := exists_index_ne hpair.injective eR0 eR
  set NR := R.num - Polynomial.C (a i') * R.denom with hNRdef
  have hNR : NR ≠ 0 := num_sub_ne_zero (hRnc _)
  have hdegNR : NR.natDegree = d := heR _ hie'
  have hNR0 : NR.rootMultiplicity 0 = 0 := heR0 _ hie0'
  set Z' := NR.roots.toFinset.erase 0 with hZ'def
  have hsumR' : ∑ t ∈ Z', mult (ratEval R) (a i' : Sphere) t = d := by
    rw [Finset.sum_congr rfl (fun t _ => mult_ratEval_eq_rootMultiplicity R hNR t)]
    have := sum_rootMultiplicity_nonzero NR
    rw [← hZ'def] at this
    rw [← hNRdef]
    omega
  have hsumS' : ∑ t ∈ Z', mult (ratEval S) (a i' : Sphere) t ≤ d := by
    rw [Finset.sum_congr rfl
      (fun t _ => mult_ratEval_eq_rootMultiplicity S (num_sub_ne_zero (hSnc (a i'))) t), hdeg]
    exact (sum_rootMultiplicity_le _ Z').trans (natDegree_num_sub_le S _)
  have hZ' : ∀ t ∈ Z', α * (mult (ratEval S) (a i' : Sphere) t : ℂ) =
      β * (mult (ratEval R) (a i' : Sphere) t : ℂ) := by
    intro t ht
    rw [hZ'def, Finset.mem_erase, Multiset.mem_toFinset, mem_roots hNR] at ht
    have hpos : 0 < mult (ratEval R) (a i' : Sphere) t := by
      rw [mult_ratEval_eq_rootMultiplicity R hNR t]
      exact (rootMultiplicity_pos hNR).2 ht.2
    exact hr t ht.1 i' hpos
  have h2 : α * ((∑ t ∈ Z', mult (ratEval S) (a i' : Sphere) t : ℕ) : ℂ) = β * (d : ℂ) := by
    rw [← hsumR']; push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hZ'
  set M := ∑ t ∈ Z, mult (ratEval R) (a i : Sphere) t
  set M' := ∑ t ∈ Z', mult (ratEval S) (a i' : Sphere) t
  have hMM : (d : ℂ) * d = M * M' := by
    apply mul_left_cancel₀ hα
    linear_combination (d : ℂ) * h1 - (M : ℂ) * h2
  have hMM' : d * d = M * M' := by exact_mod_cast hMM
  have hMd : M = d := by
    by_contra hne
    have hlt : M < d := lt_of_le_of_ne hsumR hne
    have : M * M' < d * d :=
      lt_of_le_of_lt (Nat.mul_le_mul_left M hsumS') (Nat.mul_lt_mul_of_pos_right hlt hdpos)
    omega
  have hαβ : α = β := by
    rw [hMd] at h1
    exact mul_right_cancel₀ (by exact_mod_cast hdpos.ne') h1
  have hcm : ∀ l : Fin 3, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a l : Sphere) := by
    intro l t ht
    by_cases hm : 0 < mult (ratEval R) (a l : Sphere) t
    · have := hr t ht l hm
      rw [hαβ] at this
      exact_mod_cast (mul_left_cancel₀ hβ this).symm
    · have hm' : ¬ 0 < mult (ratEval S) (a l : Sphere) t := fun h => hm ((hpair.im l t ht).2 h)
      omega
  intro i
  fin_cases i
  exacts [hcm 0, hcm 1, hcm 2, hpair.cm_top]

/-- **Lemma 9.4** (finite endpoint case), endpoint `0`, assuming the conclusions of Lemma 9.2.
Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` for the finite values `a 0, a 1, a 2`
(nonconstant, distinct, sharing the `a j` IM and `∞` CM on `ℂ*`), such that

* the coincidence multiplicity is one at the common points in `ℂ*`, and there are no other
  coincidences or critical points in `ℂ*` (Lemma 9.2);
* `R, S` have the same degree `max (deg num) (deg denom)` (Lemma 9.2);
* both are finite at `0`, with distinct values `R(0) = a j`, `S(0) = a k` (Lemma 9.2: both
  endpoints lie in the inverse image of the four values, with no coincidence there).

Then `R, S` share all four values `a 0, a 1, a 2, ∞` CM on `ℂ*`. -/
theorem rational_finite_endpoint {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t)
    (hdeg : max R.num.natDegree R.denom.natDegree = max S.num.natDegree S.denom.natDegree)
    (hR0 : R.denom.eval 0 ≠ 0) (hS0 : S.denom.eval 0 ≠ 0) {j k : Fin 3} (hjk : j ≠ k)
    (hRj : ratEval R 0 = a j) (hSk : ratEval S 0 = a k) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] i) := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨α, β, hα, hβ, u, v, hU, hV, -⟩ := rational_monomials hpair hco
  have hRa : AnalyticAt ℂ (ratEval R) 0 := by
    rw [funext (ratEval_eq R)]
    exact (R.num.differentiable.analyticAt 0).div (R.denom.differentiable.analyticAt 0) hR0
  have hSa : AnalyticAt ℂ (ratEval S) 0 := by
    rw [funext (ratEval_eq S)]
    exact (S.num.differentiable.analyticAt 0).div (S.denom.differentiable.analyticAt 0) hS0
  have hRS0 : ratEval R 0 ≠ ratEval S 0 := by
    rw [hRj, hSk]; exact hpair.injective.ne hjk
  have hu : u = 0 := by
    have h1 := order_mul_auxU_endpoint hpair.injective hRa hSa hRj hRS0
      (order_ratEval_sub_ne_top (hRnc _) 0)
    rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite hU 0),
      order_monomial_zero hα] at h1
    exact_mod_cast h1
  have hv : v = 0 := by
    have h1 := order_mul_auxU_endpoint hpair.injective hSa hRa hSk hRS0.symm
      (order_ratEval_sub_ne_top (hSnc _) 0)
    have e : (fun t => t * auxU a (ratEval S) (ratEval R) t) =
        fun t => -(t * auxV a (ratEval R) (ratEval S) t) := by
      ext t; simp only [auxV, auxU]; ring
    rw [e, order_neg_eq, meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite hV 0),
      order_monomial_zero hβ] at h1
    exact_mod_cast h1
  subst hu hv
  exact cm_of_same_exponent hpair hdeg hα hβ hU hV

end ThreeIM
