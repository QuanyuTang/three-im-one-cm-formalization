module

public import RequestProject.ThreeIM.MathlibImports
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Polynomial.Basic

/-!
# Derivative signs of real rational functions (Lemma 9.26, sign propagation)

The second half of Lemma 9.26 propagates the sign of the derivative of a real rational function
along a real interval: the derivative does not vanish on the interval away from the poles, the
poles are simple (so the derivative has the same sign on both sides of each pole), and the sign
is known at one point.  Then the derivative has that sign on the whole interval.

* `eventually_pos_of_preconnected`: an abstract sign-propagation principle on a preconnected set.
* `quotDeriv_pos_of_preconnected`: the statement for a quotient `p / q` of real polynomials.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- If `P` holds on a punctured neighbourhood of `t`, then for `s` near `t` with `s ≠ t`, `P`
holds on a punctured neighbourhood of `s`. -/
lemma eventually_nhdsNE_nhdsNE {P : ℝ → Prop} {t : ℝ} (h : ∀ᶠ s in 𝓝[≠] t, P s) :
    ∀ᶠ s in 𝓝 t, s ≠ t → ∀ᶠ u in 𝓝[≠] s, P u := by
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h.eventually_nhds] with s hs hst
  apply nhdsWithin_le_nhds
  filter_upwards [hs, isOpen_ne.mem_nhds hst] with u hu hut using hu hut

/-- **Sign propagation.**  Let `φ` be a real function such that near every point of a
preconnected set `I` it has a constant strict sign on a punctured neighbourhood.  If the sign is
positive near one point of `I`, then it is positive near every point of `I`. -/
theorem eventually_pos_of_preconnected {φ : ℝ → ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (h : ∀ t ∈ I, (∀ᶠ s in 𝓝[≠] t, 0 < φ s) ∨ (∀ᶠ s in 𝓝[≠] t, φ s < 0))
    {t₀ t₁ : ℝ} (h₀ : t₀ ∈ I) (h₁ : t₁ ∈ I) (hpos : ∀ᶠ s in 𝓝[≠] t₀, 0 < φ s) :
    ∀ᶠ s in 𝓝[≠] t₁, 0 < φ s := by
  classical
  let g : ℝ → Bool := fun t => decide (∀ᶠ s in 𝓝[≠] t, 0 < φ s)
  have hnot : ∀ t, (∀ᶠ s in 𝓝[≠] t, φ s < 0) → ¬ ∀ᶠ s in 𝓝[≠] t, 0 < φ s := by
    intro t hn hp
    obtain ⟨s, h1, h2⟩ := (hn.and hp).exists
    linarith
  have hcont : ContinuousOn g I := by
    intro t ht
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    apply nhdsWithin_le_nhds
    rcases h t ht with hp | hn
    · filter_upwards [eventually_nhdsNE_nhdsNE hp] with s hs
      by_cases hst : s = t
      · rw [hst]
      · simp only [g, hs hst, hp]
    · filter_upwards [eventually_nhdsNE_nhdsNE hn] with s hs
      by_cases hst : s = t
      · rw [hst]
      · simp only [g, hnot s (hs hst), hnot t hn]
  have := hI.constant hcont h₀ h₁
  simp only [g, hpos, decide_true] at this
  exact of_decide_eq_true this.symm

/-- The derivative of `p / q` as a polynomial quotient: `(p' q - p q') / q²`. -/
noncomputable def quotDerivFormula (p q : ℝ[X]) (x : ℝ) : ℝ :=
  (p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2

lemma hasDerivAt_quot (p q : ℝ[X]) {x : ℝ} (hx : q.eval x ≠ 0) :
    HasDerivAt (fun y => p.eval y / q.eval y) (quotDerivFormula p q x) x :=
  (p.hasDerivAt x).div (q.hasDerivAt x) hx

lemma deriv_quot_eq (p q : ℝ[X]) {x : ℝ} (hx : q.eval x ≠ 0) :
    deriv (fun y => p.eval y / q.eval y) x = quotDerivFormula p q x :=
  (hasDerivAt_quot p q hx).deriv

/-- The derivative of `p / q` agrees with the formula near any point where `q ≠ 0`, and on a
punctured neighbourhood of any point when `q ≠ 0`. -/
lemma deriv_quot_eventuallyEq_nhdsNE {p q : ℝ[X]} (hq : q ≠ 0) (t : ℝ) :
    ∀ᶠ x in 𝓝[≠] t, q.eval x ≠ 0 ∧
      deriv (fun y => p.eval y / q.eval y) x = quotDerivFormula p q x := by
  have hfin : ({x : ℝ | q.eval x = 0} \ {t}).Finite :=
    (Polynomial.finite_setOf_isRoot hq).subset diff_subset
  have hev : ∀ᶠ x in 𝓝[≠] t, q.eval x ≠ 0 := by
    have := hfin.isClosed.isOpen_compl.mem_nhds
      (show t ∈ ({x : ℝ | q.eval x = 0} \ {t})ᶜ by simp)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [this] with x hx hxt hq0
    exact hx ⟨hq0, hxt⟩
  filter_upwards [hev] with x hx using ⟨hx, deriv_quot_eq p q hx⟩

/-- Local sign of the derivative of `p / q` at a point where `q ≠ 0` and the derivative does not
vanish. -/
lemma quot_sign_regular {p q : ℝ[X]} {t : ℝ} (ht : q.eval t ≠ 0)
    (hd : deriv (fun y => p.eval y / q.eval y) t ≠ 0) :
    (∀ᶠ s in 𝓝[≠] t, 0 < deriv (fun y => p.eval y / q.eval y) s) ∨
      (∀ᶠ s in 𝓝[≠] t, deriv (fun y => p.eval y / q.eval y) s < 0) := by
  have hq : q ≠ 0 := by rintro rfl; simp at ht
  have hc : ContinuousAt (quotDerivFormula p q) t := by
    unfold quotDerivFormula
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 ht)
  rw [deriv_quot_eq p q ht] at hd
  rcases hd.lt_or_gt with hneg | hpos
  · right
    filter_upwards [deriv_quot_eventuallyEq_nhdsNE (p := p) hq t,
      nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const hneg)] with s hs hs'
    rw [hs.2]; exact hs'
  · left
    filter_upwards [deriv_quot_eventuallyEq_nhdsNE (p := p) hq t,
      nhdsWithin_le_nhds (continuousAt_const.eventually_lt hc hpos)] with s hs hs'
    rw [hs.2]; exact hs'

/-- At a simple pole of `p / q` (`q(t) = 0`, `q'(t) ≠ 0`, `p(t) ≠ 0`), the derivative has the
same strict sign on both sides of the pole. -/
lemma quot_sign_simple_pole {p q : ℝ[X]} {t : ℝ} (ht : q.eval t = 0)
    (hq' : q.derivative.eval t ≠ 0) (hp : p.eval t ≠ 0) :
    (∀ᶠ s in 𝓝[≠] t, 0 < deriv (fun y => p.eval y / q.eval y) s) ∨
      (∀ᶠ s in 𝓝[≠] t, deriv (fun y => p.eval y / q.eval y) s < 0) := by
  have hq : q ≠ 0 := by rintro rfl; simp at hq'
  set N : ℝ → ℝ := fun x => p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x
  have hN : N t ≠ 0 := by simp only [N, ht, mul_zero, zero_sub, neg_ne_zero]; exact mul_ne_zero hp hq'
  have hNc : ContinuousAt N t := by simp only [N]; fun_prop
  have key : ∀ x, q.eval x ≠ 0 → quotDerivFormula p q x = N x / q.eval x ^ 2 := fun x _ => rfl
  rcases hN.lt_or_gt with hneg | hpos
  · right
    filter_upwards [deriv_quot_eventuallyEq_nhdsNE (p := p) hq t,
      nhdsWithin_le_nhds (hNc.eventually_lt continuousAt_const hneg)] with s hs hs'
    rw [hs.2, key s hs.1]
    have := hs.1
    exact div_neg_of_neg_of_pos hs' (by positivity)
  · left
    filter_upwards [deriv_quot_eventuallyEq_nhdsNE (p := p) hq t,
      nhdsWithin_le_nhds (continuousAt_const.eventually_lt hNc hpos)] with s hs hs'
    rw [hs.2, key s hs.1]
    have := hs.1
    exact div_pos hs' (by positivity)

/-- **Lemma 9.26, sign propagation**, for a quotient `p / q` of real polynomials.  Let `I` be a
real interval (any preconnected set).  Suppose every zero of `q` in `I` is a simple pole of
`p / q` (`q' ≠ 0` and `p ≠ 0` there), the derivative of `p / q` has no zero in `I` away from
the zeros of `q`, and it is positive at some point of `I`.  Then it is positive at every point
of `I` where `q ≠ 0`. -/
theorem quotDeriv_pos_of_preconnected {p q : ℝ[X]} {I : Set ℝ} (hI : IsPreconnected I)
    (hpole : ∀ t ∈ I, q.eval t = 0 → q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0)
    (hcrit : ∀ t ∈ I, q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t ≠ 0)
    {t₀ : ℝ} (h₀ : t₀ ∈ I) (hq₀ : q.eval t₀ ≠ 0)
    (hpos₀ : 0 < deriv (fun y => p.eval y / q.eval y) t₀) :
    ∀ t ∈ I, q.eval t ≠ 0 → 0 < deriv (fun y => p.eval y / q.eval y) t := by
  have hsign : ∀ t ∈ I, (∀ᶠ s in 𝓝[≠] t, 0 < deriv (fun y => p.eval y / q.eval y) s) ∨
      (∀ᶠ s in 𝓝[≠] t, deriv (fun y => p.eval y / q.eval y) s < 0) := by
    intro t ht
    by_cases hqt : q.eval t = 0
    · exact quot_sign_simple_pole hqt (hpole t ht hqt).1 (hpole t ht hqt).2
    · exact quot_sign_regular hqt (hcrit t ht hqt)
  have hev₀ : ∀ᶠ s in 𝓝[≠] t₀, 0 < deriv (fun y => p.eval y / q.eval y) s := by
    rcases hsign t₀ h₀ with h | h
    · exact h
    · exfalso
      have hc : ContinuousAt (quotDerivFormula p q) t₀ := by
        unfold quotDerivFormula
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hq₀)
      rw [deriv_quot_eq p q hq₀] at hpos₀
      have hq : q ≠ 0 := by rintro rfl; simp at hq₀
      obtain ⟨s, h1, h2, h3⟩ := (h.and ((deriv_quot_eventuallyEq_nhdsNE (p := p) hq t₀).and
        (nhdsWithin_le_nhds (continuousAt_const.eventually_lt hc hpos₀)))).exists
      rw [h2.2] at h1; linarith
  intro t ht hqt
  have hev := eventually_pos_of_preconnected hI hsign h₀ ht hev₀
  have hc : ContinuousAt (quotDerivFormula p q) t := by
    unfold quotDerivFormula
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hqt)
  have hq : q ≠ 0 := by rintro rfl; simp at hqt
  have hlim : Tendsto (quotDerivFormula p q) (𝓝[≠] t) (𝓝 (quotDerivFormula p q t)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hge : 0 ≤ quotDerivFormula p q t := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hev, deriv_quot_eventuallyEq_nhdsNE (p := p) hq t] with s h1 h2
    rw [← h2.2]; exact h1.le
  have hne := hcrit t ht hqt
  rw [deriv_quot_eq p q hqt] at hne ⊢
  exact lt_of_le_of_ne hge (Ne.symm hne)


lemma quotNum_coeff {p q : ℝ[X]} {d : ℕ} (hp : p.natDegree = d + 1) (hq : q.natDegree = d) :
    (derivative p * q - p * derivative q).natDegree ≤ d + d ∧
      (derivative p * q - p * derivative q).coeff (d + d) = p.leadingCoeff * q.leadingCoeff := by
  have h1 : (derivative p * q).natDegree ≤ d + d :=
    (natDegree_mul_le).trans (add_le_add (by have := natDegree_derivative_le p; omega) hq.le)
  have c1 : (derivative p * q).coeff (d + d) = p.leadingCoeff * q.leadingCoeff * (d + 1) := by
    rw [coeff_mul_add_eq_of_natDegree_le (by have := natDegree_derivative_le p; omega) hq.le,
      coeff_derivative, leadingCoeff, leadingCoeff, hp, hq]; ring
  rcases Nat.eq_zero_or_eq_succ_pred d with hd | hd
  · subst hd
    have : derivative q = 0 := derivative_of_natDegree_zero hq
    simp only [this, mul_zero, sub_zero]
    exact ⟨h1, by rw [c1]; simp⟩
  · set k := d.pred
    have hq' : (derivative q).natDegree ≤ k := by have := natDegree_derivative_le q; omega
    have h2 : (p * derivative q).natDegree ≤ d + d :=
      (natDegree_mul_le).trans (by omega)
    have c2 : (p * derivative q).coeff (d + d) = p.leadingCoeff * q.leadingCoeff * d := by
      rw [show d + d = (k + 2) + k by omega, coeff_mul_add_eq_of_natDegree_le (by omega) hq',
        coeff_derivative, leadingCoeff, leadingCoeff, hp, hq, show k + 1 = d by omega,
        show k + 2 = d + 1 by omega]
      rw [hd]; push_cast; ring
    refine ⟨(natDegree_sub_le _ _).trans (max_le h1 h2), ?_⟩
    rw [coeff_sub, c1, c2]; ring

/-- If `deg p = deg q + 1`, the derivative of `p / q` tends to `lc(p)/lc(q)` at `+∞` and `-∞`
(the paper's `R'(t) = 1/κ + O(t^{-2})`). -/
lemma tendsto_quotDerivFormula {p q : ℝ[X]} (hq : q ≠ 0) (hdeg : p.natDegree = q.natDegree + 1) :
    Tendsto (quotDerivFormula p q) atTop (𝓝 (p.leadingCoeff / q.leadingCoeff)) ∧
      Tendsto (quotDerivFormula p q) atBot (𝓝 (p.leadingCoeff / q.leadingCoeff)) := by
  set d := q.natDegree
  obtain ⟨hN, hc⟩ := quotNum_coeff hdeg rfl
  set N := derivative p * q - p * derivative q
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq
  have hlp : p.leadingCoeff ≠ 0 := by
    have : p ≠ 0 := by rintro rfl; simp at hdeg
    exact leadingCoeff_ne_zero.2 this
  have hNd : N.natDegree = d + d :=
    natDegree_eq_of_le_of_coeff_ne_zero hN (by rw [hc]; exact mul_ne_zero hlp hlq)
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at hc; exact mul_ne_zero hlp hlq hc.symm
  have hdeg2 : N.degree = (q ^ 2).degree := by
    rw [degree_eq_natDegree hN0, degree_eq_natDegree (pow_ne_zero 2 hq), natDegree_pow, hNd]
    congr 1; ring
  have hlN : N.leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
    rw [leadingCoeff, hNd, hc]
  have hval : N.leadingCoeff / (q ^ 2).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
    rw [hlN, leadingCoeff_pow]; field_simp
  have hfun : quotDerivFormula p q = fun x => N.eval x / (q ^ 2).eval x := by
    ext x; simp [quotDerivFormula, N]
  rw [hfun, ← hval]
  exact ⟨div_tendsto_atTop_leadingCoeff_div_of_degree_eq N (q ^ 2) hdeg2,
    div_tendsto_atBot_leadingCoeff_div_of_degree_eq N (q ^ 2) hdeg2⟩

/-- Sign propagation with a negative sign. -/
theorem quotDeriv_neg_of_preconnected {p q : ℝ[X]} {I : Set ℝ} (hI : IsPreconnected I)
    (hpole : ∀ t ∈ I, q.eval t = 0 → q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0)
    (hcrit : ∀ t ∈ I, q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t ≠ 0)
    {t₀ : ℝ} (h₀ : t₀ ∈ I) (hq₀ : q.eval t₀ ≠ 0)
    (hneg₀ : deriv (fun y => p.eval y / q.eval y) t₀ < 0) :
    ∀ t ∈ I, q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t < 0 := by
  have hf : ∀ x, q.eval x ≠ 0 →
      deriv (fun y => (-p).eval y / q.eval y) x = -deriv (fun y => p.eval y / q.eval y) x := by
    intro x hx
    rw [deriv_quot_eq _ _ hx, deriv_quot_eq _ _ hx, quotDerivFormula, quotDerivFormula]
    simp only [derivative_neg, eval_neg]; ring
  intro t ht hqt
  have := quotDeriv_pos_of_preconnected (p := -p) hI
    (fun t ht h0 => ⟨(hpole t ht h0).1, by simpa using (hpole t ht h0).2⟩)
    (fun t ht h0 => by rw [hf t h0]; exact neg_ne_zero.2 (hcrit t ht h0))
    h₀ hq₀ (by rw [hf t₀ hq₀]; linarith) t ht hqt
  rw [hf t hqt] at this; linarith

/-- **Lemma 9.26, sign of `R'`** (real form).  Let `R = p / q` be a real rational function with
`deg p = deg q + 1` and positive leading-coefficient ratio (`R(t) ∼ t/κ` with `κ > 0`).  Suppose
the poles of `R` with `|t| ≥ 1` are simple and `R'` has no zero with `|t| ≥ 1`.  Then `R' > 0`
at every real `t` with `|t| ≥ 1` that is not a pole. -/
theorem real_signs_R {p q : ℝ[X]} (hdeg : p.natDegree = q.natDegree + 1)
    (hlc : 0 < p.leadingCoeff / q.leadingCoeff)
    (hpole : ∀ t : ℝ, 1 ≤ |t| → q.eval t = 0 → q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0)
    (hcrit : ∀ t : ℝ, 1 ≤ |t| → q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t ≠ 0) :
    ∀ t : ℝ, 1 ≤ |t| → q.eval t ≠ 0 → 0 < deriv (fun y => p.eval y / q.eval y) t := by
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hlc
  obtain ⟨hTop, hBot⟩ := tendsto_quotDerivFormula hq hdeg
  have hqTop : ∀ᶠ x in atTop, q.eval x ≠ 0 :=
    (Polynomial.finite_setOf_isRoot hq).compl_mem_cofinite |> (Filter.atTop_le_cofinite ·)
  have hqBot : ∀ᶠ x in atBot, q.eval x ≠ 0 :=
    (Polynomial.finite_setOf_isRoot hq).compl_mem_cofinite |> (Filter.atBot_le_cofinite ·)
  obtain ⟨t₁, ht₁, hq₁, hp₁⟩ := ((eventually_ge_atTop 1).and
    (hqTop.and (hTop.eventually (lt_mem_nhds hlc)))).exists
  obtain ⟨t₂, ht₂, hq₂, hp₂⟩ := ((eventually_le_atBot (-1)).and
    (hqBot.and (hBot.eventually (lt_mem_nhds hlc)))).exists
  intro t ht hqt
  rcases le_abs'.1 ht with hneg | hpos
  · refine quotDeriv_pos_of_preconnected isPreconnected_Iic
      (fun s hs => hpole s (by rw [mem_Iic] at hs; rw [abs_of_neg (by linarith)]; linarith))
      (fun s hs => hcrit s (by rw [mem_Iic] at hs; rw [abs_of_neg (by linarith)]; linarith))
      (show t₂ ∈ Iic (-1) from ht₂) hq₂ (by rw [deriv_quot_eq p q hq₂]; exact hp₂) t
      (show t ∈ Iic (-1) by rw [mem_Iic]; linarith) hqt
  · refine quotDeriv_pos_of_preconnected isPreconnected_Ici
      (fun s hs => hpole s (by rw [mem_Ici] at hs; rw [abs_of_pos (by linarith)]; linarith))
      (fun s hs => hcrit s (by rw [mem_Ici] at hs; rw [abs_of_pos (by linarith)]; linarith))
      (show t₁ ∈ Ici 1 from ht₁) hq₁ (by rw [deriv_quot_eq p q hq₁]; exact hp₁) t
      (show t ∈ Ici 1 from hpos) hqt

/-- **Lemma 9.26, sign of `S'`** (real form).  Let `S = p / q` be a real rational function with a
simple pole at `0` of positive residue `p(0)/q'(0)` (`S(t) ∼ 1/(κ t)` with `κ > 0`).  Suppose
the poles of `S` with `|t| ≤ 1` are simple and `S'` has no zero with `|t| ≤ 1`.  Then `S' < 0`
at every real `t` with `|t| ≤ 1` that is not a pole. -/
theorem real_signs_S {p q : ℝ[X]} (hq0 : q.eval 0 = 0) (hres : 0 < p.eval 0 / q.derivative.eval 0)
    (hpole : ∀ t : ℝ, |t| ≤ 1 → q.eval t = 0 → q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0)
    (hcrit : ∀ t : ℝ, |t| ≤ 1 → q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t ≠ 0) :
    ∀ t : ℝ, |t| ≤ 1 → q.eval t ≠ 0 → deriv (fun y => p.eval y / q.eval y) t < 0 := by
  have hI : IsPreconnected (Icc (-1 : ℝ) 1) := isPreconnected_Icc
  have hmem : ∀ s, s ∈ Icc (-1 : ℝ) 1 ↔ |s| ≤ 1 := fun s => by rw [abs_le, mem_Icc]
  have hq'0 : q.derivative.eval 0 ≠ 0 := (hpole 0 (by simp) hq0).1
  -- the derivative is negative on a punctured neighbourhood of the simple pole at `0`
  have hNneg : p.derivative.eval 0 * q.eval 0 - p.eval 0 * q.derivative.eval 0 < 0 := by
    rw [hq0, mul_zero, zero_sub, neg_lt_zero]
    rcases div_pos_iff.1 hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_pos h1 h2
    · exact mul_pos_of_neg_of_neg h1 h2
  have hq : q ≠ 0 := by rintro rfl; simp at hq'0
  have hNc : ContinuousAt (fun x => p.derivative.eval x * q.eval x -
      p.eval x * q.derivative.eval x) 0 := by fun_prop
  have hNev : ∀ᶠ x in 𝓝 (0 : ℝ),
      p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x < 0 :=
    hNc.eventually_lt continuousAt_const hNneg
  have hNev' : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x < 0 :=
    nhdsWithin_le_nhds hNev
  have hIcc : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ∈ Icc (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos)
  obtain ⟨t₀, hlt, hneg⟩ :=
    ((deriv_quot_eventuallyEq_nhdsNE (p := p) hq 0).and (hNev'.and hIcc)).exists
  refine fun t ht hqt => quotDeriv_neg_of_preconnected hI
    (fun s hs => hpole s ((hmem s).1 hs)) (fun s hs => hcrit s ((hmem s).1 hs)) hneg.2 hlt.1 ?_ t
    ((hmem t).2 ht) hqt
  rw [hlt.2, quotDerivFormula]
  have := hlt.1
  exact div_neg_of_neg_of_pos hneg.1 (by positivity)

end ThreeIM
