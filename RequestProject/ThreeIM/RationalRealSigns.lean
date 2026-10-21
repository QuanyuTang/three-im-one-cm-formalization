module

public import RequestProject.ThreeIM.RationalCritical
public import RequestProject.ThreeIM.RealSigns

/-!
# Lemma 9.26 (derivative signs) for real rational functions, and Lemma 9.27 without the
sign hypotheses

`realRatFun p q` is the complex rational function `p / q` with real coefficients.  For a pair
`R = realRatFun p q`, `S = realRatFun p₂ q₂` (the reality conclusion of Lemma 9.26) satisfying
the conclusions of Lemma 9.2 and the endpoint identities with `ρ = 1`, we prove the derivative
signs of Lemma 9.26:

  `R'(t) > 0` for real `|t| ≥ 1`, and `S'(t) < 0` for real `0 < |t| ≤ 1` (at finite points),

and then the conclusion of Lemma 9.27 (the zero fiber in `ℂ*` is empty) with these signs
discharged.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- The complex rational function `p / q` with real coefficients. -/
noncomputable def realRatFun (p q : ℝ[X]) : ℂ → ℂ :=
  fun z => (p.map (algebraMap ℝ ℂ)).eval z / (q.map (algebraMap ℝ ℂ)).eval z

lemma eval_map_ofReal (p : ℝ[X]) (t : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  rw [eval_map, show (t : ℂ) = algebraMap ℝ ℂ t from rfl, eval₂_at_apply]; rfl

/-- Order of a polynomial quotient at a point where the numerator does not vanish. -/
lemma order_polyQuot {P Q : ℂ[X]} (hQ : Q ≠ 0) {z : ℂ} (hP : P.eval z ≠ 0) :
    meromorphicOrderAt (fun w => P.eval w / Q.eval w) z =
      ((-(Q.rootMultiplicity z : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ z
  have hrz : r.eval z ≠ 0 := fun h => hdvd (dvd_iff_isRoot.2 h)
  have hf : MeromorphicAt (fun w => P.eval w / Q.eval w) z :=
    (P.differentiable.analyticAt z).meromorphicAt.div (Q.differentiable.analyticAt z).meromorphicAt
  rw [meromorphicOrderAt_eq_int_iff hf]
  refine ⟨fun w => P.eval w / r.eval w, ?_, by simp [hP, hrz], ?_⟩
  · exact (P.differentiable.analyticAt z).div (r.differentiable.analyticAt z) hrz
  · have hev : ∀ᶠ w in 𝓝[≠] z, w ≠ z := self_mem_nhdsWithin
    filter_upwards [hev] with w hw
    have hw' : w - z ≠ 0 := sub_ne_zero.2 hw
    conv_lhs => rw [hr]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
    rw [zpow_neg, zpow_natCast]
    field_simp

section realRatFun

variable {p q : ℝ[X]}

/-- At a zero of the denominator, the pole order of `p / q` (coprime) is the root multiplicity
of `q`. -/
lemma mult_top_realRatFun (hcop : IsCoprime p q) (hq : q ≠ 0) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) :
    mult (realRatFun p q) ⊤ z = (q.map (algebraMap ℝ ℂ)).rootMultiplicity z := by
  have hP : (p.map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
    obtain ⟨u, v, huv⟩ := hcop.map (Polynomial.mapRingHom (algebraMap ℝ ℂ))
    intro h0
    have := congrArg (eval z) huv
    simp only [coe_mapRingHom, eval_add, eval_mul, h0, hz, mul_zero, add_zero, eval_one] at this
    exact zero_ne_one this
  have hQ : q.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℝ ℂ).injective).2 hq
  rw [mult_top, show realRatFun p q = fun w => (p.map (algebraMap ℝ ℂ)).eval w /
    (q.map (algebraMap ℝ ℂ)).eval w from rfl, order_polyQuot hQ hP,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg, WithTop.untop₀_coe]
  simp

/-- Where the denominator does not vanish, `p / q` is analytic. -/
lemma analyticAt_realRatFun {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z ≠ 0) :
    AnalyticAt ℂ (realRatFun p q) z :=
  ((p.map _).differentiable.analyticAt z).div ((q.map _).differentiable.analyticAt z) hz

/-- A point with no pole of `p / q` (coprime) is not a zero of `q`. -/
lemma eval_ne_zero_of_mult_top (hcop : IsCoprime p q) (hq : q ≠ 0) {z : ℂ}
    (h : mult (realRatFun p q) ⊤ z = 0) : (q.map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  intro hz
  rw [mult_top_realRatFun hcop hq hz] at h
  have hQ : q.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℝ ℂ).injective).2 hq
  exact absurd h ((rootMultiplicity_pos hQ).2 hz).ne'

/-- At a real point where `q ≠ 0`, the complex derivative of `p / q` is the real derivative. -/
lemma deriv_realRatFun {t : ℝ} (ht : q.eval t ≠ 0) :
    deriv (realRatFun p q) t = ((deriv (fun y : ℝ => p.eval y / q.eval y) t : ℝ) : ℂ) := by
  have hQ : (q.map (algebraMap ℝ ℂ)).eval (t : ℂ) ≠ 0 := by
    rw [eval_map_ofReal]; exact_mod_cast ht
  have h := ((p.map (algebraMap ℝ ℂ)).hasDerivAt (t : ℂ)).div
    ((q.map (algebraMap ℝ ℂ)).hasDerivAt (t : ℂ)) hQ
  rw [show realRatFun p q = (fun w => (p.map (algebraMap ℝ ℂ)).eval w) /
    (fun w => (q.map (algebraMap ℝ ℂ)).eval w) from rfl, h.deriv, deriv_quot_eq p q ht,
    quotDerivFormula]
  simp only [derivative_map, eval_map_ofReal]
  push_cast; rfl

/-- At a real simple pole (pole order one) of `p / q` (coprime), `q' ≠ 0` and `p ≠ 0`. -/
lemma simple_pole_realRatFun (hcop : IsCoprime p q) (hq : q ≠ 0) {t : ℝ} (ht : q.eval t = 0)
    (h1 : mult (realRatFun p q) ⊤ t = 1) : q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0 := by
  have hz : (q.map (algebraMap ℝ ℂ)).eval (t : ℂ) = 0 := by rw [eval_map_ofReal, ht]; simp
  have hQ : q.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℝ ℂ).injective).2 hq
  rw [mult_top_realRatFun hcop hq hz] at h1
  constructor
  · intro hd
    have : 1 < (q.map (algebraMap ℝ ℂ)).rootMultiplicity (t : ℂ) := by
      rw [one_lt_rootMultiplicity_iff_isRoot hQ]
      refine ⟨hz, ?_⟩
      rw [IsRoot, derivative_map, eval_map_ofReal, hd]; simp
    omega
  · intro hp
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (eval t) huv
    simp only [eval_add, eval_mul, hp, ht, mul_zero, add_zero, eval_one] at this
    exact zero_ne_one this

end realRatFun

variable {p q p₂ q₂ : ℝ[X]} {a : Fin 3 → ℂ} {κ : ℝ}

/-- At a real pole `t ≠ 0` of `R` or `S`, the conclusions of Lemma 9.2 make the pole simple for
both maps. -/
lemma mult_top_eq_one_of_coincidence {f g : ℂ → ℂ} (hpair : NormalizedPair {0}ᶜ f g a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a f g t) {z : ℂ} (hz : z ≠ 0)
    (hp : 0 < mult f ⊤ z) : mult f ⊤ z = 1 ∧ mult g ⊤ z = 1 := by
  have h := (hpair.pole_of_coincidence hz hp ((hco z hz).pole hp)).1
  exact ⟨h, by rw [← hpair.cm_top z hz]; exact h⟩

/-- **Lemma 9.26** (derivative signs).  Let `R = p / q` and `S = p₂ / q₂` be real rational
functions (coprime numerators and denominators) forming a normalized pair on `ℂ*` for the
values `a`, satisfying the conclusions of Lemma 9.2 (coincidence multiplicity one on `ℂ*`) and
the endpoint identities with `ρ = 1`:

* `U = (R - S) DR/P(R) = κ t^{-1}` and `V = (R - S) DS/P(S) = κ t` with `κ > 0`;
* `R(t) ∼ t/κ` at `∞` (`deg p = deg q + 1`, `lc(p)/lc(q) = 1/κ`);
* `S(t) ∼ 1/(κ t)` at `0` (`q₂(0) = 0`, residue `p₂(0)/q₂'(0) = 1/κ`).

Then `R'(t) > 0` at real `t` with `|t| ≥ 1` and `S'(t) < 0` at real `t` with `0 < |t| ≤ 1`,
wherever the maps are finite. -/
theorem rational_real_signs (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ (realRatFun p q) (realRatFun p₂ q₂) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (realRatFun p q) (realRatFun p₂ q₂) t)
    (hU : ∀ᶠ t in cofinite,
      t * auxU a (realRatFun p q) (realRatFun p₂ q₂) t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite,
      t * auxV a (realRatFun p q) (realRatFun p₂ q₂) t = κ * t ^ (1 : ℤ))
    (hcop : IsCoprime p q) (hcop₂ : IsCoprime p₂ q₂)
    (hdeg : p.natDegree = q.natDegree + 1) (hlc : p.leadingCoeff / q.leadingCoeff = 1 / κ)
    (hq₂0 : q₂.eval 0 = 0) (hres : p₂.eval 0 / q₂.derivative.eval 0 = 1 / κ) :
    (∀ t : ℝ, 1 ≤ |t| → mult (realRatFun p q) ⊤ t = 0 →
      0 < (deriv (realRatFun p q) t).re) ∧
    (∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → mult (realRatFun p₂ q₂) ⊤ t = 0 →
      (deriv (realRatFun p₂ q₂) t).re < 0) := by
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hpos : (0 : ℝ) < 1 / κ := by positivity
  have hq : q ≠ 0 := by rintro rfl; simp at hlc; linarith
  have hq₂ : q₂ ≠ 0 := by
    rintro rfl; simp at hres; linarith
  have hmapR : ∀ t : ℝ, (q.map (algebraMap ℝ ℂ)).eval (t : ℂ) = 0 ↔ q.eval t = 0 := fun t => by
    rw [eval_map_ofReal]; exact_mod_cast Iff.rfl
  have hmapS : ∀ t : ℝ, (q₂.map (algebraMap ℝ ℂ)).eval (t : ℂ) = 0 ↔ q₂.eval t = 0 := fun t => by
    rw [eval_map_ofReal]; exact_mod_cast Iff.rfl
  -- poles off `0` are simple
  have hpoleR : ∀ t : ℝ, t ≠ 0 → q.eval t = 0 → q.derivative.eval t ≠ 0 ∧ p.eval t ≠ 0 := by
    intro t ht0 hqt
    have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hz := (hmapR t).2 hqt
    have hmpos : 0 < mult (realRatFun p q) ⊤ t := by
      rw [mult_top_realRatFun hcop hq hz]
      exact (rootMultiplicity_pos ((Polynomial.map_ne_zero_iff
        (algebraMap ℝ ℂ).injective).2 hq)).2 hz
    exact simple_pole_realRatFun hcop hq hqt
      (mult_top_eq_one_of_coincidence hpair hco ht0' hmpos).1
  have hpoleS : ∀ t : ℝ, t ≠ 0 → q₂.eval t = 0 → q₂.derivative.eval t ≠ 0 ∧ p₂.eval t ≠ 0 := by
    intro t ht0 hqt
    have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hz := (hmapS t).2 hqt
    have hmpos : 0 < mult (realRatFun p₂ q₂) ⊤ t := by
      rw [mult_top_realRatFun hcop₂ hq₂ hz]
      exact (rootMultiplicity_pos ((Polynomial.map_ne_zero_iff
        (algebraMap ℝ ℂ).injective).2 hq₂)).2 hz
    have hmposf : 0 < mult (realRatFun p q) ⊤ t := by rw [hpair.cm_top _ ht0']; exact hmpos
    exact simple_pole_realRatFun hcop₂ hq₂ hqt
      (mult_top_eq_one_of_coincidence hpair hco ht0' hmposf).2
  constructor
  · -- the sign of `R'`
    have hreal := real_signs_R hdeg (by rw [hlc]; exact hpos)
      (fun t ht hqt => hpoleR t (by rintro rfl; simp at ht; linarith) hqt)
      (fun t ht hqt => by
        have hz : (q.map (algebraMap ℝ ℂ)).eval (t : ℂ) ≠ 0 := fun h => hqt ((hmapR t).1 h)
        have := deriv_ne_zero_R hpair hco hκ' hU hV ht (analyticAt_realRatFun hz)
        rw [deriv_realRatFun hqt] at this
        exact_mod_cast this)
    intro t ht hm
    have hqt : q.eval t ≠ 0 := fun h => eval_ne_zero_of_mult_top hcop hq hm ((hmapR t).2 h)
    rw [deriv_realRatFun hqt, Complex.ofReal_re]
    exact hreal t ht hqt
  · -- the sign of `S'`
    have hres' : 0 < p₂.eval 0 / q₂.derivative.eval 0 := by rw [hres]; exact hpos
    have hreal := real_signs_S hq₂0 hres'
      (fun t ht hqt => by
        by_cases ht0 : t = 0
        · subst ht0
          refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hres' <;> simp at hres'
        · exact hpoleS t ht0 hqt)
      (fun t ht hqt => by
        have ht0 : t ≠ 0 := by rintro rfl; exact hqt hq₂0
        have hz : (q₂.map (algebraMap ℝ ℂ)).eval (t : ℂ) ≠ 0 := fun h => hqt ((hmapS t).1 h)
        have := deriv_ne_zero_S hpair hco hκ' hU hV ht0 ht (analyticAt_realRatFun hz)
        rw [deriv_realRatFun hqt] at this
        exact_mod_cast this)
    intro t _ ht hm
    have hqt : q₂.eval t ≠ 0 := fun h => eval_ne_zero_of_mult_top hcop₂ hq₂ hm ((hmapS t).2 h)
    rw [deriv_realRatFun hqt, Complex.ofReal_re]
    exact hreal t ht hqt

/-- **Lemmas 9.26 + 9.27**: under the hypotheses of `rational_real_signs`, with the values
normalized to `0, 1, c` (`c < 0`), the common zero fiber of `R` and `S` in `ℂ*` is empty. -/
theorem rational_zero_fiber_empty {c : ℝ} (hc : c < 0) (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ (realRatFun p q) (realRatFun p₂ q₂) ![0, 1, (c : ℂ)])
    (hco : ∀ t : ℂ, t ≠ 0 →
      CoincidenceSimpleAt ![0, 1, (c : ℂ)] (realRatFun p q) (realRatFun p₂ q₂) t)
    (hU : ∀ᶠ t in cofinite,
      t * auxU ![0, 1, (c : ℂ)] (realRatFun p q) (realRatFun p₂ q₂) t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite,
      t * auxV ![0, 1, (c : ℂ)] (realRatFun p q) (realRatFun p₂ q₂) t = κ * t ^ (1 : ℤ))
    (hcop : IsCoprime p q) (hcop₂ : IsCoprime p₂ q₂)
    (hdeg : p.natDegree = q.natDegree + 1) (hlc : p.leadingCoeff / q.leadingCoeff = 1 / κ)
    (hq₂0 : q₂.eval 0 = 0) (hres : p₂.eval 0 / q₂.derivative.eval 0 = 1 / κ) :
    ∀ t₀ : ℂ, t₀ ≠ 0 → mult (realRatFun p q) ((0 : ℂ) : Sphere) t₀ = 0 := by
  have hpos : (0 : ℝ) < 1 / κ := by positivity
  have hq : q ≠ 0 := by rintro rfl; simp at hlc; linarith
  have hq₂ : q₂ ≠ 0 := by rintro rfl; simp at hres; linarith
  obtain ⟨hsR, hsS⟩ := rational_real_signs hκ hpair hco hU hV hcop hcop₂ hdeg hlc hq₂0 hres
  exact zero_fiber_empty hc hκ hpair hU hV
    (fun t _ hm => analyticAt_realRatFun (eval_ne_zero_of_mult_top hcop hq hm))
    (fun t _ hm => analyticAt_realRatFun (eval_ne_zero_of_mult_top hcop₂ hq₂ hm)) hsR hsS

/-! ### Reality (first part of Lemma 9.26, algebraic core) -/

/-- A complex polynomial whose roots are all real is its leading coefficient times a monic real
polynomial. -/
lemma exists_real_monic_of_real_roots {A : ℂ[X]} (hr : ∀ z ∈ A.roots, z.im = 0) :
    ∃ P : ℝ[X], P.Monic ∧ A = C A.leadingCoeff * P.map (algebraMap ℝ ℂ) := by
  refine ⟨(A.roots.map fun z => X - C z.re).prod, monic_multiset_prod_of_monic _ _
    (fun z _ => monic_X_sub_C _), ?_⟩
  have hsplit : A.roots.card = A.natDegree :=
    (Splits.natDegree_eq_card_roots (IsAlgClosed.splits A)).symm
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit]
  congr 1
  rw [Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro z hz
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  congr 2
  apply Complex.ext <;> simp [hr z hz]

/-- **Lemma 9.26, reality step.**  A rational function `A / B` whose zeros and poles are all real
and whose limiting leading-coefficient ratio `lc(A)/lc(B)` is real is a real rational function:
`A / B = p / q` with `p, q ∈ ℝ[X]` (`q` monic), at every point. -/
theorem real_of_real_divisor {A B : ℂ[X]} (hB : B ≠ 0) (hAr : ∀ z ∈ A.roots, z.im = 0)
    (hBr : ∀ z ∈ B.roots, z.im = 0) (hlc : (A.leadingCoeff / B.leadingCoeff).im = 0) :
    ∃ p q : ℝ[X], q.Monic ∧ ∀ z, A.eval z / B.eval z = realRatFun p q z := by
  obtain ⟨P, -, hP⟩ := exists_real_monic_of_real_roots hAr
  obtain ⟨Q, hQm, hQ⟩ := exists_real_monic_of_real_roots hBr
  have hlB : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hB
  set lam : ℝ := (A.leadingCoeff / B.leadingCoeff).re
  have hlam : ((lam : ℝ) : ℂ) = A.leadingCoeff / B.leadingCoeff := by
    apply Complex.ext <;> simp [lam, hlc]
  refine ⟨C lam * P, Q, hQm, fun z => ?_⟩
  simp only [realRatFun, Polynomial.map_mul, map_C, eval_mul, eval_C]
  conv_lhs => rw [hP, hQ]
  simp only [eval_mul, eval_C]
  rw [show algebraMap ℝ ℂ lam = A.leadingCoeff / B.leadingCoeff from hlam]
  by_cases hz : (Q.map (algebraMap ℝ ℂ)).eval z = 0
  · simp [hz]
  · field_simp

/-- **Lemma 9.26, reality step (Möbius part).**  If `H = p / q` is a real rational function and
`c` is real, then `R = (c H - 1)/(H - 1)` is the real rational function `(c p - q)/(p - q)` at
every point where `q ≠ 0`. -/
theorem mobius_realRatFun (p q : ℝ[X]) (c : ℝ) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z ≠ 0) :
    (c * realRatFun p q z - 1) / (realRatFun p q z - 1) = realRatFun (C c * p - q) (p - q) z := by
  simp only [realRatFun, Polynomial.map_sub, Polynomial.map_mul, map_C, eval_sub, eval_mul,
    eval_C]
  set P := (p.map (algebraMap ℝ ℂ)).eval z
  set Q := (q.map (algebraMap ℝ ℂ)).eval z
  rw [show algebraMap ℝ ℂ c = (c : ℂ) from rfl]
  by_cases hPQ : P - Q = 0
  · have hPQ' : P = Q := sub_eq_zero.1 hPQ
    rw [hPQ, hPQ', div_self hz, sub_self, div_zero, div_zero]
  · have h1 : P / Q - 1 = (P - Q) / Q := by field_simp
    rw [h1, show (c : ℂ) * (P / Q) - 1 = (c * P - Q) / Q by field_simp]
    field_simp

end ThreeIM
