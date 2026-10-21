module

public import RequestProject.ThreeIM.RationalRealSigns
public import RequestProject.ThreeIM.Pullback

/-!
# Lemma 9.26 (reality), and the conclusion of Proposition 9.28 for a pair with `ρ = 1`

This file closes the gap between the complex rational functions `R, S ∈ ℂ(t)` of the paper and
the real rational functions `realRatFun p q` used in `rational_real_signs`.

* `real_num_denom_of_eventually`: a complex rational function that agrees, off a finite set,
  with a quotient of real polynomials has real reduced numerator and denominator.
* `ratFunc_real_of_real_points`: if the solutions of `R = 1` and `R = c` (`c` real) are real
  and the limiting value of `(R - 1)/(R - c)` at infinity is real, then `R` is real
  (first paragraph of the proof of Lemma 9.26).
* `rational_reality`: under the endpoint identities with `ρ = 1`, both `R` and `S` are real
  (Lemma 9.26, reality).
* `rational_cm_rho_one`: under the same hypotheses, `R, S` share all four values CM on `ℂ*`
  (Lemmas 9.26, 9.27 and the last step of the proof of Proposition 9.28).
-/

@[expose] public section

open Filter Set Topology Polynomial ComplexConjugate

namespace ThreeIM

/-! ### Conjugation of polynomials -/

lemma eval_map_conj (P : ℂ[X]) (z : ℂ) :
    (P.map (starRingEnd ℂ)).eval z = conj (P.eval (conj z)) := by
  rw [eval_map, ← eval₂_at_apply, Complex.conj_conj]

lemma map_real_map_conj (P : ℝ[X]) :
    (P.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = P.map (algebraMap ℝ ℂ) := by
  rw [Polynomial.map_map]; congr 1; ext x; simp

lemma realRatFun_conj (P Q : ℝ[X]) (z : ℂ) :
    realRatFun P Q (conj z) = conj (realRatFun P Q z) := by
  have h := fun (P : ℝ[X]) => eval_map_conj (P.map (algebraMap ℝ ℂ)) z
  simp only [map_real_map_conj] at h
  simp only [realRatFun, map_div₀, h, Complex.conj_conj]

/-- A complex polynomial fixed by conjugation is real. -/
lemma exists_real_of_map_conj {N : ℂ[X]} (h : N.map (starRingEnd ℂ) = N) :
    ∃ p : ℝ[X], N = p.map (algebraMap ℝ ℂ) := by
  have : N ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hn := congrArg (fun P => P.coeff n) h
    simp only [coeff_map] at hn
    exact ⟨(N.coeff n).re, (Complex.conj_eq_iff_re.1 hn)⟩
  obtain ⟨p, hp⟩ := this
  exact ⟨p, hp.symm⟩

/-- A complex rational function which agrees off a finite set with a quotient of real
polynomials has real reduced numerator and (monic) denominator. -/
theorem real_num_denom_of_eventually {R : RatFunc ℂ} {P Q : ℝ[X]}
    (h : ∀ᶠ z in cofinite, ratEval R z = realRatFun P Q z) :
    ∃ p q : ℝ[X], IsCoprime p q ∧ q.Monic ∧ R.num = p.map (algebraMap ℝ ℂ) ∧
      R.denom = q.map (algebraMap ℝ ℂ) := by
  set N := R.num
  set D := R.denom
  have hD : D ≠ 0 := R.denom_ne_zero
  have hconj : Tendsto (starRingEnd ℂ) cofinite cofinite :=
    (starRingEnd ℂ).injective.tendsto_cofinite
  have hDc : ∀ᶠ z in cofinite, D.eval z ≠ 0 :=
    (D.finite_setOf_isRoot hD).compl_mem_cofinite
  have hev : ∀ᶠ z in cofinite, ratEval R z = realRatFun P Q z ∧
      ratEval R (conj z) = realRatFun P Q (conj z) ∧ D.eval z ≠ 0 ∧ D.eval (conj z) ≠ 0 :=
    h.and ((hconj.eventually h).and (hDc.and (hconj.eventually hDc)))
  have hzero : N * D.map (starRingEnd ℂ) - N.map (starRingEnd ℂ) * D = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.Finite.infinite_compl hev)
    intro z hz
    simp only [compl_compl, Set.mem_setOf_eq] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [Set.mem_setOf_eq, IsRoot, eval_sub, eval_mul, eval_map_conj]
    rw [ratEval_eq] at h1 h2
    rw [realRatFun_conj, ← h1] at h2
    have h4' : conj (D.eval (conj z)) ≠ 0 := by simpa using h4
    have h2' := congrArg conj h2
    rw [map_div₀, Complex.conj_conj] at h2'
    rw [div_eq_div_iff h4' h3] at h2'
    rw [← h2']; ring
  have heq : N * D.map (starRingEnd ℂ) = N.map (starRingEnd ℂ) * D := sub_eq_zero.1 hzero
  have hDm : D.Monic := R.monic_denom
  have hDbm : (D.map (starRingEnd ℂ)).Monic := hDm.map _
  have hdvd : D ∣ D.map (starRingEnd ℂ) :=
    (RatFunc.isCoprime_num_denom R).symm.dvd_of_dvd_mul_left ⟨_, heq.trans (mul_comm _ _)⟩
  have hDD : D.map (starRingEnd ℂ) = D :=
    (eq_of_monic_of_dvd_of_natDegree_le hDm hDbm hdvd
      (by rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective]))
  have hNN : N.map (starRingEnd ℂ) = N := by
    rw [hDD] at heq; exact (mul_right_cancel₀ hD heq).symm
  obtain ⟨p, hp⟩ := exists_real_of_map_conj hNN
  obtain ⟨q, hq⟩ := exists_real_of_map_conj hDD
  refine ⟨p, q, ?_, ?_, hp, hq⟩
  · have := RatFunc.isCoprime_num_denom R
    rw [show R.num = N from rfl, show R.denom = D from rfl, hp, hq] at this
    exact (Polynomial.isCoprime_map (algebraMap ℝ ℂ)).1 this
  · have := hDm.leadingCoeff
    rw [hq, leadingCoeff_map_of_injective (algebraMap ℝ ℂ).injective] at this
    exact (algebraMap ℝ ℂ).injective (by rw [this, map_one])

/-- **Lemma 9.26, reality step.**  Let `R = N/D ∈ ℂ(t)` (reduced) and `c ∈ ℝ`, `c ≠ 1`.  If
every solution of `N = D` (i.e. `R = 1`) and of `N = c D` (i.e. `R = c`) is real, and the
leading-coefficient ratio of `(N - D)/(N - c D)` (the value of `(R - 1)/(R - c)` at infinity) is
real, then `R` has real reduced numerator and denominator. -/
theorem ratFunc_real_of_real_points {R : RatFunc ℂ} {c : ℝ} (hc : c ≠ 1)
    (hB : R.num - C (c : ℂ) * R.denom ≠ 0)
    (hA : ∀ z, R.num.eval z = R.denom.eval z → z.im = 0)
    (hC : ∀ z, R.num.eval z = c * R.denom.eval z → z.im = 0)
    (hlc : ((R.num - R.denom).leadingCoeff / (R.num - C (c : ℂ) * R.denom).leadingCoeff).im = 0) :
    ∃ p q : ℝ[X], IsCoprime p q ∧ q.Monic ∧ R.num = p.map (algebraMap ℝ ℂ) ∧
      R.denom = q.map (algebraMap ℝ ℂ) := by
  obtain ⟨P₀, Q₀, hQm, hPQ⟩ := real_of_real_divisor hB
    (fun z hz => hA z (by
      have := (mem_roots'.1 hz).2
      simp only [IsRoot, eval_sub] at this
      exact sub_eq_zero.1 this))
    (fun z hz => hC z (by
      have := (mem_roots'.1 hz).2
      simp only [IsRoot, eval_sub, eval_mul, eval_C] at this
      exact sub_eq_zero.1 this)) hlc
  have hQ₀ : Q₀.map (algebraMap ℝ ℂ) ≠ 0 := (hQm.map _).ne_zero
  have hc1 : (c : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hc)
  refine real_num_denom_of_eventually (P := C c * P₀ - Q₀) (Q := P₀ - Q₀) ?_
  filter_upwards [(R.denom.finite_setOf_isRoot R.denom_ne_zero).compl_mem_cofinite,
    (Polynomial.finite_setOf_isRoot hB).compl_mem_cofinite,
    (Polynomial.finite_setOf_isRoot hQ₀).compl_mem_cofinite] with z hD hBz hQz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hD hBz hQz
  rw [← mobius_realRatFun P₀ Q₀ c hQz, ← hPQ, ratEval_eq]
  simp only [eval_sub, eval_mul, eval_C] at hBz ⊢
  have hBz' : R.num.eval z - c * R.denom.eval z ≠ 0 := by simpa [IsRoot] using hBz
  have e1 : (c : ℂ) * ((R.num.eval z - R.denom.eval z) / (R.num.eval z - c * R.denom.eval z)) - 1
      = (c - 1) * R.num.eval z / (R.num.eval z - c * R.denom.eval z) := by
    rw [mul_div_assoc', div_sub_one hBz']; congr 1; ring
  have e2 : (R.num.eval z - R.denom.eval z) / (R.num.eval z - c * R.denom.eval z) - 1
      = (c - 1) * R.denom.eval z / (R.num.eval z - c * R.denom.eval z) := by
    rw [div_sub_one hBz']; congr 1; ring
  have hDz : R.denom.eval z ≠ 0 := hD
  have hB2 : R.num.eval z - R.denom.eval z * c ≠ 0 := by rwa [mul_comm] at hBz'
  rw [e1, e2]
  field_simp

/-! ### The shared points are real -/

/-- With the endpoint identities for `ρ = 1` (`U = κ t^{-1}`, `V = κ t`), every finite shared
point `t₀ ∈ ℂ*` satisfies `t₀² = n/m > 0`, hence is real. -/
lemma im_eq_zero_of_shared {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {κ : ℂ}
    (hpair : NormalizedPair {0}ᶜ f g a) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ))
    {t₀ : ℂ} (ht₀ : t₀ ≠ 0) {j : Fin 3} (hj : 0 < mult f (a j : Sphere) t₀) : t₀.im = 0 := by
  have h := rational_aux_ratio hpair hκ hU hV ht₀ hj
  set m := mult f (a j : Sphere) t₀
  set n := mult g (a j : Sphere) t₀
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  have hsq : t₀ ^ 2 = ((n / m : ℝ) : ℂ) := by
    push_cast
    rw [zpow_neg, zpow_one] at h
    field_simp at h
    field_simp
    first | linear_combination h | linear_combination -h
  obtain ⟨s, hs, -⟩ := exists_real_of_sq_eq (by positivity) hsq
  rw [hs, Complex.ofReal_im]

/-- At a point where the denominator does not vanish, `R(z) = w` gives a point of the `w`-fiber,
provided `R` is not identically `w` near `z`. -/
lemma mult_pos_of_ratEval_eq {R : RatFunc ℂ} {z w : ℂ} (hD : R.denom.eval z ≠ 0)
    (hR : ratEval R z = w)
    (hne : meromorphicOrderAt (fun t => ratEval R t - w) z ≠ ⊤) :
    0 < mult (ratEval R) (w : Sphere) z := by
  have han : AnalyticAt ℂ (fun t => ratEval R t - w) z := by
    have : (fun t => ratEval R t - w) = fun t => R.num.eval t / R.denom.eval t - w :=
      funext fun t => by rw [ratEval_eq]
    rw [this]
    exact ((R.num.differentiable.analyticAt z).div (R.denom.differentiable.analyticAt z) hD).sub
      analyticAt_const
  have hpos := (analyticAt_eq_zero_iff_order_pos han).1 (by simp [hR])
  rw [mult_coe]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hk] at hpos ⊢
  simp only [WithTop.untop₀_coe]
  have : (0 : ℤ) < k := by exact_mod_cast hpos
  omega

/-- The reduced numerator and denominator of a rational function do not vanish simultaneously. -/
lemma num_or_denom_ne_zero (R : RatFunc ℂ) (z : ℂ) :
    R.num.eval z ≠ 0 ∨ R.denom.eval z ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom R
  have := congrArg (eval z) huv
  simp [h.1, h.2] at this

/-! ### Lemma 9.26, reality -/

/-- **Lemma 9.26** (reality).  Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` for the values
`0, 1, c` (`c` real), with endpoint identities for `ρ = 1`: `U = κ t^{-1}`, `V = κ t`
(`κ ≠ 0`), `R(0) = 0`, `R(∞) = ∞`, `S(0) = ∞` and `S(∞) = 0`.  Then `R` and `S` are real
rational functions: their reduced numerators and denominators have real coefficients. -/
theorem rational_reality {R S : RatFunc ℂ} {c : ℝ} {κ : ℂ} (hκ : κ ≠ 0)
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) ![0, 1, (c : ℂ)])
    (hU : ∀ᶠ t in cofinite,
      t * auxU ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite,
      t * auxV ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (1 : ℤ))
    (hR0 : R.num.eval 0 = 0) (hRinf : R.denom.natDegree < R.num.natDegree)
    (hS0 : S.denom.eval 0 = 0) (hSinf : S.num.natDegree < S.denom.natDegree) :
    (∃ p q : ℝ[X], IsCoprime p q ∧ q.Monic ∧ R.num = p.map (algebraMap ℝ ℂ) ∧
      R.denom = q.map (algebraMap ℝ ℂ)) ∧
    (∃ p q : ℝ[X], IsCoprime p q ∧ q.Monic ∧ S.num = p.map (algebraMap ℝ ℂ) ∧
      S.denom = q.map (algebraMap ℝ ℂ)) := by
  have hc0 : (c : ℂ) ≠ 0 := fun h => by
    have := hpair.injective.ne (show (0 : Fin 3) ≠ 2 by decide); simp [h] at this
  have hc1 : c ≠ 1 := fun h => by
    have := hpair.injective.ne (show (1 : Fin 3) ≠ 2 by decide); simp [h] at this
  constructor
  · -- `R` is real
    have key : ∀ z, ∀ j : Fin 3, R.denom.eval z ≠ 0 → z ≠ 0 →
        ratEval R z = ![0, 1, (c : ℂ)] j → z.im = 0 := fun z j hD hz hRz =>
      im_eq_zero_of_shared hpair hκ hU hV hz
        (mult_pos_of_ratEval_eq hD hRz (hpair.nonconst_f.2 z hz _))
    have hD0 : R.denom.eval 0 ≠ 0 := (num_or_denom_ne_zero R 0).resolve_left (not_not.2 hR0)
    have hDne : ∀ z, R.num.eval z = 0 → R.denom.eval z ≠ 0 := fun z hz =>
      (num_or_denom_ne_zero R z).resolve_left (not_not.2 hz)
    have hNne : R.num ≠ 0 := by
      rintro h; rw [h, natDegree_zero] at hRinf; omega
    refine ratFunc_real_of_real_points hc1 ?_ ?_ ?_ ?_
    · intro h
      have := congrArg (eval 0) h
      simp only [eval_sub, eval_mul, eval_C, hR0, eval_zero, zero_sub, neg_eq_zero,
        mul_eq_zero] at this
      tauto
    · intro z hz
      have hDz : R.denom.eval z ≠ 0 := fun h0 =>
        hDne z (by rw [hz, h0]) h0
      refine key z 1 hDz (by rintro rfl; exact hD0 (by rw [← hz, hR0])) ?_
      rw [ratEval_eq, hz, div_self hDz]; simp
    · intro z hz
      have hDz : R.denom.eval z ≠ 0 := fun h0 =>
        hDne z (by rw [hz, h0, mul_zero]) h0
      refine key z 2 hDz (by
        rintro rfl
        rw [hR0] at hz
        rcases mul_eq_zero.1 hz.symm with h | h
        · exact hc0 h
        · exact hD0 h) ?_
      rw [ratEval_eq, hz, mul_div_assoc, div_self hDz, mul_one]; simp
    · have h1 : (R.num - R.denom).leadingCoeff = R.num.leadingCoeff :=
        leadingCoeff_sub_of_degree_lt (degree_lt_degree hRinf)
      have h2 : (R.num - C (c : ℂ) * R.denom).leadingCoeff = R.num.leadingCoeff :=
        leadingCoeff_sub_of_degree_lt
          (degree_lt_degree ((natDegree_C_mul_le _ _).trans_lt hRinf))
      rw [h1, h2, div_self (leadingCoeff_ne_zero.2 hNne), Complex.one_im]
  · -- `S` is real
    have key : ∀ z, ∀ j : Fin 3, S.denom.eval z ≠ 0 → z ≠ 0 →
        ratEval S z = ![0, 1, (c : ℂ)] j → z.im = 0 := fun z j hD hz hSz =>
      im_eq_zero_of_shared hpair hκ hU hV hz ((hpair.im j z hz).2
        (mult_pos_of_ratEval_eq hD hSz (hpair.nonconst_g.2 z hz _)))
    have hN0 : S.num.eval 0 ≠ 0 := (num_or_denom_ne_zero S 0).resolve_right (not_not.2 hS0)
    have hDne : ∀ z, S.num.eval z = 0 → S.denom.eval z ≠ 0 := fun z hz =>
      (num_or_denom_ne_zero S z).resolve_left (not_not.2 hz)
    have hDnz : S.denom ≠ 0 := S.denom_ne_zero
    refine ratFunc_real_of_real_points hc1 ?_ ?_ ?_ ?_
    · intro h
      have := congrArg (eval 0) h
      simp only [eval_sub, eval_mul, eval_C, hS0, mul_zero, sub_zero, eval_zero] at this
      exact hN0 this
    · intro z hz
      have hDz : S.denom.eval z ≠ 0 := fun h0 =>
        hDne z (by rw [hz, h0]) h0
      refine key z 1 hDz (by rintro rfl; exact hN0 (by rw [hz, hS0])) ?_
      rw [ratEval_eq, hz, div_self hDz]; simp
    · intro z hz
      have hDz : S.denom.eval z ≠ 0 := fun h0 =>
        hDne z (by rw [hz, h0, mul_zero]) h0
      refine key z 2 hDz (by rintro rfl; exact hN0 (by rw [hz, hS0, mul_zero])) ?_
      rw [ratEval_eq, hz, mul_div_assoc, div_self hDz, mul_one]; simp
    · have hlD : S.denom.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hDnz
      have h1 : (S.num - S.denom).leadingCoeff = -S.denom.leadingCoeff :=
        leadingCoeff_sub_of_degree_lt' (degree_lt_degree hSinf)
      have h2 : (S.num - C (c : ℂ) * S.denom).leadingCoeff = -((c : ℂ) * S.denom.leadingCoeff) := by
        rw [leadingCoeff_sub_of_degree_lt', leadingCoeff_mul, leadingCoeff_C]
        apply degree_lt_degree
        rwa [natDegree_C_mul hc0]
      rw [h1, h2, show -S.denom.leadingCoeff / -((c : ℂ) * S.denom.leadingCoeff) =
        ((1 / c : ℝ) : ℂ) by push_cast; field_simp, Complex.ofReal_im]

/-! ### Lemmas 9.26 and 9.27, and the end of the proof of Proposition 9.28 -/

lemma ratEval_eq_realRatFun {R : RatFunc ℂ} {p q : ℝ[X]} (hp : R.num = p.map (algebraMap ℝ ℂ))
    (hq : R.denom = q.map (algebraMap ℝ ℂ)) : ratEval R = realRatFun p q :=
  funext fun z => by rw [ratEval_eq, hp, hq]; rfl

/-- If a normalized pair on `ℂ*` has no common point over one of its finite values, then all four
values `a 0, a 1, a 2, ∞` are shared CM on `ℂ*` (by External theorem 2.5, via Lemma 9.7). -/
theorem cm_of_fiber_empty {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hpair : NormalizedPair {0}ᶜ f g a)
    {j₀ : Fin 3} (hempty : ∀ t : ℂ, t ≠ 0 → mult f (a j₀ : Sphere) t = 0) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ f g (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] i) := by
  have hcm0 : SharesCMOn {0}ᶜ f g (a j₀ : Sphere) := fun t ht => by
    have h1 := hempty t ht
    have h2 : mult g (a j₀ : Sphere) t = 0 := by
      by_contra h
      have := (hpair.im j₀ t ht).2 (Nat.pos_of_ne_zero h)
      omega
    rw [h1, h2]
  set b : Fin 4 → Sphere := ![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] with hbdef
  have hb : Function.Injective b := by
    intro i k h
    fin_cases i <;> fin_cases k <;> simp [b] at h ⊢ <;>
      exact absurd (hpair.injective h) (by decide)
  have him : ∀ i, SharesIMOn {0}ᶜ f g (b i) := by
    intro i
    fin_cases i
    exacts [hpair.im 0, hpair.im 1, hpair.im 2, hpair.cm_top.sharesIMOn]
  have hbj : b j₀.castSucc = (a j₀ : Sphere) := by fin_cases j₀ <;> rfl
  have hne : j₀.castSucc ≠ (3 : Fin 4) := by fin_cases j₀ <;> decide
  exact punctured_two_cm hpair.nonconst_f hpair.nonconst_g b hb him hne
    (by rw [hbj]; exact hcm0) hpair.cm_top

/-- **Lemmas 9.26 + 9.27 and the conclusion of Proposition 9.28** for a pair with endpoint pole
order `ρ = 1`.  Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` for the values `0, 1, c` with
`c < 0`, satisfying the conclusions of Lemma 9.2 (coincidence multiplicity one on `ℂ*`) and the
endpoint identities with `ρ = 1` and `κ > 0`:

* `U = (R - S) DR/P(R) = κ t^{-1}` and `V = (R - S) DS/P(S) = κ t`;
* `R(0) = 0`, and `R(t) ∼ t/κ` at `∞` (`deg num = deg denom + 1`, leading ratio `1/κ`);
* `S(∞) = 0`, and `S(t) ∼ 1/(κ t)` at `0` (simple pole at `0` with residue `1/κ`).

Then `R` and `S` share all four values `0, 1, c, ∞` CM on `ℂ*`. -/
theorem rational_cm_rho_one {R S : RatFunc ℂ} {c κ : ℝ} (hc : c < 0) (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) ![0, 1, (c : ℂ)])
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t)
    (hU : ∀ᶠ t in cofinite,
      t * auxU ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite,
      t * auxV ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (1 : ℤ))
    (hR0 : R.num.eval 0 = 0) (hdeg : R.num.natDegree = R.denom.natDegree + 1)
    (hlc : R.num.leadingCoeff / R.denom.leadingCoeff = 1 / κ)
    (hS0 : S.denom.eval 0 = 0) (hres : S.num.eval 0 / S.denom.derivative.eval 0 = 1 / κ)
    (hSinf : S.num.natDegree < S.denom.natDegree) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![((0 : ℂ) : Sphere), ((1 : ℂ) : Sphere), ((c : ℂ) : Sphere), ⊤] i) := by
  have hκ' : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  obtain ⟨⟨p, q, hcop, -, hp, hq⟩, ⟨p₂, q₂, hcop₂, -, hp₂, hq₂⟩⟩ :=
    rational_reality hκ' hpair hU hV hR0 (by omega) hS0 hSinf
  have hdeg' : p.natDegree = q.natDegree + 1 := by
    rw [hp, hq, natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective,
      natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective] at hdeg
    exact hdeg
  have hlc' : p.leadingCoeff / q.leadingCoeff = 1 / κ := by
    rw [hp, hq, leadingCoeff_map_of_injective (algebraMap ℝ ℂ).injective,
      leadingCoeff_map_of_injective (algebraMap ℝ ℂ).injective] at hlc
    apply Complex.ofReal_injective
    push_cast
    exact hlc
  have h0 : ∀ P : ℝ[X], (P.map (algebraMap ℝ ℂ)).eval 0 = ((P.eval 0 : ℝ) : ℂ) := fun P => by
    have := eval_map_ofReal P 0
    rwa [Complex.ofReal_zero] at this
  have hq₂0 : q₂.eval 0 = 0 := by
    rw [hq₂, h0] at hS0; exact_mod_cast hS0
  have hres' : p₂.eval 0 / q₂.derivative.eval 0 = 1 / κ := by
    rw [hp₂, hq₂, derivative_map, h0, h0] at hres
    apply Complex.ofReal_injective
    push_cast
    exact hres
  rw [ratEval_eq_realRatFun hp hq, ratEval_eq_realRatFun hp₂ hq₂] at hpair hco hU hV ⊢
  have hempty := rational_zero_fiber_empty hc hκ hpair hco hU hV hcop hcop₂ hdeg' hlc' hq₂0 hres'
  have hall := cm_of_fiber_empty hpair (j₀ := 0) (fun t ht => by simpa using hempty t ht)
  intro i
  have := hall i
  fin_cases i <;> simpa using this

end ThreeIM
