module

public import RequestProject.ThreeIM.SmallEntire
public import RequestProject.ThreeIM.Growth
public import RequestProject.ThreeIM.RationalAux
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Descent of periodic functions of linear growth (Lemma 8.15)

If a meromorphic function `h` on `ℂ` has the period `2πiq` (`q > 0`) and `T(r, h) = O(r)`, then
`h(t) = R(e^{t/q})` for a rational function `R`.

The proof follows the paper, with one simplification in the last step:

* the poles of `h` in the strip `0 ≤ Im t < 2πq` are finite in number, since each of them
  generates a vertical progression of poles, and `ℓ` such progressions force
  `N(r, h) ≥ ℓ r / (2πeq)`;
* multiplying `h` by `Q(e^{t/q})`, with `Q` the polynomial whose roots are the values of
  `e^{t/q}` at those poles (with the pole orders as multiplicities), gives a periodic entire
  function `E` with `T(r, E) = O(r)`;
* the maximum modulus bound (External theorem 2.3) gives `|E(t)| ≤ A e^{B|t|}`, so
  `F(w) = E(q log w)` is holomorphic on `ℂ*` with at most polynomial growth at `0` and `∞`;
  hence `F(w) = p(w) / w^K` for a polynomial `p` (removable singularity theorem and Cauchy
  estimates).
-/

@[expose] public section

open Filter Set Topology Metric Nat Polynomial

namespace ThreeIM

/-! ### Entire functions of polynomial growth -/

/-- An entire function with `|G(z)| ≤ A |z|^K` for `|z| ≥ 1` is a polynomial. -/
theorem polynomial_of_growth {G : ℂ → ℂ} (hG : Differentiable ℂ G) {A : ℝ} {K : ℕ}
    (hb : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖G z‖ ≤ A * ‖z‖ ^ K) :
    ∃ p : Polynomial ℂ, ∀ z, G z = p.eval z := by
  refine polynomial_of_iteratedDeriv_eq_zero hG (N := K) fun n hn => ?_
  have hcauchy : ∀ r ≥ (1:ℝ), ‖iteratedDeriv n G 0‖ ≤ n ! * |A| / r := by
    intro r hr1
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (c := 0)
      (C := |A| * r ^ K) (by linarith : (0 : ℝ) < r) hG.diffContOnCl
      (fun z hz => by
        rw [mem_sphere_zero_iff_norm] at hz
        refine (hb z (by linarith)).trans ?_
        rw [hz]; exact mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
    refine h.trans ?_
    have hrn : r ^ n = r ^ K * r ^ (n - K) := by rw [← pow_add]; congr 1; omega
    have hge : r ≤ r ^ (n - K) := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ (n - K) := pow_le_pow_right₀ hr1 (by omega)
    rw [hrn, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : 0 ≤ (n ! : ℝ) * |A| * r ^ K := by positivity
    have := mul_le_mul_of_nonneg_left hge hpos
    nlinarith
  apply norm_le_zero_iff.1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set r := max 1 (n ! * |A| / ε + 1)
  have hr : 1 ≤ r := le_max_left _ _
  have hrpos : 0 < r := by positivity
  have hr2 : n ! * |A| / ε < r := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have : (n ! : ℝ) * |A| / r ≤ ε := by
    rw [div_le_iff₀ hrpos]
    rw [div_lt_iff₀ hε] at hr2
    linarith
  linarith [hcauchy r hr]

/-- A holomorphic function on `ℂ*` with `|F(w)| ≤ A max(|w|, |w|⁻¹)^K` is of the form
`p(w) / w^K` with a polynomial `p`. -/
theorem laurent_of_growth {F : ℂ → ℂ} (hF : ∀ w ≠ 0, DifferentiableAt ℂ F w) {A : ℝ} {K : ℕ}
    (hb : ∀ w : ℂ, w ≠ 0 → ‖F w‖ ≤ A * (max ‖w‖ ‖w‖⁻¹) ^ K) :
    ∃ p : Polynomial ℂ, ∀ w ≠ 0, F w = p.eval w / w ^ K := by
  set G : ℂ → ℂ := fun w => w ^ K * F w with hGdef
  have hGd : ∀ w ≠ 0, DifferentiableAt ℂ G w := fun w hw =>
    (differentiableAt_pow K).mul (hF w hw)
  set G' := Function.update G 0 (limUnder (𝓝[≠] (0:ℂ)) G) with hG'
  have hball : DifferentiableOn ℂ G' (ball 0 1) := by
    apply Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds _ one_pos)
    · intro w hw
      exact (hGd w hw.2).differentiableWithinAt
    · refine ⟨A, ?_⟩
      rintro _ ⟨w, ⟨hw1, hw0⟩, rfl⟩
      have hw0' : w ≠ 0 := hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0'
      have hw1' : ‖w‖ < 1 := by simpa using hw1
      have hmax : max ‖w‖ ‖w‖⁻¹ = ‖w‖⁻¹ := max_eq_right (by
        rw [le_inv_comm₀ hn hn]; nlinarith [one_lt_inv_iff₀.2 ⟨hn, hw1'⟩])
      simp only [Function.comp, hGdef, norm_mul, norm_pow]
      rw [mul_comm]
      calc ‖F w‖ * ‖w‖ ^ K ≤ A * (‖w‖⁻¹) ^ K * ‖w‖ ^ K := by
            rw [← hmax]; exact mul_le_mul_of_nonneg_right (hb w hw0') (by positivity)
        _ = A := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow, mul_one]
  have hG'd : Differentiable ℂ G' := by
    intro w
    by_cases hw : w = 0
    · subst hw; exact hball.differentiableAt (ball_mem_nhds _ one_pos)
    · have : G' =ᶠ[𝓝 w] G := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
        exact Function.update_of_ne hz _ _
      exact (hGd w hw).congr_of_eventuallyEq this
  obtain ⟨p, hp⟩ := polynomial_of_growth hG'd (A := A) (K := 2 * K) (fun z hz => by
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    rw [hG', Function.update_of_ne hz0]
    have hmax : max ‖z‖ ‖z‖⁻¹ = ‖z‖ := max_eq_left (by
      calc ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
        _ ≤ ‖z‖ := hz)
    simp only [hGdef, norm_mul, norm_pow]
    calc ‖z‖ ^ K * ‖F z‖ ≤ ‖z‖ ^ K * (A * ‖z‖ ^ K) := by
          rw [← hmax]; exact mul_le_mul_of_nonneg_left (hb z hz0) (by positivity)
      _ = A * ‖z‖ ^ (2 * K) := by ring)
  refine ⟨p, fun w hw => ?_⟩
  have := hp w
  rw [hG', Function.update_of_ne hw] at this
  rw [← this, hGdef]
  field_simp

/-! ### Periodic entire functions of exponential type -/

lemma eq_of_exp_eq_of_periodic {E : ℂ → ℂ} {q : ℝ}
    (hper : ∀ t, E (t + 2 * Real.pi * Complex.I * q) = E t) {u v : ℂ}
    (huv : Complex.exp u = Complex.exp v) : E (q * u) = E (q * v) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 huv
  have hP : Function.Periodic E (2 * Real.pi * Complex.I * q) := hper
  rw [hn, show (q:ℂ) * (v + n * (2 * Real.pi * Complex.I)) =
    q * v + n * (2 * Real.pi * Complex.I * q) by ring]
  exact hP.int_mul n (q * v)

lemma log_max_eq_abs {x : ℝ} (hx : 0 < x) : Real.log (max x x⁻¹) = |Real.log x| := by
  rcases le_total 1 x with h | h
  · rw [max_eq_left (by calc x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      _ ≤ x := h), abs_of_nonneg (Real.log_nonneg h)]
  · rw [max_eq_right (by calc x ≤ 1 := h
      _ ≤ x⁻¹ := one_le_inv_iff₀.2 ⟨hx, h⟩), Real.log_inv,
      abs_of_nonpos (Real.log_nonpos hx.le h)]

/-- A `2πiq`-periodic entire function with `|E(t)| ≤ A e^{B|t|}` is of the form
`p(e^{t/q}) / e^{Kt/q}` with a polynomial `p`. -/
theorem periodic_entire_descent {E : ℂ → ℂ} (hE : Differentiable ℂ E) {q : ℝ} (hq : 0 < q)
    (hper : ∀ t, E (t + 2 * Real.pi * Complex.I * q) = E t) {A B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, ‖E t‖ ≤ A * Real.exp (B * ‖t‖)) :
    ∃ (p : Polynomial ℂ) (K : ℕ), ∀ t, E t =
      p.eval (Complex.exp (t / q)) / Complex.exp (t / q) ^ K := by
  set F : ℂ → ℂ := fun w => E (q * Complex.log w) with hFdef
  have hF : ∀ w ≠ 0, DifferentiableAt ℂ F w := by
    intro w hw
    by_cases hs : w ∈ Complex.slitPlane
    · exact (hE _).comp w ((differentiableAt_const _).mul (Complex.differentiableAt_log hs))
    · have hs' : -w ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff] at hs ⊢
        push_neg at hs
        left
        have hre : w.re ≠ 0 := fun h => hw (Complex.ext h hs.2)
        simp only [Complex.neg_re]
        have := hs.1
        exact neg_pos.2 (lt_of_le_of_ne this hre)
      have heq : (fun z => E (q * (Complex.log (-z) + Real.pi * Complex.I))) =ᶠ[𝓝 w] F := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
        apply eq_of_exp_eq_of_periodic hper
        rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hz), Complex.exp_log hz,
          Complex.exp_pi_mul_I]; ring
      refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
      refine (hE _).comp w ((differentiableAt_const _).mul ?_)
      exact ((Complex.differentiableAt_log hs').comp w differentiableAt_id.neg).add
        (differentiableAt_const _)
  set K : ℕ := ⌈B * q⌉₊
  have hA : 0 ≤ A := by
    have := hb 0; simp at this; linarith [norm_nonneg (E 0)]
  have hFb : ∀ w : ℂ, w ≠ 0 →
      ‖F w‖ ≤ (A * Real.exp (B * q * Real.pi)) * (max ‖w‖ ‖w‖⁻¹) ^ K := by
    intro w hw
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hM1 : 1 ≤ max ‖w‖ ‖w‖⁻¹ := by
      rcases le_total 1 ‖w‖ with h | h
      · exact h.trans (le_max_left _ _)
      · exact (one_le_inv_iff₀.2 ⟨hn, h⟩).trans (le_max_right _ _)
    have hlog : ‖(q:ℂ) * Complex.log w‖ ≤ q * (|Real.log ‖w‖| + Real.pi) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
      apply mul_le_mul_of_nonneg_left _ hq.le
      calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖w‖| + Real.pi :=
          add_le_add (le_of_eq (by rw [Complex.log_re]))
            (by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w)
    calc ‖F w‖ ≤ A * Real.exp (B * ‖(q:ℂ) * Complex.log w‖) := hb _
      _ ≤ A * Real.exp (B * (q * (|Real.log ‖w‖| + Real.pi))) := by gcongr
      _ = (A * Real.exp (B * q * Real.pi)) * Real.exp (B * q * Real.log (max ‖w‖ ‖w‖⁻¹)) := by
          rw [log_max_eq_abs hn, mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (A * Real.exp (B * q * Real.pi)) * (max ‖w‖ ‖w‖⁻¹) ^ K := by
          gcongr
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), mul_comm (Real.log _)]
          gcongr
          · exact Real.log_nonneg hM1
          · exact Nat.le_ceil _
  obtain ⟨p, hp⟩ := laurent_of_growth hF hFb
  refine ⟨p, K, fun t => ?_⟩
  rw [← hp _ (Complex.exp_ne_zero _), hFdef]
  simp only
  have := eq_of_exp_eq_of_periodic hper (Complex.exp_log (Complex.exp_ne_zero (t / q)))
  have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [this]; congr 1; field_simp

/-! ### Exponential bound from linear growth of the characteristic -/

/-- An entire function with `T(r, E) = O(r)` satisfies `|E(t)| ≤ A e^{B|t|}`. -/
theorem entire_exp_bound {E : ℂ → ℂ} (hE : Differentiable ℂ E) {K : ℝ}
    (hT : ∀ᶠ r in atTop, charT E r ≤ K * r) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ t, ‖E t‖ ≤ A * Real.exp (B * ‖t‖) := by
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 hT
  set ρ := max r₀ 1
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) (2 * ρ)).exists_bound_of_continuousOn
    hE.continuous.continuousOn
  refine ⟨max M 1, 6 * |K|, by positivity, fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ 2 * ρ
  · calc ‖E t‖ ≤ M := hM t (by simpa using ht)
      _ ≤ max M 1 * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max M 1 * Real.exp (6 * |K| * ‖t‖) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (by positivity)
  · push_neg at ht
    set r := ‖t‖
    have hρ1 : 1 ≤ ρ := le_max_right _ _
    have hr1 : 1 ≤ r := by linarith
    have h1 := ext_entire_posLog_le hE hr1 (show r < 2 * r by linarith) rfl
    have h2 := hr₀ (2 * r) (by linarith [le_max_left r₀ 1])
    rw [show (2 * r + r) / (2 * r - r) = 3 by field_simp; ring] at h1
    have h3 : Real.posLog ‖E t‖ ≤ 6 * |K| * r := by
      nlinarith [le_abs_self K]
    calc ‖E t‖ ≤ Real.exp (Real.posLog ‖E t‖) := le_exp_posLog _
      _ ≤ Real.exp (6 * |K| * r) := Real.exp_le_exp.2 h3
      _ ≤ max M 1 * Real.exp (6 * |K| * r) :=
          le_mul_of_one_le_left (by positivity) (le_max_right _ _)

/-! ### Poles in a period strip -/

/-- Periodicity (off a discrete set) preserves orders. -/
lemma meromorphicOrderAt_add_period {h : ℂ → ℂ} {ω : ℂ}
    (hper : ∀ᶠ t in codiscrete ℂ, h (t + ω) = h t) (t : ℂ) :
    meromorphicOrderAt h (t + ω) = meromorphicOrderAt h t := by
  have h1 : meromorphicOrderAt (h ∘ fun z => z + ω) t = meromorphicOrderAt h (t + ω) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)
  rw [← h1]
  apply meromorphicOrderAt_congr
  have := (mem_codiscrete.1 hper) t
  rw [disjoint_principal_right, compl_compl] at this
  exact this

lemma meromorphicOrderAt_add_int_mul_period {h : ℂ → ℂ} {ω : ℂ}
    (hper : ∀ᶠ t in codiscrete ℂ, h (t + ω) = h t) (t : ℂ) (n : ℤ) :
    meromorphicOrderAt h (t + n * ω) = meromorphicOrderAt h t := by
  have hN : ∀ (m : ℕ) (t : ℂ), meromorphicOrderAt h (t + m * ω) = meromorphicOrderAt h t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro t
      rw [show t + ((m + 1 : ℕ) : ℂ) * ω = (t + m * ω) + ω by push_cast; ring,
        meromorphicOrderAt_add_period hper, ih]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact_mod_cast hN m t
  · have := hN m (t + ((-(m:ℤ) : ℤ) : ℂ) * ω)
    rw [show t + ((-(m:ℤ) : ℤ) : ℂ) * ω + m * ω = t by push_cast; ring] at this
    exact this.symm

/-- `ℓ` disjoint vertical progressions in the support of a divisor force
`N(r) ≥ ℓ r / (e · spacing)`. -/
lemma logCounting_progressions (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) (S : Finset ℂ)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hdisj : ∀ s ∈ S, ∀ s' ∈ S, ∀ k k' : ℤ,
      s + Complex.I * ℓ * k = s' + Complex.I * ℓ * k' → s = s' ∧ k = k')
    (hpts : ∀ s ∈ S, ∀ k : ℤ, 1 ≤ D (s + Complex.I * ℓ * k)) :
    ∀ᶠ r in atTop, (S.card : ℝ) / (Real.exp 1 * ℓ) * r ≤
      Function.locallyFinsuppWithin.logCounting D r := by
  set e := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  have he1 : 1 ≤ e := by rw [he]; exact Real.one_le_exp zero_le_one
  set M := ∑ s ∈ S, ‖s‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsM : ∀ s ∈ S, ‖s‖ ≤ M := fun s hs =>
    Finset.single_le_sum (f := fun s => ‖s‖) (fun _ _ => norm_nonneg _) hs
  filter_upwards [eventually_ge_atTop (e * (2 * M + 4 * ℓ) + 1)] with r hr
  have hr1 : 1 ≤ r := by
    have : 0 ≤ e * (2 * M + 4 * ℓ) := by positivity
    linarith
  have hr0 : 0 < r := by linarith
  set K : ℕ := ⌊(r / e - M) / ℓ⌋₊ with hK
  set zk : ℂ × ℤ → ℂ := fun p => p.1 + Complex.I * ℓ * p.2 with hzk
  set P := ((S ×ˢ Finset.Icc (-(K : ℤ)) K).image zk).erase 0 with hP
  have hbound : ∀ p ∈ S ×ˢ Finset.Icc (-(K : ℤ)) K, ‖zk p‖ ≤ r / e := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    have hk' : |(p.2 : ℝ)| ≤ K := by
      rw [abs_le]; constructor <;> [have := hp.2.1; have := hp.2.2] <;> exact_mod_cast (by omega)
    have hKle : (K : ℝ) ≤ (r / e - M) / ℓ := by
      apply Nat.floor_le
      apply div_nonneg _ hℓ.le
      rw [sub_nonneg, le_div_iff₀ he0]; nlinarith
    have := norm_progression_le p.1 hℓ p.2
    have h2 : ℓ * |(p.2 : ℝ)| ≤ r / e - M := by
      calc ℓ * |(p.2 : ℝ)| ≤ ℓ * K := by gcongr
        _ ≤ ℓ * ((r / e - M) / ℓ) := by gcongr
        _ = r / e - M := by field_simp
    have := hsM p.1 hp.1
    simp only [hzk]; linarith
  have hsum := logCounting_ge_sum D hD hr1 P (by
    intro z hz
    rw [hP, Finset.mem_erase, Finset.mem_image] at hz
    obtain ⟨hz0, p, hp, rfl⟩ := hz
    refine ⟨hpts p.1 (Finset.mem_product.1 hp).1 p.2, ?_, hz0⟩
    have := hbound p hp
    have : r / e ≤ r := div_le_self hr0.le he1
    linarith)
  have hterm : ∀ z ∈ P, (1 : ℝ) ≤ Real.log (r * ‖z‖⁻¹) := by
    intro z hz
    rw [hP, Finset.mem_erase, Finset.mem_image] at hz
    obtain ⟨hz0, p, hp, rfl⟩ := hz
    have hb := hbound p hp
    have hpos : 0 < ‖zk p‖ := norm_pos_iff.2 hz0
    rw [Real.le_log_iff_exp_le (by positivity), ← he, ← div_eq_mul_inv, le_div_iff₀ hpos]
    rw [le_div_iff₀ he0] at hb; linarith
  have hinj : Set.InjOn zk ↑(S ×ˢ Finset.Icc (-(K : ℤ)) K) := by
    intro p hp p' hp' hpp
    have hp1 := (Finset.mem_product.1 hp).1
    have hp1' := (Finset.mem_product.1 hp').1
    obtain ⟨h1, h2⟩ := hdisj p.1 hp1 p'.1 hp1' p.2 p'.2 hpp
    exact Prod.ext h1 h2
  have hcard : 2 * (K : ℝ) * S.card ≤ P.card := by
    have h1 := Finset.pred_card_le_card_erase (s := (S ×ˢ Finset.Icc (-(K : ℤ)) K).image zk)
      (a := 0)
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Int.card_Icc] at h1
    have : (↑K + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
    rw [this] at h1
    have : 2 * K * S.card ≤ P.card := by
      rw [hP]
      rcases Nat.eq_zero_or_pos S.card with h | h
      · rw [h]; simp
      · have : 2 * K * S.card + 1 ≤ S.card * (2 * K + 1) := by nlinarith
        omega
    exact_mod_cast this
  have hsum2 : (P.card : ℝ) ≤ ∑ z ∈ P, Real.log (r * ‖z‖⁻¹) := by
    simpa using Finset.card_nsmul_le_sum P _ 1 hterm
  have hKge : (r / e - M) / ℓ - 1 ≤ K := (Nat.sub_one_lt_floor _).le
  have h2K : 1 / (e * ℓ) * r ≤ 2 * K := by
    have : 1 / (e * ℓ) * r ≤ 2 * ((r / e - M) / ℓ - 1) := by
      rw [show 1 / (e * ℓ) * r = (r / e) / ℓ by field_simp]
      rw [show 2 * ((r / e - M) / ℓ - 1) = (2 * (r / e) - 2 * M - 2 * ℓ) / ℓ by
        field_simp]
      apply div_le_div_of_nonneg_right _ hℓ.le
      have : e * (2 * M + 4 * ℓ) ≤ r := by linarith
      have : 2 * M + 4 * ℓ ≤ r / e := by rw [le_div_iff₀ he0]; linarith
      linarith
    linarith
  have hc0 : (0:ℝ) ≤ S.card := by positivity
  calc (S.card : ℝ) / (e * ℓ) * r = (1 / (e * ℓ) * r) * S.card := by ring
    _ ≤ 2 * K * S.card := mul_le_mul_of_nonneg_right h2K hc0
    _ ≤ _ := by linarith

/-- A `2πiq`-periodic meromorphic function with `T(r, h) = O(r)` has only finitely many poles in
the strip `0 ≤ Im t < 2πq`. -/
theorem finite_poles_strip {h : ℂ → ℂ} (hh : MeromorphicOn h univ) {q : ℝ} (hq : 0 < q)
    (hper : ∀ᶠ t in codiscrete ℂ, h (t + 2 * Real.pi * Complex.I * q) = h t)
    {K : ℝ} (hT : ∀ᶠ r in atTop, charT h r ≤ K * r) :
    {s : ℂ | 0 ≤ s.im ∧ s.im < 2 * Real.pi * q ∧ meromorphicOrderAt h s < 0}.Finite := by
  by_contra hinf
  set ℓ : ℝ := 2 * Real.pi * q with hℓdef
  have hℓ : 0 < ℓ := by positivity
  set e := Real.exp 1
  set m : ℕ := ⌈e * ℓ * K⌉₊ + 1
  obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf m
  set D := (MeromorphicOn.divisor h univ)⁻ with hD
  have hD0 : 0 ≤ D := negPart_nonneg _
  have hdisj : ∀ s ∈ S, ∀ s' ∈ S, ∀ k k' : ℤ,
      s + Complex.I * ℓ * k = s' + Complex.I * ℓ * k' → s = s' ∧ k = k' := by
    intro s hs s' hs' k k' hkk
    obtain ⟨h1, h2, -⟩ := hSsub hs
    obtain ⟨h1', h2', -⟩ := hSsub hs'
    have him := congrArg Complex.im hkk
    simp at him
    have hk : k = k' := by
      have hlt1 : ℓ * ((k:ℝ) - k') < ℓ := by nlinarith
      have hlt2 : ℓ * ((k':ℝ) - k) < ℓ := by nlinarith
      have a1 : ((k:ℝ) - k') < 1 := by nlinarith
      have a2 : ((k':ℝ) - k) < 1 := by nlinarith
      have b1 : k - k' < 1 := by exact_mod_cast a1
      have b2 : k' - k < 1 := by exact_mod_cast a2
      omega
    subst hk
    exact ⟨by simpa using hkk, rfl⟩
  have hpts : ∀ s ∈ S, ∀ k : ℤ, 1 ≤ D (s + Complex.I * ℓ * k) := by
    intro s hs k
    obtain ⟨-, -, hneg⟩ := hSsub hs
    have hord : meromorphicOrderAt h (s + Complex.I * ℓ * k) = meromorphicOrderAt h s := by
      rw [show s + Complex.I * ℓ * k = s + k * (2 * Real.pi * Complex.I * q) by
        rw [hℓdef]; push_cast; ring]
      exact meromorphicOrderAt_add_int_mul_period hper s k
    rw [hD, Function.locallyFinsuppWithin.negPart_apply,
      MeromorphicOn.divisor_apply hh (mem_univ _), hord]
    have hne : meromorphicOrderAt h s ≠ ⊤ := ne_top_of_lt hneg
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hn] at hneg ⊢
    have : n < 0 := by exact_mod_cast hneg
    simp only [WithTop.untop₀_coe]
    rw [negPart_eq_neg.2 this.le]; omega
  have hev := logCounting_progressions D hD0 S hℓ hdisj hpts
  obtain ⟨r, hr2, hr3, hr1⟩ := (hev.and (hT.and (eventually_ge_atTop 1))).exists
  have hlc : Function.locallyFinsuppWithin.logCounting D r ≤ charT h r := by
    unfold charT ValueDistribution.characteristic
    rw [ValueDistribution.logCounting_top]
    have := ValueDistribution.proximity_nonneg (f := h) (a := ⊤) r
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
    linarith
  have hS : (S.card : ℝ) = m := by exact_mod_cast hScard
  have h3 : (m : ℝ) / (e * ℓ) * r ≤ K * r := by rw [← hS]; linarith
  have h4 : (m : ℝ) / (e * ℓ) ≤ K := le_of_mul_le_mul_right h3 (by linarith)
  have he : 0 < e := Real.exp_pos 1
  rw [div_le_iff₀ (by positivity)] at h4
  have : e * ℓ * K < m := by
    have := Nat.le_ceil (e * ℓ * K)
    simp only [m]; push_cast; linarith
  linarith

/-! ### Auxiliary facts for the assembly -/

lemma poly_eval_bound (Q : ℂ[X]) : ∃ C ≥ 0, ∀ w : ℂ,
    ‖Q.eval w‖ ≤ C * max 1 ‖w‖ ^ Q.natDegree := by
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖, by positivity, fun w => ?_⟩
  rw [Q.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ‖w‖ ^ i ≤ (max 1 ‖w‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
    _ ≤ (max 1 ‖w‖) ^ Q.natDegree := pow_le_pow_right₀ (le_max_left _ _) hi'

lemma analyticAt_polyExp (Q : ℂ[X]) (q : ℂ) (t : ℂ) :
    AnalyticAt ℂ (fun t => Q.eval (Complex.exp (t / q))) t :=
  (AnalyticOnNhd.eval_polynomial Q _ (mem_univ _)).comp (f := fun t => Complex.exp (t / q))
    (by fun_prop)

lemma proximity_polyExp_le (Q : ℂ[X]) {q : ℝ} (hq : 0 < q) : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
    ValueDistribution.proximity (fun t => Q.eval (Complex.exp (t / q))) ⊤ r ≤
      C + Q.natDegree / q * r := by
  obtain ⟨C, hC0, hC⟩ := poly_eval_bound Q
  refine ⟨Real.posLog C, fun r hr => ?_⟩
  rw [ValueDistribution.proximity_top]
  apply Real.circleAverage_mono_on_of_le_circle
  · apply circleIntegrable_posLog_norm_meromorphicOn
    intro z _
    exact (analyticAt_polyExp Q q z).meromorphicAt
  · intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_nonneg hr] at hz
    have hexp : ‖Complex.exp (z / q)‖ ≤ Real.exp (r / q) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      have : (z / q).re = z.re / q := by
        rw [show (z / (q:ℂ)) = z * ((q⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_mul_ofReal]; ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hq.le
      rw [← hz]; exact Complex.re_le_norm z
    have hmax : max 1 ‖Complex.exp (z / q)‖ ≤ Real.exp (r / q) :=
      max_le (Real.one_le_exp (by positivity)) hexp
    calc Real.posLog ‖Q.eval (Complex.exp (z / q))‖
        ≤ Real.posLog (C * max 1 ‖Complex.exp (z / q)‖ ^ Q.natDegree) :=
          Real.posLog_le_posLog ((by norm_num : (-1 : ℝ) ≤ 0).trans (norm_nonneg _)) (hC _)
      _ ≤ Real.posLog C + Real.posLog (max 1 ‖Complex.exp (z / q)‖ ^ Q.natDegree) :=
          Real.posLog_mul
      _ ≤ Real.posLog C + Real.posLog (Real.exp (r / q) ^ Q.natDegree) := by
          gcongr
          exact (by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity)
      _ = Real.posLog C + Q.natDegree / q * r := by
          rw [← Real.exp_nat_mul, Real.posLog_apply (x := Real.exp _), Real.log_exp,
            max_eq_right (by positivity)]
          ring

/-- A continuous function agreeing off a discrete set with a function that is periodic off a
discrete set is periodic. -/
lemma periodic_of_codiscrete {E E0 : ℂ → ℂ} (hE : Continuous E) {ω : ℂ}
    (hEE : E =ᶠ[codiscrete ℂ] E0) (hper : ∀ᶠ t in codiscrete ℂ, E0 (t + ω) = E0 t) (t : ℂ) :
    E (t + ω) = E t := by
  have hloc : ∀ {p : ℂ → Prop}, (∀ᶠ z in codiscrete ℂ, p z) → ∀ x, ∀ᶠ z in 𝓝[≠] x, p z := by
    intro p hp x
    have := (mem_codiscrete.1 hp) x
    rw [disjoint_principal_right, compl_compl] at this
    exact this
  have htr : Tendsto (fun z => z + ω) (𝓝[≠] t) (𝓝[≠] (t + ω)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_id.add_const ω).tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have h1 : ∀ᶠ z in 𝓝[≠] t, E (z + ω) = E z := by
    filter_upwards [htr.eventually (hloc hEE (t + ω)), hloc hEE t, hloc hper t] with z h1 h2 h3
    rw [h1, h2, h3]
  have hc1 : Tendsto (fun z => E (z + ω)) (𝓝[≠] t) (𝓝 (E (t + ω))) :=
    ((hE.comp (continuous_id.add_const ω)).tendsto t).mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto E (𝓝[≠] t) (𝓝 (E t)) := (hE.tendsto t).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (hc1.congr' h1) hc2

/-- The preimage of a cofinite set under `t ↦ e^{t/q}` is codiscrete. -/
lemma exp_div_preimage_codiscrete {q : ℝ} (hq : 0 < q) {s : Set ℂ} (hs : s ∈ cofinite) :
    {t : ℂ | Complex.exp (t / q) ∈ s} ∈ codiscrete ℂ := by
  have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have han : AnalyticOnNhd ℂ (fun t : ℂ => Complex.exp (t / q)) univ := by
    intro x _; fun_prop
  have hs' : s ∈ codiscreteWithin ((fun t : ℂ => Complex.exp (t / q)) '' univ) :=
    Filter.codiscreteWithin.mono (subset_univ _) (codiscrete_le_cofinite hs)
  refine han.preimage_mem_codiscreteWithin (fun x _ hc => ?_) hs'
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hc
  have h0 := hc.deriv_eq
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (t / q)) (Complex.exp (x / q) * (1 / q)) x :=
    (Complex.hasDerivAt_exp (x / q)).comp x ((hasDerivAt_id x).div_const (q:ℂ))
  rw [hd.deriv, deriv_const] at h0
  exact mul_ne_zero (Complex.exp_ne_zero _) (one_div_ne_zero hq') h0

/-- Multiplying by `Q(e^{t/q})`, where `Q` has a root of multiplicity `k` at `e^{s/q}` for every
pole `s` of order `k` in the period strip, removes all poles of a periodic function. -/
lemma order_nonneg_of_poles {h : ℂ → ℂ} (hh : MeromorphicOn h univ) {q : ℝ} (hq : 0 < q)
    (hper : ∀ᶠ t in codiscrete ℂ, h (t + 2 * Real.pi * Complex.I * q) = h t) (Ps : Finset ℂ)
    (hPs : ∀ s, s ∈ Ps ↔ (0 ≤ s.im ∧ s.im < 2 * Real.pi * q ∧ meromorphicOrderAt h s < 0))
    (t : ℂ) :
    0 ≤ meromorphicOrderAt (fun t => (∏ s ∈ Ps, (X - C (Complex.exp (s / q))) ^
      (-(meromorphicOrderAt h s).untop₀).toNat).eval (Complex.exp (t / q)) * h t) t := by
  set F : ℂ → ℂ[X] := fun s =>
    (X - C (Complex.exp (s / q))) ^ (-(meromorphicOrderAt h s).untop₀).toNat with hF
  set Q := ∏ s ∈ Ps, F s
  have hQa : AnalyticAt ℂ (fun t => Q.eval (Complex.exp (t / q))) t := analyticAt_polyExp Q q t
  show 0 ≤ meromorphicOrderAt ((fun t => Q.eval (Complex.exp (t / q))) * h) t
  rw [meromorphicOrderAt_mul hQa.meromorphicAt (hh t (mem_univ t))]
  rcases le_or_gt 0 (meromorphicOrderAt h t) with hpos | hneg
  · exact add_nonneg (hQa.meromorphicOrderAt_nonneg) hpos
  set ℓ : ℝ := 2 * Real.pi * q with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  set n : ℤ := ⌊t.im / ℓ⌋ with hn
  set s : ℂ := t - n * (2 * Real.pi * Complex.I * q) with hs
  have hts : t = s + n * (2 * Real.pi * Complex.I * q) := by rw [hs]; ring
  have hord : meromorphicOrderAt h s = meromorphicOrderAt h t := by
    rw [hts, meromorphicOrderAt_add_int_mul_period hper]
  have hsim : s.im = t.im - n * ℓ := by
    rw [hs, hℓ]; simp
  have hsPs : s ∈ Ps := by
    rw [hPs]
    refine ⟨?_, ?_, hord ▸ hneg⟩
    · rw [hsim]
      have := Int.floor_le (t.im / ℓ)
      rw [le_div_iff₀ hℓ0] at this; linarith
    · rw [hsim]
      have := Int.lt_floor_add_one (t.im / ℓ)
      rw [div_lt_iff₀ hℓ0] at this; linarith
  have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hgs : Complex.exp (s / q) = Complex.exp (t / q) := by
    rw [hts, add_div, Complex.exp_add,
      show (n : ℂ) * (2 * Real.pi * Complex.I * q) / q = n * (2 * Real.pi * Complex.I) by
        field_simp]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set k := (-(meromorphicOrderAt h s).untop₀).toNat with hk
  set Q' := ∏ s ∈ Ps.erase s, F s
  have hQ : ∏ s ∈ Ps, F s = F s * Q' := (Finset.mul_prod_erase Ps F hsPs).symm
  set g : ℂ → ℂ := fun t => Complex.exp (t / q)
  have hga : AnalyticAt ℂ g t := by fun_prop
  have hsa : AnalyticAt ℂ (fun t' => g t' - g t) t := hga.sub analyticAt_const
  have hfun : (fun t' => eval (g t') (∏ s ∈ Ps, F s)) =
      (fun t' => g t' - g t) ^ k * (fun t' => eval (g t') Q') := by
    funext t'
    simp only [hQ, eval_mul, F, eval_pow, eval_sub, eval_X, eval_C, Pi.mul_apply, Pi.pow_apply]
    rw [hgs]
  have hd : deriv g t ≠ 0 := by
    have hd : HasDerivAt g (Complex.exp (t / q) * (1 / q)) t :=
      (Complex.hasDerivAt_exp (t / q)).comp t ((hasDerivAt_id t).div_const (q:ℂ))
    rw [hd.deriv]; exact mul_ne_zero (Complex.exp_ne_zero _) (one_div_ne_zero hq')
  have h1 : meromorphicOrderAt (fun t' => g t' - g t) t = 1 := by
    rw [hsa.meromorphicOrderAt_eq, hga.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd]
    rfl
  have hQ'a : AnalyticAt ℂ (fun t' => eval (g t') Q') t := analyticAt_polyExp Q' q t
  change 0 ≤ meromorphicOrderAt (fun t' => eval (g t') (∏ s ∈ Ps, F s)) t + _
  rw [hfun, meromorphicOrderAt_mul (hsa.meromorphicAt.pow k)
    hQ'a.meromorphicAt, meromorphicOrderAt_pow hsa.meromorphicAt, h1]
  have hne : meromorphicOrderAt h t ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  have hn0 : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
  have hkn : (k : ℤ) = -n := by
    rw [hk, hord, ← hn, WithTop.untop₀_coe]; omega
  have h2 := hQ'a.meromorphicOrderAt_nonneg
  rw [← hn]
  by_cases htop : meromorphicOrderAt (fun t' => eval (g t') Q') t = ⊤
  · rw [htop]; simp
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hm] at h2 ⊢
    have : (0:ℤ) ≤ m := by exact_mod_cast h2
    simp only [mul_one]
    have e1 : ((k : ℕ) : WithTop ℤ) = ((k : ℤ) : WithTop ℤ) := by simp
    rw [e1]
    exact_mod_cast (show (0:ℤ) ≤ k + m + n by omega)

/-! ### Lemma 8.15 -/

/-- **Lemma 8.15** (descent of periodic functions of linear growth).  Let `h` be meromorphic on
`ℂ`, `q > 0`, `h(t + 2πiq) = h(t)` and `T(r, h) = O(r)`.  Then `h(t) = R(e^{t/q})` for a rational
function `R` (as meromorphic functions, i.e. off a discrete set). -/
theorem periodic_linear_growth_descent {h : ℂ → ℂ} (hh : MeromorphicOn h univ) {q : ℝ}
    (hq : 0 < q) (hper : ∀ᶠ t in codiscrete ℂ, h (t + 2 * Real.pi * Complex.I * q) = h t)
    {K : ℝ} (hT : ∀ᶠ r in atTop, charT h r ≤ K * r) :
    ∃ R : RatFunc ℂ, ∀ᶠ t in codiscrete ℂ, h t = ratEval R (Complex.exp (t / q)) := by
  have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hfin := finite_poles_strip hh hq hper hT
  set Ps := hfin.toFinset with hPsdef
  have hPs : ∀ s, s ∈ Ps ↔
      (0 ≤ s.im ∧ s.im < 2 * Real.pi * q ∧ meromorphicOrderAt h s < 0) := fun s => by
    rw [hPsdef, Set.Finite.mem_toFinset]; rfl
  set Q : ℂ[X] := ∏ s ∈ Ps, (X - C (Complex.exp (s / q))) ^
    (-(meromorphicOrderAt h s).untop₀).toNat with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_sub_C_ne_zero _)
  set Qg : ℂ → ℂ := fun t => Q.eval (Complex.exp (t / q)) with hQg
  set E0 : ℂ → ℂ := fun t => Qg t * h t with hE0
  have hord : ∀ t, 0 ≤ meromorphicOrderAt E0 t := order_nonneg_of_poles hh hq hper Ps hPs
  have hQgm : Meromorphic Qg := fun t => (analyticAt_polyExp Q q t).meromorphicAt
  have hhm : Meromorphic h := fun t => hh t (mem_univ t)
  have hE0m : MeromorphicOn E0 univ := fun t _ => (hQgm t).mul (hhm t)
  set E := toMeromorphicNFOn E0 univ with hEdef
  have hEE0 : E0 =ᶠ[codiscrete ℂ] E := toMeromorphicNFOn_eqOn_codiscrete hE0m
  have hEan : ∀ x, AnalyticAt ℂ E x := fun x => by
    apply (meromorphicNFOn_toMeromorphicNFOn E0 univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hE0m.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))]
    exact hord x
  have hEd : Differentiable ℂ E := fun x => (hEan x).differentiableAt
  -- linear growth of `T(r, E)`
  obtain ⟨C₁, hC₁⟩ := proximity_polyExp_le Q hq
  have hTE : ∀ᶠ r in atTop, charT E r ≤ (|C₁| + Q.natDegree / q + |K|) * r := by
    filter_upwards [hT, eventually_ge_atTop 1] with r hr hr1
    have hlc : ValueDistribution.logCounting E ⊤ r = 0 := by
      rw [ValueDistribution.logCounting_top]
      have h0 : (MeromorphicOn.divisor E univ)⁻ = 0 :=
        negPart_eq_zero.2 (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun x _ => hEan x))
      rw [h0, map_zero]; rfl
    have hprox : ValueDistribution.proximity E ⊤ r = ValueDistribution.proximity E0 ⊤ r :=
      (ValueDistribution.proximity_congr_codiscrete hEE0 (by linarith)).symm
    have hmul := ValueDistribution.proximity_mul_top_le hQgm hhm r
    have hph : ValueDistribution.proximity h ⊤ r ≤ charT h r := by
      unfold charT ValueDistribution.characteristic
      have := ValueDistribution.logCounting_nonneg (f := h) (e := ⊤) hr1
      simp only [Pi.add_apply]; linarith
    have hQb := hC₁ r (by linarith)
    have hE0eq : E0 = Qg * h := rfl
    unfold charT ValueDistribution.characteristic
    simp only [Pi.add_apply]
    rw [hlc, hprox, hE0eq]
    simp only [Pi.add_apply] at hmul
    have h1 : C₁ ≤ |C₁| * r := (le_abs_self C₁).trans (le_mul_of_one_le_right (abs_nonneg _) hr1)
    have h2 : K * r ≤ |K| * r := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    nlinarith
  -- periodicity of `E`
  have hE0per : ∀ᶠ t in codiscrete ℂ,
      E0 (t + 2 * Real.pi * Complex.I * q) = E0 t := by
    filter_upwards [hper] with t ht
    simp only [hE0, hQg, ht]
    congr 2
    rw [add_div, Complex.exp_add,
      show (2 * Real.pi * Complex.I * q : ℂ) / q = 2 * Real.pi * Complex.I by field_simp,
      Complex.exp_two_pi_mul_I, mul_one]
  have hEper := periodic_of_codiscrete hEd.continuous hEE0.symm hE0per
  obtain ⟨A, B, hB, hb⟩ := entire_exp_bound hEd hTE
  obtain ⟨p, N, hp⟩ := periodic_entire_descent hEd hq hEper hB hb
  -- the rational function
  have hden : (X ^ N * Q : ℂ[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ0
  refine ⟨algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * Q), ?_⟩
  have hrat := exp_div_preimage_codiscrete hq (ratEval_div_eventually p (X ^ N * Q) hden)
  have hQne := exp_div_preimage_codiscrete hq
    ((Q.finite_setOf_isRoot hQ0).compl_mem_cofinite)
  filter_upwards [hEE0, hrat, hQne] with t h1 h2 h3
  simp only [mem_setOf_eq, mem_compl_iff, IsRoot.def] at h2 h3
  rw [h2, eval_mul, eval_pow, eval_X]
  have hE0t : E0 t = Qg t * h t := rfl
  rw [h1, hp t] at hE0t
  simp only [hQg] at hE0t
  have hw : Complex.exp (t / q) ^ N ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  field_simp
  rw [div_eq_iff hw] at hE0t
  linear_combination -hE0t

end ThreeIM
