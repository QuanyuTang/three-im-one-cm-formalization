module

public import RequestProject.ThreeIM.SmallEntire
public import RequestProject.ThreeIM.TwoCMCharacteristic
public import RequestProject.ThreeIM.Holomorphic

/-!
# The Mues estimate (Lemma 3.10, first part) and finite order (Lemmas 3.10 + 4.11)

For a normalized pair on `ℂ`, `T(r, Ψ) = O(L(r))` outside a set of finite linear measure.
The proof follows the paper: partial fractions express `h^j h'/P(h)` through the logarithmic
derivatives `h'/(h - a_i)`, the logarithmic derivative lemma (External theorem 2.3) bounds their
proximity functions, and `|f - g|² ≤ 2(|f|² + |g|²)` bounds `|Ψ|`.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

/-- Proximity of a constant multiple. -/
lemma proximity_const_mul_le (c : ℂ) {F : ℂ → ℂ} (hF : Meromorphic F) (r : ℝ) :
    proximity (fun z => c * F z) ⊤ r ≤ log⁺ ‖c‖ + proximity F ⊤ r := by
  have h := proximity_mul_top_le (f₁ := fun _ => c) (f₂ := F)
    (fun x => MeromorphicAt.const c x) hF r
  have hc : proximity (fun _ : ℂ => c) ⊤ r = log⁺ ‖c‖ := by
    simp
  simp only [Pi.add_apply, hc] at h
  exact h

/-- Proximity of a sum of three functions. -/
lemma proximity_add3_le {F₀ F₁ F₂ : ℂ → ℂ} (h₀ : Meromorphic F₀) (h₁ : Meromorphic F₁)
    (h₂ : Meromorphic F₂) (r : ℝ) :
    proximity (fun z => F₀ z + F₁ z + F₂ z) ⊤ r ≤
      proximity F₀ ⊤ r + proximity F₁ ⊤ r + proximity F₂ ⊤ r + 2 * log 2 := by
  have e1 := proximity_add_top_le (f₁ := F₀ + F₁) (f₂ := F₂) (h₀.add h₁) h₂ r
  have e2 := proximity_add_top_le (f₁ := F₀) (f₂ := F₁) h₀ h₁ r
  simp only [Pi.add_apply] at e1 e2
  show proximity (F₀ + F₁ + F₂) ⊤ r ≤ _
  linarith

/-- Partial fractions for `w^j / P(w)`, `j ≤ 2`. -/
lemma partial_fractions {a : Fin 3 → ℂ} (ha : Function.Injective a) {w : ℂ}
    (hw : ∀ i, w ≠ a i) {j : ℕ} (hj : j ≤ 2) :
    w ^ j / cubicP a w =
      a 0 ^ j / ((a 0 - a 1) * (a 0 - a 2)) * (1 / (w - a 0)) +
      a 1 ^ j / ((a 1 - a 0) * (a 1 - a 2)) * (1 / (w - a 1)) +
      a 2 ^ j / ((a 2 - a 0) * (a 2 - a 1)) * (1 / (w - a 2)) := by
  have hne : ∀ i k : Fin 3, i ≠ k → a i - a k ≠ 0 := fun i k hik h =>
    hik (ha (sub_eq_zero.1 h))
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h12 := hne 1 2 (by decide)
  have h10 := hne 1 0 (by decide)
  have h20 := hne 2 0 (by decide)
  have h21 := hne 2 1 (by decide)
  have hw0 : w - a 0 ≠ 0 := sub_ne_zero.2 (hw 0)
  have hw1 : w - a 1 ≠ 0 := sub_ne_zero.2 (hw 1)
  have hw2 : w - a 2 ≠ 0 := sub_ne_zero.2 (hw 2)
  unfold cubicP
  interval_cases j <;> (field_simp; ring)

/-- A nonconstant meromorphic function on `ℂ` takes a given finite value only on a discrete
set. -/
lemma IsNonconstMeroOn.eventually_ne {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) (c : ℂ) :
    ∀ᶠ z in codiscrete ℂ, h z ≠ c := by
  refine codiscrete_iff_nhdsNE.2 fun x => ?_
  have hm : MeromorphicAt (fun w => h w - c) x := (hh.1 x (mem_univ x)).sub (MeromorphicAt.const c x)
  rcases hm.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h0) (hh.2 x (mem_univ x) c)
  · filter_upwards [h0] with w hw
    exact sub_ne_zero.1 hw

/-- The logarithmic derivative `h'/(h - c)` is meromorphic. -/
lemma meromorphic_logDeriv_sub {h : ℂ → ℂ} (hm : Meromorphic h) (c : ℂ) :
    Meromorphic (fun z => deriv h z / (h z - c)) := fun x =>
  ((hm x).deriv).div ((hm x).sub (MeromorphicAt.const c x))

/-- Proximity of `h^j h'/P(h)` through the proximity functions of the logarithmic derivatives
`h'/(h - a_i)`. -/
lemma proximity_pow_mul_deriv_div_cubicP_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ)
    {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ r : ℝ, r ≠ 0 →
      proximity (fun z => h z ^ j * deriv h z / cubicP a (h z)) ⊤ r ≤
        K + ∑ i, proximity (fun z => deriv h z / (h z - a i)) ⊤ r := by
  have hm : Meromorphic h := fun x => hh.1 x (mem_univ x)
  set c : Fin 3 → ℂ := ![a 0 ^ j / ((a 0 - a 1) * (a 0 - a 2)),
    a 1 ^ j / ((a 1 - a 0) * (a 1 - a 2)), a 2 ^ j / ((a 2 - a 0) * (a 2 - a 1))]
  set D : Fin 3 → ℂ → ℂ := fun i z => deriv h z / (h z - a i)
  have hD : ∀ i, Meromorphic (D i) := fun i => meromorphic_logDeriv_sub hm (a i)
  refine ⟨2 * log 2 + ∑ i, log⁺ ‖c i‖, fun r hr => ?_⟩
  have heq : (fun z => h z ^ j * deriv h z / cubicP a (h z)) =ᶠ[codiscrete ℂ]
      fun z => c 0 * D 0 z + c 1 * D 1 z + c 2 * D 2 z := by
    filter_upwards [hh.eventually_ne (a 0), hh.eventually_ne (a 1), hh.eventually_ne (a 2)]
      with z h0 h1 h2
    have hw : ∀ i, h z ≠ a i := fun i => by fin_cases i <;> assumption
    have hpf := partial_fractions ha hw hj
    simp only [c, D, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_comm (h z ^ j), mul_div_assoc, hpf]
    ring
  rw [proximity_congr_codiscrete heq hr]
  have e := proximity_add3_le (F₀ := fun z => c 0 * D 0 z) (F₁ := fun z => c 1 * D 1 z)
    (F₂ := fun z => c 2 * D 2 z) (fun x => (MeromorphicAt.const _ x).mul (hD 0 x))
    (fun x => (MeromorphicAt.const _ x).mul (hD 1 x))
    (fun x => (MeromorphicAt.const _ x).mul (hD 2 x)) r
  have e0 := proximity_const_mul_le (c 0) (hD 0) r
  have e1 := proximity_const_mul_le (c 1) (hD 1) r
  have e2 := proximity_const_mul_le (c 2) (hD 2) r
  simp only [Fin.sum_univ_three]
  simp only [D] at e e0 e1 e2 ⊢
  linarith

/-- The pointwise Mues bound `log⁺|Ψ| ≤ 3 log 2 + log⁺|f² f'/P(f) · g'/P(g)| +
log⁺|f'/P(f) · g² g'/P(g)|`, from `|f - g|² ≤ 2(|f|² + |g|²)`. -/
lemma posLog_auxPsi_le (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (z : ℂ) :
    log⁺ ‖auxPsi a f g z‖ ≤ 3 * log 2 +
      log⁺ ‖f z ^ 2 * deriv f z / cubicP a (f z) * (deriv g z / cubicP a (g z))‖ +
      log⁺ ‖deriv f z / cubicP a (f z) * (g z ^ 2 * deriv g z / cubicP a (g z))‖ := by
  set A := deriv f z / cubicP a (f z)
  set B := deriv g z / cubicP a (g z)
  have hΨ : auxPsi a f g z = (f z - g z) ^ 2 * A * B := by
    simp only [auxPsi, auxU, auxV, A, B]; ring
  have h1 : f z ^ 2 * deriv f z / cubicP a (f z) * B = f z ^ 2 * A * B := by
    simp only [A]; ring
  have h2 : A * (g z ^ 2 * deriv g z / cubicP a (g z)) = g z ^ 2 * A * B := by
    simp only [B]; ring
  rw [hΨ, h1, h2]
  have hsq : ‖f z - g z‖ ^ 2 ≤ 2 * (‖f z‖ ^ 2 + ‖g z‖ ^ 2) := by
    have := norm_sub_le (f z) (g z)
    nlinarith [sq_nonneg (‖f z‖ - ‖g z‖), norm_nonneg (f z - g z)]
  have hle : ‖(f z - g z) ^ 2 * A * B‖ ≤
      2 * ‖f z ^ 2 * A * B‖ + 2 * ‖g z ^ 2 * A * B‖ := by
    simp only [norm_mul, norm_pow]
    have hAB : 0 ≤ ‖A‖ * ‖B‖ := by positivity
    nlinarith
  have hlog2 : log⁺ (2 : ℝ) = log 2 := by
    rw [Real.posLog_apply, max_eq_right (Real.log_nonneg (by norm_num))]
  calc log⁺ ‖(f z - g z) ^ 2 * A * B‖
      ≤ log⁺ (2 * ‖f z ^ 2 * A * B‖ + 2 * ‖g z ^ 2 * A * B‖) :=
        Real.posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) hle
    _ ≤ log 2 + log⁺ (2 * ‖f z ^ 2 * A * B‖) + log⁺ (2 * ‖g z ^ 2 * A * B‖) := Real.posLog_add
    _ ≤ log 2 + (log⁺ 2 + log⁺ ‖f z ^ 2 * A * B‖) + (log⁺ 2 + log⁺ ‖g z ^ 2 * A * B‖) := by
        gcongr <;> exact Real.posLog_mul
    _ = _ := by rw [hlog2]; ring

/-- The proximity function of `Ψ` is bounded by those of the logarithmic derivatives
`f'/(f - a_i)` and `g'/(g - a_i)`. -/
lemma proximity_auxPsi_le {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    ∃ K : ℝ, ∀ r : ℝ, r ≠ 0 → proximity (auxPsi a f g) ⊤ r ≤
      K + 2 * ∑ i, (proximity (fun z => deriv f z / (f z - a i)) ⊤ r +
        proximity (fun z => deriv g z / (g z - a i)) ⊤ r) := by
  have hf : Meromorphic f := fun x => hp.nonconst_f.1 x (mem_univ x)
  have hg : Meromorphic g := fun x => hp.nonconst_g.1 x (mem_univ x)
  obtain ⟨Kf2, hKf2⟩ := proximity_pow_mul_deriv_div_cubicP_le hp.nonconst_f hp.injective
    (j := 2) le_rfl
  obtain ⟨Kf0, hKf0⟩ := proximity_pow_mul_deriv_div_cubicP_le hp.nonconst_f hp.injective
    (j := 0) (by norm_num)
  obtain ⟨Kg2, hKg2⟩ := proximity_pow_mul_deriv_div_cubicP_le hp.nonconst_g hp.injective
    (j := 2) le_rfl
  obtain ⟨Kg0, hKg0⟩ := proximity_pow_mul_deriv_div_cubicP_le hp.nonconst_g hp.injective
    (j := 0) (by norm_num)
  refine ⟨3 * log 2 + Kf2 + Kf0 + Kg2 + Kg0, fun r hr => ?_⟩
  -- the four auxiliary functions
  set F2 : ℂ → ℂ := fun z => f z ^ 2 * deriv f z / cubicP a (f z)
  set F0 : ℂ → ℂ := fun z => f z ^ 0 * deriv f z / cubicP a (f z)
  set G2 : ℂ → ℂ := fun z => g z ^ 2 * deriv g z / cubicP a (g z)
  set G0 : ℂ → ℂ := fun z => g z ^ 0 * deriv g z / cubicP a (g z)
  have hF2 : Meromorphic F2 := fun x => by
    have := hf x; have := (hf x).deriv; simp only [F2, cubicP]; fun_prop
  have hF0 : Meromorphic F0 := fun x => by
    have := hf x; have := (hf x).deriv; simp only [F0, cubicP]; fun_prop
  have hG2 : Meromorphic G2 := fun x => by
    have := hg x; have := (hg x).deriv; simp only [G2, cubicP]; fun_prop
  have hG0 : Meromorphic G0 := fun x => by
    have := hg x; have := (hg x).deriv; simp only [G0, cubicP]; fun_prop
  have hΨ : Meromorphic (auxPsi a f g) := fun x => by
    have := hf x; have := (hf x).deriv; have := hg x; have := (hg x).deriv
    unfold auxPsi auxU auxV cubicP; fun_prop
  -- pointwise bound, integrated
  have hpt : ∀ z, log⁺ ‖auxPsi a f g z‖ ≤ 3 * log 2 + log⁺ ‖(F2 * G0) z‖ + log⁺ ‖(F0 * G2) z‖ := by
    intro z
    have := posLog_auxPsi_le a f g z
    simpa [F2, F0, G2, G0] using this
  have hint1 := circleIntegrable_posLog_norm_meromorphicOn (c := 0) (R := r)
    (fun x _ => (hF2.mul hG0) x)
  have hint2 := circleIntegrable_posLog_norm_meromorphicOn (c := 0) (R := r)
    (fun x _ => (hF0.mul hG2) x)
  have hmono : proximity (auxPsi a f g) ⊤ r ≤
      3 * log 2 + proximity (F2 * G0) ⊤ r + proximity (F0 * G2) ⊤ r := by
    rw [proximity_top, proximity_top, proximity_top]
    calc circleAverage (fun z => log⁺ ‖auxPsi a f g z‖) 0 r
        ≤ circleAverage (fun z => 3 * log 2 + log⁺ ‖(F2 * G0) z‖ + log⁺ ‖(F0 * G2) z‖) 0 r := by
          apply circleAverage_mono
          · exact circleIntegrable_posLog_norm_meromorphicOn (fun x _ => hΨ x)
          · exact ((circleIntegrable_const _ _ _).add hint1).add hint2
          · exact fun z _ => hpt z
      _ = 3 * log 2 + circleAverage (fun z => log⁺ ‖(F2 * G0) z‖) 0 r +
            circleAverage (fun z => log⁺ ‖(F0 * G2) z‖) 0 r := by
          show circleAverage ((fun _ => 3 * log 2) + (fun z => log⁺ ‖(F2 * G0) z‖) +
            (fun z => log⁺ ‖(F0 * G2) z‖)) 0 r = _
          rw [circleAverage_add ((circleIntegrable_const _ _ _).add hint1) hint2,
            circleAverage_add (circleIntegrable_const _ _ _) hint1, circleAverage_const]
  have m1 := proximity_mul_top_le hF2 hG0 r
  have m2 := proximity_mul_top_le hF0 hG2 r
  simp only [Pi.add_apply] at m1 m2
  have e2 := hKf2 r hr
  have e0 := hKf0 r hr
  have g2 := hKg2 r hr
  have g0 := hKg0 r hr
  simp only [Finset.sum_add_distrib, mul_add]
  linarith

lemma charT_nonneg {h : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) : 0 ≤ charT h r :=
  characteristic_nonneg hr

lemma one_le_pairL {f g : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) : 1 ≤ pairL f g r := by
  have hT : 0 ≤ pairT f g r := le_max_of_le_left (charT_nonneg hr)
  have h := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ Real.exp 1 + r * pairT f g r by nlinarith)
  rwa [Real.log_exp] at h

lemma log_charT_le_pairL_left {f g : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) :
    Real.log (Real.exp 1 + r * charT f r) ≤ pairL f g r :=
  Real.log_le_log (by nlinarith [charT_nonneg (h := f) hr, Real.exp_pos 1])
    (by have : charT f r ≤ pairT f g r := le_max_left _ _
        nlinarith)

lemma log_charT_le_pairL_right {f g : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) :
    Real.log (Real.exp 1 + r * charT g r) ≤ pairL f g r :=
  Real.log_le_log (by nlinarith [charT_nonneg (h := g) hr, Real.exp_pos 1])
    (by have : charT g r ≤ pairT f g r := le_max_right _ _
        nlinarith)

/-- **Lemma 3.10** (Mues estimate, first part): for a normalized pair on `ℂ`,
`m(r, Ψ) = O(L(r))` outside a set of finite linear measure.  (Since `Ψ` is entire, this is
`T(r, Ψ) = O(L(r))`.) -/
theorem mues_estimate {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => proximity (auxPsi a f g) ⊤ r ≤ C * pairL f g r := by
  obtain ⟨K, hK⟩ := proximity_auxPsi_le hp
  choose Cf Ef hEfm hEfv rf hrf using fun i => log_derivative_estimate hp.nonconst_f (a i)
  choose Cg Eg hEgm hEgv rg hrg using fun i => log_derivative_estimate hp.nonconst_g (a i)
  set S : ℝ := ∑ i, (|Cf i| + |Cg i|)
  refine ⟨|K| + 2 * S, ⋃ i, (Ef i ∪ Eg i), MeasurableSet.iUnion fun i => (hEfm i).union (hEgm i),
    ?_, 1 + ∑ i, (|rf i| + |rg i|), fun r hr hrE => ?_⟩
  · refine lt_of_le_of_lt (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    exact lt_of_le_of_lt (MeasureTheory.measure_union_le _ _)
      (ENNReal.add_lt_top.2 ⟨hEfv i, hEgv i⟩)
  have hsum_nonneg : ∀ i, 0 ≤ |rf i| + |rg i| := fun i => by positivity
  have hri : ∀ i, |rf i| + |rg i| ≤ ∑ i, (|rf i| + |rg i|) := fun i =>
    Finset.single_le_sum (fun i _ => hsum_nonneg i) (Finset.mem_univ i)
  have hr1 : 1 ≤ r := le_trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => hsum_nonneg i)) hr
  have hL := one_le_pairL (f := f) (g := g) hr1
  have hrE' : ∀ i, r ∉ Ef i ∧ r ∉ Eg i := fun i => by
    simp only [mem_iUnion, mem_union, not_exists, not_or] at hrE
    exact hrE i
  have hbf : ∀ i, proximity (fun z => deriv f z / (f z - a i)) ⊤ r ≤ |Cf i| * pairL f g r := by
    intro i
    have h1 := hrf i r (by linarith [le_abs_self (rf i), abs_nonneg (rg i), hri i])
      (hrE' i).1
    have h2 := log_charT_le_pairL_left (f := f) (g := g) hr1
    have h3 : 0 ≤ Real.log (Real.exp 1 + r * charT f r) :=
      Real.log_nonneg (by nlinarith [charT_nonneg (h := f) hr1, Real.add_one_le_exp 1])
    calc _ ≤ Cf i * Real.log (Real.exp 1 + r * charT f r) := h1
      _ ≤ |Cf i| * Real.log (Real.exp 1 + r * charT f r) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |Cf i| * pairL f g r := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hbg : ∀ i, proximity (fun z => deriv g z / (g z - a i)) ⊤ r ≤ |Cg i| * pairL f g r := by
    intro i
    have h1 := hrg i r (by linarith [le_abs_self (rg i), abs_nonneg (rf i), hri i])
      (hrE' i).2
    have h2 := log_charT_le_pairL_right (f := f) (g := g) hr1
    have h3 : 0 ≤ Real.log (Real.exp 1 + r * charT g r) :=
      Real.log_nonneg (by nlinarith [charT_nonneg (h := g) hr1, Real.add_one_le_exp 1])
    calc _ ≤ Cg i * Real.log (Real.exp 1 + r * charT g r) := h1
      _ ≤ |Cg i| * Real.log (Real.exp 1 + r * charT g r) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |Cg i| * pairL f g r := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hmain := hK r (by linarith)
  have hsumle : ∑ i, (proximity (fun z => deriv f z / (f z - a i)) ⊤ r +
      proximity (fun z => deriv g z / (g z - a i)) ⊤ r) ≤ S * pairL f g r := by
    simp only [S, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => by rw [add_mul]; exact add_le_add (hbf i) (hbg i)
  nlinarith [le_abs_self K, abs_nonneg K]

/-- For a pair of finite order, `L(r) = O(log r)`. -/
lemma pairL_le_log_of_finite_order {f g : ℂ → ℂ} (hf : ¬ InfiniteOrder f)
    (hg : ¬ InfiniteOrder g) : ∃ M : ℝ, 0 ≤ M ∧ ∃ r₂ : ℝ, ∀ r ≥ r₂,
      pairL f g r ≤ M * Real.log r := by
  simp only [InfiniteOrder, not_forall, Filter.not_frequently, not_le] at hf hg
  obtain ⟨Kf, hKf⟩ := hf
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨rf, hrf⟩ := Filter.eventually_atTop.1 hKf
  obtain ⟨rg, hrg⟩ := Filter.eventually_atTop.1 hKg
  set K := max (max Kf Kg) 0
  refine ⟨K + 2, by positivity, max (max rf rg) 3, fun r hr => ?_⟩
  have hr3 : 3 ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := by linarith
  have hT : pairT f g r ≤ r ^ K := by
    apply max_le
    · exact (hrf r (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr)).le.trans
        (Real.rpow_le_rpow_of_exponent_le hr1 (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact (hrg r (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr)).le.trans
        (Real.rpow_le_rpow_of_exponent_le hr1 (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hT0 : 0 ≤ pairT f g r := le_max_of_le_left (charT_nonneg hr1)
  have hrK : r ≤ r ^ (K + 1) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [le_max_right (max Kf Kg) 0])
  have hpow : r * r ^ K = r ^ (K + 1) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
  have he : Real.exp 1 ≤ r := by
    have := Real.exp_one_lt_d9; linarith
  have h1 : Real.exp 1 + r * pairT f g r ≤ 2 * r ^ (K + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℝ) ≤ r)]
  have hrpos : 0 < r := by linarith
  calc pairL f g r = Real.log (Real.exp 1 + r * pairT f g r) := rfl
    _ ≤ Real.log (2 * r ^ (K + 1)) :=
        Real.log_le_log (by nlinarith [Real.exp_pos 1]) h1
    _ = Real.log 2 + (K + 1) * Real.log r := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hrpos]
    _ ≤ (K + 2) * Real.log r := by
        have : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) (by linarith)
        nlinarith

/-- **Lemmas 3.10 and 4.11** (Mues estimate and small entire functions).  If both members of a
normalized pair on `ℂ` have finite order, then the Mues function `Ψ` is a polynomial (off a
discrete set). -/
theorem psi_polynomial_of_finite_order' {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (h : NormalizedPair univ f g a) (hf : ¬ InfiniteOrder f) (hg : ¬ InfiniteOrder g) :
    ∃ p : Polynomial ℂ, ∀ᶠ z in codiscrete ℂ, auxPsi a f g z = p.eval z := by
  set Ψ := auxPsi a f g
  have hfm : Meromorphic f := fun x => h.nonconst_f.1 x (mem_univ x)
  have hgm : Meromorphic g := fun x => h.nonconst_g.1 x (mem_univ x)
  have hΨm : MeromorphicOn Ψ univ := fun x _ => by
    have := hfm x; have := (hfm x).deriv; have := hgm x; have := (hgm x).deriv
    simp only [Ψ]; unfold auxPsi auxU auxV cubicP; fun_prop
  set H := toMeromorphicNFOn Ψ univ
  have hΨH : Ψ =ᶠ[codiscrete ℂ] H := toMeromorphicNFOn_eqOn_codiscrete hΨm
  have hHa : ∀ x, AnalyticAt ℂ H x := by
    intro x
    apply (meromorphicNFOn_toMeromorphicNFOn Ψ univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hΨm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))]
    exact (h.order_aux (mem_univ x)).2.2.1
  have hH : Differentiable ℂ H := fun x => (hHa x).differentiableAt
  -- `T(r, H) = m(r, Ψ)`
  have hlc : logCounting H ⊤ = 0 := by
    have := logCounting_add_analyticOn (f := (0 : ℂ → ℂ)) (g := H) (fun x => analyticAt_const.meromorphicAt)
      (fun x _ => (hHa x).analyticWithinAt)
    rw [zero_add] at this
    rw [this, logCounting_const_zero]
  have hTH : ∀ r : ℝ, r ≠ 0 → charT H r = proximity Ψ ⊤ r := by
    intro r hr
    simp only [charT, characteristic, Pi.add_apply, hlc, Pi.zero_apply, add_zero]
    exact proximity_congr_codiscrete hΨH.symm hr
  obtain ⟨C, E, hEm, hEv, r₀, hr₀⟩ := mues_estimate h
  obtain ⟨M, hM, r₂, hr₂⟩ := pairL_le_log_of_finite_order hf hg
  obtain ⟨p, hp⟩ := polynomial_of_small_charT hH (C := |C| * M)
    ⟨E, hEm, hEv, max (max r₀ r₂) 1, fun r hr hrE => by
      have hr0 : r₀ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
      have hr2 : r₂ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
      have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
      show charT H r ≤ |C| * M * Real.log r
      rw [hTH r (by linarith)]
      have hL := one_le_pairL (f := f) (g := g) hr1
      calc proximity Ψ ⊤ r ≤ C * pairL f g r := hr₀ r hr0 hrE
        _ ≤ |C| * pairL f g r := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
        _ ≤ |C| * (M * Real.log r) := mul_le_mul_of_nonneg_left (hr₂ r hr2) (abs_nonneg C)
        _ = |C| * M * Real.log r := by ring⟩
  exact ⟨p, hΨH.mono fun z hz => by rw [hz, hp z]⟩

end ThreeIM
