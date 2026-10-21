module

public import RequestProject.ThreeIM.ThetaLocal
public import RequestProject.ThreeIM.TwoCMCharacteristic

/-!
# Proximity of the logarithmic auxiliary functions (Lemma 4.4, global part)

`m(r, θ_a) = O(L(r))` outside a set of finite linear measure, together with some general
facts used along the way (`T(r, h) ≥ 1` for large `r`, hence `log r ≤ L(r)`).
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory Function

namespace ThreeIM

lemma OutsideFiniteMeasure.of_ge {P : ℝ → Prop} {r₀ : ℝ} (h : ∀ r ≥ r₀, P r) :
    OutsideFiniteMeasure P :=
  ⟨∅, MeasurableSet.empty, by simp, r₀, fun r hr _ => h r hr⟩

/-- Elementary: if `S ≤ A T + B log (e + r T)` then `log (e + r S) ≤ log (e + r T) + O(1) + log r`. -/
lemma log_le_of_le_mul_add_log {r T S A B : ℝ} (hr : 1 ≤ r) (hT : 0 ≤ T) (hS0 : 0 ≤ S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : S ≤ A * T + B * log (exp 1 + r * T)) :
    log (exp 1 + r * S) ≤ log (exp 1 + r * T) + log (1 + A + B) + log r := by
  have he : 0 < exp 1 := exp_pos 1
  have hr0 : 0 < r := by linarith
  have hx : 0 < exp 1 + r * T := by positivity
  have hl : log (exp 1 + r * T) ≤ exp 1 + r * T := by
    linarith [Real.log_le_sub_one_of_pos hx]
  have hBl : B * log (exp 1 + r * T) ≤ B * (exp 1 + r * T) := mul_le_mul_of_nonneg_left hl hB
  have h1 : r * S ≤ r * (A * T + B * (exp 1 + r * T)) :=
    mul_le_mul_of_nonneg_left (by linarith) hr0.le
  have key : exp 1 + r * S ≤ (1 + A + B) * r * (exp 1 + r * T) := by
    have hr1 : 0 ≤ r - 1 := by linarith
    nlinarith [mul_nonneg hr1 he.le, mul_nonneg (mul_nonneg hr1 hA) hT,
      mul_nonneg (mul_nonneg hr1 hA) he.le, mul_nonneg (mul_nonneg hr0.le hr1) hT,
      mul_nonneg (mul_nonneg hr0.le hA) hT, mul_nonneg hr0.le hT,
      mul_nonneg (mul_nonneg hr0.le hr1) (mul_nonneg hA hT)]
  calc log (exp 1 + r * S) ≤ log ((1 + A + B) * r * (exp 1 + r * T)) :=
        Real.log_le_log (by positivity) key
    _ = _ := by
        rw [Real.log_mul (by positivity) hx.ne', Real.log_mul (by positivity) hr0.ne']; ring

/-- `m(r, h''/h') = O(log (e + r T(r, h)) + log r)` outside a set of finite linear measure. -/
lemma proximity_logDeriv_deriv_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => deriv (deriv h) z / deriv h z) ⊤ r ≤
        C * (log (exp 1 + r * charT h r) + log r) := by
  have hm := hh.meromorphic
  have hdm : Meromorphic (deriv h) := fun x => (hm x).deriv
  by_cases hd : IsNonconstMeroOn (deriv h) univ
  · obtain ⟨C₁, hC₁⟩ := log_derivative_estimate hd 0
    obtain ⟨C₂, hC₂⟩ := charT_deriv_le_log_error hh
    refine ⟨|C₁| * (1 + log (3 + |C₂|)), (hC₁.and hC₂).mono fun r hr ⟨h1, h2⟩ => ?_⟩
    simp only [sub_zero] at h1
    have hT := charT_nonneg (h := h) hr
    have hT' := charT_nonneg (h := deriv h) hr
    have he : 0 < exp 1 := exp_pos 1
    have hL1 : 1 ≤ log (exp 1 + r * charT h r) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; nlinarith
    have hL0 : 0 ≤ log (exp 1 + r * charT (deriv h) r) :=
      Real.log_nonneg (by nlinarith [Real.add_one_le_exp 1])
    have hlr : 0 ≤ log r := Real.log_nonneg hr
    have hS : charT (deriv h) r ≤ 2 * charT h r + |C₂| * log (exp 1 + r * charT h r) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self C₂) (by linarith : 0 ≤ log (exp 1 + r * charT h r))
      linarith
    have hlog := log_le_of_le_mul_add_log hr hT hT' (by norm_num) (abs_nonneg C₂) hS
    have h3 : (1 : ℝ) + 2 + |C₂| = 3 + |C₂| := by ring
    rw [h3] at hlog
    have hl3 : 0 ≤ log (3 + |C₂|) := Real.log_nonneg (by linarith [abs_nonneg C₂])
    have k1 : C₁ * log (exp 1 + r * charT (deriv h) r) ≤
        |C₁| * log (exp 1 + r * charT (deriv h) r) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hL0
    have k2 : |C₁| * log (exp 1 + r * charT (deriv h) r) ≤
        |C₁| * (log (exp 1 + r * charT h r) + log (3 + |C₂|) + log r) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    have k3 : log (3 + |C₂|) ≤ log (3 + |C₂|) * (log (exp 1 + r * charT h r) + log r) := by
      nlinarith
    have k4 := mul_le_mul_of_nonneg_left k3 (abs_nonneg C₁)
    nlinarith
  · -- `h'` is constant
    have hd' : ∃ z₀ c, meromorphicOrderAt (fun w => deriv h w - c) z₀ = ⊤ := by
      by_contra hne
      push_neg at hne
      exact hd ⟨fun x _ => hdm x, fun z _ c => hne z c⟩
    obtain ⟨z₀, c, hz₀⟩ := hd'
    have hall : ∀ x, meromorphicOrderAt (fun w => deriv h w - c) x = ⊤ := by
      intro x
      by_contra hx
      have := MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        (f := fun w => deriv h w - c) (U := univ)
        (fun y _ => (hdm y).sub (MeromorphicAt.const c y)) isPreconnected_univ
        (mem_univ x) (mem_univ z₀) hx
      exact this hz₀
    have hev : (fun z => deriv (deriv h) z / deriv h z) =ᶠ[codiscrete ℂ] fun _ => 0 := by
      refine codiscrete_iff_nhdsNE.2 fun x => ?_
      have h1 := meromorphicOrderAt_eq_top_iff.1 (hall x)
      have h2 : ∀ᶠ w in 𝓝[≠] x, deriv h w = c := h1.mono fun w hw => sub_eq_zero.1 hw
      filter_upwards [deriv_eventually_zero_of_eventually_const h2] with w hw
      simp [hw]
    refine ⟨0, OutsideFiniteMeasure.of_ge (r₀ := 1) fun r hr => ?_⟩
    rw [proximity_congr_codiscrete hev (by linarith)]
    simp

/-- `m(r, Θ_a(h)) = O(log (e + r T(r, h)) + log r)` outside a set of finite linear measure. -/
lemma proximity_ThetaFun_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) (a : Fin 3 → ℂ)
    (j : Fin 3) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (ThetaFun a j h) ⊤ r ≤ C * (log (exp 1 + r * charT h r) + log r) := by
  have hm := hh.meromorphic
  have hdm : Meromorphic (deriv h) := fun x => (hm x).deriv
  have hddm : Meromorphic (deriv (deriv h)) := fun x => (hdm x).deriv
  obtain ⟨C₀, hC₀⟩ := proximity_logDeriv_deriv_le hh
  obtain ⟨C₁, hC₁⟩ := log_derivative_estimate hh (a j)
  obtain ⟨C₂, hC₂⟩ := log_derivative_estimate hh (a (j + 1))
  obtain ⟨C₃, hC₃⟩ := log_derivative_estimate hh (a (j + 2))
  set T₀ : ℂ → ℂ := fun z => deriv (deriv h) z / deriv h z
  set T₁ : ℂ → ℂ := fun z => deriv h z / (h z - a j)
  set T₂ : ℂ → ℂ := fun z => deriv h z / (h z - a (j + 1))
  set T₃ : ℂ → ℂ := fun z => deriv h z / (h z - a (j + 2))
  have m₀ : Meromorphic T₀ := fun x => (hddm x).div (hdm x)
  have m₁ : Meromorphic T₁ := fun x => (hdm x).div ((hm x).sub (MeromorphicAt.const _ x))
  have m₂ : Meromorphic T₂ := fun x => (hdm x).div ((hm x).sub (MeromorphicAt.const _ x))
  have m₃ : Meromorphic T₃ := fun x => (hdm x).div ((hm x).sub (MeromorphicAt.const _ x))
  have m₁' : Meromorphic (fun z => (2 : ℂ) * T₁ z) := fun x => (MeromorphicAt.const _ x).mul (m₁ x)
  have m₂' : Meromorphic (fun z => (-1 : ℂ) * T₂ z) :=
    fun x => (MeromorphicAt.const _ x).mul (m₂ x)
  have m₃' : Meromorphic (fun z => (-1 : ℂ) * T₃ z) :=
    fun x => (MeromorphicAt.const _ x).mul (m₃ x)
  have hΘ : ThetaFun a j h = fun z => (T₀ z + (2 : ℂ) * T₁ z) + (-1 : ℂ) * T₂ z +
      (-1 : ℂ) * T₃ z := by
    ext z; simp only [ThetaFun, T₀, T₁, T₂, T₃]; ring
  refine ⟨|C₀| + |C₁| + |C₂| + |C₃| + 4,
    (((hC₀.and hC₁).and hC₂).and hC₃).mono fun r hr ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ?_⟩
  have e1 := proximity_add3_le (m₀.add m₁') m₂' m₃' r
  have e2 := proximity_add_top_le m₀ m₁' r
  simp only [Pi.add_apply] at e2
  have e3 := proximity_const_mul_le 2 m₁ r
  have e4 := proximity_const_mul_le (-1) m₂ r
  have e5 := proximity_const_mul_le (-1) m₃ r
  simp only [norm_neg, norm_one, Real.posLog_one, zero_add] at e4 e5
  have h2n : log⁺ ‖(2 : ℂ)‖ = log 2 := by
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num, Real.posLog_apply, max_eq_right]
    exact Real.log_nonneg (by norm_num)
  rw [h2n] at e3
  have hT := charT_nonneg (h := h) hr
  have he : 0 < exp 1 := exp_pos 1
  have hL1 : 1 ≤ log (exp 1 + r * charT h r) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; nlinarith
  have hlr : 0 ≤ log r := Real.log_nonneg hr
  set X := log (exp 1 + r * charT h r) + log r with hX
  have hX1 : 1 ≤ X := by linarith
  have hl2 : log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have b : ∀ C : ℝ, C * log (exp 1 + r * charT h r) ≤ |C| * X := fun C => by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith : 0 ≤ log (exp 1 + r * charT h r))
    have := mul_le_mul_of_nonneg_left (by linarith : log (exp 1 + r * charT h r) ≤ X) (abs_nonneg C)
    linarith
  have b0 : C₀ * X ≤ |C₀| * X := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have b1 := b C₁
  have b2 := b C₂
  have b3 := b C₃
  have hp0 : proximity (fun z => (T₀ z + (2 : ℂ) * T₁ z) + (-1 : ℂ) * T₂ z + (-1 : ℂ) * T₃ z) ⊤ r
      = proximity (fun z => (T₀ + fun z => (2 : ℂ) * T₁ z) z + (-1 : ℂ) * T₂ z +
          (-1 : ℂ) * T₃ z) ⊤ r := rfl
  rw [hΘ, hp0]
  have : (|C₀| + |C₁| + |C₂| + |C₃| + 4) * X = |C₀| * X + |C₁| * X + |C₂| * X + |C₃| * X + 4 * X := by
    ring
  rw [this]
  simp only [T₁, T₂, T₃] at h1 h2 h3 e3 e4 e5
  linarith

section Pair

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

/-- For a pair on `ℂ`, `log r ≤ L(r)` for large `r` (since `T(r, f) ≥ log r - O(1)`). -/
lemma log_le_pairL (hp : NormalizedPair univ f g a) :
    ∃ r₀ : ℝ, ∀ r ≥ r₀, log r ≤ pairL f g r := by
  obtain ⟨r₀, hr₀⟩ := one_le_charT_eventually hp.nonconst_f
  refine ⟨max r₀ 1, fun r hr => ?_⟩
  have h1 := hr₀ r (le_trans (le_max_left _ _) hr)
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hT : charT f r ≤ pairT f g r := le_max_left _ _
  unfold pairL
  apply Real.log_le_log (by linarith)
  nlinarith [Real.exp_pos 1]


/-- `m(r, θ_a) = O(L)` (Lemma 4.4), for all three values at once. -/
lemma proximity_thetaAux_le (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ∀ j, proximity (thetaAux a j f g) ⊤ r ≤ C * pairL f g r := by
  have key : ∀ j, ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (thetaAux a j f g) ⊤ r ≤ C * pairL f g r := by
    intro j
    obtain ⟨Cf, hCf⟩ := proximity_ThetaFun_le hp.nonconst_f a j
    obtain ⟨Cg, hCg⟩ := proximity_ThetaFun_le hp.nonconst_g a j
    obtain ⟨r₀, hr₀⟩ := log_le_pairL hp
    have hfm := hp.nonconst_f.meromorphic
    have hgm := hp.nonconst_g.meromorphic
    have mf : Meromorphic (ThetaFun a j f) := fun x => by
      have hf' := (hfm x).deriv; have hf'' := hf'.deriv
      have := hfm x
      unfold ThetaFun; fun_prop
    have mg : Meromorphic (ThetaFun a j g) := fun x => by
      have hg' := (hgm x).deriv; have hg'' := hg'.deriv
      have := hgm x
      unfold ThetaFun; fun_prop
    have mg' : Meromorphic (fun z => (-1 : ℂ) * ThetaFun a j g z) :=
      fun x => (MeromorphicAt.const _ x).mul (mg x)
    refine ⟨2 * |Cf| + 2 * |Cg| + 1,
      ((hCf.and hCg).and (OutsideFiniteMeasure.of_ge (r₀ := r₀) fun r hr => hr₀ r hr)).mono
        fun r hr ⟨⟨h1, h2⟩, h3⟩ => ?_⟩
    have hθ : thetaAux a j f g = ThetaFun a j f + fun z => (-1 : ℂ) * ThetaFun a j g z := by
      ext z; simp [thetaAux]; ring
    have e1 := proximity_add_top_le mf mg' r
    have e2 := proximity_const_mul_le (-1) mg r
    simp only [norm_neg, norm_one, Real.posLog_one, zero_add] at e2
    have hL := one_le_pairL (f := f) (g := g) hr
    have hlf := log_charT_le_pairL_left (f := f) (g := g) hr
    have hlg := log_charT_le_pairL_right (f := f) (g := g) hr
    have hTf := charT_nonneg (h := f) hr
    have hTg := charT_nonneg (h := g) hr
    have he : 0 < exp 1 := exp_pos 1
    have hlr : 0 ≤ log r := Real.log_nonneg hr
    have hLf : 0 ≤ log (exp 1 + r * charT f r) := Real.log_nonneg (by nlinarith [Real.add_one_le_exp 1])
    have hLg : 0 ≤ log (exp 1 + r * charT g r) := Real.log_nonneg (by nlinarith [Real.add_one_le_exp 1])
    have k1 : Cf * (log (exp 1 + r * charT f r) + log r) ≤ |Cf| * (2 * pairL f g r) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self Cf) (by linarith :
        0 ≤ log (exp 1 + r * charT f r) + log r)
      have := mul_le_mul_of_nonneg_left (by linarith :
        log (exp 1 + r * charT f r) + log r ≤ 2 * pairL f g r) (abs_nonneg Cf)
      linarith
    have k2 : Cg * (log (exp 1 + r * charT g r) + log r) ≤ |Cg| * (2 * pairL f g r) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self Cg) (by linarith :
        0 ≤ log (exp 1 + r * charT g r) + log r)
      have := mul_le_mul_of_nonneg_left (by linarith :
        log (exp 1 + r * charT g r) + log r ≤ 2 * pairL f g r) (abs_nonneg Cg)
      linarith
    have hl2 : log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    rw [hθ]
    simp only [Pi.add_apply] at e1
    nlinarith
  choose C hC using key
  refine ⟨|C 0| + |C 1| + |C 2|, ((hC 0).and ((hC 1).and (hC 2))).mono
    fun r hr ⟨h0, h1, h2⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have b : ∀ i, C i * pairL f g r ≤ |C i| * pairL f g r := fun i =>
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have n : ∀ i, 0 ≤ |C i| * pairL f g r := fun i => mul_nonneg (abs_nonneg _) (by linarith)
  intro j
  fin_cases j
  · simp only [Fin.zero_eta]; nlinarith [b 0, n 1, n 2]
  · simp only [Fin.mk_one]; nlinarith [b 1, n 0, n 2]
  · show proximity (thetaAux a 2 f g) ⊤ r ≤ _; nlinarith [b 2, n 0, n 1]

end Pair

end ThreeIM
