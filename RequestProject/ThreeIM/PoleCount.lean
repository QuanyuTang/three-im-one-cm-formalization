module

public import RequestProject.ThreeIM.ThetaProximity
public import RequestProject.ThreeIM.Defects
public import RequestProject.ThreeIM.SharedValueCounting

/-!
# The common pole bound (Lemma 4.5)

For a normalized pair on `ℂ` that does not share all four values CM, the integrated counting
function of the common poles satisfies `N_∞(r) ≤ (4/5) T(r) + O(L(r))` outside a set of finite
linear measure.

Since the value `∞` is shared CM, the counting function `N(r, f)` of the poles of `f` (with
multiplicity) is the common pole count `N_∞(r)`; we state the bound for `N(r, f)`.

The proof follows the paper: with `W_a = θ_a² - c_a² Ψ`,

* `N_∞ ≤ N(r, 1/W_a) + N(r, 1/Ψ)`, since `W_a` vanishes at common simple poles and `Ψ` has a
  zero of order `≥ 2k - 2 ≥ k` at a common pole of order `k ≥ 2`;
* `T(W_a) ≤ 2 T(θ_a) + O(L)` and `m(θ_a) = O(L)`;
* `∑_a N(r, θ_a) ≤ N(r, 1/(f - g)) + 3 N(r, 1/Ψ)`, since the poles of `θ_a` are simple and lie
  over `a`-defects (zeros of `f - g`) or zeros of `Ψ`;
* `N(r, 1/(f - g)) ≤ T(r, f - g) + O(1) ≤ T(r, f) + T(r, g) - N_∞ + O(1)`.

Together: `3 N_∞ ≤ 2 (2T - N_∞) + O(L)`.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory Function

namespace ThreeIM

/-! ### General Nevanlinna facts -/

/-- `T(r, c) = log⁺ |c|` for a constant. -/
lemma charT_const (c : ℂ) (r : ℝ) : charT (fun _ => c) r = log⁺ ‖c‖ := by
  simp [charT, characteristic]

section Pair

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

lemma meromorphic_thetaAux (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (thetaAux a j f g) := fun x => by
  have hf := hp.nonconst_f.meromorphic x
  have hg := hp.nonconst_g.meromorphic x
  have hf' := hf.deriv; have hg' := hg.deriv
  have hf'' := hf'.deriv; have hg'' := hg'.deriv
  unfold thetaAux ThetaFun
  fun_prop

lemma meromorphic_WAux (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (WAux a j f g) := fun x => by
  have h1 := meromorphic_thetaAux hp j x
  have h2 := hp.meromorphic_auxPsi x
  unfold WAux
  fun_prop

/-- `T(W_a) ≤ 2 T(θ_a) + T(Ψ) + O(1)`. -/
lemma charT_WAux_le (hp : NormalizedPair univ f g a) (j : Fin 3) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      charT (WAux a j f g) r ≤ 2 * charT (thetaAux a j f g) r + charT (auxPsi a f g) r + K := by
  have hθ := meromorphic_thetaAux hp j
  have hΨ := hp.meromorphic_auxPsi
  set c : ℂ := -(cAux a j ^ 2)
  refine ⟨log 2 + log⁺ ‖c‖, fun r hr => ?_⟩
  have hθ2 : Meromorphic (thetaAux a j f g ^ 2) := fun x => (hθ x).pow 2
  have hcΨ : Meromorphic ((fun _ => c) * auxPsi a f g) := fun x =>
    (MeromorphicAt.const c x).mul (hΨ x)
  have hW : WAux a j f g = thetaAux a j f g ^ 2 + (fun _ => c) * auxPsi a f g := by
    ext z; simp [WAux, c]; ring
  have e1 := characteristic_add_top_le hθ2 hcΨ hr
  have e2 : characteristic (thetaAux a j f g ^ 2) ⊤ r = 2 * charT (thetaAux a j f g) r := by
    rw [characteristic_pow_top hθ]; simp [charT]
  have hΨ0 : 0 ≤ charT (auxPsi a f g) r := charT_nonneg hr
  have e3 : characteristic ((fun _ => c) * auxPsi a f g) ⊤ r ≤
      log⁺ ‖c‖ + charT (auxPsi a f g) r := by
    by_cases hc : c = 0
    · have : (fun _ => c) * auxPsi a f g = fun _ => (0 : ℂ) := by ext z; simp [hc]
      rw [this]
      have := charT_const 0 r
      simp only [norm_zero, Real.posLog_zero] at this
      unfold charT at this
      rw [this]; have := Real.posLog_nonneg (x := ‖c‖); linarith
    · have h := characteristic_mul_top_le hr (fun x => MeromorphicAt.const c x)
        (fun z => by rw [order_const_eq c hc]; exact WithTop.zero_ne_top) hΨ
        (fun z => (hp.order_aux (mem_univ z)).2.2.2)
      simp only [Pi.add_apply] at h
      have := charT_const c r
      unfold charT at this ⊢
      rw [this] at h
      exact h
  rw [hW]
  unfold charT at e2 e3 hΨ0 ⊢
  linarith

/-- `W_a` is not identically zero near any point (it has a double pole at an `a`-defect). -/
lemma order_WAux_ne_top (hp : NormalizedPair univ f g a)
    (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) (j : Fin 3) (z : ℂ) :
    meromorphicOrderAt (WAux a j f g) z ≠ ⊤ := by
  obtain ⟨zd, hd⟩ := hp.exists_defect hnot j
  have hθm := meromorphic_thetaAux hp j
  have hΨm := hp.meromorphic_auxPsi
  have hθ := (thetaAux_order hp j zd).2.2 hd
  have h2 : meromorphicOrderAt (thetaAux a j f g ^ 2) zd = 2 * (-1 : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow (hθm zd), hθ]; rfl
  have h3 : 0 ≤ meromorphicOrderAt ((fun _ => -(cAux a j ^ 2)) * auxPsi a f g) zd := by
    rw [meromorphicOrderAt_mul (MeromorphicAt.const _ _) (hΨm zd)]
    exact add_nonneg (order_const_nonneg _) (hp.order_aux (mem_univ zd)).2.2.1
  have hW : WAux a j f g = thetaAux a j f g ^ 2 + (fun _ => -(cAux a j ^ 2)) * auxPsi a f g := by
    ext w; simp [WAux]; ring
  have hlt : meromorphicOrderAt (thetaAux a j f g ^ 2) zd <
      meromorphicOrderAt ((fun _ => -(cAux a j ^ 2)) * auxPsi a f g) zd := by
    rw [h2]; exact lt_of_lt_of_le (by decide) h3
  have hWd : meromorphicOrderAt (WAux a j f g) zd ≠ ⊤ := by
    rw [hW, meromorphicOrderAt_add_eq_left_of_lt ((MeromorphicAt.const _ _).mul (hΨm zd)) hlt, h2]
    decide
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => meromorphic_WAux hp j y) isPreconnected_univ (mem_univ zd) (mem_univ z) hWd

/-- Pointwise: `(poles of f) ≤ (zeros of W_a) + (zeros of Ψ)`. -/
lemma negPart_divisor_le (hp : NormalizedPair univ f g a)
    (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) (j : Fin 3) :
    (MeromorphicOn.divisor f univ)⁻ ≤
      (MeromorphicOn.divisor (WAux a j f g) univ)⁺ +
        (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  have hfm := hp.nonconst_f.meromorphic
  have hWm := meromorphic_WAux hp j
  have hΨm := hp.meromorphic_auxPsi
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [MeromorphicOn.divisor_apply (fun x _ => hfm x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hWm x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hΨm x) (mem_univ z)]
  have hW0 : 0 ≤ (meromorphicOrderAt (WAux a j f g) z).untop₀⁺ := posPart_nonneg _
  have hΨ0 : 0 ≤ (meromorphicOrderAt (auxPsi a f g) z).untop₀⁺ := posPart_nonneg _
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z))
  rw [← hn, WithTop.untop₀_coe]
  rcases le_or_gt 0 n with h0 | h0
  · rw [negPart_eq_zero.2 h0]; positivity
  rcases eq_or_lt_of_le (show n ≤ -1 by omega) with h1 | h1
  · -- simple pole
    subst h1
    have hlim := tendsto_WAux_simple_pole hp j (z₀ := z) (by rw [← hn]; rfl)
    have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos (hWm z)).1 hlim
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (order_WAux_ne_top hp hnot j z)
    rw [← hm] at hpos ⊢
    have : (0 : ℤ) < m := by exact_mod_cast hpos
    rw [WithTop.untop₀_coe, posPart_eq_self.2 this.le]
    simp only [negPart_def]
    omega
  · -- pole of order `k ≥ 2`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hΨ := order_auxPsi_at_pole hp (z₀ := z) (k := k) (by omega) (by rw [← hn, hk]; rfl)
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
    rw [← hm] at hΨ ⊢
    have : 2 * (k : ℤ) - 2 ≤ m := by exact_mod_cast hΨ
    rw [WithTop.untop₀_coe, posPart_eq_self.2 (show (0 : ℤ) ≤ m by omega)]
    simp only [negPart_def]
    omega

/-- Two defects at the same point are over the same value. -/
lemma defect_unique (hp : NormalizedPair univ f g a) {j k : Fin 3} {z : ℂ}
    (hj : IsDefect f g (a j : Sphere) z) (hk : IsDefect f g (a k : Sphere) z) : j = k := by
  by_contra hjk
  have hpos : 0 < meromorphicOrderAt (fun w => f w - a j) z := by
    rw [order_sub_eq_mult hj.1]; exact_mod_cast hj.1
  have h0 := order_sub_const_eq_zero_of_pos (hp.nonconst_f.meromorphic z)
    (hp.injective.ne hjk) hpos
  have := hk.1
  simp only [mult_coe, h0] at this
  simp at this

/-- Integer facts about the poles of `θ_a` at a point. -/
lemma negPart_theta_facts (hp : NormalizedPair univ f g a) (j : Fin 3) (z : ℂ) :
    (meromorphicOrderAt (thetaAux a j f g) z).untop₀⁻ ≤ 1 ∧
      (0 < (meromorphicOrderAt (thetaAux a j f g) z).untop₀⁻ →
        IsDefect f g (a j : Sphere) z ∨ 0 < meromorphicOrderAt (auxPsi a f g) z) := by
  obtain ⟨h1, h2, -⟩ := thetaAux_order hp j z
  induction h : meromorphicOrderAt (thetaAux a j f g) z using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [h] at h1 h2
    have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 h1
    simp only [WithTop.untop₀_coe, negPart_def]
    refine ⟨by omega, fun hpos => h2 ?_⟩
    have : n < 0 := by omega
    exact_mod_cast this

/-- Pointwise: `∑_a (poles of θ_a) ≤ (zeros of f - g) + 3 (zeros of Ψ)`. -/
lemma sum_negPart_divisor_theta_le (hp : NormalizedPair univ f g a) :
    ∑ j : Fin 3, (MeromorphicOn.divisor (thetaAux a j f g) univ)⁻ ≤
      (MeromorphicOn.divisor (fun z => f z - g z) univ)⁺ +
        3 • (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  have hsm : MeromorphicOn (fun z => f z - g z) univ := fun x _ => (hfm x).sub (hgm x)
  have hθm := meromorphic_thetaAux hp
  have hΨm := hp.meromorphic_auxPsi
  intro z
  simp only [Fin.sum_univ_three, Function.locallyFinsuppWithin.coe_add,
    Function.locallyFinsuppWithin.coe_nsmul, Pi.add_apply, Pi.smul_apply,
    Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.posPart_apply]
  rw [MeromorphicOn.divisor_apply (fun x _ => hθm 0 x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hθm 1 x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hθm 2 x) (mem_univ z),
    MeromorphicOn.divisor_apply hsm (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hΨm x) (mem_univ z)]
  obtain ⟨a0, b0⟩ := negPart_theta_facts hp 0 z
  obtain ⟨a1, b1⟩ := negPart_theta_facts hp 1 z
  obtain ⟨a2, b2⟩ := negPart_theta_facts hp 2 z
  have n0 := negPart_nonneg (meromorphicOrderAt (thetaAux a 0 f g) z).untop₀
  have n1 := negPart_nonneg (meromorphicOrderAt (thetaAux a 1 f g) z).untop₀
  have n2 := negPart_nonneg (meromorphicOrderAt (thetaAux a 2 f g) z).untop₀
  have hS0 := posPart_nonneg (meromorphicOrderAt (fun z => f z - g z) z).untop₀
  have hP0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  rw [nsmul_eq_mul]
  by_cases hΨ : 0 < meromorphicOrderAt (auxPsi a f g) z
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
    rw [← hm] at hΨ ⊢
    have : (0 : ℤ) < m := by exact_mod_cast hΨ
    rw [WithTop.untop₀_coe, posPart_eq_self.2 this.le]
    push_cast
    omega
  · have hS : ∀ k : Fin 3, IsDefect f g (a k : Sphere) z →
        1 ≤ (meromorphicOrderAt (fun z => f z - g z) z).untop₀⁺ := by
      intro k hk
      have hle := min_mult_le_order_sub (hfm z) (hgm z) hk.1 hk.2.1
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z (mem_univ z))
      rw [← hm] at hle ⊢
      have h1 : ((min (mult f (a k : Sphere) z) (mult g (a k : Sphere) z) : ℕ) : ℤ) ≤ m := by
        exact_mod_cast hle
      have h2 : 1 ≤ min (mult f (a k : Sphere) z) (mult g (a k : Sphere) z) :=
        le_min hk.1 hk.2.1
      rw [WithTop.untop₀_coe, posPart_eq_self.2 (by omega)]
      omega
    have d0 : 0 < (meromorphicOrderAt (thetaAux a 0 f g) z).untop₀⁻ → IsDefect f g (a 0 : Sphere) z :=
      fun h => (b0 h).resolve_right hΨ
    have d1 : 0 < (meromorphicOrderAt (thetaAux a 1 f g) z).untop₀⁻ → IsDefect f g (a 1 : Sphere) z :=
      fun h => (b1 h).resolve_right hΨ
    have d2 : 0 < (meromorphicOrderAt (thetaAux a 2 f g) z).untop₀⁻ → IsDefect f g (a 2 : Sphere) z :=
      fun h => (b2 h).resolve_right hΨ
    have u01 : ¬ (0 < (meromorphicOrderAt (thetaAux a 0 f g) z).untop₀⁻ ∧
        0 < (meromorphicOrderAt (thetaAux a 1 f g) z).untop₀⁻) :=
      fun ⟨h, h'⟩ => absurd (defect_unique hp (d0 h) (d1 h')) (by decide)
    have u02 : ¬ (0 < (meromorphicOrderAt (thetaAux a 0 f g) z).untop₀⁻ ∧
        0 < (meromorphicOrderAt (thetaAux a 2 f g) z).untop₀⁻) :=
      fun ⟨h, h'⟩ => absurd (defect_unique hp (d0 h) (d2 h')) (by decide)
    have u12 : ¬ (0 < (meromorphicOrderAt (thetaAux a 1 f g) z).untop₀⁻ ∧
        0 < (meromorphicOrderAt (thetaAux a 2 f g) z).untop₀⁻) :=
      fun ⟨h, h'⟩ => absurd (defect_unique hp (d1 h) (d2 h')) (by decide)
    have s0 := fun h => hS 0 (d0 h)
    have s1 := fun h => hS 1 (d1 h)
    have s2 := fun h => hS 2 (d2 h)
    omega

/-- `N_∞ ≤ N(r, 1/W_a) + N(r, 1/Ψ)`. -/
lemma logCounting_top_le_W (hp : NormalizedPair univ f g a)
    (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) (j : Fin 3) {r : ℝ} (hr : 1 ≤ r) :
    logCounting f ⊤ r ≤ logCounting (WAux a j f g) 0 r + logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_le hp hnot j) hr
  rw [map_add] at h
  rw [logCounting_top, logCounting_zero, logCounting_zero]
  exact h

/-- `∑_a N(r, θ_a) ≤ N(r, 1/(f - g)) + 3 N(r, 1/Ψ)`. -/
lemma sum_logCounting_theta_le (hp : NormalizedPair univ f g a) {r : ℝ} (hr : 1 ≤ r) :
    ∑ j : Fin 3, logCounting (thetaAux a j f g) ⊤ r ≤
      logCounting (fun z => f z - g z) 0 r + 3 * logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (sum_negPart_divisor_theta_le hp) hr
  rw [map_sum, map_add, map_nsmul] at h
  simp only [Finset.sum_apply, Pi.add_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
  simp only [logCounting_top, logCounting_zero]
  exact h

end Pair

/-- **Lemma 4.5** (the common pole bound).  If a normalized pair on `ℂ` does not share all four
values CM, then `N_∞(r) ≤ (4/5) T(r) + O(L(r))` outside a set of finite linear measure. -/
theorem pole_count {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ValueDistribution.logCounting f ⊤ r ≤ 4 / 5 * pairT f g r + C * pairL f g r := by
  obtain ⟨K₁, hK₁⟩ := logCounting_zero_le_charT (F := fun z => f z - g z)
    (fun x => (hp.nonconst_f.meromorphic x).sub (hp.nonconst_g.meromorphic x))
  choose K₂ hK₂ using fun j => logCounting_zero_le_charT (meromorphic_WAux hp j)
  choose K₃ hK₃ using fun j => charT_WAux_le hp j
  obtain ⟨CΨ, hCΨ⟩ := charT_auxPsi_le hp
  obtain ⟨CΨ₀, hCΨ₀⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨Cθ, hCθ⟩ := proximity_thetaAux_le hp
  set K : ℝ := |K₁| + ∑ j, (|K₂ j| + |K₃ j|) + log 2 with hK
  refine ⟨(2 * (2 * |Cθ| + |CΨ| + 4 * |CΨ₀|) * 3 + 3 * K) / 5,
    ((hCΨ.and hCΨ₀).and hCθ).mono fun r hr ⟨⟨h1, h2⟩, h3⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hl2 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ j, (|K₂ j| + |K₃ j|) := Finset.sum_nonneg fun j _ => by positivity
    rw [hK]; positivity
  -- the bound through each `W_a`
  have hW : ∀ j, logCounting f ⊤ r ≤ 2 * proximity (thetaAux a j f g) ⊤ r +
      2 * logCounting (thetaAux a j f g) ⊤ r + charT (auxPsi a f g) r + |K₂ j| + |K₃ j| +
      logCounting (auxPsi a f g) 0 r := by
    intro j
    have e1 := logCounting_top_le_W hp hnot j hr
    have e2 := hK₂ j r hr
    have e3 := hK₃ j r hr
    have e4 : charT (thetaAux a j f g) r =
        proximity (thetaAux a j f g) ⊤ r + logCounting (thetaAux a j f g) ⊤ r := rfl
    linarith [le_abs_self (K₂ j), le_abs_self (K₃ j)]
  -- summing over the three values
  have hsum := sum_logCounting_theta_le hp hr
  have hfg := hK₁ r hr
  have hsub := charT_sub_le hp hr
  have hTf : charT f r = proximity f ⊤ r + logCounting f ⊤ r := rfl
  have hTg : charT g r = proximity g ⊤ r + logCounting g ⊤ r := rfl
  have hNg : logCounting g ⊤ r = logCounting f ⊤ r := by rw [logCounting_top_eq hp]
  have hpf : charT f r ≤ pairT f g r := le_max_left _ _
  have hpg : charT g r ≤ pairT f g r := le_max_right _ _
  have hW0 := hW 0
  have hW1 := hW 1
  have hW2 := hW 2
  have h30 := h3 0
  have h31 := h3 1
  have h32 := h3 2
  simp only [Fin.sum_univ_three] at hsum
  have hK₂s : |K₂ 0| + |K₃ 0| + (|K₂ 1| + |K₃ 1|) + (|K₂ 2| + |K₃ 2|) ≤ K := by
    have : ∑ j, (|K₂ j| + |K₃ j|) = |K₂ 0| + |K₃ 0| + (|K₂ 1| + |K₃ 1|) + (|K₂ 2| + |K₃ 2|) := by
      simp [Fin.sum_univ_three]
    rw [hK, ← this]; linarith [abs_nonneg K₁]
  have hK₁K : K₁ + log 2 ≤ K := by
    have : 0 ≤ ∑ j, (|K₂ j| + |K₃ j|) := Finset.sum_nonneg fun j _ => by positivity
    rw [hK]; linarith [le_abs_self K₁]
  have k1 : Cθ * pairL f g r ≤ |Cθ| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k2 : CΨ * pairL f g r ≤ |CΨ| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k3 : CΨ₀ * pairL f g r ≤ |CΨ₀| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k4 : K ≤ K * pairL f g r := le_mul_of_one_le_right hK0 hL
  have k5 : 0 ≤ |Cθ| * pairL f g r := mul_nonneg (abs_nonneg _) (by linarith)
  have k6 : 0 ≤ |CΨ| * pairL f g r := mul_nonneg (abs_nonneg _) (by linarith)
  have k7 : 0 ≤ |CΨ₀| * pairL f g r := mul_nonneg (abs_nonneg _) (by linarith)
  have : (2 * (2 * |Cθ| + |CΨ| + 4 * |CΨ₀|) * 3 + 3 * K) / 5 * pairL f g r =
      (6 * (2 * (|Cθ| * pairL f g r) + |CΨ| * pairL f g r + 4 * (|CΨ₀| * pairL f g r)) +
        3 * (K * pairL f g r)) / 5 := by ring
  rw [this]
  linarith

end ThreeIM
