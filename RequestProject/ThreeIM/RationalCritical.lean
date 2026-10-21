module

public import RequestProject.ThreeIM.RationalZeroFiber
public import RequestProject.ThreeIM.Scalar

/-!
# Location of the critical points (Lemma 9.26, first step of the sign argument)

Under the endpoint normalization `U = κ t^{-1}`, `V = κ t` (endpoint pole order `ρ = 1`) and the
conclusions of Lemma 9.2, every critical point of `R` in `ℂ*` lies in a finite common fiber of
type `(m, 1)` with `m > 1`, so `t² = 1/m`; every critical point of `S` lies in a fiber of type
`(1, n)` with `n > 1`, so `t² = n`.  In particular `R'` does not vanish at the real points with
`|t| ≥ 1` and `S'` does not vanish at the real points with `0 < |t| ≤ 1`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {κ : ℂ}

/-- At an analytic common `c`-point, `F' = 0` iff the multiplicity is at least two. -/
lemma deriv_eq_zero_iff_two_le_mult {F : ℂ → ℂ} {t₀ c : ℂ} (hFm : MeromorphicAt F t₀)
    (hFa : AnalyticAt ℂ F t₀) (hm : 0 < mult F (c : Sphere) t₀) :
    deriv F t₀ = 0 ↔ 2 ≤ mult F (c : Sphere) t₀ := by
  rw [analyticAt_eq_zero_iff_order_pos hFa.deriv,
    order_deriv_of_order_sub hFm hm (order_sub_eq_mult hm),
    show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
  omega

/-- The Mues function `Ψ = U V = κ² t^{-2}` has order zero at every `t₀ ≠ 0`. -/
lemma order_auxPsi_eq_zero_of_monomials (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    meromorphicOrderAt (auxPsi a f g) t₀ = 0 := by
  have heq : auxPsi a f g =ᶠ[𝓝[≠] t₀] fun t => κ ^ 2 / t ^ 2 := by
    filter_upwards [eventually_nhdsNE_of_cofinite hU t₀, eventually_nhdsNE_of_cofinite hV t₀,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t h1 h2 ht
    have e1 : auxU a f g t = κ * t ^ (-1 : ℤ) / t := by rw [← h1]; field_simp
    have e2 : auxV a f g t = κ * t ^ (1 : ℤ) / t := by rw [← h2]; field_simp
    simp only [auxPsi]
    rw [e1, e2, zpow_neg_one, zpow_one]
    field_simp
  have hA : AnalyticAt ℂ (fun t : ℂ => κ ^ 2 / t ^ 2) t₀ :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 ht₀)
  rw [meromorphicOrderAt_congr heq]
  have hne : ¬ (fun t : ℂ => κ ^ 2 / t ^ 2) t₀ = 0 := by simp [ht₀, hκ]
  rw [analyticAt_eq_zero_iff_order_pos hA, not_lt] at hne
  exact le_antisymm hne hA.meromorphicOrderAt_nonneg

/-- The ratio identity `n = t₀² m` at a finite common point, from `U = κ t^{-1}`, `V = κ t`. -/
lemma mult_ratio_of_monomials (hpair : NormalizedPair {0}ᶜ f g a) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {j : Fin 3} (hm : 0 < mult f (a j : Sphere) t₀) :
    (mult g (a j : Sphere) t₀ : ℂ) = t₀ ^ 2 * mult f (a j : Sphere) t₀ := by
  have h := rational_aux_ratio hpair hκ hU hV ht₀ hm
  rw [zpow_neg_one, zpow_one] at h
  have := congrArg (· * (t₀ / κ)) h
  field_simp at this
  linear_combination this

/-- **Critical points of `R`** (Lemma 9.26).  Under the conclusions of Lemma 9.2 and the
endpoint normalization `U = κ t^{-1}`, `V = κ t`, every critical point `t₀ ∈ ℂ*` of `f` at which
`f` is analytic lies in a common fiber of type `(m, 1)` with `m ≥ 2`; hence `t₀² m = 1`. -/
theorem critical_point_R (hpair : NormalizedPair {0}ᶜ f g a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a f g t) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hfa : AnalyticAt ℂ f t₀) (hcrit : deriv f t₀ = 0) :
    ∃ m : ℕ, 2 ≤ m ∧ t₀ ^ 2 * m = 1 := by
  have hfm := hpair.nonconst_f.1 t₀ ht₀
  have hgm := hpair.nonconst_g.1 t₀ ht₀
  by_cases hj : ∃ j, 0 < mult f (a j : Sphere) t₀
  · obtain ⟨j, hm⟩ := hj
    have hm2 := (deriv_eq_zero_iff_two_le_mult hfm hfa hm).1 hcrit
    have hmin := hpair.min_mult_eq_one_of_psi ht₀ hm
      (order_auxPsi_eq_zero_of_monomials hκ hU hV ht₀)
    have hn1 : mult g (a j : Sphere) t₀ = 1 := by
      rcases min_eq_iff.1 hmin with h | h
      · omega
      · exact h.1
    refine ⟨mult f (a j : Sphere) t₀, hm2, ?_⟩
    have := mult_ratio_of_monomials hpair hκ hU hV ht₀ hm
    rw [hn1] at this
    push_cast at this
    exact this.symm
  · push_neg at hj
    have hgen := (hco t₀ ht₀).generic (fun j => Nat.eq_zero_of_le_zero (hj j))
      (mult_top_eq_zero_of_analyticAt hfa)
    have := (analyticAt_eq_zero_iff_order_pos hfa.deriv).1 hcrit
    rw [hgen.2.1] at this
    exact absurd this (lt_irrefl 0)

/-- **Critical points of `S`** (Lemma 9.26).  Under the same hypotheses, every critical point
`t₀ ∈ ℂ*` of `g` at which `g` is analytic lies in a common fiber of type `(1, n)` with `n ≥ 2`;
hence `t₀² = n`. -/
theorem critical_point_S (hpair : NormalizedPair {0}ᶜ f g a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a f g t) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hga : AnalyticAt ℂ g t₀) (hcrit : deriv g t₀ = 0) :
    ∃ n : ℕ, 2 ≤ n ∧ t₀ ^ 2 = n := by
  have hfm := hpair.nonconst_f.1 t₀ ht₀
  have hgm := hpair.nonconst_g.1 t₀ ht₀
  by_cases hj : ∃ j, 0 < mult g (a j : Sphere) t₀
  · obtain ⟨j, hn⟩ := hj
    have hm : 0 < mult f (a j : Sphere) t₀ := (hpair.im j t₀ ht₀).2 hn
    have hn2 := (deriv_eq_zero_iff_two_le_mult hgm hga hn).1 hcrit
    have hmin := hpair.min_mult_eq_one_of_psi ht₀ hm
      (order_auxPsi_eq_zero_of_monomials hκ hU hV ht₀)
    have hm1 : mult f (a j : Sphere) t₀ = 1 := by
      rcases min_eq_iff.1 hmin with h | h
      · exact h.1
      · omega
    refine ⟨mult g (a j : Sphere) t₀, hn2, ?_⟩
    have := mult_ratio_of_monomials hpair hκ hU hV ht₀ hm
    rw [hm1] at this
    push_cast at this
    rw [this, mul_one]
  · push_neg at hj
    have hf0 : ∀ j, mult f (a j : Sphere) t₀ = 0 := fun j => by
      by_contra h
      have := (hpair.im j t₀ ht₀).1 (Nat.pos_of_ne_zero h)
      exact absurd (hj j) (not_le.2 this)
    have hftop : mult f ⊤ t₀ = 0 := by
      rw [hpair.cm_top t₀ ht₀]; exact mult_top_eq_zero_of_analyticAt hga
    have hgen := (hco t₀ ht₀).generic hf0 hftop
    have := (analyticAt_eq_zero_iff_order_pos hga.deriv).1 hcrit
    rw [hgen.2.2] at this
    exact absurd this (lt_irrefl 0)

/-- Consequence for real points: `f'` does not vanish at real `t` with `|t| ≥ 1` where `f` is
analytic. -/
theorem deriv_ne_zero_R (hpair : NormalizedPair {0}ᶜ f g a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a f g t) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t : ℝ} (ht : 1 ≤ |t|)
    (hfa : AnalyticAt ℂ f t) : deriv f t ≠ 0 := by
  intro hcrit
  have ht0 : (t : ℂ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; simp at ht; linarith
    exact_mod_cast this
  obtain ⟨m, hm, hsq⟩ := critical_point_R hpair hco hκ hU hV ht0 hfa hcrit
  have hr : t ^ 2 * (m : ℝ) = 1 := by exact_mod_cast hsq
  have h1 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Consequence for real points: `g'` does not vanish at real `t` with `0 < |t| ≤ 1` where `g` is
analytic. -/
theorem deriv_ne_zero_S (hpair : NormalizedPair {0}ᶜ f g a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a f g t) (hκ : κ ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = κ * t ^ (1 : ℤ)) {t : ℝ} (ht0 : t ≠ 0)
    (ht : |t| ≤ 1) (hga : AnalyticAt ℂ g t) : deriv g t ≠ 0 := by
  intro hcrit
  have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  obtain ⟨n, hn, hsq⟩ := critical_point_S hpair hco hκ hU hV ht0' hga hcrit
  have hr : t ^ 2 = (n : ℝ) := by exact_mod_cast hsq
  have h1 : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end ThreeIM
