module

public import RequestProject.ThreeIM.Reduction
public import RequestProject.ThreeIM.Covariance
public import RequestProject.ThreeIM.Defects
public import RequestProject.ThreeIM.Growth
public import RequestProject.ThreeIM.Mues
public import RequestProject.ThreeIM.ConstantRatio

/-!
# The periodic infinite-order reduction (Lemma 4.12)

Lemma 4.12 is derived here from

* Lemma 4.8 (first part, proved in `Growth.lean`): a value taken along a vertical progression
  forces `T(r) ≥ c r`;
* Lemma 4.10 (`ConstantRatio.lean`): a constant auxiliary ratio forces all four values to be
  shared CM;
* Lemmas 3.10 and 4.11: if both members have finite order, the Mues function `Ψ` is a
  polynomial;

together with the (fully formalized) exponential precomposition, Lemma 3.8, and the fact that
a periodic polynomial is constant.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- **Lemmas 3.10 and 4.11** (Mues estimate and small entire functions).  If both members of a
normalized pair on `ℂ` have finite order, then `T(r, Ψ) = O(log r)` outside a set of finite
measure, so the entire function `Ψ` is a polynomial. -/
theorem psi_polynomial_of_finite_order {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (h : NormalizedPair univ f g a) (hf : ¬ InfiniteOrder f) (hg : ¬ InfiniteOrder g) :
    ∃ p : Polynomial ℂ, ∀ᶠ z in codiscrete ℂ, auxPsi a f g z = p.eval z :=
  psi_polynomial_of_finite_order' h hf hg

lemma deriv_periodic {f : ℂ → ℂ} {ω : ℂ} (hf : ∀ t, f (t + ω) = f t) (t : ℂ) :
    deriv f (t + ω) = deriv f t := by
  have : f = fun s => f (s + ω) := funext fun s => (hf s).symm
  conv_rhs => rw [this]
  rw [deriv_comp_add_const]

lemma infinite_of_mem_nhdsNE {s : Set ℂ} {x : ℂ} (hs : s ∈ 𝓝[≠] x) : s.Infinite := by
  intro hfin
  have h1 : (s \ {x})ᶜ ∈ 𝓝[≠] x :=
    nhdsWithin_le_nhds ((hfin.diff).isClosed.isOpen_compl.mem_nhds (by simp))
  have h2 := inter_mem (inter_mem hs h1) (self_mem_nhdsWithin : {x}ᶜ ∈ 𝓝[≠] x)
  obtain ⟨y, ⟨⟨hy1, hy2⟩, hy3⟩⟩ := Filter.nonempty_of_mem h2
  exact hy2 ⟨hy1, hy3⟩

lemma eventually_nhdsNE_of_codiscrete' {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  have := (mem_codiscrete.1 h) x
  rw [Filter.disjoint_principal_right, compl_compl] at this
  exact this

/-- Step of **Lemma 4.12**: after the exponential precomposition, the Mues function
`Ψ_h(t) = e^{2t} Ψ₀(z⋆ - 1 + e^t)` is not a polynomial. -/
theorem not_psi_polynomial_comp_expShift {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (zs : ℂ) (p : Polynomial ℂ)
    (hpΨ : ∀ᶠ t in codiscrete ℂ,
      auxPsi a (f ∘ expShift zs) (g ∘ expShift zs) t = p.eval t) : False := by
  set h := expShift zs with hh_def
  set Ψ₁ := auxPsi a (f ∘ h) (g ∘ h) with hΨ₁
  set Ψ₀ := auxPsi a f g with hΨ₀
  set ω : ℂ := 2 * Real.pi * Complex.I with hω
  have hω0 : ω ≠ 0 := by simp [hω, Real.pi_ne_zero, Complex.I_ne_zero]
  have hhan := expShift_analyticAt zs
  have hh' : ∀ t, deriv h t ≠ 0 := fun t => by
    rw [hh_def, deriv_expShift]; exact Complex.exp_ne_zero t
  have hp₁ := hp.comp hhan hh'
  -- Step A: `Ψ₁` is `ω`-periodic
  have hper : ∀ t, Ψ₁ (t + ω) = Ψ₁ t := by
    intro t
    have hf1 : ∀ s, (f ∘ h) (s + ω) = (f ∘ h) s := fun s => by
      simp [hh_def, hω, expShift_periodic]
    have hg1 : ∀ s, (g ∘ h) (s + ω) = (g ∘ h) s := fun s => by
      simp [hh_def, hω, expShift_periodic]
    simp only [hΨ₁, auxPsi, auxU, auxV, deriv_periodic hf1, deriv_periodic hg1, hf1, hg1]
  -- Step B: the polynomial is periodic, hence constant
  have hS0 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), Ψ₁ t = p.eval t := eventually_nhdsNE_of_codiscrete' hpΨ 0
  have hSω : ∀ᶠ t in 𝓝[≠] ω, Ψ₁ t = p.eval t := eventually_nhdsNE_of_codiscrete' hpΨ ω
  have htr : Tendsto (fun t : ℂ => t + ω) (𝓝[≠] 0) (𝓝[≠] ω) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun t : ℂ => t + ω) (𝓝 0) (𝓝 (0 + ω)) :=
        (continuous_id.add_const ω).tendsto 0
      rw [zero_add] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hboth : ∀ᶠ t in 𝓝[≠] (0 : ℂ), p.eval (t + ω) = p.eval t := by
    filter_upwards [hS0, htr.eventually hSω] with t h1 h2
    rw [← h1, ← h2, hper]
  have hpper : ∀ z, p.eval (z + ω) = p.eval z := by
    have hq : p.comp (Polynomial.X + Polynomial.C ω) - p = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine (infinite_of_mem_nhdsNE hboth).mono fun t ht => ?_
      simp only [mem_setOf_eq] at ht
      simp [Polynomial.IsRoot, ht]
    intro z
    have := congrArg (fun q => q.eval z) hq
    simpa [sub_eq_zero] using this
  have hpC := polynomial_eq_C_of_periodic hω0 hpper
  set c := p.eval 0 with hc
  have hΨc : ∀ᶠ t in codiscrete ℂ, Ψ₁ t = c := hpΨ.mono fun t ht => by
    rw [ht, hpC, Polynomial.eval_C]
  -- Step C: near `0`, `Ψ₁(s) = e^{2s} Ψ₀(h s)`
  have hcontH : Continuous h := by rw [hh_def]; unfold expShift; fun_prop
  have hhne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), h s ≠ h 0 := by
    have hball : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with s hs
      simpa using hs
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs hs0
    intro heq
    simp only [hh_def, expShift, add_right_inj, Complex.exp_zero] at heq
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 heq
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact hs0 hn
    have : ‖s‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, norm_mul, norm_mul, norm_mul]
      simp [abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    nlinarith [Real.pi_gt_three]
  have htend : Tendsto h (𝓝[≠] 0) (𝓝[≠] (h 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hcontH.tendsto 0).mono_left nhdsWithin_le_nhds) hhne
  have hfan : ∀ᶠ s in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ f (h s) :=
    htend.eventually (hp.nonconst_f.1 (h 0) (mem_univ _)).eventually_analyticAt
  have hgan : ∀ᶠ s in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ g (h s) :=
    htend.eventually (hp.nonconst_g.1 (h 0) (mem_univ _)).eventually_analyticAt
  -- Step D: `Q(w) = Ψ₀(w) (w - w₀)² - c` vanishes near `h 0`, hence identically
  set w₀ := zs - 1 with hw₀
  set Q : ℂ → ℂ := fun w => Ψ₀ w * (w - w₀) ^ 2 - c with hQ
  have hΨ₀m : Meromorphic Ψ₀ := by
    intro z
    have hf := hp.nonconst_f.1 z (mem_univ z)
    have hg := hp.nonconst_g.1 z (mem_univ z)
    have hf' := hf.deriv
    have hg' := hg.deriv
    rw [hΨ₀]
    show MeromorphicAt (fun z => ((f z - g z) * deriv f z / ((f z - a 0) * (f z - a 1) *
      (f z - a 2))) * ((f z - g z) * deriv g z / ((g z - a 0) * (g z - a 1) * (g z - a 2)))) z
    fun_prop
  have hQm : MeromorphicOn Q univ := fun z _ => by
    have := hΨ₀m z
    fun_prop
  have hQh : (Q ∘ h) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hfan, hgan, eventually_nhdsNE_of_codiscrete' hΨc 0] with s h1 h2 h3
    have hcomp := (auxPsi_auxPhi_comp (a := a) h1.differentiableAt h2.differentiableAt
      ((hhan s).differentiableAt)).1
    rw [hh_def, deriv_expShift] at hcomp
    simp only [Function.comp_apply, hQ]
    have hsub : h s - w₀ = Complex.exp s := by simp [hh_def, expShift, hw₀]
    rw [hsub, ← h3, hΨ₁, hcomp]
    ring
  have hQtop : meromorphicOrderAt Q (h 0) = ⊤ := by
    rw [← meromorphicOrderAt_comp_of_deriv_ne_zero (hhan 0) (hh' 0)]
    rw [meromorphicOrderAt_congr hQh]
    exact meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)
  have hQw₀ : meromorphicOrderAt Q w₀ = ⊤ := by
    by_contra hne
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hQm isPreconnected_univ
      (mem_univ w₀) (mem_univ (h 0)) hne hQtop
  -- hence `c = 0`, using that `Ψ₀` has nonnegative order at `w₀` (Lemma 3.8)
  have hc0 : c = 0 := by
    by_contra hc0
    have hev : (fun w => Ψ₀ w * (w - w₀) ^ 2) =ᶠ[𝓝[≠] w₀] fun _ => c :=
      (meromorphicOrderAt_eq_top_iff.1 hQw₀).mono fun w hw => sub_eq_zero.1 hw
    have h1 := meromorphicOrderAt_congr hev
    rw [order_const_eq _ hc0] at h1
    have hsq : meromorphicOrderAt (fun w => (w - w₀) ^ 2) w₀ = ((2 : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun w => by
        rw [smul_eq_mul, mul_one]; norm_cast⟩
    have hmul : (fun w => Ψ₀ w * (w - w₀) ^ 2) = Ψ₀ * fun w => (w - w₀) ^ 2 := rfl
    rw [hmul, meromorphicOrderAt_mul (hΨ₀m w₀) (by fun_prop), hsq] at h1
    have hnn := (hp.order_aux (mem_univ w₀)).2.2
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hnn.2
    rw [← hk, ← WithTop.coe_add] at h1
    have h2 : k + 2 = 0 := by exact_mod_cast h1
    have h3 : (0 : ℤ) ≤ k := by have := hnn.1; rw [← hk] at this; exact_mod_cast this
    omega
  -- finally `Ψ₁ ≡ 0` contradicts Lemma 3.8 for the composed pair
  have hz : meromorphicOrderAt Ψ₁ 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact (eventually_nhdsNE_of_codiscrete' hΨc 0).mono fun t ht => by rw [ht, hc0]
  exact (hp₁.order_aux (mem_univ 0)).2.2.2 hz

/-- **Lemma 4.12** (periodic infinite-order reduction).  If a normalized pair on `ℂ` has a
defect over a finite shared value, then there is a periodic counterexample: a `2πi`-periodic
normalized pair with a defect, one member of infinite order, nonconstant auxiliary ratio, and
`T(r) ≥ c r` for large `r`. -/
theorem exists_periodicCounterexample {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (h : NormalizedPair univ f g a) (hd : ∃ j z, IsDefect f g (a j : Sphere) z) :
    ∃ f₁ g₁ : ℂ → ℂ, PeriodicCounterexample a f₁ g₁ := by
  obtain ⟨j, zs, hd⟩ := hd
  obtain ⟨hp, hperf, hperg, hdk⟩ := h.comp_expShift hd
  refine ⟨f ∘ expShift zs, g ∘ expShift zs, hp, ⟨j, 0, by simpa using hdk 0⟩, hperf, hperg,
    ?_, ?_, ?_⟩
  · -- one member has infinite order
    by_contra hfin
    rw [not_or] at hfin
    obtain ⟨p, hpΨ⟩ := psi_polynomial_of_finite_order hp hfin.1 hfin.2
    exact not_psi_polynomial_comp_expShift h zs p hpΨ
  · -- the auxiliary ratio is nonconstant
    intro c z hcz
    have hcm := constant_ratio hp ⟨c, z, hcz⟩
    exact (hdk 0).2.2 (hcm j _ (mem_univ _))
  · -- linear growth
    obtain ⟨c, hc, hev⟩ := linear_growth_of_progression hp.nonconst_f.1 (a := a j) (z₀ := 0)
      (ℓ := 2 * Real.pi) (by positivity) (fun k => by
        have := (hdk k).1
        convert this using 2
        push_cast; ring)
    exact ⟨c, hc, hev.mono fun r hr => hr.trans (le_max_left _ _)⟩

end ThreeIM
