module

public import RequestProject.ThreeIM.ExponentialGrowthCore
public import RequestProject.ThreeIM.RationalFinal

/-! # The rational-exponent branch from an explicit stable formula

These implications take the actual formula or period as an input. They
do not assume or use the universal rational stable-expansion theorem.
The local-to-global period and rational descent hold as meromorphic
germ identities, so no assigned value at a pole or removable point is used.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Topology

namespace ThreeIM

private lemma periodFormula_exp_args (C : ℂ) {p q : ℕ} (hq : 0 < q) (t : ℂ) :
    Complex.exp (-(t + 2 * Real.pi * Complex.I * q)) = Complex.exp (-t) ∧
      C * Complex.exp (-((p : ℂ) / q) * (t + 2 * Real.pi * Complex.I * q)) =
        C * Complex.exp (-((p : ℂ) / q) * t) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · have key := Complex.exp_int_mul_two_pi_mul_I (-(q : ℤ))
    push_cast at key
    rw [show -(t + 2 * Real.pi * Complex.I * q) = -t + -(q : ℂ) * (2 * Real.pi * Complex.I) by
      ring, Complex.exp_add, key, mul_one]
  · congr 1
    have key := Complex.exp_int_mul_two_pi_mul_I (-(p : ℤ))
    push_cast at key
    rw [show -((p : ℂ) / q) * (t + 2 * Real.pi * Complex.I * q) =
        -((p : ℂ) / q) * t + -(p : ℂ) * (2 * Real.pi * Complex.I) by
      field_simp; ring, Complex.exp_add, key, mul_one]

private lemma periodFormula_nhdsNE_of_codiscreteWithin_halfplane {p : ℂ → Prop} {R₀ : ℝ}
    (hp : ∀ᶠ t in codiscreteWithin {t : ℂ | R₀ < t.re}, p t) {x : ℂ} (hx : R₀ < x.re) :
    ∀ᶠ t in 𝓝[≠] x, p t := by
  have hd := (mem_codiscreteWithin.1 hp) x hx
  rw [disjoint_principal_right] at hd
  have hU : {t : ℂ | R₀ < t.re} ∈ 𝓝[≠] x :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
  filter_upwards [hd, hU] with t h1 h2
  by_contra hc
  exact h1 ⟨h2, hc⟩

/-- An explicit rational stable formula supplies a common meromorphic
period. Analyticity of the model is unnecessary for this implication:
the two arguments themselves are invariant under the stated shift. -/
theorem ExponentialPair.period_of_rational_stable_formula
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {j : Fin 3} {p q : ℕ} (hq : 0 < q) {C : ℂ} {H V : ℂ × ℂ → ℂ} {R₀ : ℝ}
    (hexp : ∀ᶠ t in codiscreteWithin {t : ℂ | R₀ < t.re},
      f t = a j + H (Complex.exp (-t), C * Complex.exp (-((p : ℂ) / q) * t)) ∧
        (g t)⁻¹ = Complex.exp (-t) *
          V (Complex.exp (-t), H (Complex.exp (-t), C * Complex.exp (-((p : ℂ) / q) * t)))) :
    (∀ᶠ t in codiscrete ℂ, f (t + 2 * Real.pi * Complex.I * q) = f t) ∧
      (∀ᶠ t in codiscrete ℂ, g (t + 2 * Real.pi * Complex.I * q) = g t) := by
  set ω : ℂ := 2 * Real.pi * Complex.I * q
  set z₀ : ℂ := ((R₀ + 1 : ℝ) : ℂ)
  have hz₀ : R₀ < z₀.re := by simp [z₀]
  have hz₀ω : R₀ < (z₀ + ω).re := by simp [z₀, ω]
  set Fexp : ℂ → ℂ := fun t =>
    a j + H (Complex.exp (-t), C * Complex.exp (-((p : ℂ) / q) * t))
  set Gexp : ℂ → ℂ := fun t => (Complex.exp (-t) *
    V (Complex.exp (-t), H (Complex.exp (-t), C * Complex.exp (-((p : ℂ) / q) * t))))⁻¹
  have hFp : ∀ t, Fexp (t + ω) = Fexp t := by
    intro t
    obtain ⟨e1, e2⟩ := periodFormula_exp_args C (p := p) hq t
    simp only [Fexp, ω, e1, e2]
  have hGp : ∀ t, Gexp (t + ω) = Gexp t := by
    intro t
    obtain ⟨e1, e2⟩ := periodFormula_exp_args C (p := p) hq t
    simp only [Gexp, ω, e1, e2]
  have hf : ∀ x : ℂ, R₀ < x.re → ∀ᶠ t in 𝓝[≠] x, f t = Fexp t := fun x hx =>
    (periodFormula_nhdsNE_of_codiscreteWithin_halfplane hexp hx).mono fun t ht => ht.1
  have hg : ∀ x : ℂ, R₀ < x.re → ∀ᶠ t in 𝓝[≠] x, g t = Gexp t := fun x hx =>
    (periodFormula_nhdsNE_of_codiscreteWithin_halfplane hexp hx).mono fun t ht => by
      simp only [Gexp, ← ht.2, inv_inv]
  exact ⟨codiscrete_period_of_local h.pair.nonconst_f.1 hFp (hf z₀ hz₀) (hf _ hz₀ω),
    codiscrete_period_of_local h.pair.nonconst_g.1 hGp (hg z₀ hz₀) (hg _ hz₀ω)⟩

/-- Given the actual common period, the already proved linear growth
and periodic descent produce rational functions on the exponential
coordinate. No stable-expansion existence theorem is invoked. -/
theorem ExponentialPair.eq_rational_exp_of_period
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {q : ℕ} (hq : 0 < q)
    (hpf : ∀ᶠ t in codiscrete ℂ, f (t + 2 * Real.pi * Complex.I * q) = f t)
    (hpg : ∀ᶠ t in codiscrete ℂ, g (t + 2 * Real.pi * Complex.I * q) = g t) :
    ∃ R S : RatFunc ℂ, ∀ᶠ t in codiscrete ℂ,
      f t = ratEval R (Complex.exp (t / q)) ∧
        g t = ratEval S (Complex.exp (t / q)) := by
  obtain ⟨K, hK⟩ := h.linear_growth
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpf' : ∀ᶠ t in codiscrete ℂ, f (t + 2 * Real.pi * Complex.I * ((q : ℝ) : ℂ)) = f t := by
    simpa using hpf
  have hpg' : ∀ᶠ t in codiscrete ℂ, g (t + 2 * Real.pi * Complex.I * ((q : ℝ) : ℂ)) = g t := by
    simpa using hpg
  obtain ⟨R, hR⟩ := periodic_linear_growth_descent h.pair.nonconst_f.1 hq' hpf'
    (hK.mono fun _ hr => hr.1)
  obtain ⟨S, hS⟩ := periodic_linear_growth_descent h.pair.nonconst_g.1 hq' hpg'
    (hK.mono fun _ hr => hr.2)
  refine ⟨R, S, ?_⟩
  filter_upwards [hR, hS] with t h1 h2
  simp only [Complex.ofReal_natCast] at h1 h2
  exact ⟨h1, h2⟩

private lemma periodFormula_ratEval_C (c t : ℂ) : ratEval (RatFunc.C c) t = c := by
  simp [ratEval]

private lemma periodFormula_mult_eq_of_codiscrete {f F : ℂ → ℂ}
    (h : ∀ᶠ t in codiscrete ℂ, f t = F t) (b : Sphere) (z : ℂ) :
    mult f b z = mult F b z :=
  mult_congr_nhdsNE (eventually_nhdsNE_of_codiscrete h z) b

/-- A rational exponential representation suffices for all three finite
CM conclusions, by the proved rational four-values theorem on the
punctured plane. This is the rational branch's terminal implication. -/
theorem ExponentialPair.sharesCM_of_rational_exp
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {q : ℕ} (hq : 0 < q) {R S : RatFunc ℂ}
    (hRS : ∀ᶠ t in codiscrete ℂ, f t = ratEval R (Complex.exp (t / q)) ∧
      g t = ratEval S (Complex.exp (t / q))) (j : Fin 3) :
    SharesCMOn univ f g (a j : Sphere) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set e : ℂ → ℂ := fun t => Complex.exp (t / q) with he
  have hfR : ∀ b z, mult f b z = mult (ratEval R ∘ e) b z :=
    periodFormula_mult_eq_of_codiscrete (hRS.mono fun t ht => ht.1)
  have hgS : ∀ b z, mult g b z = mult (ratEval S ∘ e) b z :=
    periodFormula_mult_eq_of_codiscrete (hRS.mono fun t ht => ht.2)
  have hP := h.pair
  have hnc : ∀ (F : ℂ → ℂ) (T : RatFunc ℂ), IsNonconstMeroOn F univ →
      (∀ᶠ t in codiscrete ℂ, F t = ratEval T (e t)) → ∀ c : ℂ, T ≠ RatFunc.C c := by
    intro F T hF hFT c hc
    apply hF.2 0 (mem_univ _) c
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [eventually_nhdsNE_of_codiscrete hFT 0] with w hw
    rw [hw, hc, periodFormula_ratEval_C, sub_self]
  have hR := hnc f R hP.nonconst_f (hRS.mono fun t ht => ht.1)
  have hS := hnc g S hP.nonconst_g (hRS.mono fun t ht => ht.2)
  have hIM : ∀ b, SharesIMOn univ f g b → SharesIMOn {0}ᶜ (ratEval R) (ratEval S) b := by
    intro b hb
    rw [sharesIMOn_punctured_iff_comp_exp_div hq']
    intro z hz
    rw [← hfR, ← hgS]; exact hb z hz
  have hCMtop : SharesCMOn {0}ᶜ (ratEval R) (ratEval S) ⊤ := by
    rw [sharesCMOn_punctured_iff_comp_exp_div hq']
    intro z hz
    rw [← hfR, ← hgS]; exact hP.cm_top z hz
  let b : Fin 4 → Sphere := ![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤]
  have hb : Function.Injective b := by
    intro i i' hii'
    have ha := hP.injective
    fin_cases i <;> fin_cases i' <;> simp [b] at hii' ⊢ <;>
      exact absurd (ha hii') (by decide)
  have hbIM : ∀ i : Fin 3, SharesIMOn {0}ᶜ (ratEval R) (ratEval S) (b i.castSucc) := by
    intro i; fin_cases i <;> exact hIM _ (hP.im _)
  have hall := rational_four_values hR hS b hb hbIM hCMtop
  have hj : b j.castSucc = (a j : Sphere) := by fin_cases j <;> rfl
  have hcm := hall j.castSucc
  rw [hj, sharesCMOn_punctured_iff_comp_exp_div hq'] at hcm
  intro z hz
  rw [hfR, hgS]; exact hcm z hz

end ThreeIM
