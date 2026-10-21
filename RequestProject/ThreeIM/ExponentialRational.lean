module

public import RequestProject.ThreeIM.ExponentialDefectExclusion
public import RequestProject.ThreeIM.ExponentialStableExpansion
public import RequestProject.ThreeIM.RationalFinal

/-!
# Exponential pairs carry no defect (last step of Lemma 10.5)

Actual real stable data are constructed from the exponential pair. In a putative defect,
the critical phase argument forces the real exponent to be rational. The resulting actual
period, rational descent and rational four-values theorem exclude that defect. No universal
rational stable-expansion existence theorem is an input.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

lemma ratEval_C (c t : ℂ) : ratEval (RatFunc.C c) t = c := by
  simp [ratEval]

/-- If `f = R(e^{t/q})` off a discrete set, the local degrees of `f` are those of
`R ∘ e^{·/q}`. -/
lemma mult_eq_of_codiscrete {f F : ℂ → ℂ} (h : ∀ᶠ t in codiscrete ℂ, f t = F t)
    (b : Sphere) (z : ℂ) : mult f b z = mult F b z :=
  mult_congr_nhdsNE (eventually_nhdsNE_of_codiscrete h z) b

/-- **Lemma 10.5, last step.** Actual stable data and the critical/rational defect
exclusion imply the three finite CM conclusions. Infinity is already shared CM. -/
theorem ExponentialPair.sharesCM {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (j : Fin 3) : SharesCMOn univ f g (a j : Sphere) := by
  intro z _
  by_contra hne
  have hiff := h.pair.im j z (mem_univ z)
  have hfpos : 0 < mult f (a j : Sphere) z := by
    by_contra hn
    have hfzero : mult f (a j : Sphere) z = 0 := by omega
    have hgzero : mult g (a j : Sphere) z = 0 := by
      by_contra hg
      have hp := hiff.mpr (Nat.pos_of_ne_zero hg)
      omega
    exact hne (hfzero.trans hgzero.symm)
  have hgpos : 0 < mult g (a j : Sphere) z := hiff.mp hfpos
  exact h.not_isDefect_of_real_stable_data_factory
    (fun F G hFG => hFG.exists_real_stable_data) j z ⟨hfpos, hgpos, hne⟩

/-- An exponential pair has no defect over any of its finite shared values. -/
theorem ExponentialPair.not_isDefect {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (j : Fin 3) (z : ℂ) : ¬ IsDefect f g (a j : Sphere) z :=
  fun hd => hd.2.2 (h.sharesCM j z (mem_univ z))

/-! ### The affine source change of Lemma 10.5 -/

/-- An affine map `t ↦ λ t + μ`, `λ ≠ 0`, maps punctured neighbourhoods to punctured
neighbourhoods. -/
lemma tendsto_affine_nhdsNE {l : ℂ} (hl : l ≠ 0) (μ x : ℂ) :
    Tendsto (fun t => l * t + μ) (𝓝[≠] x) (𝓝[≠] (l * x + μ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((Continuous.tendsto (by fun_prop) x).mono_left nhdsWithin_le_nhds), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
  intro he
  exact ht (mul_left_cancel₀ hl (add_right_cancel he))

/-- Pulling back a codiscrete property by an affine map `t ↦ λ t + μ`, `λ ≠ 0`. -/
lemma codiscrete_comp_affine {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z) {l : ℂ}
    (hl : l ≠ 0) (μ : ℂ) : ∀ᶠ t in codiscrete ℂ, p (l * t + μ) := by
  rw [codiscrete_iff_nhdsNE] at h ⊢
  intro x
  exact (tendsto_affine_nhdsNE hl μ x).eventually (h _)

lemma hasDerivAt_two_mul_add (μ z : ℂ) : HasDerivAt (fun t : ℂ => 2 * t + μ) 2 z := by
  simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).add_const μ

/-- **Lemma 10.5, affine source change.**  Let `f, g` be a normalized pair on `ℂ` whose
auxiliary functions are `U(s) = c⁻¹ √q e^{s/2}` and `V(s) = c⁻¹ q^{-1/2} e^{-s/2}`, with
`c ≠ 0` and `q > 0`.  Then after the change of variable `s = 2t - log q` the pair is an
exponential pair with `κ = 2/c`. -/
theorem NormalizedPair.exponentialPair_of_aux {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hP : NormalizedPair univ f g a) {c : ℂ} (hc : c ≠ 0) {q : ℝ} (hq : 0 < q)
    (hU : ∀ᶠ s in codiscrete ℂ,
      auxU a f g s = c⁻¹ * (Real.sqrt q : ℂ) * Complex.exp (s / 2))
    (hV : ∀ᶠ s in codiscrete ℂ,
      auxV a f g s = c⁻¹ * (Real.sqrt q : ℂ)⁻¹ * Complex.exp (-s / 2)) :
    ExponentialPair a (f ∘ fun t => 2 * t + (-(Real.log q : ℂ)))
      (g ∘ fun t => 2 * t + (-(Real.log q : ℂ))) (2 / c) := by
  set L : ℂ := (Real.log q : ℂ)
  set h : ℂ → ℂ := fun t => 2 * t + -L with hh
  have hsq : (Real.sqrt q : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hexpL : Complex.exp (L / 2) = (Real.sqrt q : ℂ) := by
    rw [show L / 2 = ((Real.log q / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
    congr 2; ring
  have hha : ∀ z, AnalyticAt ℂ h z := fun z => by rw [hh]; fun_prop
  have hderiv : ∀ z, deriv h z = 2 := fun z => (hasDerivAt_two_mul_add (-L) z).deriv
  have hh' : ∀ z, deriv h z ≠ 0 := fun z => by rw [hderiv]; norm_num
  have hfa : ∀ᶠ s in codiscrete ℂ, AnalyticAt ℂ f s := by
    simpa only [Filter.codiscrete] using MeromorphicOn.eventually_codiscreteWithin_analyticAt f hP.nonconst_f.1
  have hga : ∀ᶠ s in codiscrete ℂ, AnalyticAt ℂ g s := by
    simpa only [Filter.codiscrete] using MeromorphicOn.eventually_codiscreteWithin_analyticAt g hP.nonconst_g.1
  refine ⟨hP.comp hha hh', div_ne_zero two_ne_zero hc, ?_, ?_⟩
  · filter_upwards [codiscrete_comp_affine (hU.and hfa) two_ne_zero (-L)] with t ht
    rw [auxU_comp (h := h) ht.2.differentiableAt (hha t).differentiableAt, hderiv, ht.1]
    have : Complex.exp ((2 * t + -L) / 2) = Complex.exp t * (Real.sqrt q : ℂ)⁻¹ := by
      rw [← hexpL, ← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
    rw [this]; field_simp
  · filter_upwards [codiscrete_comp_affine (hV.and hga) two_ne_zero (-L)] with t ht
    rw [auxV_comp (h := h) ht.2.differentiableAt (hha t).differentiableAt, hderiv, ht.1]
    have : Complex.exp (-(2 * t + -L) / 2) = Complex.exp (-t) * (Real.sqrt q : ℂ) := by
      rw [← hexpL, ← Complex.exp_add]; congr 1; ring
    rw [this]; field_simp

/-- **Lemma 10.5, conclusion.**  A normalized pair on `ℂ` whose auxiliary functions are
`U(s) = c⁻¹ √q e^{s/2}` and `V(s) = c⁻¹ q^{-1/2} e^{-s/2}` (`c ≠ 0`, `q > 0`) has no defect.
It is an exponential pair after an affine change of variable; the actual stable-data
factory and critical/rational defect exclusion apply. -/
theorem NormalizedPair.not_isDefect_of_aux {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hP : NormalizedPair univ f g a) {c : ℂ} (hc : c ≠ 0) {q : ℝ} (hq : 0 < q)
    (hU : ∀ᶠ s in codiscrete ℂ,
      auxU a f g s = c⁻¹ * (Real.sqrt q : ℂ) * Complex.exp (s / 2))
    (hV : ∀ᶠ s in codiscrete ℂ,
      auxV a f g s = c⁻¹ * (Real.sqrt q : ℂ)⁻¹ * Complex.exp (-s / 2))
    (j : Fin 3) (z : ℂ) : ¬ IsDefect f g (a j : Sphere) z := by
  have hE := hP.exponentialPair_of_aux hc hq hU hV
  set L : ℂ := (Real.log q : ℂ)
  have hz : 2 * ((z + L) / 2) + -L = z := by ring
  have hha : AnalyticAt ℂ (fun t : ℂ => 2 * t + -L) ((z + L) / 2) := by fun_prop
  have hd : deriv (fun t : ℂ => 2 * t + -L) ((z + L) / 2) ≠ 0 := by
    rw [(hasDerivAt_two_mul_add (-L) _).deriv]; norm_num
  intro hdef
  apply hE.not_isDefect j ((z + L) / 2)
  unfold IsDefect
  rw [mult_comp_of_deriv_ne_zero hha hd, mult_comp_of_deriv_ne_zero hha hd, hz]
  exact hdef

end ThreeIM
