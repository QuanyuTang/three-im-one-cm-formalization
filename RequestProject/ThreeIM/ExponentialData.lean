module

public import RequestProject.ThreeIM.Rational
public import RequestProject.ThreeIM.Holomorphic
public import RequestProject.ThreeIM.PeriodicDescent

/-! # Exponential pair data and local identities -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- **Definition 8.1** (exponential pair).  A normalized pair `f, g` on `ℂ` (three distinct finite
values shared IM, `∞` shared CM) together with `κ ≠ 0` such that
`(f - g) f' / P(f) = κ e^t` and `(f - g) g' / P(g) = κ e^{-t}` as meromorphic functions
(that is, off a discrete set). -/
structure ExponentialPair (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (κ : ℂ) : Prop where
  pair : NormalizedPair univ f g a
  κ_ne_zero : κ ≠ 0
  eq_U : ∀ᶠ t in codiscrete ℂ, auxU a f g t = κ * Complex.exp t
  eq_V : ∀ᶠ t in codiscrete ℂ, auxV a f g t = κ * Complex.exp (-t)

lemma eventually_nhdsNE_of_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  have := (mem_codiscrete.1 h) x
  rw [Filter.disjoint_principal_right, compl_compl] at this
  exact this

/-- **Lemma 8.2** (finite part).  For an exponential pair, every finite shared point has
multiplicities `(m, n)` with `min(m, n) = 1`, and `e^{2t} = m/n` there. -/
theorem ExponentialPair.shared_point {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {t : ℂ} {j : Fin 3} (hj : 0 < mult f (a j : Sphere) t) :
    min (mult f (a j : Sphere) t) (mult g (a j : Sphere) t) = 1 ∧
      Complex.exp (2 * t) = (mult f (a j : Sphere) t : ℂ) / (mult g (a j : Sphere) t) := by
  have hP := h.pair
  have hfm := hP.nonconst_f.1 t (mem_univ t)
  have hgm := hP.nonconst_g.1 t (mem_univ t)
  have hj' : 0 < mult g (a j : Sphere) t := (hP.im j t (mem_univ t)).1 hj
  have hU := eventually_nhdsNE_of_codiscrete h.eq_U t
  have hV := eventually_nhdsNE_of_codiscrete h.eq_V t
  constructor
  · apply hP.min_mult_eq_one_of_psi (mem_univ t) hj
    have : auxPsi a f g =ᶠ[𝓝[≠] t] fun _ => κ ^ 2 := by
      filter_upwards [hU, hV] with w hu hv
      simp only [auxPsi, hu, hv]
      rw [mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ring
    rw [meromorphicOrderAt_congr this, order_const_eq _ (pow_ne_zero 2 h.κ_ne_zero)]
  · have hlim := tendsto_auxPhi_at_shared hfm hgm hP.injective hj hj'
      (order_sub_eq_mult hj) (order_sub_eq_mult hj') (hP.distinct t (mem_univ t))
    have heq : auxPhi a f g =ᶠ[𝓝[≠] t] fun w => Complex.exp (2 * w) := by
      filter_upwards [hU, hV] with w hu hv
      simp only [auxPhi, hu, hv]
      rw [mul_div_mul_left _ _ h.κ_ne_zero, ← Complex.exp_sub]
      ring_nf
    have hcont : Tendsto (fun w => Complex.exp (2 * w)) (𝓝[≠] t) (𝓝 (Complex.exp (2 * t))) :=
      ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto t).mono_left
        nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hcont.congr' heq.symm) hlim

/-- **Identity theorem for periods.**  If a meromorphic function on `ℂ` agrees, on punctured
neighbourhoods of `z₀` and of `z₀ + ω`, with an `ω`-periodic function, then it has period `ω`
off a discrete set. -/
lemma codiscrete_period_of_local {h F : ℂ → ℂ} (hh : MeromorphicOn h univ) {ω z₀ : ℂ}
    (hF : ∀ t, F (t + ω) = F t) (h₁ : ∀ᶠ t in 𝓝[≠] z₀, h t = F t)
    (h₂ : ∀ᶠ t in 𝓝[≠] (z₀ + ω), h t = F t) :
    ∀ᶠ t in codiscrete ℂ, h (t + ω) = h t := by
  set D : ℂ → ℂ := fun t => h (t + ω) - h t with hD
  have hshift : MeromorphicOn (fun t => h (t + ω)) univ := fun x _ =>
    (hh (x + ω) (mem_univ _)).comp_analyticAt (g := fun t => t + ω) (x := x) (by fun_prop)
  have hDm : MeromorphicOn D univ := hshift.sub hh
  have htr : Tendsto (fun z => z + ω) (𝓝[≠] z₀) (𝓝[≠] (z₀ + ω)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_id.add_const ω).tendsto z₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have htop : meromorphicOrderAt D z₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [htr.eventually h₂, h₁] with z e₂ e₁
    simp only [hD, e₂, e₁, hF, sub_self]
  have hall : ∀ x : ℂ, meromorphicOrderAt D x = ⊤ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := hne
    have := (hDm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, mem_univ x⟩, hx⟩ ⟨z₀, mem_univ z₀⟩
    exact this htop
  rw [Filter.Eventually, mem_codiscrete]
  intro x
  rw [disjoint_principal_right, compl_compl]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hall x)] with z hz
  exact sub_eq_zero.1 hz

end ThreeIM
