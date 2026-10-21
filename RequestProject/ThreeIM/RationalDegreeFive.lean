module

public import RequestProject.ThreeIM.RationalCount
public import RequestProject.ThreeIM.ThetaLocal

/-!
# Degree bound in the presence of a defect (Lemma 9.8)

In the endpoint configuration of Lemma 9.5 (`U = α t^{-ρ}`, `V = β t^ρ`), put
`Φ_j(t) = (t θ_j(t))² - c_j² α β`, where `θ_j = Θ_{a_j}(R) - Θ_{a_j}(S)` is the logarithmic
auxiliary function of Definition 4.3 (so that `t θ_j` is the paper's `θ_j` written with
`D = t d/dt`) and `c_j = 2 a_j - a_k - a_l`.  Then `Φ_j` is a rational function, finite at `0`
and at `∞`, with a double pole at each defect over `a_j` in `ℂ*` and no other poles, and it
vanishes at each common pole in `ℂ*`.  Counting zeros against poles gives
`#(common poles in ℂ*) ≤ 2 D_j`; summing over `j` gives `d ≤ 5ρ`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- `Φ_j(t) = (t θ_j(t))² - K`. -/
noncomputable def PhiFun (a : Fin 3 → ℂ) (j : Fin 3) (K : ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun t => (t * thetaAux a j f g t) ^ 2 - K

/-! ### Rationality -/

lemma IsRatFun.thetaFun {h : ℂ → ℂ} (hh : IsRatFun h) (a : Fin 3 → ℂ) (j : Fin 3) :
    IsRatFun (ThetaFun a j h) := by
  have h1 := hh.deriv
  have h2 := h1.deriv
  unfold ThetaFun
  exact (((h2.div h1).add ((IsRatFun.const 2).mul (h1.div (hh.sub (IsRatFun.const _))))).sub
    (h1.div (hh.sub (IsRatFun.const _)))).sub (h1.div (hh.sub (IsRatFun.const _)))

lemma IsRatFun.phiFun {f g : ℂ → ℂ} (hf : IsRatFun f) (hg : IsRatFun g) (a : Fin 3 → ℂ)
    (j : Fin 3) (K : ℂ) : IsRatFun (PhiFun a j K f g) := by
  unfold PhiFun thetaAux
  exact ((IsRatFun.id.mul ((hf.thetaFun a j).sub (hg.thetaFun a j))).pow 2).sub
    (IsRatFun.const K)

/-! ### Finiteness at the endpoints -/

/-- Near a point where `H` is meromorphic of finite order, `(t - z₀) H'/H` is analytic. -/
lemma exists_analytic_mul_logDeriv {H : ℂ → ℂ} {z₀ : ℂ} (hH : MeromorphicAt H z₀)
    (hn : meromorphicOrderAt H z₀ ≠ ⊤) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧
      ∀ᶠ t in 𝓝[≠] z₀, (t - z₀) * (deriv H t / H t) = E t := by
  obtain ⟨n, hn'⟩ := WithTop.ne_top_iff_exists.1 hn
  obtain ⟨E₀, hE₀, h⟩ := logDeriv_local hH hn'.symm
  refine ⟨fun t => (n : ℂ) + (t - z₀) * E₀ t, by fun_prop, ?_⟩
  filter_upwards [h, self_mem_nhdsWithin] with t ht htz
  have : t - z₀ ≠ 0 := sub_ne_zero.2 htz
  rw [ht]; field_simp

/-- If `F₁, F₂` are meromorphic at `0` and nonconstant near `0`, then `Φ_j(F₁, F₂)` has
nonnegative order at `0`. -/
theorem order_phiFun_nonneg {F₁ F₂ : ℂ → ℂ} (h₁ : MeromorphicAt F₁ 0) (h₂ : MeromorphicAt F₂ 0)
    (hd₁ : meromorphicOrderAt (deriv F₁) 0 ≠ ⊤) (hd₂ : meromorphicOrderAt (deriv F₂) 0 ≠ ⊤)
    (hc₁ : ∀ c, meromorphicOrderAt (fun w => F₁ w - c) 0 ≠ ⊤)
    (hc₂ : ∀ c, meromorphicOrderAt (fun w => F₂ w - c) 0 ≠ ⊤)
    (a : Fin 3 → ℂ) (j : Fin 3) (K : ℂ) :
    0 ≤ meromorphicOrderAt (PhiFun a j K F₁ F₂) 0 := by
  have key : ∀ F : ℂ → ℂ, MeromorphicAt F 0 → meromorphicOrderAt (deriv F) 0 ≠ ⊤ →
      (∀ c, meromorphicOrderAt (fun w => F w - c) 0 ≠ ⊤) →
      ∃ E : ℂ → ℂ, AnalyticAt ℂ E 0 ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ), t * ThetaFun a j F t = E t := by
    intro F hF hd hc
    have hsub : ∀ c : ℂ, deriv (fun w => F w - c) = deriv F :=
      fun c => funext fun w => deriv_sub_const c
    obtain ⟨E₀, hE₀, e₀⟩ := exists_analytic_mul_logDeriv hF.deriv hd
    obtain ⟨E₁, hE₁, e₁⟩ := exists_analytic_mul_logDeriv
      (H := fun w => F w - a j) (hF.sub (MeromorphicAt.const (a j) 0)) (hc (a j))
    obtain ⟨E₂, hE₂, e₂⟩ := exists_analytic_mul_logDeriv
      (H := fun w => F w - a (j + 1)) (hF.sub (MeromorphicAt.const (a (j + 1)) 0)) (hc (a (j + 1)))
    obtain ⟨E₃, hE₃, e₃⟩ := exists_analytic_mul_logDeriv
      (H := fun w => F w - a (j + 2)) (hF.sub (MeromorphicAt.const (a (j + 2)) 0)) (hc (a (j + 2)))
    refine ⟨fun t => E₀ t + 2 * E₁ t - E₂ t - E₃ t, by fun_prop, ?_⟩
    filter_upwards [e₀, e₁, e₂, e₃] with t h0 h1 h2 h3
    rw [hsub, sub_zero] at h1 h2 h3
    rw [sub_zero] at h0
    simp only [ThetaFun]
    rw [← h0, ← h1, ← h2, ← h3]
    ring
  obtain ⟨E, hE, e⟩ := key F₁ h₁ hd₁ hc₁
  obtain ⟨E', hE', e'⟩ := key F₂ h₂ hd₂ hc₂
  have hA : AnalyticAt ℂ (fun t => (E t - E' t) ^ 2 - K) 0 := by fun_prop
  have heq : PhiFun a j K F₁ F₂ =ᶠ[𝓝[≠] 0] fun t => (E t - E' t) ^ 2 - K := by
    filter_upwards [e, e'] with t h1 h2
    simp only [PhiFun, thetaAux, mul_sub, h1, h2]
  rw [meromorphicOrderAt_congr heq]
  exact hA.meromorphicOrderAt_nonneg

/-- Inversion `t ↦ 1/t`: `Φ_j(f, g)(1/s) = Φ_j(f ∘ inv, g ∘ inv)(s)` at every `s ≠ 0` with
`f, g` analytic at `1/s` and `f'(1/s), g'(1/s) ≠ 0`. -/
theorem phiFun_inv {f g : ℂ → ℂ} {s : ℂ} (hs : s ≠ 0) (hf : AnalyticAt ℂ f s⁻¹)
    (hg : AnalyticAt ℂ g s⁻¹) (hf' : deriv f s⁻¹ ≠ 0) (hg' : deriv g s⁻¹ ≠ 0)
    (a : Fin 3 → ℂ) (j : Fin 3) (K : ℂ) :
    PhiFun a j K f g s⁻¹ = PhiFun a j K (fun w => f w⁻¹) (fun w => g w⁻¹) s := by
  have hderivs : ∀ F : ℂ → ℂ, AnalyticAt ℂ F s⁻¹ →
      deriv (fun w => F w⁻¹) s = deriv F s⁻¹ * (-(s ^ 2)⁻¹) ∧
      deriv (deriv (fun w => F w⁻¹)) s =
        deriv (deriv F) s⁻¹ * (-(s ^ 2)⁻¹) * (-(s ^ 2)⁻¹) +
          deriv F s⁻¹ * (2 * s ^ 1 / (s ^ 2) ^ 2) := by
    intro F hF
    have hinv : Tendsto (fun w : ℂ => w⁻¹) (𝓝 s) (𝓝 s⁻¹) := tendsto_inv₀ hs
    have hev : ∀ᶠ w in 𝓝 s, AnalyticAt ℂ F w⁻¹ ∧ w ≠ 0 :=
      (hinv.eventually hF.eventually_analyticAt).and (eventually_ne_nhds hs)
    have hloc : deriv (fun w => F w⁻¹) =ᶠ[𝓝 s] fun w => deriv F w⁻¹ * (-(w ^ 2)⁻¹) := by
      filter_upwards [hev] with w ⟨hw, hw0⟩
      exact ((hw.differentiableAt.hasDerivAt).comp w (hasDerivAt_inv hw0)).deriv
    refine ⟨hloc.eq_of_nhds, ?_⟩
    rw [hloc.deriv_eq]
    have h1 : HasDerivAt (fun w => deriv F w⁻¹) (deriv (deriv F) s⁻¹ * (-(s ^ 2)⁻¹)) s :=
      (hF.deriv.differentiableAt.hasDerivAt).comp s (hasDerivAt_inv hs)
    have h2 : HasDerivAt (fun w : ℂ => -(w ^ 2)⁻¹) (2 * s ^ 1 / (s ^ 2) ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)).neg
      convert this using 1
      push_cast; ring
    exact (h1.mul h2).deriv
  obtain ⟨f1, f2⟩ := hderivs f hf
  obtain ⟨g1, g2⟩ := hderivs g hg
  simp only [PhiFun, thetaAux, ThetaFun]
  rw [f1, f2, g1, g2]
  congr 1
  simp only [div_eq_mul_inv]
  generalize (f s⁻¹ - a j)⁻¹ = u₁
  generalize (f s⁻¹ - a (j + 1))⁻¹ = u₂
  generalize (f s⁻¹ - a (j + 2))⁻¹ = u₃
  generalize (g s⁻¹ - a j)⁻¹ = v₁
  generalize (g s⁻¹ - a (j + 1))⁻¹ = v₂
  generalize (g s⁻¹ - a (j + 2))⁻¹ = v₃
  generalize deriv (deriv f) s⁻¹ = Y
  generalize deriv (deriv g) s⁻¹ = Y'
  generalize deriv f s⁻¹ = X at hf' ⊢
  generalize deriv g s⁻¹ = X' at hg' ⊢
  field_simp
  ring

end ThreeIM
