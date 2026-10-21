module

public import RequestProject.ThreeIM.Holomorphic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Analytic.Order

/-!
# Persistence of a fixed marked order

Locally uniform holomorphic convergence preserves a lower bound on the
vanishing order at a fixed point. All low-order derivative identities are
derived from the order bound and Weierstrass convergence of derivatives.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem analytic_order_le_iff_meromorphic_order_le {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (m : ℕ) :
    (m : ℕ∞) ≤ analyticOrderAt f z ↔ (m : ℤ) ≤ meromorphicOrderAt f z := by
  rw [hf.meromorphicOrderAt_eq]
  cases ho : analyticOrderAt f z with
  | top => simp
  | coe k =>
    rw [ENat.map_coe]
    constructor <;> intro h <;> exact_mod_cast h

private theorem marked_analytic_iteratedDeriv {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k f) Ω := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv

/-- Weierstrass convergence holds for every iterated derivative; no
convergence of derivatives is imposed as a separate assumption. -/
theorem locallyUniformlyOn_iteratedDeriv {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
      (iteratedDeriv k f) atTop Ω := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hconv
  | succ k hk =>
    have hFk : ∀ᶠ n in atTop, DifferentiableOn ℂ (iteratedDeriv k (F n)) Ω :=
      hF.mono fun n hn => (marked_analytic_iteratedDeriv (hn.analyticOnNhd hΩ) k).differentiableOn
    simpa only [iteratedDeriv_succ, Function.comp_def] using hk.deriv hFk hΩ

theorem analytic_order_ge_of_locallyUniformlyOn {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) (m : ℕ)
    (horder : ∀ᶠ n in atTop, (m : ℕ∞) ≤ analyticOrderAt (F n) z) :
    (m : ℕ∞) ≤ analyticOrderAt f z := by
  have hfa : AnalyticAt ℂ f z := (hconv.differentiableOn hF hΩ).analyticOnNhd hΩ z hz
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfa).mpr
  intro i hi
  have hdconv := (locallyUniformlyOn_iteratedDeriv hΩ hF hconv i).tendsto_at hz
  have hzero : (fun n => iteratedDeriv i (F n) z) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [hF, horder] with n hn ho
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((hn.analyticOnNhd hΩ) z hz)).mp ho i hi
  exact tendsto_nhds_unique_of_eventuallyEq hdconv tendsto_const_nhds hzero

/-- The marked order is lower semicontinuous. The limit is analytic by
Weierstrass; even a locally constant limit is allowed in this inequality. -/
theorem marked_order_ge_of_locallyUniformlyOn {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) (a : ℂ) (m : ℕ)
    (horder : ∀ᶠ n in atTop, (m : ℤ) ≤ meromorphicOrderAt (fun w => F n w - a) z) :
    (m : ℤ) ≤ meromorphicOrderAt (fun w => f w - a) z := by
  have hFs : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => F n w - a) Ω :=
    hF.mono fun n hn => hn.sub (differentiableOn_const a)
  have hc : TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : ℂ) => a) (fun _ => a) atTop Ω :=
    by
      have htc : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      exact (htc.tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
  have hcs : TendstoLocallyUniformlyOn (fun n w => F n w - a) (fun w => f w - a) atTop Ω :=
    hconv.sub hc
  have hAo : ∀ᶠ n in atTop, (m : ℕ∞) ≤ analyticOrderAt (fun w => F n w - a) z := by
    filter_upwards [hFs, horder] with n hn ho
    exact (analytic_order_le_iff_meromorphic_order_le ((hn.analyticOnNhd hΩ) z hz) m).mpr ho
  have hlimit := analytic_order_ge_of_locallyUniformlyOn hΩ hz hFs hcs m hAo
  exact (analytic_order_le_iff_meromorphic_order_le
    ((hcs.differentiableOn hFs hΩ).analyticOnNhd hΩ z hz) m).mp hlimit

theorem marked_mult_ge_of_locallyUniformlyOn {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) (a : ℂ) (m : ℕ)
    (horder : ∀ᶠ n in atTop, (m : ℤ) ≤ meromorphicOrderAt (fun w => F n w - a) z)
    (hfinite : meromorphicOrderAt (fun w => f w - a) z ≠ ⊤) :
    m ≤ mult f (a : Sphere) z := by
  have ho := marked_order_ge_of_locallyUniformlyOn hΩ hz hF hconv a m horder
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hmk : (m : ℤ) ≤ k := by
    rw [← hk] at ho
    exact_mod_cast ho
  simp only [mult_coe, ← hk, WithTop.untop₀_coe]
  omega

theorem marked_order_one_of_analytic {f : ℂ → ℂ} {z a : ℂ}
    (hf : AnalyticAt ℂ f z) (hvalue : f z = a) (hderiv : deriv f z ≠ 0) :
    meromorphicOrderAt (fun w => f w - a) z = (1 : ℤ) := by
  have ho : analyticOrderAt (fun w => f w - a) z = 1 := by
    simpa only [hvalue] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv
  have hs : AnalyticAt ℂ (fun w => f w - a) z := hf.sub analyticAt_const
  rw [hs.meromorphicOrderAt_eq, ho]
  norm_num

theorem marked_mult_one_of_analytic {f : ℂ → ℂ} {z a : ℂ}
    (hf : AnalyticAt ℂ f z) (hvalue : f z = a) (hderiv : deriv f z ≠ 0) :
    mult f (a : Sphere) z = 1 := by
  rw [mult_coe, marked_order_one_of_analytic hf hvalue hderiv]
  change (((1 : ℤ) : WithTop ℤ).untop₀).toNat = 1
  rw [WithTop.untop₀_coe]
  rfl

end ThreeIM
