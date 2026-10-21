module

public import RequestProject.ThreeIM.SimpleLocalInjectivity

/-!
# The Phi coefficient at a diagonal holomorphic limit

The common difference is canceled codiscretely before taking the limit.
Consequently the argument does not divide two auxiliary functions whose
limits are both zero.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem auxPhi_diagonal_limit_eq_one {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {z : ℂ} (hz : z ∈ Ω) (a : Fin 3 → ℂ)
    {F G φ : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {c : ℂ}
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hG : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) Ω)
    (hFconv : TendstoLocallyUniformlyOn F H atTop Ω)
    (hGconv : TendstoLocallyUniformlyOn G H atTop Ω)
    (hHderiv : deriv H z ≠ 0) (hHP : cubicP a (H z) ≠ 0)
    (hp : ∀ᶠ n in atTop, NormalizedPair Ω (F n) (G n) a)
    (hΦ : ∀ᶠ n in atTop, auxPhi a (F n) (G n) =ᶠ[codiscreteWithin Ω] φ n)
    (hφ : ∀ᶠ n in atTop, ContinuousAt (φ n) z)
    (hφconv : Tendsto (fun n => φ n z) atTop (𝓝 c)) : c = 1 := by
  have hdf := (hFconv.deriv hF hΩ).tendsto_at hz
  have hdg := (hGconv.deriv hG hΩ).tendsto_at hz
  have hPF := ((auxiliary_continuous_cubicP a).tendsto (H z)).comp
    (hFconv.tendsto_at hz)
  have hPG := ((auxiliary_continuous_cubicP a).tendsto (H z)).comp
    (hGconv.tendsto_at hz)
  have hnz : deriv H z * cubicP a (H z) ≠ 0 := mul_ne_zero hHderiv hHP
  have hden := (hdg.mul hPF).eventually_ne hnz
  have hcenter : ∀ᶠ n in atTop, φ n z =
      deriv (F n) z * cubicP a (G n z) / (deriv (G n) z * cubicP a (F n z)) := by
    filter_upwards [hF, hG, hp, hΦ, hφ, hden] with n hnF hnG hnp hnΦ hnφ hnd
    have hFa := hnF.analyticOnNhd hΩ
    have hGa := hnG.analyticOnNhd hΩ
    have hFc := hFa.continuousOn.continuousAt (hΩ.mem_nhds hz)
    have hGc := hGa.continuousOn.continuousAt (hΩ.mem_nhds hz)
    have hdFc := hFa.deriv.continuousOn.continuousAt (hΩ.mem_nhds hz)
    have hdGc := hGa.deriv.continuousOn.continuousAt (hΩ.mem_nhds hz)
    have hPFc := (auxiliary_continuous_cubicP a).continuousAt.comp hFc
    have hPGc := (auxiliary_continuous_cubicP a).continuousAt.comp hGc
    have hQc : ContinuousAt
        (fun w => deriv (F n) w * cubicP a (G n w) /
          (deriv (G n) w * cubicP a (F n w))) z :=
      (hdFc.mul hPGc).div (hdGc.mul hPFc) hnd
    have hlocal := auxiliary_local_of_codiscreteWithin hΩ
      (hnΦ.symm.trans (auxPhi_cancel_difference hnp)) hz
    exact tendsto_nhds_unique_of_eventuallyEq
      (hnφ.tendsto.mono_left nhdsWithin_le_nhds)
      (hQc.tendsto.mono_left nhdsWithin_le_nhds) hlocal
  have hquot : Tendsto
      (fun n => deriv (F n) z * cubicP a (G n z) /
        (deriv (G n) z * cubicP a (F n z))) atTop (𝓝 (1 : ℂ)) := by
    convert (hdf.mul hPG).div (hdg.mul hPF) hnz using 1 <;>
      (try simp only [div_self hnz]) <;> ext n <;> rfl
  exact tendsto_nhds_unique_of_eventuallyEq hφconv hquot hcenter

/-- A nonconstant meromorphic function has an ordinary point where both its
derivative and the marked cubic are nonzero. No entire-growth hypothesis is
required for this choice. -/
theorem exists_regular_cubic_point {H : ℂ → ℂ} (hH : IsNonconstMeroOn H univ)
    (a : Fin 3 → ℂ) : ∃ z, deriv H z ≠ 0 ∧ cubicP a (H z) ≠ 0 := by
  have hM := hH.1 0 (mem_univ (0 : ℂ))
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv H z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hM.deriv).mp
      (order_deriv_of_nonconst hH (mem_univ (0 : ℂ))).1
  have hn (c : ℂ) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z - c ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hM.sub analyticAt_const.meromorphicAt)).mp (hH.2 0 (mem_univ (0 : ℂ)) c)
  have hevent : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv H z ≠ 0 ∧ cubicP a (H z) ≠ 0 := by
    filter_upwards [hd, hn (a 0), hn (a 1), hn (a 2)] with z hdz h0 h1 h2
    exact ⟨hdz, mul_ne_zero (mul_ne_zero h0 h1) h2⟩
  exact hevent.exists

end ThreeIM
