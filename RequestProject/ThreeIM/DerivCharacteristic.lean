module

public import RequestProject.ThreeIM.Holomorphic

/-!
# The characteristic of the derivative (part of External theorem 2.3)

For a nonconstant meromorphic `h` on `ℂ` and `r ≥ 1` we prove
`T(r, h') ≤ 2 T(r, h) + m(r, h'/h)`.

* Poles: at a pole of order `k` of `h`, `h'` has a pole of order `k + 1 ≤ 2k`, and `h'` is
  holomorphic wherever `h` is; hence `N(r, ∞; h') ≤ 2 N(r, ∞; h)`.
* Proximity: `h' = h · (h'/h)` off the discrete zero set of `h`, so
  `m(r, h') ≤ m(r, h) + m(r, h'/h)`.

Combined with the logarithmic derivative lemma `m(r, h'/h) = O(log(e + r T(r, h)))`, this gives
the second estimate of External theorem 2.3, `T(r, h') ≤ 2T(r, h) + O(log(e + r T(r, h)))`
(see `ext_charT_deriv_le` in `External.lean`).
-/

@[expose] public section

open Filter Topology Set

namespace ThreeIM

lemma order_deriv_nonneg_of_order_nonneg {h : ℂ → ℂ} {z : ℂ} (hh : MeromorphicAt h z)
    (h0 : 0 ≤ meromorphicOrderAt h z) : 0 ≤ meromorphicOrderAt (deriv h) z := by
  obtain ⟨G, hGa, hG⟩ : ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ h =ᶠ[𝓝[≠] z] G := by
    rcases eq_or_ne (meromorphicOrderAt h z) ⊤ with htop | hne
    · exact ⟨0, analyticAt_const, (meromorphicOrderAt_eq_top_iff.1 htop)⟩
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
      obtain ⟨g, hga, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hh).1 hn.symm
      have hn0 : 0 ≤ n := by rw [← hn] at h0; exact_mod_cast h0
      refine ⟨fun w => (w - z) ^ n.toNat * g w, by fun_prop, ?_⟩
      filter_upwards [hfg] with w hw
      rw [hw, smul_eq_mul, ← zpow_natCast, Int.toNat_of_nonneg hn0]
  rw [meromorphicOrderAt_congr hG.nhdsNE_deriv]
  exact hGa.deriv.meromorphicOrderAt_nonneg

/-- The pole order of `h'` at a point is at most twice the pole order of `h`. -/
lemma negPart_order_deriv_le {h : ℂ → ℂ} {z : ℂ} (hh : MeromorphicAt h z) :
    ((meromorphicOrderAt (deriv h) z).untop₀)⁻ ≤ 2 * ((meromorphicOrderAt h z).untop₀)⁻ := by
  rcases le_or_gt 0 (meromorphicOrderAt h z) with h0 | h0
  · have h1 := order_deriv_nonneg_of_order_nonneg hh h0
    have e1 : ((meromorphicOrderAt (deriv h) z).untop₀)⁻ = 0 := by
      rw [negPart_eq_zero]
      exact WithTop.untop₀_nonneg.2 h1
    rw [e1]; positivity
  · have hne : meromorphicOrderAt h z ≠ ⊤ := h0.ne_top
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    have hn0 : n < 0 := by rw [← hn] at h0; exact_mod_cast h0
    have hd := order_deriv_of_order_eq (a := 0) hh hn0.ne (by simpa using hn.symm)
    rw [hd, ← hn, WithTop.untop₀_coe, WithTop.untop₀_coe]
    simp only [negPart_eq_neg.2 hn0.le, negPart_eq_neg.2 (show n - 1 ≤ 0 by omega)]
    omega

/-- `N(r, ∞; h') ≤ 2 N(r, ∞; h)` for `r ≥ 1`. -/
lemma logCounting_deriv_top_le {h : ℂ → ℂ} (hh : Meromorphic h) {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.logCounting (deriv h) ⊤ r ≤ 2 * ValueDistribution.logCounting h ⊤ r := by
  have hD : (MeromorphicOn.divisor (deriv h) univ)⁻ ≤ 2 • (MeromorphicOn.divisor h univ)⁻ := by
    intro z
    have hm : MeromorphicOn h univ := fun x _ => hh x
    have hm' : MeromorphicOn (deriv h) univ := fun x _ => (hh x).deriv
    simp only [Function.locallyFinsuppWithin.negPart_apply,
      Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
      MeromorphicOn.divisor_apply hm (mem_univ z), MeromorphicOn.divisor_apply hm' (mem_univ z),
      nsmul_eq_mul, Nat.cast_ofNat]
    exact negPart_order_deriv_le (hh z)
  rw [ValueDistribution.logCounting_top, ValueDistribution.logCounting_top]
  have := Function.locallyFinsuppWithin.logCounting_le hD hr
  rw [map_nsmul] at this
  simpa using this

/-- `m(r, h') ≤ m(r, h) + m(r, h'/h)`. -/
lemma proximity_deriv_top_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.proximity (deriv h) ⊤ r ≤ ValueDistribution.proximity h ⊤ r +
      ValueDistribution.proximity (fun z => deriv h z / (h z - 0)) ⊤ r := by
  have hm : Meromorphic h := fun x => hh.1 x (mem_univ x)
  have hne : ∀ᶠ z in codiscrete ℂ, h z ≠ 0 := by
    rw [Filter.Eventually, mem_codiscrete]
    intro x
    rw [disjoint_principal_right, compl_compl]
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm x)).1
      (by simpa using hh.2 x (mem_univ x) 0)
  have hfg : deriv h =ᶠ[codiscrete ℂ] h * (fun z => deriv h z / (h z - 0)) := by
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, sub_zero]
    field_simp
  rw [ValueDistribution.proximity_congr_codiscrete hfg hr]
  have hq : Meromorphic (fun z => deriv h z / (h z - 0)) := by
    simp only [sub_zero]; exact hm.deriv.div hm
  exact ValueDistribution.proximity_mul_top_le hm hq r

/-- **Characteristic of the derivative**: for a nonconstant meromorphic `h` on `ℂ` and `r ≥ 1`,
`T(r, h') ≤ 2 T(r, h) + m(r, h'/h)`. -/
theorem charT_deriv_le {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) {r : ℝ} (hr : 1 ≤ r) :
    charT (deriv h) r ≤ 2 * charT h r +
      ValueDistribution.proximity (fun z => deriv h z / (h z - 0)) ⊤ r := by
  have hm : Meromorphic h := fun x => hh.1 x (mem_univ x)
  have h1 := proximity_deriv_top_le hh (show r ≠ 0 by linarith)
  have h2 := logCounting_deriv_top_le hm hr
  have h3 : 0 ≤ ValueDistribution.proximity h ⊤ r := ValueDistribution.proximity_nonneg r
  simp only [charT, ValueDistribution.characteristic, Pi.add_apply]
  linarith

end ThreeIM
