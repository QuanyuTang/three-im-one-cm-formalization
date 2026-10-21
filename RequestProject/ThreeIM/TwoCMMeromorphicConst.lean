module

public import RequestProject.ThreeIM.ThetaLocal

/-!
# Meromorphic functions with zero derivative are constant as germs

A pole would force a pole of the derivative. After ruling poles out, the
normal-form representative is entire and the usual constant-function theorem
applies. Junk values are retained only off a discrete exceptional set.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- A meromorphic function whose derivative vanishes codiscretely is a
constant off a discrete set. No nonconstancy hypothesis is required. -/
theorem twoCM_const_of_deriv_zero {K : ℂ → ℂ} (hK : Meromorphic K)
    (hzero : deriv K =ᶠ[codiscrete ℂ] (fun _ => 0)) :
    ∃ c : ℂ, K =ᶠ[codiscrete ℂ] (fun _ => c) := by
  have hnn : ∀ z, 0 ≤ meromorphicOrderAt K z := by
    intro z
    by_contra hnot
    have hneg : meromorphicOrderAt K z < 0 := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hneg)
    have hnneg : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
    have hder : meromorphicOrderAt (deriv K) z = ((n - 1 : ℤ) : WithTop ℤ) :=
      order_deriv_of_order_eq (hK z) (a := 0) (by omega)
        (by simpa only [sub_zero] using hn.symm)
    have htop : meromorphicOrderAt (deriv K) z = ⊤ :=
      meromorphicOrderAt_eq_top_iff.2 (codiscrete_iff_nhdsNE.1 hzero z)
    rw [hder] at htop
    exact WithTop.coe_ne_top htop
  have hKm : MeromorphicOn K univ := fun z _ => hK z
  let H := toMeromorphicNFOn K univ
  have hKH : K =ᶠ[codiscrete ℂ] H := toMeromorphicNFOn_eqOn_codiscrete hKm
  have hHa : ∀ z, AnalyticAt ℂ H z := by
    intro z
    apply (meromorphicNFOn_toMeromorphicNFOn K univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hKm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z))]
    exact hnn z
  have hHd : ∀ z, deriv H z = 0 := by
    intro z
    have hlocal : K =ᶠ[𝓝[≠] z] H := codiscrete_iff_nhdsNE.1 hKH z
    have hlocal0 : deriv K =ᶠ[𝓝[≠] z] (fun _ => 0) := codiscrete_iff_nhdsNE.1 hzero z
    have heq : deriv H =ᶠ[𝓝[≠] z] (fun _ => 0) := hlocal.nhdsNE_deriv.symm.trans hlocal0
    exact tendsto_nhds_unique ((hHa z).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' heq.symm)
  have hconst : ∀ z, H z = H 0 :=
    fun z => is_const_of_deriv_eq_zero (fun w => (hHa w).differentiableAt) hHd z 0
  exact ⟨H 0, hKH.trans (Eventually.of_forall hconst)⟩

/-- Equal logarithmic derivatives of nonzero meromorphic germs give a
nonzero constant ratio, without any hypothesis on zeros or pole sharing. -/
theorem twoCM_const_ratio_of_log_deriv_eq {U V : ℂ → ℂ}
    (hU : Meromorphic U) (hV : Meromorphic V)
    (hUf : ∀ z, meromorphicOrderAt U z ≠ ⊤) (hVf : ∀ z, meromorphicOrderAt V z ≠ ⊤)
    (hlog : (fun z => deriv U z / U z) =ᶠ[codiscrete ℂ] (fun z => deriv V z / V z)) :
    ∃ c : ℂ, c ≠ 0 ∧ U =ᶠ[codiscrete ℂ] (fun z => c * V z) := by
  have hUne : ∀ᶠ z in codiscrete ℂ, U z ≠ 0 := codiscrete_iff_nhdsNE.2 fun z =>
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hU z)).1 (hUf z)
  have hVne : ∀ᶠ z in codiscrete ℂ, V z ≠ 0 := codiscrete_iff_nhdsNE.2 fun z =>
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hV z)).1 (hVf z)
  let Q : ℂ → ℂ := fun z => U z / V z
  have hQm : Meromorphic Q := fun z => (hU z).div (hV z)
  have hQd : deriv Q =ᶠ[codiscrete ℂ] (fun _ => 0) := by
    filter_upwards [eventually_analyticAt_of_meromorphic hU,
      eventually_analyticAt_of_meromorphic hV, hUne, hVne, hlog] with z hUa hVa hUn hVn hl
    have hc : deriv U z * V z - U z * deriv V z = 0 := by
      have hcross := (div_eq_div_iff hUn hVn).1 hl
      linear_combination hcross
    change deriv (fun w => U w / V w) z = 0
    rw [deriv_fun_div hUa.differentiableAt hVa.differentiableAt hVn, hc, zero_div]
  obtain ⟨c, hc⟩ := twoCM_const_of_deriv_zero hQm hQd
  have hc0 : c ≠ 0 := by
    intro hczero
    have hEq : Q =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => 0) := by
      simpa only [hczero, Filter.EventuallyEq] using (codiscrete_iff_nhdsNE.1 hc (0 : ℂ))
    have hQne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q z ≠ 0 := by
      filter_upwards [codiscrete_iff_nhdsNE.1 hUne (0 : ℂ),
        codiscrete_iff_nhdsNE.1 hVne (0 : ℂ)] with z hu hv
      exact div_ne_zero hu hv
    obtain ⟨z, hz, hzn⟩ := (hEq.and hQne).exists
    exact hzn hz
  refine ⟨c, hc0, ?_⟩
  filter_upwards [hc, hVne] with z hz hv
  exact (div_eq_iff hv).1 hz

/-- Integrating an integer-weighted equality of logarithmic derivatives is
expressed by a constant ratio of powers. Exponents zero are permitted. -/
theorem twoCM_power_identity_of_log_deriv_eq {U V : ℂ → ℂ}
    (hU : Meromorphic U) (hV : Meromorphic V)
    (hUf : ∀ z, meromorphicOrderAt U z ≠ ⊤) (hVf : ∀ z, meromorphicOrderAt V z ≠ ⊤)
    (p q : ℕ)
    (hlog : (fun z => (p : ℂ) * (deriv U z / U z)) =ᶠ[codiscrete ℂ]
      (fun z => (q : ℂ) * (deriv V z / V z))) :
    ∃ c : ℂ, c ≠ 0 ∧ (fun z => U z ^ p) =ᶠ[codiscrete ℂ] (fun z => c * V z ^ q) := by
  have hUp : Meromorphic (fun z => U z ^ p) := fun z => (hU z).pow p
  have hVq : Meromorphic (fun z => V z ^ q) := fun z => (hV z).pow q
  have hUpf : ∀ z, meromorphicOrderAt (fun w => U w ^ p) z ≠ ⊤ := by
    intro z
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hUp z)).2
    exact ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hU z)).1 (hUf z)).mono
      fun w hw => pow_ne_zero p hw
  have hVqf : ∀ z, meromorphicOrderAt (fun w => V w ^ q) z ≠ ⊤ := by
    intro z
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hVq z)).2
    exact ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hV z)).1 (hVf z)).mono
      fun w hw => pow_ne_zero q hw
  apply twoCM_const_ratio_of_log_deriv_eq hUp hVq hUpf hVqf
  filter_upwards [eventually_analyticAt_of_meromorphic hU,
    eventually_analyticAt_of_meromorphic hV, hlog] with z hUa hVa hl
  change logDeriv (fun w => U w ^ p) z = logDeriv (fun w => V w ^ q) z
  rw [logDeriv_fun_pow hUa.differentiableAt p, logDeriv_fun_pow hVa.differentiableAt q]
  exact hl

end ThreeIM
