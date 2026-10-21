module

public import RequestProject.ThreeIM.MarkedDerivative

/-! # The derivative formula from marked finite orders -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem analytic_eq_const_of_order_sub_pos {f : ℂ → ℂ} {z a : ℂ}
    (hf : AnalyticAt ℂ f z) (hpos : 0 < meromorphicOrderAt (fun w => f w - a) z) :
    f z = a := by
  have ha : AnalyticAt ℂ (fun w => f w - a) z := hf.sub analyticAt_const
  have ht := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).2 hpos
  exact sub_eq_zero.1 (tendsto_nhds_unique
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht)

theorem deriv_ne_zero_of_order_sub_one {f : ℂ → ℂ} {z a : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hm : meromorphicOrderAt (fun w => f w - a) z = (1 : ℤ)) : deriv f z ≠ 0 := by
  have ho := order_deriv_of_order_sub hf.meromorphicAt (m := 1) (by decide) hm
  have ho0 : meromorphicOrderAt (deriv f) z = 0 := by simpa using ho
  exact hf.deriv.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.1 ho0

theorem deriv_eq_zero_of_order_sub_ge_two {f : ℂ → ℂ} {z a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f z) (hm : 2 ≤ m)
    (horder : meromorphicOrderAt (fun w => f w - a) z = (m : ℤ)) : deriv f z = 0 := by
  have ho := order_deriv_of_order_sub hf.meromorphicAt (m := m) (by omega) horder
  have hpos : 0 < meromorphicOrderAt (deriv f) z := by
    rw [ho]
    exact_mod_cast (by omega : (0 : ℤ) < (m : ℤ) - 1)
  have ht := (tendsto_zero_iff_meromorphicOrderAt_pos hf.deriv.meromorphicAt).2 hpos
  exact tendsto_nhds_unique (hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht

theorem marked_derivative_of_orders {f g u : ℂ → ℂ} {z : ℂ}
    {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : Fin 3} {m : ℕ} (hm : 2 ≤ m)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hford : meromorphicOrderAt (fun w => f w - a j) z = (1 : ℤ))
    (hgord : meromorphicOrderAt (fun w => g w - a j) z = (m : ℤ))
    (hu : ContinuousAt u z) (hU : auxU a f g =ᶠ[𝓝[≠] z] u) :
    deriv f z ≠ 0 ∧ deriv f z = (∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z := by
  have hf0 : f z = a j := analytic_eq_const_of_order_sub_pos hf (by rw [hford]; norm_num)
  have hg0 : g z = a j := analytic_eq_const_of_order_sub_pos hg (by
    rw [hgord]
    exact_mod_cast (by omega : 0 < m))
  have hf' := deriv_ne_zero_of_order_sub_one hf hford
  exact ⟨hf', deriv_eq_prod_auxU_of_simple_analytic ha hf hg hf0 hg0 hf'
    (deriv_eq_zero_of_order_sub_ge_two hg hm hgord) hu hU⟩

theorem order_sub_eq_nat_of_mult_pos (f : ℂ → ℂ) (a z : ℂ) {m : ℕ}
    (hm : 0 < m) (hmult : mult f (a : Sphere) z = m) :
    meromorphicOrderAt (fun w => f w - a) z = (m : ℤ) := by
  have hfinite : meromorphicOrderAt (fun w => f w - a) z ≠ ⊤ := by
    intro ht
    have he : 0 = m := by simpa only [mult_coe, ht, WithTop.untop₀_top, Int.toNat_zero] using hmult
    omega
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hfinite
  have hkm : k.toNat = m := by
    simpa only [mult_coe, ← hk, WithTop.untop₀_coe] using hmult
  have hkpos : 0 < k := Int.pos_iff_toNat_pos.2 (by rwa [hkm])
  have heq : (k.toNat : ℤ) = (m : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hkm
  rw [Int.toNat_of_nonneg hkpos.le] at heq
  rw [← hk, heq]

theorem marked_derivative_of_mult {f g u : ℂ → ℂ} {z : ℂ}
    {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : Fin 3} {m : ℕ} (hm : 2 ≤ m)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hmf : mult f (a j : Sphere) z = 1) (hmg : mult g (a j : Sphere) z = m)
    (hu : ContinuousAt u z) (hU : auxU a f g =ᶠ[𝓝[≠] z] u) :
    deriv f z ≠ 0 ∧ deriv f z = (∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z :=
  marked_derivative_of_orders ha hm hf hg
    (order_sub_eq_nat_of_mult_pos f (a j) z (by decide) hmf)
    (order_sub_eq_nat_of_mult_pos g (a j) z (by omega) hmg) hu hU

end ThreeIM
