module

public import RequestProject.ThreeIM.AuxiliaryAmplitudeSystem
public import RequestProject.ThreeIM.TransportCompactProfiles
public import RequestProject.ThreeIM.MarkedMultiplicity

/-!
# Coefficient limits and marked values of the actual amplitudes

The relative profiles are multiplied by their fixed nonzero profiles before
taking limits. No division by a sequence converging to zero is used as a
convergence rule. The finite product at the marked shared value stays
nonzero on every fixed disk.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

private theorem amplitude_constant_tlu (c : ℂ) :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : ℂ) => c) (fun _ => c) atTop univ :=
  (tendsto_const_nhds.tendstoUniformlyOn_const univ).tendstoLocallyUniformlyOn

theorem amplitudeRemainder_locallyUniformly {F : ℕ → ℂ → ℂ} {b : ℂ}
    (a : Fin 3 → ℂ) (j : Fin 3)
    (hF : TendstoLocallyUniformlyOn F (fun _ => b) atTop univ) :
    TendstoLocallyUniformlyOn (fun n z => amplitudeRemainder a j (F n z))
      (fun _ => amplitudeRemainder a j b) atTop univ := by
  classical
  have hprod (s : Finset (Fin 3)) :
      TendstoLocallyUniformlyOn (fun n z => ∏ i ∈ s, (F n z - a i))
        (fun _ => ∏ i ∈ s, (b - a i)) atTop univ := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using amplitude_constant_tlu 1
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      convert (hF.sub (amplitude_constant_tlu (a i))).mul₀ ih
        continuousOn_const continuousOn_const using 1 <;>
        funext n <;> (try funext z) <;> rfl
  exact hprod (Finset.univ.erase j)

theorem amplitudeRemainder_eventually_nonzero {F : ℕ → ℂ → ℂ}
    {a : Fin 3 → ℂ} (ha : Function.Injective a) (j : Fin 3)
    (hF : TendstoLocallyUniformlyOn F (fun _ => a j) atTop univ) (R : ℝ) :
    ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      amplitudeRemainder a j (F n z) ≠ 0 := by
  have hq := amplitudeRemainder_locallyUniformly a j hF
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hq
    (closedBall (0 : ℂ) R) (subset_univ _) (isCompact_closedBall _ _)
  have hpos := norm_pos_iff.mpr (amplitudeRemainder_nonzero ha j)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu _ hpos] with n hn z hz heq
  have hd := hn z hz
  rw [heq, dist_zero_right] at hd
  exact lt_irrefl _ hd

theorem transport_scaled_coefficient_tendsto_profile
    {ε : ℕ → ℝ} {u : ℕ → ℂ → ℂ} {D : ℂ → ℂ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hD : Continuous D) (hD0 : ∀ z, D z ≠ 0)
    (hprof : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ z ∈ transportRect (ε n) R, ‖u n z / ((ε n : ℂ) * D z) - 1‖ ≤ η) :
    TendstoLocallyUniformlyOn (fun n z => u n z / (ε n : ℂ)) D atTop univ := by
  have hrel := transport_profile_tendsto_one hεpos hε hprof
  have hfixed : TendstoLocallyUniformlyOn (fun _ : ℕ => D) D atTop univ :=
    by
      apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
      rw [Metric.tendstoUniformlyOn_iff]
      intro η hη
      exact Eventually.of_forall fun n z _ => by simpa only [dist_self] using hη
  have hmul := (hrel.mul₀ hfixed continuousOn_const hD.continuousOn).congr_right
    (fun z _ => one_mul (D z))
  apply hmul.congr
  intro n z _
  change (u n z / ((ε n : ℂ) * D z)) * D z = u n z / (ε n : ℂ)
  have hε0 : (ε n : ℂ) ≠ 0 := by exact_mod_cast (hεpos n).ne'
  field_simp [hε0, hD0 z]

theorem auxiliary_amplitude_coefficient_limit
    {ε : ℕ → ℝ} {u F : ℕ → ℂ → ℂ} {D : ℂ → ℂ}
    (a : Fin 3 → ℂ) (j : Fin 3)
    (hD : Continuous D)
    (hu : TendstoLocallyUniformlyOn (fun n z => u n z / (ε n : ℂ)) D atTop univ)
    (hF : TendstoLocallyUniformlyOn F (fun _ => a j) atTop univ) :
    TendstoLocallyUniformlyOn
      (fun n z => (u n z / (ε n : ℂ)) * amplitudeRemainder a j (F n z))
      (fun z => D z * amplitudeRemainder a j (a j)) atTop univ :=
  hu.mul₀ (amplitudeRemainder_locallyUniformly a j hF) hD.continuousOn continuousOn_const

theorem auxiliary_amplitude_marked {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G : ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ} (hm : 2 ≤ m)
    (hF : DifferentiableOn ℂ F Ω) (hG : DifferentiableOn ℂ G Ω)
    {z : ℂ} (hz : z ∈ Ω) (hmF : mult F (a j : Sphere) z = 1)
    (hmG : mult G (a j : Sphere) z = m) {ε : ℂ} (hε : ε ≠ 0) :
    (F z - a j) / ε = 0 ∧ (G z - a j) / ε = 0 ∧
      deriv (fun w => (F w - a j) / ε) z ≠ 0 ∧
      deriv (fun w => (G w - a j) / ε) z = 0 := by
  have hf := hF.analyticOnNhd hΩ z hz
  have hg := hG.analyticOnNhd hΩ z hz
  have hfo := order_sub_eq_nat_of_mult_pos F (a j) z (by decide) hmF
  have hgo := order_sub_eq_nat_of_mult_pos G (a j) z (by omega) hmG
  have hfv := analytic_eq_const_of_order_sub_pos hf (by rw [hfo]; norm_num)
  have hgv := analytic_eq_const_of_order_sub_pos hg (by
    rw [hgo]
    exact_mod_cast (by omega : 0 < m))
  have hfd := deriv_ne_zero_of_order_sub_one hf hfo
  have hgd := deriv_eq_zero_of_order_sub_ge_two hg hm hgo
  refine ⟨by rw [hfv]; simp, by rw [hgv]; simp, ?_, ?_⟩
  · rw [deriv_div_const, deriv_sub_const]
    exact div_ne_zero hfd hε
  · rw [deriv_div_const, deriv_sub_const, hgd, zero_div]

end ThreeIM
