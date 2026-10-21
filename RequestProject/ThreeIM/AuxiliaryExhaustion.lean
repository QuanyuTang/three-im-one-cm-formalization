module

public import RequestProject.ThreeIM.AuxiliaryNormality

/-!
# Auxiliary normality on exhausting domains

Each fixed disk needs the prescribed pair data only eventually. Removing a
finite prefix, applying the fixed-domain theorem, and restoring the prefix
give local normality. The proved spherical exhaustion diagonal then gives
normality on the whole plane.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem auxiliary_pairs_isNormalAt_eventually {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    {u v : ℂ → ℂ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hv0 : ∀ z ∈ Ω, v z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop Ω)
    (hsimple : ∀ z ∈ Ω, u z = v z → deriv (fun w => u w / v w) z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    IsNormalAt (range (fun n => sphereGermValue (F n))) z₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hseq
  have hseqN : ∀ n, AuxiliaryPairOn Ω (F (n + N)) (G (n + N))
      (uₙ (n + N)) (vₙ (n + N)) a := fun n => hN (n + N) (Nat.le_add_left N n)
  have huN : TendstoLocallyUniformlyOn (fun n => uₙ (n + N)) u atTop Ω := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := huconv e he z hz
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩
  have hvN : TendstoLocallyUniformlyOn (fun n => vₙ (n + N)) v atTop Ω := by
    intro e he z hz
    obtain ⟨t, ht, hev⟩ := hvconv e he z hz
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩
  exact isNormalAt_range_of_normal_tail (fun n => sphereGermValue (F n)) N
    (auxiliary_pairs_isNormalAt hΩ hseqN hu hv hv0 huN hvN hsimple hz₀)

theorem auxiliary_pairs_isNormal_of_locally_eventually
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    {u v : ℂ → ℂ} (hu : Continuous u) (hv : Continuous v) (hv0 : ∀ z, v z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop univ)
    (hsimple : ∀ z, u z = v z → deriv (fun w => u w / v w) z ≠ 0) :
    IsNormal (range (fun n => sphereGermValue (F n))) univ := by
  apply sphere_isNormal_of_forall_isNormalAt
  intro z
  obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
  exact auxiliary_pairs_isNormalAt_eventually hΩ hev hu.continuousOn hv.continuousOn
    (fun w _ => hv0 w) (huconv.mono (subset_univ Ω)) (hvconv.mono (subset_univ Ω))
    (fun w _ => hsimple w) hzΩ

theorem auxiliary_pairs_isNormal_of_exhaustion {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u v : ℂ → ℂ} (hu : Continuous u) (hv : Continuous v) (hv0 : ∀ z, v z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop univ)
    (hsimple : ∀ z, u z = v z → deriv (fun w => u w / v w) z ≠ 0) :
    IsNormal (range (fun n => sphereGermValue (F n))) univ := by
  refine auxiliary_pairs_isNormal_of_locally_eventually (G := G) (a := a)
    ?_ hu hv hv0 huconv hvconv hsimple
  intro z
  refine ⟨ball z 1, isOpen_ball, mem_ball_self (by norm_num), ?_⟩
  filter_upwards [hr.eventually (eventually_ge_atTop (‖z‖ + 1))] with n hn
  apply (hseq n).restrict
  intro w hw
  rw [mem_ball_zero_iff]
  have hwz : ‖w - z‖ < 1 := mem_ball_iff_norm.mp hw
  have hnorm := norm_sub_norm_le w z
  linarith

end ThreeIM
