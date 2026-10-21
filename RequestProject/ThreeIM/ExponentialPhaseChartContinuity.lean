module

public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Bases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public import RequestProject.ThreeIM.SphereLimits
public import Mathlib.Topology.Sequences
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import RequestProject.ThreeIM.ExponentialUnitRigidity
public import RequestProject.ThreeIM.ExponentialPhaseFibers
import Mathlib.Tactic.FinCases

/-!
# Dense positive imaginary-shift phases for an irrational exponent

The additive-circle irrational-rotation theorem gives integer density.
Compact-group recurrence converts it to positive powers and then to a
strictly increasing subsequence approaching each prescribed unit phase.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Topology

namespace ThreeIM

noncomputable def exponentialUnitPhase (μ : ℝ) (n : ℕ) : Circle :=
  Circle.exp ((n : ℝ) * (-2 * Real.pi * μ))

theorem coe_exponentialUnitPhase (μ : ℝ) (n : ℕ) :
    (exponentialUnitPhase μ n : ℂ) =
      Complex.exp (-(μ : ℂ) * ((n : ℂ) * (2 * Real.pi * Complex.I))) := by
  rw [exponentialUnitPhase, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem denseRange_exponentialUnitPhase {μ : ℝ} (hμ : Irrational μ) :
    DenseRange (exponentialUnitPhase μ) := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hrot : DenseRange (fun n : ℤ => n • ((-μ : ℝ) : AddCircle (1 : ℝ))) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa only [div_one, irrational_neg_iff] using hμ
  have he := e.surjective.denseRange.comp hrot e.continuous
  have hi : DenseRange (fun n : ℤ => Circle.exp (-2 * Real.pi * μ) ^ n) := by
    convert he using 1
    funext n
    change Circle.exp (-2 * Real.pi * μ) ^ n = e (n • ((-μ : ℝ) : AddCircle (1 : ℝ)))
    dsimp only [e]
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul,
      AddCircle.toCircle_apply_mk]
    congr 2
    ring
  have hn := (denseRange_zpow_iff_pow (x := Circle.exp (-2 * Real.pi * μ))).mp hi
  convert hn using 1
  funext n
  exact Circle.exp_natCast_mul (-2 * Real.pi * μ) n

theorem exists_strictMono_exponentialUnitPhase_tendsto {μ : ℝ} (hμ : Irrational μ)
    (η : Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun k => exponentialUnitPhase μ (n k)) atTop (𝓝 η) := by
  let ζ : Circle := Circle.exp (-2 * Real.pi * μ)
  have hpow : (fun n : ℕ => ζ ^ n) = exponentialUnitPhase μ := by
    funext n
    exact (Circle.exp_natCast_mul (-2 * Real.pi * μ) n).symm
  have hn : DenseRange (fun n : ℕ => ζ ^ n) := by
    rw [hpow]
    exact denseRange_exponentialUnitPhase hμ
  have hc : MapClusterPt η atTop (fun n : ℕ => ζ ^ n) :=
    ((mapClusterPt_atTop_pow_tfae η ζ).out 1 3).mpr (hn η)
  obtain ⟨n, hmono, hconv⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hc
  refine ⟨n, hmono, ?_⟩
  have heq : (fun k => exponentialUnitPhase μ (n k)) = (fun k => ζ ^ n k) := by
    funext k
    exact Circle.exp_natCast_mul (-2 * Real.pi * μ) (n k)
  rw [heq]
  exact hconv

theorem exists_strictMono_complex_exponentialPhase_tendsto {μ : ℝ} (hμ : Irrational μ)
    (η : Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => Complex.exp (-(μ : ℂ) * ((n k : ℂ) * (2 * Real.pi * Complex.I))))
        atTop (𝓝 (η : ℂ)) := by
  obtain ⟨n, hmono, hconv⟩ := exists_strictMono_exponentialUnitPhase_tendsto hμ η
  refine ⟨n, hmono, ?_⟩
  have hcoe : Tendsto (fun k => (exponentialUnitPhase μ (n k) : ℂ))
      atTop (𝓝 (η : ℂ)) := (continuous_subtype_val.tendsto η).comp hconv
  simpa only [coe_exponentialUnitPhase] using hcoe

end ThreeIM

end

/-!
# Honest phase models and critical-fiber locking

Continuous point models determine honest sphere values. Connected
phase support fixes the critical fiber and locks the phase maps.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

/-- An honest sphere value reads a continuous local model that agrees with
the raw representative off a discrete set. No value of the raw function at
the center is used. -/
theorem sphereGermValue_eq_model_of_codiscreteWithin
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hg : ContinuousOn g Ω)
    (hEq : f =ᶠ[codiscreteWithin Ω] g) {z : ℂ} (hz : z ∈ Ω) :
    sphereGermValue f z = (g z : OnePoint ℂ) := by
  have hpunctured : f =ᶠ[𝓝[≠] z] g := by
    have heq := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hEq z hz
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ Ω :=
      (show ∀ᶠ w in 𝓝 z, w ∈ Ω from hΩ.mem_nhds hz).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [heq, hmem] with w hw hwΩ
    exact hw.resolve_right fun hnot => hnot hwΩ
  have hcoe : (fun w => (f w : OnePoint ℂ)) =ᶠ[𝓝[≠] z]
      (fun w => (g w : OnePoint ℂ)) :=
    hpunctured.mono fun w hw => congrArg OnePoint.some hw
  exact tendsto_nhds_unique_of_eventuallyEq (tendsto_sphereGermValue (hf z hz))
    ((OnePoint.continuous_coe.tendsto _).comp
      ((hg.continuousAt (hΩ.mem_nhds hz)).mono_left nhdsWithin_le_nhds)) hcoe

/-- Pointwise convergence of the continuous models identifies a point of a
spherical locally uniform limit. A separate locally uniform convergence
theorem for the whole model family is unnecessary. -/
theorem sphere_limit_eq_pointwise_model
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F M : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ}
    (hev : ∀ᶠ n in atTop, MeromorphicOn (F n) Ω ∧ ContinuousOn (M n) Ω ∧
      F n =ᶠ[codiscreteWithin Ω] M n)
    (hconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop Ω)
    {z c : ℂ} (hz : z ∈ Ω) (hmodel : Tendsto (fun n => M n z) atTop (𝓝 c)) :
    H z = (c : OnePoint ℂ) := by
  have hvalues : (fun n => sphereGermValue (F n) z) =ᶠ[atTop]
      (fun n => (M n z : OnePoint ℂ)) := by
    filter_upwards [hev] with n hn
    exact sphereGermValue_eq_model_of_codiscreteWithin hΩ hn.1 hn.2.1 hn.2.2 hz
  exact tendsto_nhds_unique_of_eventuallyEq (hconv.tendsto_at hz)
    ((OnePoint.continuous_coe.tendsto c).comp hmodel) hvalues

/-- The actual critical-defect branch needs only one fixed preimage.
Connected phase support and the coefficient/minimum-one identities first
give three finite CM. Multiplicity at least two at the base phase then
locks every first member to that base spherical map. The phase family and
its growth are intermediate data to be supplied by the actual hull. -/
theorem exponential_phase_first_eq_of_critical
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [PreconnectedSpace P]
    {H K : P → ℂ → OnePoint ℂ} {a : Fin 3 → ℂ} {κ : ℂ}
    (hpair : ∀ p, ExponentialPair a (fun z => chartFiniteMap (H p z))
      (fun z => chartFiniteMap (K p z)) κ)
    (hH : ∀ p, SphereHolomorphicOn (H p) univ)
    (hHnc : ∀ p, ¬ ∃ c : OnePoint ℂ, ∀ z, H p z = c)
    (hsub : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun n => H (s (ψ n))) (H p) atTop univ)
    (hgrowth : ∀ p, ∃ C R₀ : ℝ, ∀ r, R₀ ≤ r →
      charT (fun z => chartFiniteMap (H p z)) r ≤ C * r)
    (p₀ : P) (j : Fin 3) (z : ℂ)
    (hm : 2 ≤ mult (fun w => chartFiniteMap (H p₀ w)) (a j : Sphere) z) :
    ∀ p w, H p w = H p₀ w := by
  have hsg (p : P) :
      sphereGermValue (fun w => chartFiniteMap (H p w)) = H p :=
    funext (sphereGermValue_chartFiniteMap (hH p) (hHnc p))
  have hs : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ TendstoLocallyUniformlyOn
        (fun n => sphereGermValue (fun w => chartFiniteMap (H (s (ψ n)) w)))
        (sphereGermValue (fun w => chartFiniteMap (H p w))) atTop univ := by
    intro p s hsp
    obtain ⟨ψ, hψ, hc⟩ := hsub p s hsp
    exact ⟨ψ, hψ, by simpa only [hsg] using hc⟩
  have hj1 : j ≠ j + 1 := by fin_cases j <;> decide
  have hj2 : j ≠ j + 2 := by fin_cases j <;> decide
  have h12 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  intro p w
  obtain ⟨C, R₀, hbase⟩ := hgrowth p₀
  obtain ⟨D, R₁, hphase⟩ := hgrowth p
  have hlock := sphere_maps_eq_of_three_cm_at_critical (hH p₀) (hH p)
    (hHnc p₀) (hHnc p)
    ((hpair p₀).pair.injective.ne h12)
    ((hpair p₀).pair.injective.ne hj1)
    ((hpair p₀).pair.injective.ne hj2)
    (fun v => (exponential_phase_three_cm_of_subseq hpair hs p₀ p (j + 1) v).1)
    (fun v => (exponential_phase_three_cm_of_subseq hpair hs p₀ p (j + 2) v).1)
    (exponential_phase_three_cm_of_subseq hpair hs p₀ p j z).1 hm hbase hphase
  exact (hlock w).symm

end ThreeIM

end
