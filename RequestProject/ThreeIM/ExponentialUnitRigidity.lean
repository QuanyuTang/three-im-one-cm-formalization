module

public import RequestProject.ThreeIM.ClusterFactorControl
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import RequestProject.ThreeIM.CMPersistence
public import RequestProject.ThreeIM.TwoCMCharTransforms
public import RequestProject.ThreeIM.SphereGerm
public import RequestProject.ThreeIM.SphereHolomorphicBridge
public import RequestProject.ThreeIM.MarkedMultiplicity

/-!
# Entire units of linear characteristic

The actual divisor-factor estimate bounds the logarithmic derivative of an
entire nowhere-zero function with linear characteristic. Liouville then
gives its exponential-affine form. No global logarithm, Hadamard theorem,
or assertion about arbitrary assigned singular values is needed.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real ValueDistribution NoWanderingDomains
open scoped BigOperators

namespace ThreeIM

theorem entire_unit_order_eq_zero {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0) (z : ℂ) :
    meromorphicOrderAt Q z = 0 :=
  ((hQ z (mem_univ z)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 (hQ0 z)

namespace DivisorFactorData

/-- An actual entire unit has no roots or poles in the extracted support. -/
theorem support_eq_empty_of_entire_unit {Q : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Q ρ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hQ0 : ∀ z, Q z ≠ 0) : D.support = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzb : z ∈ closedBall (0 : ℂ) ρ := by
    simpa only [mem_closedBall, dist_zero_right] using D.roots z hz
  have he : D.exponent z = 0 := by
    rw [D.exponent_eq_order z hzb, entire_unit_order_eq_zero hQ hQ0 z]
    rfl
  exact (D.support_iff z).mp hz he

/-- The codiscrete factor identity extends to the entire open extraction
disk by continuity. In particular no raw values at a removed point enter
the logarithmic-derivative argument. -/
theorem eqOn_g_of_entire_unit {Q : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Q ρ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hQ0 : ∀ z, Q z ≠ 0) : EqOn Q D.g (ball 0 ρ) := by
  classical
  have hfac : Q =ᶠ[codiscreteWithin (closedBall (0 : ℂ) ρ)] D.g := by
    simpa only [D.support_eq_empty_of_entire_unit hQ hQ0,
      Finset.prod_empty, one_mul] using D.factor
  intro z hz
  have hzc : z ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hz
  have hp : Q =ᶠ[𝓝[≠] z] D.g := by
    have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfac z hzc
    have hballmem : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) ρ := isOpen_ball.mem_nhds hz
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ closedBall (0 : ℂ) ρ :=
      (hballmem.mono fun _ hw => ball_subset_closedBall hw).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [h, hmem] with w hw hwc
    exact hw.resolve_right fun hn => hn hwc
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hQ z (mem_univ z)).continuousAt.mono_left nhdsWithin_le_nhds)
    ((D.g_analytic z hzc).continuousAt.mono_left nhdsWithin_le_nhds) hp

theorem deriv_H_eq_logDeriv_of_entire_unit {Q : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Q ρ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hQ0 : ∀ z, Q z ≠ 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    deriv D.H z = logDeriv Q z := by
  have heq : Q =ᶠ[𝓝 z] D.g := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact D.eqOn_g_of_entire_unit hQ hQ0 hw
  rw [D.deriv_H_eq_logDeriv_g hz, ← heq.deriv_eq,
    ← D.eqOn_g_of_entire_unit hQ hQ0 hz]
  rfl

end DivisorFactorData

/-- First-main inversion converts an eventual one-sided linear bound into
an eventual paired bound, with a nonnegative coefficient. -/
theorem characteristic_pair_linear_of_linear {Q : ℂ → ℂ} (hQ : Meromorphic Q)
    {C R₀ : ℝ} (hgrowth : ∀ r, R₀ ≤ r → charT Q r ≤ C * r) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ r, max 1 R₀ ≤ r →
      charT Q r + charT Q⁻¹ r ≤ C' * r := by
  let K : ℝ := max |log ‖Q 0‖| |log ‖meromorphicTrailingCoeffAt Q 0‖|
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨2 * |C| + K, by positivity, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 ≤ r := by linarith
  have hg := hgrowth r ((le_max_right _ _).trans hr)
  have hi := characteristic_sub_characteristic_inv_le (R := r) hQ
  change |charT Q r - charT Q⁻¹ r| ≤ K at hi
  have hi' := (abs_le.mp hi).1
  have hCr : C * r ≤ |C| * r := mul_le_mul_of_nonneg_right (le_abs_self C) hr0
  have hKr : K ≤ K * r := le_mul_of_one_le_right hK hr1
  nlinarith

/-- The coupled factor bound at radii 4R and 5R gives a global bound for
the genuinely entire logarithmic derivative. -/
theorem logDeriv_bounded_of_entire_unit_pair_linear {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {C R₀ : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ r, R₀ ≤ r → charT Q r + charT Q⁻¹ r ≤ C * r) :
    ∀ z, ‖logDeriv Q z‖ ≤ 640 * C + 40 := by
  classical
  intro z
  let R : ℝ := max 1 (max R₀ ‖z‖)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : R₀ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hzR : ‖z‖ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRp : 0 < R := by linarith
  have hQm : MeromorphicOn Q univ := fun w _ => (hQ w (mem_univ w)).meromorphicAt
  obtain ⟨D⟩ := exists_divisorFactorData (F := Q) (R := 4 * R) (by positivity)
    (fun w _ => hQm w (mem_univ w)) (fun w _ => by
      rw [entire_unit_order_eq_zero hQ hQ0 w]
      exact WithTop.zero_ne_top)
  have hds : D.support = ∅ := D.support_eq_empty_of_entire_unit hQ hQ0
  have hbd := D.norm_deriv_H_le_characteristic_gap hQm
    (show 1 ≤ 4 * R by linarith) (show 4 * R ≤ 5 * R by linarith) hRp
    (z := z) (show ‖z‖ ≤ 4 * R - 2 * R by linarith)
  have hzb : z ∈ ball (0 : ℂ) (4 * R) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  rw [D.deriv_H_eq_logDeriv_of_entire_unit hQ hQ0 hzb] at hbd
  simp only [hds, Finset.sum_empty, mul_zero, zero_mul, add_zero] at hbd
  change ‖logDeriv Q z‖ ≤
    8 * (2 * (2 * (4 * R) / R * (charT Q (5 * R) + charT Q⁻¹ (5 * R))) + 5) / R at hbd
  have hbudget := hgrowth (5 * R) (by linarith)
  have hstep :
      8 * (2 * (2 * (4 * R) / R * (charT Q (5 * R) + charT Q⁻¹ (5 * R))) + 5) / R ≤
      8 * (2 * (2 * (4 * R) / R * (C * (5 * R))) + 5) / R := by
    gcongr <;> first | exact hbudget | positivity
  have halg : 8 * (2 * (2 * (4 * R) / R * (C * (5 * R))) + 5) / R =
      640 * C + 40 / R := by
    field_simp [hRp.ne']
    <;> ring
  have hlast : 40 / R ≤ 40 := (div_le_iff₀ hRp).2 (by linarith)
  exact hbd.trans (hstep.trans (by rw [halg]; linarith))

theorem logDeriv_const_of_entire_unit_linear {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {C R₀ : ℝ} (hgrowth : ∀ r, R₀ ≤ r → charT Q r ≤ C * r) :
    ∀ z, logDeriv Q z = logDeriv Q 0 := by
  obtain ⟨C', hC', hpair⟩ := characteristic_pair_linear_of_linear
    (fun z => (hQ z (mem_univ z)).meromorphicAt) hgrowth
  have hb := logDeriv_bounded_of_entire_unit_pair_linear hQ hQ0 hC' hpair
  have hd : Differentiable ℂ (logDeriv Q) := by
    intro z
    exact (hQ.deriv z (mem_univ z)).differentiableAt.div
      (hQ z (mem_univ z)).differentiableAt (hQ0 z)
  have hbounded : Bornology.IsBounded (range (logDeriv Q)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨640 * C' + 40, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hb z
  exact fun z => hd.apply_eq_apply_of_bounded hbounded z 0

/-- A constant logarithmic derivative determines an entire unit from its
value at any base point. -/
theorem entire_unit_eq_exp_of_logDeriv_eq_const {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {A : ℂ} (hA : ∀ z, logDeriv Q z = A) (z₀ : ℂ) :
    ∀ z, Q z = Q z₀ * Complex.exp (A * (z - z₀)) := by
  let E : ℂ → ℂ := fun z => Complex.exp (A * (z - z₀))
  have hE : Differentiable ℂ E := by dsimp [E]; fun_prop
  have hEn : ∀ z ∈ (univ : Set ℂ), E z ≠ 0 := by
    intro z _
    exact Complex.exp_ne_zero _
  have hlogE (z : ℂ) : logDeriv E z = A := by
    have hd : HasDerivAt E (Complex.exp (A * (z - z₀)) * A) z := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id z).sub_const z₀).const_mul A).cexp
    rw [logDeriv_apply, hd.deriv]
    dsimp [E]
    field_simp
  have heq : EqOn (logDeriv Q) (logDeriv E) univ :=
    fun z _ => (hA z).trans (hlogE z).symm
  obtain ⟨c, -, hc⟩ := (logDeriv_eqOn_iff hQ.differentiableOn hE.differentiableOn
    isOpen_univ isPreconnected_univ hEn (fun z _ => hQ0 z)).mp heq
  have hcz : c = Q z₀ := by
    have hh := hc (mem_univ z₀)
    simpa only [Pi.smul_apply, smul_eq_mul, E, sub_self, mul_zero,
      Complex.exp_zero, mul_one] using hh.symm
  intro z
  simpa only [Pi.smul_apply, smul_eq_mul, E, hcz] using hc (mem_univ z)

theorem entire_unit_exp_affine_of_linear_characteristic {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {C R₀ : ℝ} (hgrowth : ∀ r, R₀ ≤ r → charT Q r ≤ C * r) (z₀ : ℂ) :
    ∀ z, Q z = Q z₀ * Complex.exp (logDeriv Q z₀ * (z - z₀)) := by
  apply entire_unit_eq_exp_of_logDeriv_eq_const hQ hQ0 (z₀ := z₀)
  intro z
  exact (logDeriv_const_of_entire_unit_linear hQ hQ0 hgrowth z).trans
    (logDeriv_const_of_entire_unit_linear hQ hQ0 hgrowth z₀).symm

theorem entire_unit_exp_normalized_of_linear_characteristic {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {C R₀ : ℝ} (hgrowth : ∀ r, R₀ ≤ r → charT Q r ≤ C * r)
    {z₀ : ℂ} (hz₀ : Q z₀ = 1) :
    ∀ z, Q z = Complex.exp (deriv Q z₀ * (z - z₀)) := by
  simpa only [logDeriv_apply, hz₀, div_one, one_mul] using
    entire_unit_exp_affine_of_linear_characteristic hQ hQ0 hgrowth z₀

theorem entire_unit_eq_one_of_linear_characteristic_of_critical {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q univ) (hQ0 : ∀ z, Q z ≠ 0)
    {C R₀ : ℝ} (hgrowth : ∀ r, R₀ ≤ r → charT Q r ≤ C * r)
    {z₀ : ℂ} (hz₀ : Q z₀ = 1) (hd : deriv Q z₀ = 0) : ∀ z, Q z = 1 := by
  simpa only [hd, zero_mul, Complex.exp_zero] using
    entire_unit_exp_normalized_of_linear_characteristic hQ hQ0 hgrowth hz₀

end ThreeIM

end

/-!
# The genuine entire unit comparing two three-CM functions

The cross-ratio quotient is normalized before it is called a unit. The
finite fiber multiplicities determine its orders, even at poles of either
original function. The local value and derivative conclusions use actual
analytic representatives at the third finite target.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real ValueDistribution NoWanderingDomains

namespace ThreeIM

noncomputable def finiteTargetRatio (f : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ :=
  fun z => (f z - a) / (f z - b)

noncomputable def exponentialCrossRatioUnit (f F : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z) univ

theorem finiteTargetRatio_meromorphic {f : ℂ → ℂ} (hf : Meromorphic f) (a b : ℂ) :
    Meromorphic (finiteTargetRatio f a b) :=
  fun z => ((hf z).sub (MeromorphicAt.const a z)).div ((hf z).sub (MeromorphicAt.const b z))

theorem finiteTargetRatio_order {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    (a b z : ℂ) :
    meromorphicOrderAt (finiteTargetRatio f a b) z =
      (((mult f (a : Sphere) z : ℤ) - (mult f (b : Sphere) z : ℤ) : ℤ) : WithTop ℤ) := by
  have hfa : MeromorphicAt (fun w => f w - a) z :=
    (hf.1 z (mem_univ z)).sub (MeromorphicAt.const a z)
  have hfb : MeromorphicAt (fun w => f w - b) z :=
    (hf.1 z (mem_univ z)).sub (MeromorphicAt.const b z)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hf.2 z (mem_univ z) a)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hf.2 z (mem_univ z) b)
  have hfun : finiteTargetRatio f a b = (fun w => f w - a) * (fun w => f w - b)⁻¹ := by
    ext w
    exact div_eq_mul_inv _ _
  have ho : meromorphicOrderAt (finiteTargetRatio f a b) z = ((m - n : ℤ) : WithTop ℤ) := by
    rw [hfun, meromorphicOrderAt_mul hfa hfb.inv, meromorphicOrderAt_inv, ← hm, ← hn,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    rfl
  rw [ho]
  congr 1
  by_cases hpole : meromorphicOrderAt f z < 0
  · have hmn : m = n := by
      apply WithTop.coe_injective
      exact hm.trans ((order_sub_const_of_neg hpole a).trans
        ((order_sub_const_of_neg hpole b).symm.trans hn.symm))
    subst n
    simp only [mult_coe, ← hm, ← hn, WithTop.untop₀_coe, sub_self]
  · have hnneg := le_of_not_gt hpole
    have hm0 : 0 ≤ m := by
      have hh := order_sub_const_nonneg (hf.1 z (mem_univ z)) hnneg a
      rw [← hm] at hh
      exact_mod_cast hh
    have hn0 : 0 ≤ n := by
      have hh := order_sub_const_nonneg (hf.1 z (mem_univ z)) hnneg b
      rw [← hn] at hh
      exact_mod_cast hh
    simp only [mult_coe, ← hm, ← hn, WithTop.untop₀_coe,
      Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0]

theorem finiteTargetRatio_order_ne_top {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    (a b z : ℂ) : meromorphicOrderAt (finiteTargetRatio f a b) z ≠ ⊤ := by
  rw [finiteTargetRatio_order hf a b z]
  exact WithTop.coe_ne_top

theorem exponentialCrossRatioUnit_analytic_nonzero {f F : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ) (a b : ℂ)
    (ha : ∀ z, mult f (a : Sphere) z = mult F (a : Sphere) z)
    (hb : ∀ z, mult f (b : Sphere) z = mult F (b : Sphere) z) :
    AnalyticOnNhd ℂ (exponentialCrossRatioUnit f F a b) univ ∧
      ∀ z, exponentialCrossRatioUnit f F a b z ≠ 0 := by
  have hrf := finiteTargetRatio_meromorphic (fun z => hf.1 z (mem_univ z)) a b
  have hrF := finiteTargetRatio_meromorphic (fun z => hF.1 z (mem_univ z)) a b
  have hunit := analytic_unit_nf_quotient (Ω := univ) hrf.meromorphicOn hrF.meromorphicOn
    (fun z _ => by rw [finiteTargetRatio_order hf, finiteTargetRatio_order hF, ha, hb])
    (fun z _ => finiteTargetRatio_order_ne_top hf a b z)
  exact ⟨hunit.1, fun z => hunit.2 z (mem_univ z)⟩

theorem exponentialCrossRatioUnit_eq_one_at_third_target {f F : ℂ → ℂ} {a b c z : ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    (hfa : AnalyticAt ℂ f z) (hFa : AnalyticAt ℂ F z)
    (hfc : f z = c) (hFc : F z = c) (hca : c ≠ a) (hcb : c ≠ b) :
    exponentialCrossRatioUnit f F a b z = 1 := by
  have hrf := finiteTargetRatio_meromorphic (fun w => hf.1 w (mem_univ w)) a b
  have hrF := finiteTargetRatio_meromorphic (fun w => hF.1 w (mem_univ w)) a b
  have hfb : f z - b ≠ 0 := by rw [hfc]; exact sub_ne_zero.mpr hcb
  have hFb : F z - b ≠ 0 := by rw [hFc]; exact sub_ne_zero.mpr hcb
  have hFv : finiteTargetRatio F a b z ≠ 0 := by
    exact div_ne_zero (by rw [hFc]; exact sub_ne_zero.mpr hca) hFb
  have hh := nf_quotient_eq_at_of_ne_zero (hrf.meromorphicOn.div hrF.meromorphicOn)
    (mem_univ z) ((hfa.sub analyticAt_const).div (hfa.sub analyticAt_const) hfb)
    ((hFa.sub analyticAt_const).div (hFa.sub analyticAt_const) hFb) hFv
  change exponentialCrossRatioUnit f F a b z =
    finiteTargetRatio f a b z / finiteTargetRatio F a b z at hh
  rw [hh]
  have he : finiteTargetRatio f a b z = finiteTargetRatio F a b z := by
    simp only [finiteTargetRatio, hfc, hFc]
  rw [he, div_self hFv]

/-- The normalized quotient's derivative vanishes at a common critical
point over the third target. This is the actual-defect phase-locking input. -/
theorem exponentialCrossRatioUnit_deriv_eq_zero_at_common_critical
    {f F : ℂ → ℂ} {a b c z : ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    (hfa : AnalyticAt ℂ f z) (hFa : AnalyticAt ℂ F z)
    (hfc : f z = c) (hFc : F z = c) (hca : c ≠ a) (hcb : c ≠ b)
    (hfd : deriv f z = 0) (hFd : deriv F z = 0) :
    deriv (exponentialCrossRatioUnit f F a b) z = 0 := by
  have hrf := finiteTargetRatio_meromorphic (fun w => hf.1 w (mem_univ w)) a b
  have hrF := finiteTargetRatio_meromorphic (fun w => hF.1 w (mem_univ w)) a b
  have hfb : f z - b ≠ 0 := by rw [hfc]; exact sub_ne_zero.mpr hcb
  have hFb : F z - b ≠ 0 := by rw [hFc]; exact sub_ne_zero.mpr hcb
  have hrfA : AnalyticAt ℂ (finiteTargetRatio f a b) z :=
    (hfa.sub analyticAt_const).div (hfa.sub analyticAt_const) hfb
  have hrFA : AnalyticAt ℂ (finiteTargetRatio F a b) z :=
    (hFa.sub analyticAt_const).div (hFa.sub analyticAt_const) hFb
  have hFv : finiteTargetRatio F a b z ≠ 0 := by
    exact div_ne_zero (by rw [hFc]; exact sub_ne_zero.mpr hca) hFb
  have hdrf : HasDerivAt (finiteTargetRatio f a b) 0 z := by
    change HasDerivAt (fun w => (f w - a) / (f w - b)) 0 z
    convert ((hfa.differentiableAt.hasDerivAt.sub_const a).fun_div
      (hfa.differentiableAt.hasDerivAt.sub_const b) hfb) using 1
    simp only [hfd, zero_mul, mul_zero, sub_self, zero_div]
  have hdrF : HasDerivAt (finiteTargetRatio F a b) 0 z := by
    change HasDerivAt (fun w => (F w - a) / (F w - b)) 0 z
    convert ((hFa.differentiableAt.hasDerivAt.sub_const a).fun_div
      (hFa.differentiableAt.hasDerivAt.sub_const b) hFb) using 1
    simp only [hFd, zero_mul, mul_zero, sub_self, zero_div]
  have hraw : AnalyticAt ℂ
      (fun w => finiteTargetRatio f a b w / finiteTargetRatio F a b w) z :=
    hrfA.div hrFA hFv
  have hquot : MeromorphicOn
      (fun w => finiteTargetRatio f a b w / finiteTargetRatio F a b w) univ :=
    hrf.meromorphicOn.div hrF.meromorphicOn
  have hloc : toMeromorphicNFOn
      (fun w => finiteTargetRatio f a b w / finiteTargetRatio F a b w) univ =ᶠ[𝓝 z]
      toMeromorphicNFAt (fun w => finiteTargetRatio f a b w / finiteTargetRatio F a b w) z :=
    toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hquot (mem_univ z)
  rw [toMeromorphicNFAt_eq_self.mpr hraw.meromorphicNFAt] at hloc
  change exponentialCrossRatioUnit f F a b =ᶠ[𝓝 z]
    (fun w => finiteTargetRatio f a b w / finiteTargetRatio F a b w) at hloc
  rw [hloc.deriv_eq]
  simpa only [zero_mul, mul_zero, sub_self, zero_div] using (hdrf.fun_div hdrF hFv).deriv

/-- The quotient's linear growth follows from the two original linear
growth bounds and the first-main transformations. -/
theorem exponentialCrossRatioUnit_linear_characteristic {f F : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    {a b : ℂ} (hab : a ≠ b) {C D R₀ R₁ : ℝ}
    (hfgrowth : ∀ r, R₀ ≤ r → charT f r ≤ C * r)
    (hFgrowth : ∀ r, R₁ ≤ r → charT F r ≤ D * r) :
    ∃ C' R' : ℝ, ∀ r, R' ≤ r → charT (exponentialCrossRatioUnit f F a b) r ≤ C' * r := by
  obtain ⟨Cf, hCf⟩ := charT_crossRatio_abs_le hf hab
  obtain ⟨CF, hCF⟩ := charT_crossRatio_abs_le hF hab
  let K : ℝ := max |log ‖finiteTargetRatio F a b 0‖|
    |log ‖meromorphicTrailingCoeffAt (finiteTargetRatio F a b) 0‖|
  have hK : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
  have hrf := finiteTargetRatio_meromorphic (fun z => hf.1 z (mem_univ z)) a b
  have hrF := finiteTargetRatio_meromorphic (fun z => hF.1 z (mem_univ z)) a b
  have hrfi (z : ℂ) : meromorphicOrderAt (finiteTargetRatio F a b)⁻¹ z ≠ ⊤ := by
    rw [meromorphicOrderAt_inv, finiteTargetRatio_order hF]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact WithTop.coe_ne_top
  refine ⟨|C| + |D| + |Cf| + |CF| + K, max 1 (max R₀ R₁), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 ≤ r := by linarith
  have hff := hfgrowth r ((le_max_left _ _).trans ((le_max_right _ _).trans hr))
  have hFF := hFgrowth r ((le_max_right _ _).trans ((le_max_right _ _).trans hr))
  have hfr := (abs_le.mp (hCf r hr1)).2
  have hFr := (abs_le.mp (hCF r hr1)).2
  change charT (finiteTargetRatio f a b) r - charT f r ≤ Cf at hfr
  change charT (finiteTargetRatio F a b) r - charT F r ≤ CF at hFr
  have hinv := characteristic_sub_characteristic_inv_le (R := r) hrF
  change |charT (finiteTargetRatio F a b) r - charT (finiteTargetRatio F a b)⁻¹ r| ≤ K at hinv
  have hinvl := (abs_le.mp hinv).1
  have hprod := characteristic_mul_top_le hr1 hrf (finiteTargetRatio_order_ne_top hf a b)
    (fun z => (hrF z).inv) hrfi
  have hraw : MeromorphicOn
      (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z) univ :=
    hrf.meromorphicOn.div hrF.meromorphicOn
  have hcod : (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z)
      =ᶠ[codiscrete ℂ] exponentialCrossRatioUnit f F a b := by
    exact toMeromorphicNFOn_eqOn_codiscrete hraw
  have heq := characteristic_congr_codiscrete (a := (⊤ : WithTop ℂ))
    hcod (by linarith : r ≠ 0)
  change charT (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z) r =
    charT (exponentialCrossRatioUnit f F a b) r at heq
  have hmul : (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z) =
      finiteTargetRatio f a b * (finiteTargetRatio F a b)⁻¹ := by ext z; exact div_eq_mul_inv _ _
  rw [hmul] at heq
  change charT (finiteTargetRatio f a b * (finiteTargetRatio F a b)⁻¹) r ≤
    charT (finiteTargetRatio f a b) r + charT (finiteTargetRatio F a b)⁻¹ r at hprod
  rw [heq] at hprod
  have hCr := mul_le_mul_of_nonneg_right (le_abs_self C) hr0
  have hDr := mul_le_mul_of_nonneg_right (le_abs_self D) hr0
  have hKr := le_mul_of_one_le_right hK hr1
  have hCfr := le_mul_of_one_le_right (abs_nonneg Cf) hr1
  have hCFr := le_mul_of_one_le_right (abs_nonneg CF) hr1
  nlinarith [le_abs_self Cf, le_abs_self CF]

/-- Equality of the normalized quotient to one recovers equality of the
original meromorphic germs through the injective target coordinate. -/
theorem eq_codiscrete_of_exponentialCrossRatioUnit_eq_one {f F : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    {a b : ℂ} (hab : a ≠ b)
    (hunit : ∀ z, exponentialCrossRatioUnit f F a b z = 1) :
    f =ᶠ[codiscrete ℂ] F := by
  have hfm : Meromorphic f := fun z => hf.1 z (mem_univ z)
  have hFm : Meromorphic F := fun z => hF.1 z (mem_univ z)
  have hrf := finiteTargetRatio_meromorphic hfm a b
  have hrF := finiteTargetRatio_meromorphic hFm a b
  have hraw : MeromorphicOn
      (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z) univ :=
    hrf.meromorphicOn.div hrF.meromorphicOn
  have hcod : (fun z => finiteTargetRatio f a b z / finiteTargetRatio F a b z)
      =ᶠ[codiscrete ℂ] exponentialCrossRatioUnit f F a b := by
    exact toMeromorphicNFOn_eqOn_codiscrete hraw
  have hrFnz := eventually_ne_zero_of_order_ne_top hrF (finiteTargetRatio_order_ne_top hF a b)
  have hfbnz := eventually_ne_zero_of_order_ne_top
    (fun z => (hfm z).sub (MeromorphicAt.const b z)) (fun z => hf.2 z (mem_univ z) b)
  have hFbnz := eventually_ne_zero_of_order_ne_top
    (fun z => (hFm z).sub (MeromorphicAt.const b z)) (fun z => hF.2 z (mem_univ z) b)
  filter_upwards [hcod, hrFnz, hfbnz, hFbnz] with z hz hRnz hfb hFb
  have hdiv : finiteTargetRatio f a b z / finiteTargetRatio F a b z = 1 :=
    hz.trans (hunit z)
  have hr : finiteTargetRatio f a b z = finiteTargetRatio F a b z :=
    (div_eq_one_iff_eq hRnz).mp hdiv
  change (f z - a) / (f z - b) = (F z - a) / (F z - b) at hr
  change f z - b ≠ 0 at hfb
  change F z - b ≠ 0 at hFb
  have hx : (f z - a) * (F z - b) = (F z - a) * (f z - b) :=
    (div_eq_div_iff hfb hFb).mp hr
  have hfactor : (a - b) * (f z - F z) = 0 := by linear_combination hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hab))

theorem sphereGermValue_eq_of_exponentialCrossRatioUnit_eq_one {f F : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    {a b : ℂ} (hab : a ≠ b)
    (hunit : ∀ z, exponentialCrossRatioUnit f F a b z = 1) :
    ∀ z, sphereGermValue f z = sphereGermValue F z := by
  have heq := eq_codiscrete_of_exponentialCrossRatioUnit_eq_one hf hF hab hunit
  intro z
  exact sphereGermValue_congr (hf.1 z (mem_univ z)) (hF.1 z (mem_univ z))
    (codiscrete_iff_nhdsNE.mp heq z)

/-- In the actual-defect branch the third-target critical point locks the
entire unit to one, without phase continuity of the affine coefficient. -/
theorem exponentialCrossRatioUnit_eq_one_of_common_critical
    {f F : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (hF : IsNonconstMeroOn F univ)
    {a b c z : ℂ} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : ∀ w, mult f (a : Sphere) w = mult F (a : Sphere) w)
    (hb : ∀ w, mult f (b : Sphere) w = mult F (b : Sphere) w)
    (hfa : AnalyticAt ℂ f z) (hFa : AnalyticAt ℂ F z)
    (hfc : f z = c) (hFc : F z = c) (hfd : deriv f z = 0) (hFd : deriv F z = 0)
    {C D R₀ R₁ : ℝ} (hfgrowth : ∀ r, R₀ ≤ r → charT f r ≤ C * r)
    (hFgrowth : ∀ r, R₁ ≤ r → charT F r ≤ D * r) :
    ∀ w, exponentialCrossRatioUnit f F a b w = 1 := by
  obtain ⟨hunit, hnz⟩ := exponentialCrossRatioUnit_analytic_nonzero hf hF a b ha hb
  obtain ⟨E, R, hgrowth⟩ := exponentialCrossRatioUnit_linear_characteristic hf hF hab
    hfgrowth hFgrowth
  exact entire_unit_eq_one_of_linear_characteristic_of_critical hunit hnz hgrowth
    (exponentialCrossRatioUnit_eq_one_at_third_target hf hF hfa hFa hfc hFc hca hcb)
    (exponentialCrossRatioUnit_deriv_eq_zero_at_common_critical hf hF hfa hFa hfc hFc
      hca hcb hfd hFd)

/-- In the actual-defect branch, multiplicity at least two at the fixed
third target gives the critical anchor on the honest finite charts. The
three target multiplicity data then lock the whole spherical maps. No raw
value or derivative at a removable singularity is assumed. -/
theorem sphere_maps_eq_of_three_cm_at_critical
    {S T : ℂ → OnePoint ℂ}
    (hS : SphereHolomorphicOn S univ) (hT : SphereHolomorphicOn T univ)
    (hSnc : ¬ ∃ p : OnePoint ℂ, ∀ w, S w = p)
    (hTnc : ¬ ∃ p : OnePoint ℂ, ∀ w, T w = p)
    {a b c z : ℂ} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : ∀ w, mult (fun v => chartFiniteMap (S v)) (a : Sphere) w =
      mult (fun v => chartFiniteMap (T v)) (a : Sphere) w)
    (hb : ∀ w, mult (fun v => chartFiniteMap (S v)) (b : Sphere) w =
      mult (fun v => chartFiniteMap (T v)) (b : Sphere) w)
    (hcm : mult (fun v => chartFiniteMap (S v)) (c : Sphere) z =
      mult (fun v => chartFiniteMap (T v)) (c : Sphere) z)
    (hm : 2 ≤ mult (fun v => chartFiniteMap (S v)) (c : Sphere) z)
    {C D R₀ R₁ : ℝ}
    (hSgrowth : ∀ r, R₀ ≤ r → charT (fun v => chartFiniteMap (S v)) r ≤ C * r)
    (hTgrowth : ∀ r, R₁ ≤ r → charT (fun v => chartFiniteMap (T v)) r ≤ D * r) :
    ∀ w, S w = T w := by
  let f : ℂ → ℂ := fun w => chartFiniteMap (S w)
  let F : ℂ → ℂ := fun w => chartFiniteMap (T w)
  have hf : IsNonconstMeroOn f univ := isNonconstMeroOn_chartFiniteMap hS hSnc
  have hF : IsNonconstMeroOn F univ := isNonconstMeroOn_chartFiniteMap hT hTnc
  have hmf : 2 ≤ mult f (c : Sphere) z := hm
  have hcm' : mult f (c : Sphere) z = mult F (c : Sphere) z := hcm
  have hmF : 2 ≤ mult F (c : Sphere) z := by rw [← hcm']; exact hmf
  have hfp : 0 < mult f (c : Sphere) z := lt_of_lt_of_le (by decide : 0 < 2) hmf
  have hFp : 0 < mult F (c : Sphere) z := lt_of_lt_of_le (by decide : 0 < 2) hmF
  have hsc : S z = (c : OnePoint ℂ) := by
    rw [← sphereGermValue_chartFiniteMap hS hSnc z]
    exact (mult_finite_pos_iff_sphereGermValue_eq
      (hf.1 z (mem_univ z)) (hf.2 z (mem_univ z) c)).1 hfp
  have htc : T z = (c : OnePoint ℂ) := by
    rw [← sphereGermValue_chartFiniteMap hT hTnc z]
    exact (mult_finite_pos_iff_sphereGermValue_eq
      (hF.1 z (mem_univ z)) (hF.2 z (mem_univ z) c)).1 hFp
  have hfa : AnalyticAt ℂ f z := analyticAt_chartFiniteMap_of_ne_infty hS (mem_univ z)
    (by rw [hsc]; exact OnePoint.coe_ne_infty c)
  have hFa : AnalyticAt ℂ F z := analyticAt_chartFiniteMap_of_ne_infty hT (mem_univ z)
    (by rw [htc]; exact OnePoint.coe_ne_infty c)
  have hfc : f z = c := by change chartFiniteMap (S z) = c; rw [hsc]; rfl
  have hFc : F z = c := by change chartFiniteMap (T z) = c; rw [htc]; rfl
  have hfd : deriv f z = 0 := deriv_eq_zero_of_order_sub_ge_two hfa hmf
    (order_sub_eq_nat_of_mult_pos f c z hfp rfl)
  have hFd : deriv F z = 0 := deriv_eq_zero_of_order_sub_ge_two hFa hmF
    (order_sub_eq_nat_of_mult_pos F c z hFp rfl)
  have hunit := exponentialCrossRatioUnit_eq_one_of_common_critical hf hF hab hca hcb
    ha hb hfa hFa hfc hFc hfd hFd hSgrowth hTgrowth
  have heq := sphereGermValue_eq_of_exponentialCrossRatioUnit_eq_one hf hF hab hunit
  intro w
  simpa only [f, F, sphereGermValue_chartFiniteMap hS hSnc,
    sphereGermValue_chartFiniteMap hT hTnc] using heq w

end ThreeIM

end

/-!
# Exact separation of opposite stable-coordinate phases

The retained inverse-coordinate identity separates the two nonzero
opposite graph arguments directly.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Topology

namespace ThreeIM

/-- The retained exact stable-coordinate identity separates opposite
nonzero phases directly. No separate inverse-function injectivity or
asymptotic derivative assertion is needed. -/
theorem stable_coordinate_opposite_ne
    (H J : ℂ × ℂ → ℂ) (X W : ℂ) (hW : W ≠ 0)
    (hpos : H (X, W) * Complex.exp (J (X, H (X, W))) = W)
    (hneg : H (X, -W) * Complex.exp (J (X, H (X, -W))) = -W) :
    H (X, W) ≠ H (X, -W) := by
  intro heq
  have hWneg : W = -W := hpos.symm.trans
    ((congrArg (fun u : ℂ => u * Complex.exp (J (X, u))) heq).trans hneg)
  have hzero : (2 : ℂ) * W = 0 := by linear_combination hWneg
  exact hW ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

end ThreeIM

end
