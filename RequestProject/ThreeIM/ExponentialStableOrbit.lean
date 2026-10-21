module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecificLimits.Basic
public import RequestProject.ThreeIM.ExponentialSectorExponent
public import RequestProject.ThreeIM.ExponentialStableGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consolidated stable-expansion foundations

The declarations below consolidate the stable-expansion foundations
formerly split across separate draft modules.
This grouping reduces repeated loading of their common imports.
-/

@[expose] public section

open Filter Set Topology NoWanderingDomains
open Filter Set NoWanderingDomains
open scoped Topology
open Filter Set
open scoped Topology

namespace ThreeIM

/-! ## Declarations from ExponentialStableCubic -/


def stableCubicE1 (a : Fin 3 → ℂ) : ℂ := a 0 + a 1 + a 2

def stableCubicE2 (a : Fin 3 → ℂ) : ℂ := a 0 * a 1 + a 0 * a 2 + a 1 * a 2

def stableCubicE3 (a : Fin 3 → ℂ) : ℂ := a 0 * a 1 * a 2

theorem stable_cubic_coefficients (a : Fin 3 → ℂ) (z : ℂ) :
    cubicP a z = z ^ 3 - stableCubicE1 a * z ^ 2 + stableCubicE2 a * z - stableCubicE3 a := by
  simp only [cubicP, stableCubicE1, stableCubicE2, stableCubicE3]
  ring

theorem stable_cubic_root_offset (a : Fin 3 → ℂ) (j : Fin 3) (u : ℂ) :
    cubicP a (a j + u) =
      u * (deriv (cubicP a) (a j) + (3 * a j - stableCubicE1 a) * u + u ^ 2) := by
  rw [(hasDerivAt_cubicP a (a j)).deriv]
  fin_cases j <;>
    simp only [cubicP, stableCubicE1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    ring

theorem stable_inverse_product_cubic (a : Fin 3 → ℂ) (X v : ℂ) :
    stableInverseProduct (stableCubicE1 a) (stableCubicE2 a) (stableCubicE3 a) X v =
      (1 - a 0 * X * v) * (1 - a 1 * X * v) * (1 - a 2 * X * v) := by
  simp only [stableInverseProduct, stableCubicE1, stableCubicE2, stableCubicE3]
  ring


/-! ## Declarations from ExponentialStableOrbitDecay -/


theorem ExponentialPair.canonical_real_good_eventually
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∀ᶠ r : ℝ in atTop,
      AnalyticAt ℂ (fun z => chartFiniteMap (sphereGermValue f z)) (r : ℂ) ∧
      ∀ j, chartFiniteMap (sphereGermValue f (r : ℂ)) ≠ a j := by
  let F : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue f z)
  let G : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue g z)
  have hc : ExponentialPair a F G κ := h.canonical_representatives
  have hray : Tendsto (fun r : ℝ => (r : ℂ)) atTop (rightSectorAtTop 1) := by
    simpa using tendsto_ray_rightSector 0
  obtain ⟨R, hR⟩ := hc.omits_shared_in_sectors (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hray.eventually (h.canonical_analytic_eventually_rightSector (by norm_num)),
    eventually_ge_atTop (max R 0)] with r hr hlarge
  have hr0 : 0 ≤ r := (le_max_right R 0).trans hlarge
  refine ⟨hr.1, ?_⟩
  intro j
  have hn : ‖(r : ℂ)‖ = r := by simp [Real.norm_of_nonneg hr0]
  have hm := (hR (r : ℂ) (by rw [hn]; exact (le_max_left R 0).trans hlarge)
    (by simp [hn, abs_of_nonneg hr0])) j
  exact ne_of_mult_eq_zero hr.1
    (hc.pair.nonconst_f.2 _ (mem_univ _) (a j)) hm.1

theorem ExponentialPair.canonical_real_logDeriv_tendsto
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    (j : Fin 3)
    (hj : Tendsto (fun r : ℝ => chartFiniteMap (sphereGermValue f (r : ℂ)))
      atTop (𝓝 (a j))) :
    Tendsto (fun r : ℝ =>
      deriv (fun z => chartFiniteMap (sphereGermValue f z)) (r : ℂ) /
        (chartFiniteMap (sphereGermValue f (r : ℂ)) - a j))
      atTop (𝓝 (κ ^ 2 * deriv (cubicP a) (a j))) := by
  let F : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue f z)
  have hray : Tendsto (fun r : ℝ => (r : ℂ)) atTop (rightSectorAtTop 1) := by
    simpa using tendsto_ray_rightSector 0
  have hin : Tendsto (fun r : ℝ => F (r : ℂ)) atTop (𝓝[≠] (a j)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hj, h.canonical_real_good_eventually.mono
      (fun r hr => hr.2 j)⟩
  have hquot := (tendsto_cubicP_div a j).comp hin
  have hd := (h.canonical_cubic_logDeriv_tendsto_rightSector
    (by norm_num : (0 : ℝ) < 1)).comp hray
  apply (hd.mul hquot).congr'
  filter_upwards [h.canonical_real_good_eventually] with r hr
  have hP : cubicP a (F (r : ℂ)) ≠ 0 := cubicP_ne_zero_of_ne hr.2
  have hne : F (r : ℂ) - a j ≠ 0 := sub_ne_zero.mpr (hr.2 j)
  change deriv F (r : ℂ) / cubicP a (F (r : ℂ)) *
      (cubicP a (F (r : ℂ)) / (F (r : ℂ) - a j)) =
        deriv F (r : ℂ) / (F (r : ℂ) - a j)
  field_simp [hP, hne]

theorem ExponentialPair.exists_canonical_real_exponential_decay
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∃ j : Fin 3, ∃ μ : ℝ,
      (∀ δ : ℝ, 0 < δ → Tendsto (fun z => chartFiniteMap (sphereGermValue f z))
        (rightSectorAtTop δ) (𝓝 (a j))) ∧
      0 < μ ∧ (μ : ℂ) = -(κ ^ 2 * deriv (cubicP a) (a j)) ∧
      ∃ R : ℝ, 0 < R ∧
      ∀ s t : ℝ, R ≤ s → s ≤ t →
        ‖chartFiniteMap (sphereGermValue f (t : ℂ)) - a j‖ ≤
          ‖chartFiniteMap (sphereGermValue f (s : ℂ)) - a j‖ *
            Real.exp (-(μ / 2) * (t - s)) := by
  obtain ⟨j, hj, him, hpos⟩ := h.exists_canonical_marked_limit_positive_exponent
  let μ : ℝ := (-(κ ^ 2 * deriv (cubicP a) (a j))).re
  have hμ : 0 < μ := hpos
  have hμc : (μ : ℂ) = -(κ ^ 2 * deriv (cubicP a) (a j)) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him.symm
  have hray : Tendsto (fun r : ℝ => (r : ℂ)) atTop (rightSectorAtTop 1) := by
    simpa using tendsto_ray_rightSector 0
  have hlim := h.canonical_real_logDeriv_tendsto j
    ((hj 1 (by norm_num)).comp hray)
  have hlimRe := (Complex.continuous_re.tendsto _).comp hlim
  have htarget : (κ ^ 2 * deriv (cubicP a) (a j)).re = -μ := by
    dsimp [μ]
    simp
  rw [htarget] at hlimRe
  have hbound : ∀ᶠ r : ℝ in atTop,
      (deriv (fun z => chartFiniteMap (sphereGermValue f z)) (r : ℂ) /
        (chartFiniteMap (sphereGermValue f (r : ℂ)) - a j)).re ≤ -(μ / 2) :=
    (hlimRe.eventually (eventually_lt_nhds (by linarith : -μ < -(μ / 2)))).mono
      (fun r hr => hr.le)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (h.canonical_real_good_eventually.and hbound)
  refine ⟨j, μ, hj, hμ, hμc, max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s t hs hst
  apply norm_le_exp_of_logDeriv_re_le
    (u := fun r : ℝ => chartFiniteMap (sphereGermValue f (r : ℂ)) - a j)
    (du := fun r : ℝ => deriv (fun z => chartFiniteMap (sphereGermValue f z)) (r : ℂ))
    (R := max R₀ 1)
  · intro r hr
    exact (((hR₀ r ((le_max_left _ _).trans hr)).1.1.differentiableAt.hasDerivAt).comp_ofReal).sub_const _
  · intro r hr
    exact sub_ne_zero.mpr ((hR₀ r ((le_max_left _ _).trans hr)).1.2 j)
  · intro r hr
    exact (hR₀ r ((le_max_left _ _).trans hr)).2
  · exact hs
  · exact hst


/-! ## Declarations from ExponentialStableSystem -/


theorem ExponentialPair.stable_auxV_identity_at
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ z : ℂ} (h : ExponentialPair a f g κ)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hPg : cubicP a (g z) ≠ 0) :
    (f z - g z) * deriv g z = κ * Complex.exp (-z) * cubicP a (g z) := by
  have hp : ContinuousAt (fun t => cubicP a (g t)) z := by
    unfold cubicP
    fun_prop
  have ha : ContinuousAt (auxV a f g) z :=
    ((hf.continuousAt.sub hg.continuousAt).mul hg.deriv.continuousAt).div hp hPg
  have hleft := (ha.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsNE_of_codiscrete h.eq_V z)
  have hright : Tendsto (fun t : ℂ => κ * Complex.exp (-t)) (𝓝[≠] z)
      (𝓝 (κ * Complex.exp (-z))) :=
    (continuous_const.mul (Complex.continuous_exp.comp continuous_neg)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hv : (f z - g z) * deriv g z / cubicP a (g z) =
      κ * Complex.exp (-z) := tendsto_nhds_unique hleft hright
  exact (div_eq_iff hPg).mp hv

theorem stable_scalar_system_of_auxiliary_identities
    (a : Fin 3 → ℂ) (j : Fin 3) (κ μ X Z F G DF DG : ℂ)
    (hXZ : X * Z = 1) (hG : G ≠ 0) (hFG : F - G ≠ 0)
    (hU : (F - G) * DF = κ * Z * cubicP a F)
    (hV : (F - G) * DG = κ * X * cubicP a G) :
    DF = -μ * (F - a j) + (F - a j) *
      stableRu (a j) κ (deriv (cubicP a) (a j)) (3 * a j - stableCubicE1 a) μ
        (X, F - a j, Z / G + κ) ∧
    Z / G - Z * DG / G ^ 2 = Z / G + κ + X *
      stableRw (a j) κ (stableCubicE1 a) (stableCubicE2 a) (stableCubicE3 a)
        (X, F - a j, Z / G + κ) := by
  let D : ℂ := stableDenominator (a j) κ (X, F - a j, Z / G + κ)
  have hZX : Z * X = 1 := by simpa only [mul_comm] using hXZ
  have hDval : D = 1 - F / G := by
    dsimp only [D, stableDenominator]
    rw [add_sub_cancel_right, show a j + (F - a j) = F by ring]
    simp only [div_eq_mul_inv]
    calc
      1 - X * (Z * G⁻¹) * F =
          1 - (X * Z) * (F * G⁻¹) := by ring
      _ = 1 - F * G⁻¹ := by rw [hXZ, one_mul]
  have hcoeff : F - G = -G * D := by
    rw [hDval]
    field_simp [hG]
    ring
  have hD : D ≠ 0 := by
    intro hzero
    apply hFG
    rw [hcoeff, hzero, mul_zero]
  have hDunit : IsUnit (stableDenominator (a j) κ
      (X, F - a j, Z / G + κ)) := isUnit_iff_ne_zero.mpr hD
  have hDF : DF = -κ * (Z / G) * cubicP a F / D := by
    apply (eq_div_iff hD).mpr
    apply mul_left_cancel₀ hG
    calc
      G * (DF * D) = -((F - G) * DF) := by rw [hcoeff]; ring
      _ = -(κ * Z * cubicP a F) := by rw [hU]
      _ = G * (-κ * (Z / G) * cubicP a F) := by field_simp [hG] <;> ring
  have hDG : DG = -κ * X * cubicP a G / (G * D) := by
    apply (eq_div_iff (mul_ne_zero hG hD)).mpr
    calc
      DG * (G * D) = -((F - G) * DG) := by rw [hcoeff]; ring
      _ = -(κ * X * cubicP a G) := by rw [hV]
      _ = _ := by ring
  have hPoffset : cubicP a F = (F - a j) *
      (deriv (cubicP a) (a j) +
        (3 * a j - stableCubicE1 a) * (F - a j) + (F - a j) ^ 2) := by
    have hp := stable_cubic_root_offset a j (F - a j)
    rw [show a j + (F - a j) = F by ring] at hp
    exact hp
  have hXv : X * (Z / G) = G⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, hXZ, one_mul]
  have hProd : stableInverseProduct (stableCubicE1 a) (stableCubicE2 a)
      (stableCubicE3 a) X (Z / G) = cubicP a G / G ^ 3 := by
    rw [stable_inverse_product_cubic]
    simp only [mul_assoc, hXv]
    unfold cubicP
    field_simp [hG] <;> ring
  have hZDG : Z * DG = -κ * cubicP a G / (G * D) := by
    rw [hDG]
    calc
      Z * (-κ * X * cubicP a G / (G * D)) =
          -κ * (Z * X) * cubicP a G / (G * D) := by ring
      _ = _ := by rw [hZX, mul_one]
  constructor
  · calc
      DF = -κ * (Z / G) *
          ((F - a j) * (deriv (cubicP a) (a j) +
            (3 * a j - stableCubicE1 a) * (F - a j) + (F - a j) ^ 2)) *
          Ring.inverse D := by rw [hDF, hPoffset, Ring.inverse_eq_inv, div_eq_mul_inv]
      _ = _ := by
        simpa only [add_sub_cancel_right, D] using
          stable_u_equation (a j) κ (deriv (cubicP a) (a j))
            (3 * a j - stableCubicE1 a) μ X (F - a j) (Z / G + κ) hDunit
  · calc
      Z / G - Z * DG / G ^ 2 = Z / G +
          κ * stableInverseProduct (stableCubicE1 a) (stableCubicE2 a)
            (stableCubicE3 a) X (Z / G) * Ring.inverse D := by
        rw [hZDG, hProd, Ring.inverse_eq_inv]
        field_simp [hG, hD]
        ring
      _ = _ := by
        simpa only [add_sub_cancel_right, D] using
          stable_w_equation (a j) κ (stableCubicE1 a) (stableCubicE2 a)
            (stableCubicE3 a) X (F - a j) (Z / G + κ) hDunit

theorem ExponentialPair.stable_system_hasDerivAt
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ z : ℂ} (h : ExponentialPair a f g κ)
    (j : Fin 3) (μ : ℂ)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hPf : cubicP a (f z) ≠ 0) (hPg : cubicP a (g z) ≠ 0)
    (hg0 : g z ≠ 0) (hfg : f z - g z ≠ 0) :
    HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-Complex.exp (-z)) z ∧
    HasDerivAt (fun t : ℂ => f t - a j)
      (-μ * (f z - a j) + (f z - a j) *
        stableRu (a j) κ (deriv (cubicP a) (a j)) (3 * a j - stableCubicE1 a) μ
          (Complex.exp (-z), f z - a j, Complex.exp z / g z + κ)) z ∧
    HasDerivAt (fun t : ℂ => Complex.exp t / g t + κ)
      (Complex.exp z / g z + κ + Complex.exp (-z) *
        stableRw (a j) κ (stableCubicE1 a) (stableCubicE2 a) (stableCubicE3 a)
          (Complex.exp (-z), f z - a j, Complex.exp z / g z + κ)) z := by
  have hu : (f z - g z) * deriv f z = κ * Complex.exp z * cubicP a (f z) := by
    apply (div_eq_iff hPf).mp
    simpa only [mul_div_assoc] using h.cubic_logDeriv_identity_at hf hg hPf
  have hxz : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  obtain ⟨hdf, hdw⟩ := stable_scalar_system_of_auxiliary_identities a j κ μ
    (Complex.exp (-z)) (Complex.exp z) (f z) (g z) (deriv f z) (deriv g z)
    hxz hg0 hfg hu (h.stable_auxV_identity_at hf hg hPg)
  have hw : HasDerivAt (fun t : ℂ => Complex.exp t / g t + κ)
      (Complex.exp z / g z - Complex.exp z * deriv g z / g z ^ 2) z := by
    convert ((Complex.hasDerivAt_exp z).div hg.differentiableAt.hasDerivAt hg0).add_const κ
      using 1
    field_simp [hg0] <;> ring
  refine ⟨?_, (hf.differentiableAt.hasDerivAt.sub_const (a j)).congr_deriv hdf,
    hw.congr_deriv hdw⟩
  simpa using (hasDerivAt_id z).neg.cexp

/-- Every local condition used in the scalar system is obtained internally
on the actual canonical real-axis tail. -/
theorem ExponentialPair.canonical_real_stable_system_eventually
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    (j : Fin 3) (μ : ℂ) :
    let F : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue f z)
    let G : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue g z)
    ∀ᶠ r : ℝ in atTop,
      HasDerivAt (fun s : ℝ => F (s : ℂ) - a j)
        (-μ * (F (r : ℂ) - a j) + (F (r : ℂ) - a j) *
          stableRu (a j) κ (deriv (cubicP a) (a j)) (3 * a j - stableCubicE1 a) μ
            (Complex.exp (-(r : ℂ)), F (r : ℂ) - a j,
              Complex.exp (r : ℂ) / G (r : ℂ) + κ)) r ∧
      HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ) / G (s : ℂ) + κ)
        (Complex.exp (r : ℂ) / G (r : ℂ) + κ + Complex.exp (-(r : ℂ)) *
          stableRw (a j) κ (stableCubicE1 a) (stableCubicE2 a) (stableCubicE3 a)
            (Complex.exp (-(r : ℂ)), F (r : ℂ) - a j,
              Complex.exp (r : ℂ) / G (r : ℂ) + κ)) r := by
  dsimp only
  let F : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue f z)
  let G : ℂ → ℂ := fun z => chartFiniteMap (sphereGermValue g z)
  have hc : ExponentialPair a F G κ := h.canonical_representatives
  have hray : Tendsto (fun r : ℝ => (r : ℂ)) atTop (rightSectorAtTop 1) := by
    simpa using tendsto_ray_rightSector 0
  have hbig : ∀ᶠ r : ℝ in atTop, ∀ i : Fin 3, ‖a i‖ < ‖G (r : ℂ)‖ := by
    rw [eventually_all]
    intro i
    exact ((h.canonical_g_norm_tendsto_rightSector (δ := 1) (by norm_num)).comp hray).eventually
      (eventually_gt_atTop ‖a i‖)
  have hratio : ∀ᶠ r : ℝ in atTop, F (r : ℂ) / G (r : ℂ) ≠ 1 :=
    ((h.canonical_ratio_tendsto_rightSector (δ := 1) (by norm_num)).comp hray).eventually_ne
      (by norm_num : (0 : ℂ) ≠ 1)
  filter_upwards [h.canonical_real_good_eventually,
    hray.eventually (h.canonical_analytic_eventually_rightSector (δ := 1) (by norm_num)), hbig,
    hratio] with r hfgood han hgb hq
  have hgne : ∀ i, G (r : ℂ) ≠ a i := by
    intro i heq
    have hh := hgb i
    rw [heq] at hh
    exact lt_irrefl _ hh
  have hg0 : G (r : ℂ) ≠ 0 := by
    apply norm_pos_iff.mp
    exact (norm_nonneg (a 0)).trans_lt (hgb 0)
  have hfg : F (r : ℂ) - G (r : ℂ) ≠ 0 := by
    intro heq
    apply hq
    rw [sub_eq_zero.mp heq, div_self hg0]
  have hp := hc.stable_system_hasDerivAt j μ hfgood.1 han.2
    (cubicP_ne_zero_of_ne hfgood.2) (cubicP_ne_zero_of_ne hgne) hg0 hfg
  exact ⟨hp.2.1.comp_ofReal, hp.2.2.comp_ofReal⟩


/-! ## Declarations from ExponentialStableIdentity -/


theorem meromorphic_eq_codiscreteWithin_of_frequently_eq
    {U : Set ℂ} {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsConnected U) (hx : x ∈ U)
    (heq : ∃ᶠ z in 𝓝[≠] x, f z = g z) :
    f =ᶠ[codiscreteWithin U] g := by
  let D : ℂ → ℂ := fun z => f z - g z
  have hD : MeromorphicOn D U := hf.sub hg
  have hlocal := ((hf x hx).frequently_eq_iff_eventuallyEq (hg x hx)).mp heq
  have htop : meromorphicOrderAt D x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact eventuallyEq_iff_sub.mp hlocal
  have hall : ∀ y ∈ U, meromorphicOrderAt D y = ⊤ := by
    intro y hy
    by_contra hne
    have hfinite := (hD.exists_meromorphicOrderAt_ne_top_iff_forall hU).mp
      ⟨⟨y, hy⟩, hne⟩ ⟨x, hx⟩
    exact hfinite htop
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
  intro y hy
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp (hall y hy)] with z hz
  exact Or.inl (sub_eq_zero.mp hz)

theorem frequently_complex_eq_of_eq_real_tail
    {f g : ℂ → ℂ} {R x : ℝ} (hx : R < x)
    (heq : ∀ r : ℝ, R < r → f (r : ℂ) = g (r : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (x : ℂ), f z = g z := by
  let s : ℕ → ℂ := fun n => ((x + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hreal : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1))
      atTop (𝓝 x) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))
  have hs : Tendsto s atTop (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp hreal, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      change s n ≠ (x : ℂ)
      intro hsame
      have hh : x + 1 / ((n : ℝ) + 1) = x := Complex.ofReal_injective hsame
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  apply hs.frequently
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun n => heq _ (by
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)

theorem meromorphic_eq_codiscreteWithin_of_eq_real_tail
    {U : Set ℂ} {f g : ℂ → ℂ} {R x : ℝ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsConnected U) (hxU : (x : ℂ) ∈ U) (hx : R < x)
    (heq : ∀ r : ℝ, R < r → f (r : ℂ) = g (r : ℂ)) :
    f =ᶠ[codiscreteWithin U] g :=
  meromorphic_eq_codiscreteWithin_of_frequently_eq hf hg hU hxU
    (frequently_complex_eq_of_eq_real_tail hx heq)


end ThreeIM
