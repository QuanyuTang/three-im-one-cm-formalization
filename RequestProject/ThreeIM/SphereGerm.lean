module

public import RequestProject.ThreeIM.Normalization
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Honest sphere values of meromorphic germs

The complex-valued meromorphic API permits arbitrary values at a pole or a
removable singularity. Spherical convergence requires the actual sphere
value instead. Negative order is sent to infinity; at nonnegative order the
finite value is read from the canonical normal-form representative.

This module uses only Mathlib's one-point compactification, not a normality
theorem. Fiber correspondence explicitly retains the finite-order condition:
the project's multiplicity convention sends an identically zero germ's
infinite order to zero, so it must not be identified with a positive degree.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- The topological sphere value of the germ at z, correcting both pole
values and arbitrary representatives of removable singularities. -/
noncomputable def sphereGermValue (f : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if meromorphicOrderAt f z < 0 then OnePoint.infty
  else ((toMeromorphicNFAt f z z : ℂ) : OnePoint ℂ)

/-- The original target-value type is transported to the topological sphere. -/
def sphereTarget (b : Sphere) : OnePoint ℂ :=
  WithTop.recTopCoe OnePoint.infty (fun c : ℂ => (c : OnePoint ℂ)) b

theorem sphereTarget_injective : Function.Injective sphereTarget := by
  intro x y hxy
  induction x using WithTop.recTopCoe with
  | top =>
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe a => exact (OnePoint.coe_ne_infty a hxy.symm).elim
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => exact (OnePoint.coe_ne_infty a hxy).elim
    | coe b => exact congrArg (fun c : ℂ => (c : Sphere)) (OnePoint.coe_injective hxy)

theorem sphereGermValue_eq_infty_iff (f : ℂ → ℂ) (z : ℂ) :
    sphereGermValue f z = OnePoint.infty ↔ meromorphicOrderAt f z < 0 := by
  classical
  by_cases h : meromorphicOrderAt f z < 0
  · simp [sphereGermValue, h]
  · simp [sphereGermValue, h, OnePoint.coe_ne_infty]

/-- The raw complex-valued function has the corrected sphere value as its
limit on punctured neighborhoods, including at poles. -/
theorem tendsto_sphereGermValue {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    Tendsto (fun w => (f w : OnePoint ℂ)) (𝓝[≠] z) (𝓝 (sphereGermValue f z)) := by
  classical
  unfold sphereGermValue
  split_ifs with hneg
  · have hinf : Tendsto f (𝓝[≠] z) (Filter.coclosedCompact ℂ) := by
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    exact OnePoint.tendsto_coe_infty.comp hinf
  · have heq := hf.eq_nhdsNE_toMeromorphicNFAt
    have hn : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt f z) z := by
      rw [← meromorphicOrderAt_congr heq]
      exact le_of_not_gt hneg
    have ha := (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := z)).meromorphicOrderAt_nonneg_iff_analyticAt.1 hn
    have ht : Tendsto f (𝓝[≠] z) (𝓝 (toMeromorphicNFAt f z z)) :=
      (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    exact (OnePoint.continuous_coe.tendsto _).comp ht

/-- Corrected sphere values depend only on the punctured meromorphic germ. -/
theorem sphereGermValue_congr {f g : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) (heq : f =ᶠ[𝓝[≠] z] g) :
    sphereGermValue f z = sphereGermValue g z := by
  have hfg : (fun w => (f w : OnePoint ℂ)) =ᶠ[𝓝[≠] z]
      (fun w => (g w : OnePoint ℂ)) := heq.mono fun w hw => congrArg OnePoint.some hw
  exact tendsto_nhds_unique ((tendsto_sphereGermValue hf).congr' hfg)
    (tendsto_sphereGermValue hg)

theorem sphereGermValue_eq_coe_of_analytic {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : sphereGermValue f z = (f z : OnePoint ℂ) := by
  exact tendsto_nhds_unique (tendsto_sphereGermValue hf.meromorphicAt)
    ((OnePoint.continuous_coe.tendsto _).comp
      (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))

/-- A meromorphic germ gives an actual continuous sphere-valued map. -/
theorem continuousAt_sphereGermValue {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    ContinuousAt (sphereGermValue f) z := by
  have heq : sphereGermValue f =ᶠ[𝓝[≠] z] (fun w => (f w : OnePoint ℂ)) :=
    hf.eventually_analyticAt.mono fun w hw => sphereGermValue_eq_coe_of_analytic hw
  have ht := (tendsto_sphereGermValue hf).congr' heq.symm
  change Tendsto (sphereGermValue f) (𝓝 z) (𝓝 (sphereGermValue f z))
  rw [← nhdsNE_sup_pure z]
  exact tendsto_sup.2 ⟨ht, tendsto_pure_nhds _ _⟩

theorem continuousOn_sphereGermValue {f : ℂ → ℂ} {Ω : Set ℂ} (hf : MeromorphicOn f Ω) :
    ContinuousOn (sphereGermValue f) Ω :=
  fun z hz => (continuousAt_sphereGermValue (hf z hz)).continuousWithinAt

theorem sphereGermValue_eq_coe_codiscreteWithin {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : MeromorphicOn f Ω) :
    ∀ᶠ z in codiscreteWithin Ω, sphereGermValue f z = (f z : OnePoint ℂ) := by
  filter_upwards [MeromorphicOn.eventually_codiscreteWithin_analyticAt f hf] with z hz
  exact sphereGermValue_eq_coe_of_analytic hz

theorem mult_finite_pos_iff_order_pos {f : ℂ → ℂ} {z a : ℂ}
    (hfinite : meromorphicOrderAt (fun w => f w - a) z ≠ ⊤) :
    0 < mult f (a : Sphere) z ↔ 0 < meromorphicOrderAt (fun w => f w - a) z := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfinite
  rw [mult_coe, ← hn, WithTop.untop₀_coe]
  constructor
  · intro h
    have hnpos := Int.pos_iff_toNat_pos.2 h
    exact_mod_cast hnpos
  · intro h
    apply Int.pos_iff_toNat_pos.1
    exact_mod_cast h

theorem mult_top_pos_iff_order_neg (f : ℂ → ℂ) (z : ℂ) :
    0 < mult f ⊤ z ↔ meromorphicOrderAt f z < 0 := by
  rw [mult_top]
  induction meromorphicOrderAt f z using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    constructor
    · intro h
      have hn : n < 0 := neg_pos.1 (Int.pos_iff_toNat_pos.2 h)
      exact_mod_cast hn
    · intro h
      apply Int.pos_iff_toNat_pos.1
      have hn : n < 0 := by exact_mod_cast h
      exact neg_pos.2 hn

/-- The finite fibers of a nonconstant germ agree with the corrected
sphere-valued fibers, independently of its arbitrary representative value. -/
theorem mult_finite_pos_iff_sphereGermValue_eq {f : ℂ → ℂ} {z a : ℂ}
    (hf : MeromorphicAt f z)
    (hfinite : meromorphicOrderAt (fun w => f w - a) z ≠ ⊤) :
    0 < mult f (a : Sphere) z ↔ sphereGermValue f z = (a : OnePoint ℂ) := by
  rw [mult_finite_pos_iff_order_pos hfinite]
  constructor
  · intro hpos
    have ht : Tendsto f (𝓝[≠] z) (𝓝 a) := by
      simpa only [zero_add, sub_add_cancel] using
        (tendsto_zero_of_meromorphicOrderAt_pos hpos).add_const a
    exact tendsto_nhds_unique (tendsto_sphereGermValue hf)
      ((OnePoint.continuous_coe.tendsto a).comp ht)
  · intro heq
    have ht : Tendsto (fun w => (f w : OnePoint ℂ)) (𝓝[≠] z) (𝓝 (a : OnePoint ℂ)) := by
      rw [← heq]
      exact tendsto_sphereGermValue hf
    have htf : Tendsto f (𝓝[≠] z) (𝓝 a) :=
      OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff.2 ht
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hf.sub (MeromorphicAt.const a z))).1
    have hsub : (f - fun _ => a) = (fun w => f w - a) := by
      ext w
      rfl
    rw [hsub]
    simpa only [sub_self] using htf.sub_const a

/-- The full spherical fiber correspondence used to translate the original
sharing hypotheses into statements about continuous sphere-valued maps. -/
theorem mult_pos_iff_sphereGermValue_eq {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z)
    (hfinite : ∀ c : ℂ, meromorphicOrderAt (fun w => f w - c) z ≠ ⊤) (b : Sphere) :
    0 < mult f b z ↔ sphereGermValue f z = sphereTarget b := by
  induction b using WithTop.recTopCoe with
  | top => exact (mult_top_pos_iff_order_neg f z).trans (sphereGermValue_eq_infty_iff f z).symm
  | coe a => exact mult_finite_pos_iff_sphereGermValue_eq hf (hfinite a)

/-- The original IM-sharing predicate is exactly equality of the corrected
spherical fibers. The nonconstant-germ hypotheses are the original ones. -/
theorem sharesIMOn_iff_sphereGerm_fibers {f g : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (b : Sphere) :
    SharesIMOn Ω f g b ↔ ∀ z ∈ Ω,
      (sphereGermValue f z = sphereTarget b ↔ sphereGermValue g z = sphereTarget b) := by
  constructor
  · intro h z hz
    rw [← mult_pos_iff_sphereGermValue_eq (hf.1 z hz) (hf.2 z hz),
      ← mult_pos_iff_sphereGermValue_eq (hg.1 z hz) (hg.2 z hz)]
    exact h z hz
  · intro h z hz
    rw [mult_pos_iff_sphereGermValue_eq (hf.1 z hz) (hf.2 z hz),
      mult_pos_iff_sphereGermValue_eq (hg.1 z hz) (hg.2 z hz)]
    exact h z hz

/-- At a regular germ the corrected sphere map locally reads as a genuine
analytic function, including at a removable singularity of the raw representative. -/
theorem sphereGermValue_finite_chart {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hn : 0 ≤ meromorphicOrderAt f z) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      sphereGermValue f =ᶠ[𝓝 z] (fun w => (H w : OnePoint ℂ)) := by
  let H := toMeromorphicNFAt f z
  have heq : f =ᶠ[𝓝[≠] z] H := hf.eq_nhdsNE_toMeromorphicNFAt
  have hHn : 0 ≤ meromorphicOrderAt H z := by
    rw [← meromorphicOrderAt_congr heq]
    exact hn
  have hHa : AnalyticAt ℂ H z :=
    (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := z)).meromorphicOrderAt_nonneg_iff_analyticAt.1 hHn
  have hpunct : sphereGermValue f =ᶠ[𝓝[≠] z] (fun w => (H w : OnePoint ℂ)) := by
    filter_upwards [hf.eventually_analyticAt, heq] with w hw hfw
    rw [sphereGermValue_eq_coe_of_analytic hw, hfw]
  exact ⟨H, hHa, ((continuousAt_sphereGermValue hf).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (OnePoint.continuous_coe.continuousAt.comp hHa.continuousAt)).1 hpunct⟩

/-- At a pole the inverse chart reads as an analytic function vanishing at
the pole. Its reciprocal is interpreted as infinity at its zeros. -/
theorem sphereGermValue_infty_chart {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hneg : meromorphicOrderAt f z < 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧ H z = 0 ∧
      (∀ᶠ w in 𝓝 z, sphereGermValue f w ≠ ((0 : ℂ) : OnePoint ℂ)) ∧
      sphereGermValue f =ᶠ[𝓝 z]
        (fun w => if H w = 0 then OnePoint.infty else (((H w)⁻¹ : ℂ) : OnePoint ℂ)) := by
  classical
  let H := toMeromorphicNFAt f⁻¹ z
  have heq : f⁻¹ =ᶠ[𝓝[≠] z] H := hf.inv.eq_nhdsNE_toMeromorphicNFAt
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hneg.ne_top
  have hnneg : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
  have hinvpos : 0 < meromorphicOrderAt f⁻¹ z := by
    rw [meromorphicOrderAt_inv, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (neg_pos.2 hnneg)
  have hHpos : 0 < meromorphicOrderAt H z := by
    rw [← meromorphicOrderAt_congr heq]
    exact hinvpos
  have hHa : AnalyticAt ℂ H z :=
    (meromorphicNFAt_toMeromorphicNFAt (f := f⁻¹) (x := z)).meromorphicOrderAt_nonneg_iff_analyticAt.1 hHpos.le
  have hHz : H z = 0 := tendsto_nhds_unique
    (hHa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_zero_of_meromorphicOrderAt_pos hHpos)
  have hvalue : sphereGermValue f z = OnePoint.infty :=
    (sphereGermValue_eq_infty_iff f z).2 hneg
  have hneq : sphereGermValue f z ≠ ((0 : ℂ) : OnePoint ℂ) := by
    rw [hvalue]
    exact (OnePoint.coe_ne_infty 0).symm
  have heventne := (continuousAt_sphereGermValue hf).eventually_ne hneq
  have hfnz := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).1 hneg.ne_top
  have hpunct : sphereGermValue f =ᶠ[𝓝[≠] z]
      (fun w => if H w = 0 then OnePoint.infty else (((H w)⁻¹ : ℂ) : OnePoint ℂ)) := by
    filter_upwards [hf.eventually_analyticAt, heq, hfnz] with w hw hrep hwne
    have hHw : H w = (f w)⁻¹ := hrep.symm
    rw [if_neg (by rw [hHw]; exact inv_ne_zero hwne),
      sphereGermValue_eq_coe_of_analytic hw, hHw, inv_inv]
  refine ⟨H, hHa, hHz, heventne, ?_⟩
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct
  simp only [hHz, ↓reduceIte]
  exact hvalue

/-- Nonconstant meromorphic germs on the plane give a nonconstant map into
the topological sphere. A constant infinity map is excluded explicitly. -/
theorem sphereGermValue_nonconstant {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) :
    ¬ ∃ p : OnePoint ℂ, ∀ z, sphereGermValue f z = p := by
  rintro ⟨p, hp⟩
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨w, hw⟩ := (hf.1 0 (mem_univ 0)).eventually_analyticAt.exists
    have h := hp w
    rw [sphereGermValue_eq_coe_of_analytic hw] at h
    exact OnePoint.coe_ne_infty _ h
  | coe c =>
    apply hf.2 0 (mem_univ 0) c
    apply meromorphicOrderAt_eq_top_iff.2
    filter_upwards [(hf.1 0 (mem_univ 0)).eventually_analyticAt] with w hw
    have h := hp w
    rw [sphereGermValue_eq_coe_of_analytic hw] at h
    exact sub_eq_zero.2 (OnePoint.coe_injective h)

end ThreeIM
