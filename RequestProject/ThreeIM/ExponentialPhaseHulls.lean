module

public import RequestProject.ThreeIM.ExponentialPhaseChartContinuity
public import RequestProject.ThreeIM.ExponentialHullCompactness
public import RequestProject.ThreeIM.ExponentialHullGeometry
public import RequestProject.ThreeIM.ExponentialGrowthCore
public import RequestProject.ThreeIM.RepresentativePairs

/-!
# Actual phase hulls of an irrational real stable exponent

All phase maps below are extracted from actual exponential-pair translates.
Their further subsequence property is proved using the same compactness,
uniform two-sided bounds, the local graph model, meromorphic identity, and
uniqueness of the companion. No phase-family existence is a hypothesis.

This file is a source candidate awaiting ordinary Lean verification.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

noncomputable def exponentialStablePhaseModel (d : ℂ) (μ : ℝ) (C : ℂ)
    (H : ℂ × ℂ → ℂ) (η : Circle) (z : ℂ) : ℂ :=
  d + H (Complex.exp (-z), C * (η : ℂ) * Complex.exp (-(μ : ℂ) * z))

theorem stable_phase_models_continuous_on_common_halfplane
    {H : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    {μ : ℝ} (hμ : 0 < μ) (C d : ℂ) :
    ∃ R : ℝ,
      (∀ η : Circle, ContinuousOn (exponentialStablePhaseModel d μ C H η)
        {z : ℂ | R < z.re}) ∧
      (∀ z : ℂ, R < z.re → Continuous
        (fun η : Circle => exponentialStablePhaseModel d μ C H η z)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hH.eventually_analyticAt
  obtain ⟨R, hR⟩ := real_stable_arguments_uniform_small hμ C hδ
  have harg (η : Circle) (z : ℂ) (hz : R < z.re) :
      AnalyticAt ℂ H (Complex.exp (-z), C * (η : ℂ) * Complex.exp (-(μ : ℂ) * z)) := by
    apply hball
    rw [mem_ball, dist_zero_right, Prod.norm_def]
    simpa only [Prod.norm_def, norm_mul, Circle.norm_coe, mul_one] using hR z hz.le
  refine ⟨R, fun η z hz => ?_, fun z hz => ?_⟩
  · have hinner : AnalyticAt ℂ (fun w : ℂ =>
        (Complex.exp (-w), C * (η : ℂ) * Complex.exp (-(μ : ℂ) * w))) z :=
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w)) z).prod
        (by fun_prop : AnalyticAt ℂ
          (fun w : ℂ => C * (η : ℂ) * Complex.exp (-(μ : ℂ) * w)) z)
    have hmodel : AnalyticAt ℂ (exponentialStablePhaseModel d μ C H η) z :=
      analyticAt_const.add ((harg η z hz).fun_comp (f := fun w : ℂ =>
        (Complex.exp (-w), C * (η : ℂ) * Complex.exp (-(μ : ℂ) * w))) (x := z) hinner)
    exact hmodel.continuousAt.continuousWithinAt
  · apply continuous_iff_continuousAt.mpr
    intro η
    have hinner : ContinuousAt (fun η' : Circle =>
        (Complex.exp (-z), C * (η' : ℂ) * Complex.exp (-(μ : ℂ) * z))) η :=
      continuousAt_const.prodMk
        ((continuousAt_const.mul continuous_subtype_val.continuousAt).mul continuousAt_const)
    exact continuousAt_const.add ((harg η z hz).continuousAt.comp'
      (f := fun η' : Circle =>
        (Complex.exp (-z), C * (η' : ℂ) * Complex.exp (-(μ : ℂ) * z))) (x := η) hinner)

/-- A nonempty open set of agreement determines the global honest maps.
The chart readings need not have their raw assigned values corrected in
advance; global germ identity and sphere reconstruction perform that step. -/
theorem sphere_maps_eq_of_eqOn_nonempty_open
    {S T : ℂ → OnePoint ℂ}
    (hS : SphereHolomorphicOn S univ) (hT : SphereHolomorphicOn T univ)
    (hSnc : ¬ ∃ p : OnePoint ℂ, ∀ z, S z = p)
    (hTnc : ¬ ∃ p : OnePoint ℂ, ∀ z, T z = p)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (heq : EqOn S T Ω) : S = T := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hlocal : (fun z => chartFiniteMap (S z)) =ᶠ[𝓝[≠] z₀]
      (fun z => chartFiniteMap (T z)) := by
    have hmem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Ω :=
      (show ∀ᶠ z in 𝓝 z₀, z ∈ Ω from hΩ.mem_nhds hz₀).filter_mono nhdsWithin_le_nhds
    exact hmem.mono fun z hz => congrArg chartFiniteMap (heq hz)
  have hglobal := auxiliary_globalize_identity
    (fun z => meromorphicOn_chartFiniteMap hS z (mem_univ z))
    (fun z => meromorphicOn_chartFiniteMap hT z (mem_univ z)) hlocal
  funext z
  have hg := sphereGermValue_congr
    (meromorphicOn_chartFiniteMap hS z (mem_univ z))
    (meromorphicOn_chartFiniteMap hT z (mem_univ z))
    (eventually_nhdsNE_of_codiscrete hglobal z)
  simpa only [sphereGermValue_chartFiniteMap hS hSnc,
    sphereGermValue_chartFiniteMap hT hTnc] using hg

/-- A closed region bound passes to a locally uniform limit even when the
members vary. The quantifier over all members is supplied by the original
uniform half-plane estimate, not by individual phase-dependent radii. -/
theorem sphere_family_limit_region_bound
    {F : ℕ → ℂ → OnePoint ℂ} {G : ℂ → OnePoint ℂ}
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    {P : ℝ → Prop} {p : OnePoint ℂ} {ε : ℝ}
    (hbound : ∀ n z, P z.re → dist (F n z) p ≤ ε) :
    ∀ z, P z.re → dist (G z) p ≤ ε := by
  intro z hz
  apply le_of_tendsto ((hconv.tendsto_at (mem_univ z)).dist tendsto_const_nhds)
  exact Eventually.of_forall fun n => hbound n z hz

theorem sphere_family_limit_nonconstant_of_common_bounds
    {F : ℕ → ℂ → OnePoint ℂ} {G : ℂ → OnePoint ℂ}
    (hconv : TendstoLocallyUniformlyOn F G atTop univ) {p q : OnePoint ℂ}
    (hpq : p ≠ q)
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n z, R ≤ z.re → dist (F n z) p ≤ ε)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n z, z.re ≤ -R → dist (F n z) q ≤ ε) :
    ¬ ∃ c : OnePoint ℂ, ∀ z, G z = c := by
  have hd : 0 < dist p q := dist_pos.mpr hpq
  have hε : 0 < dist p q / 4 := by positivity
  obtain ⟨R, hR⟩ := hRight (dist p q / 4) hε
  obtain ⟨L, hL⟩ := hLeft (dist p q / 4) hε
  have hr : dist (G (R : ℂ)) p ≤ dist p q / 4 :=
    sphere_family_limit_region_bound hconv (P := fun x => R ≤ x) hR (R : ℂ) (by simp)
  have hl : dist (G ((-L : ℝ) : ℂ)) q ≤ dist p q / 4 :=
    sphere_family_limit_region_bound hconv (P := fun x => x ≤ -L) hL
      ((-L : ℝ) : ℂ) (by simp)
  rintro ⟨c, hc⟩
  rw [hc] at hr hl
  have ht := dist_triangle p c q
  rw [dist_comm p c] at ht
  linarith

theorem sphereGermValue_comp_add (f : ℂ → ℂ) (hf : MeromorphicOn f univ) (c z : ℂ) :
    sphereGermValue (fun w => f (w + c)) z = sphereGermValue f (z + c) := by
  simpa only [one_mul, add_comm] using
    sphereGermValue_comp_affine (f := f) 1 c z one_ne_zero (hf _ (mem_univ _))

theorem stable_phase_model_at_nat_translate (d : ℂ) (μ : ℝ) (C : ℂ)
    (H : ℂ × ℂ → ℂ) (n : ℕ) (z : ℂ) :
    exponentialStablePhaseModel d μ C H 1 (z + (n : ℂ) * (2 * Real.pi * Complex.I)) =
      exponentialStablePhaseModel d μ C H (exponentialUnitPhase μ n) z := by
  have hc := exponential_nat_period n
  have hneg : Complex.exp (-((n : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
    rw [Complex.exp_neg, hc, inv_one]
  unfold exponentialStablePhaseModel
  rw [Circle.coe_one, mul_one, neg_add, Complex.exp_add, hneg, mul_one,
    mul_add, Complex.exp_add, coe_exponentialUnitPhase]
  congr 2
  ring

/-- The actual phase family includes both the exponential pair and a
joint further subsequence property. Neither field is an assumed black box.
The explicit first model is sufficient to identify the companion. -/
structure ExponentialPhaseHullSystem (a : Fin 3 → ℂ) (κ d : ℂ) (μ : ℝ) (C : ℂ)
    (H : ℂ × ℂ → ℂ) (R : ℝ) where
  first : Circle → ℂ → OnePoint ℂ
  second : Circle → ℂ → OnePoint ℂ
  pair : ∀ η, ExponentialPair a (fun z => chartFiniteMap (first η z))
    (fun z => chartFiniteMap (second η z)) κ
  holo_first : ∀ η, SphereHolomorphicOn (first η) univ
  holo_second : ∀ η, SphereHolomorphicOn (second η) univ
  nonconstant_first : ∀ η, ¬ ∃ p : OnePoint ℂ, ∀ z, first η z = p
  nonconstant_second : ∀ η, ¬ ∃ p : OnePoint ℂ, ∀ z, second η z = p
  model : ∀ η z, R < z.re → first η z =
    (exponentialStablePhaseModel d μ C H η z : OnePoint ℂ)
  further_subsequence : ∀ η (s : ℕ → Circle), Tendsto s atTop (𝓝 η) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => first (s (ψ n))) (first η) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => second (s (ψ n))) (second η) atTop univ

def SphereRealRegionBoundsTransfer (F G : ℂ → OnePoint ℂ) : Prop :=
  ∀ (P : ℝ → Prop) (p : OnePoint ℂ) (ε : ℝ),
    (∀ z, P z.re → dist (F z) p ≤ ε) → ∀ z, P z.re → dist (G z) p ≤ ε

/-- Positive imaginary periods and irrational rotation construct the
actual phase hulls. The four two-sided bounds are genuine consequences of
the original and reflected real stable formulae; the first formula is
used here to identify every phase. The companion needs no second model
uniqueness assumption. -/
theorem exists_exponential_phase_hull_system
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ)
    {μ : ℝ} (hμ : 0 < μ) (hμirr : Irrational μ) (C d : ℂ)
    {H : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0) {R₀ : ℝ}
    (heq : ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
      f z = d + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)))
    {pF qF pG qG : OnePoint ℂ} (hpFqF : pF ≠ qF) (hpGqG : pG ≠ qG)
    (hRightF : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue f z) pF ≤ ε)
    (hLeftF : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue f z) qF ≤ ε)
    (hRightG : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue g z) pG ≤ ε)
    (hLeftG : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue g z) qG ≤ ε) :
    ∃ R : ℝ, ∃ S : ExponentialPhaseHullSystem a κ d μ C H R,
      S.first 1 = sphereGermValue f := by
  classical
  obtain ⟨RH, hcontH, hcontη⟩ := stable_phase_models_continuous_on_common_halfplane hH hμ C d
  let R : ℝ := max R₀ RH
  let Ω : Set ℂ := {z | R < z.re}
  have hΩ : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_re
  have hΩne : Ω.Nonempty := ⟨((R + 1 : ℝ) : ℂ), by change R < R + 1; linarith⟩
  have hΩH : Ω ⊆ {z : ℂ | RH < z.re} := fun z hz =>
    (le_max_right R₀ RH).trans_lt hz
  have hΩ₀ : Ω ⊆ {z : ℂ | R₀ < z.re} := fun z hz =>
    (le_max_left R₀ RH).trans_lt hz
  have hMcont (η : Circle) : ContinuousOn (exponentialStablePhaseModel d μ C H η) Ω :=
    (hcontH η).mono hΩH
  have hMη (z : ℂ) (hz : z ∈ Ω) :
      Continuous (fun η : Circle => exponentialStablePhaseModel d μ C H η z) :=
    hcontη z (hΩH hz)
  have hOrigEq : f =ᶠ[codiscreteWithin Ω] exponentialStablePhaseModel d μ C H 1 := by
    filter_upwards [heq.filter_mono (Filter.codiscreteWithin.mono hΩ₀)] with z hz
    simpa only [exponentialStablePhaseModel, Circle.coe_one, mul_one] using hz
  have hOrig (z : ℂ) (hz : z ∈ Ω) :
      sphereGermValue f z = (exponentialStablePhaseModel d μ C H 1 z : OnePoint ℂ) :=
    sphereGermValue_eq_model_of_codiscreteWithin hΩ
      (fun w _ => h.pair.nonconst_f.1 w (mem_univ w)) (hMcont 1) hOrigEq hz
  have hEach : ∀ η : Circle, ∃ S T : ℂ → OnePoint ℂ,
      SphereHolomorphicOn S univ ∧ SphereHolomorphicOn T univ ∧
      (¬ ∃ p : OnePoint ℂ, ∀ z, S z = p) ∧
      (¬ ∃ p : OnePoint ℂ, ∀ z, T z = p) ∧
      ExponentialPair a (fun z => chartFiniteMap (S z)) (fun z => chartFiniteMap (T z)) κ ∧
      (∀ z, z ∈ Ω → S z = (exponentialStablePhaseModel d μ C H η z : OnePoint ℂ)) ∧
      SphereRealRegionBoundsTransfer (sphereGermValue f) S ∧
      SphereRealRegionBoundsTransfer (sphereGermValue g) T := by
    intro η
    obtain ⟨n, hn, hphase⟩ := exists_strictMono_exponentialUnitPhase_tendsto hμirr η
    let shift : ℕ → ℂ := fun k => (n k : ℂ) * (2 * Real.pi * Complex.I)
    have hperiod (k : ℕ) : Complex.exp (shift k) = 1 := exponential_nat_period (n k)
    have hRe (k : ℕ) : (shift k).re = 0 := by dsimp [shift]; simp
    obtain ⟨ψ, hψ, S, T, hSF, hTG⟩ := h.exists_joint_exponential_translate_limit hperiod
    let Fn : ℕ → ℂ → ℂ := fun k w => f (w + shift (ψ k))
    let Gn : ℕ → ℂ → ℂ := fun k w => g (w + shift (ψ k))
    have hseq (k : ℕ) : ExponentialPair a (Fn k) (Gn k) κ :=
      h.translate_exponential_period (hperiod (ψ k))
    have hCF : TendstoLocallyUniformlyOn (fun k => sphereGermValue (Fn k)) S atTop univ := by
      have heq : (fun k => sphereGermValue (Fn k)) =
          (fun k w => sphereGermValue f (w + shift (ψ k))) := by
        funext k w
        exact sphereGermValue_comp_add f h.pair.nonconst_f.1 (shift (ψ k)) w
      rw [heq]
      exact hSF
    have hCG : TendstoLocallyUniformlyOn (fun k => sphereGermValue (Gn k)) T atTop univ := by
      have heq : (fun k => sphereGermValue (Gn k)) =
          (fun k w => sphereGermValue g (w + shift (ψ k))) := by
        funext k w
        exact sphereGermValue_comp_add g h.pair.nonconst_g.1 (shift (ψ k)) w
      rw [heq]
      exact hTG
    have hS : SphereHolomorphicOn S univ := sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun k => sphereHolomorphicOn_sphereGermValue isOpen_univ
        (hseq k).pair.nonconst_f.1) hCF
    have hT : SphereHolomorphicOn T univ := sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun k => sphereHolomorphicOn_sphereGermValue isOpen_univ
        (hseq k).pair.nonconst_g.1) hCG
    have hSnc := sphere_translate_limit_nonconstant_of_halfplane_bounds hpFqF
      (fun k => hRe (ψ k)) hSF hRightF hLeftF
    have hTnc := sphere_translate_limit_nonconstant_of_halfplane_bounds hpGqG
      (fun k => hRe (ψ k)) hTG hRightG hLeftG
    have hpair := ExponentialPair.of_spherical_limits hseq hCF hCG hSnc hTnc
    have hmodel : ∀ z, z ∈ Ω → S z =
        (exponentialStablePhaseModel d μ C H η z : OnePoint ℂ) := by
      intro z hz
      have hmodelconv : Tendsto
          (fun k => exponentialStablePhaseModel d μ C H (exponentialUnitPhase μ (n (ψ k))) z)
          atTop (𝓝 (exponentialStablePhaseModel d μ C H η z)) :=
        (hMη z hz).tendsto η |>.comp (hphase.comp hψ.tendsto_atTop)
      have hvalues : (fun k => sphereGermValue f (z + shift (ψ k))) =ᶠ[atTop]
          (fun k => (exponentialStablePhaseModel d μ C H
            (exponentialUnitPhase μ (n (ψ k))) z : OnePoint ℂ)) := by
        apply Eventually.of_forall
        intro k
        have hzshift : z + shift (ψ k) ∈ Ω := by
          change R < (z + shift (ψ k)).re
          change R < z.re at hz
          simpa only [Complex.add_re, hRe, add_zero] using hz
        change sphereGermValue f (z + shift (ψ k)) =
          (exponentialStablePhaseModel d μ C H (exponentialUnitPhase μ (n (ψ k))) z : OnePoint ℂ)
        rw [hOrig _ hzshift]
        exact congrArg OnePoint.some (stable_phase_model_at_nat_translate d μ C H (n (ψ k)) z)
      exact tendsto_nhds_unique_of_eventuallyEq (hSF.tendsto_at (mem_univ z))
        ((OnePoint.continuous_coe.tendsto _).comp hmodelconv) hvalues
    exact ⟨S, T, hS, hT, hSnc, hTnc, hpair, hmodel,
      (fun P p ε hb => sphere_translate_limit_preserves_real_region_bound
        (fun k => hRe (ψ k)) hSF hb),
      (fun P p ε hb => sphere_translate_limit_preserves_real_region_bound
        (fun k => hRe (ψ k)) hTG hb)⟩
  choose F G hFholo hGholo hFnc hGnc hp hm htF htG using hEach
  have hrepF (η : Circle) : sphereGermValue (fun z => chartFiniteMap (F η z)) = F η :=
    funext (sphereGermValue_chartFiniteMap (hFholo η) (hFnc η))
  have hrepG (η : Circle) : sphereGermValue (fun z => chartFiniteMap (G η z)) = G η :=
    funext (sphereGermValue_chartFiniteMap (hGholo η) (hGnc η))
  have hbase : F 1 = sphereGermValue f := by
    apply sphere_maps_eq_of_eqOn_nonempty_open (hFholo 1)
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1)
      (hFnc 1) (sphereGermValue_nonconstant h.pair.nonconst_f) hΩ hΩne
    exact fun z hz => (hm 1 z hz).trans (hOrig z hz).symm
  have hsub : ∀ η (s : ℕ → Circle), Tendsto s atTop (𝓝 η) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun k => F (s (ψ k))) (F η) atTop univ ∧
        TendstoLocallyUniformlyOn (fun k => G (s (ψ k))) (G η) atTop univ := by
    intro η s hs
    obtain ⟨ψ, hψ, S, T, hCFraw, hCGraw⟩ := exists_joint_exponential_pair_limit
      (fun k => hp (s k))
    have hCF : TendstoLocallyUniformlyOn (fun k => F (s (ψ k))) S atTop univ := by
      simpa only [hrepF] using hCFraw
    have hCG : TendstoLocallyUniformlyOn (fun k => G (s (ψ k))) T atTop univ := by
      simpa only [hrepG] using hCGraw
    have hSnc : ¬ ∃ p : OnePoint ℂ, ∀ z, S z = p := by
      apply sphere_family_limit_nonconstant_of_common_bounds hCF hpFqF
      · intro ε hε
        obtain ⟨r, hr⟩ := hRightF ε hε
        exact ⟨r, fun k => htF (s (ψ k)) (fun x => r ≤ x) pF ε hr⟩
      · intro ε hε
        obtain ⟨r, hr⟩ := hLeftF ε hε
        exact ⟨r, fun k => htF (s (ψ k)) (fun x => x ≤ -r) qF ε hr⟩
    have hTnc : ¬ ∃ p : OnePoint ℂ, ∀ z, T z = p := by
      apply sphere_family_limit_nonconstant_of_common_bounds hCG hpGqG
      · intro ε hε
        obtain ⟨r, hr⟩ := hRightG ε hε
        exact ⟨r, fun k => htG (s (ψ k)) (fun x => r ≤ x) pG ε hr⟩
      · intro ε hε
        obtain ⟨r, hr⟩ := hLeftG ε hε
        exact ⟨r, fun k => htG (s (ψ k)) (fun x => x ≤ -r) qG ε hr⟩
    have hS : SphereHolomorphicOn S univ := sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun k => hFholo (s (ψ k))) hCF
    have hT : SphereHolomorphicOn T univ := sphereHolomorphicOn_of_eventually isOpen_univ
      (Eventually.of_forall fun k => hGholo (s (ψ k))) hCG
    have hSpair := ExponentialPair.of_spherical_limits
      (fun k => hp (s (ψ k))) hCFraw hCGraw hSnc hTnc
    have hSmodel (z : ℂ) (hz : z ∈ Ω) :
        S z = (exponentialStablePhaseModel d μ C H η z : OnePoint ℂ) := by
      exact tendsto_nhds_unique_of_eventuallyEq (hCF.tendsto_at (mem_univ z))
        ((OnePoint.continuous_coe.tendsto _).comp
          ((hMη z hz).tendsto η |>.comp (hs.comp hψ.tendsto_atTop)))
        (Eventually.of_forall fun k => hm (s (ψ k)) z hz)
    have hSF : S = F η := sphere_maps_eq_of_eqOn_nonempty_open hS (hFholo η)
      hSnc (hFnc η) hΩ hΩne (fun z hz => (hSmodel z hz).trans (hm η z hz).symm)
    have hmatched : ExponentialPair a (fun z => chartFiniteMap (F η z))
        (fun z => chartFiniteMap (T z)) κ := by simpa only [hSF] using hSpair
    have hTG : T = G η := by
      have hc := hmatched.companion_sphere_eq (hp η)
      simpa only [show sphereGermValue (fun z => chartFiniteMap (T z)) = T from
          funext (sphereGermValue_chartFiniteMap hT hTnc), hrepG] using hc
    exact ⟨ψ, hψ, by simpa only [hSF] using hCF, by simpa only [hTG] using hCG⟩
  exact ⟨R, {
    first := F
    second := G
    pair := hp
    holo_first := hFholo
    holo_second := hGholo
    nonconstant_first := hFnc
    nonconstant_second := hGnc
    model := hm
    further_subsequence := hsub
  }, hbase⟩

/-- The growth bound used by unit rigidity is discharged from the actual
exponential pair at each phase. No characteristic estimate is added as a
new phase-hull hypothesis. The real parameter avoids any separate circle
connectedness instance. -/
theorem ExponentialPhaseHullSystem.first_eq_base_of_critical
    {a : Fin 3 → ℂ} {κ d C : ℂ} {μ R : ℝ} {H : ℂ × ℂ → ℂ}
    (S : ExponentialPhaseHullSystem a κ d μ C H R) (j : Fin 3) (z : ℂ)
    (hm : 2 ≤ mult (fun w => chartFiniteMap (S.first 1 w)) (a j : Sphere) z) :
    ∀ η w, S.first η w = S.first 1 w := by
  have hpair (θ : ℝ) := S.pair (Circle.exp θ)
  have hsub : ∀ θ (s : ℕ → ℝ), Tendsto s atTop (𝓝 θ) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ TendstoLocallyUniformlyOn
        (fun n => S.first (Circle.exp (s (ψ n)))) (S.first (Circle.exp θ)) atTop univ := by
    intro θ s hs
    obtain ⟨ψ, hψ, hF, _⟩ := S.further_subsequence (Circle.exp θ)
      (fun n => Circle.exp (s n)) ((Circle.exp.continuous.tendsto θ).comp hs)
    exact ⟨ψ, hψ, hF⟩
  have hlin : ∀ θ : ℝ, ∃ A r₀ : ℝ, ∀ r, r₀ ≤ r →
      charT (fun w => chartFiniteMap (S.first (Circle.exp θ) w)) r ≤ A * r := by
    intro θ
    obtain ⟨A, hA⟩ := (S.pair (Circle.exp θ)).linear_growth
    obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp hA
    exact ⟨A, r₀, fun r hr => (hr₀ r hr).1⟩
  have hm₀ : 2 ≤ mult (fun w => chartFiniteMap (S.first (Circle.exp 0) w))
      (a j : Sphere) z := by simpa only [Circle.exp_zero] using hm
  have hlock := exponential_phase_first_eq_of_critical hpair
    (fun θ => S.holo_first (Circle.exp θ))
    (fun θ => S.nonconstant_first (Circle.exp θ)) hsub hlin (0 : ℝ) j z hm₀
  intro η w
  simpa only [Circle.exp_arg, Circle.exp_zero] using hlock (Complex.arg (η : ℂ)) w

/-- A critical fiber is incompatible with a complete irrational phase
hull and the actual local inverse-coordinate identity. Only the identity
at two small opposite arguments is used. -/
theorem ExponentialPhaseHullSystem.false_of_critical
    {a : Fin 3 → ℂ} {κ d C : ℂ} {μ R : ℝ} {H J : ℂ × ℂ → ℂ}
    (S : ExponentialPhaseHullSystem a κ d μ C H R)
    (hμ : 0 < μ) (hC : C ≠ 0)
    (hInv : ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      H p * Complex.exp (J (p.1, H p)) = p.2)
    (j : Fin 3) (z₀ : ℂ)
    (hm : 2 ≤ mult (fun w => chartFiniteMap (S.first 1 w)) (a j : Sphere) z₀) : False := by
  obtain ⟨δ, hδ, hδInv⟩ := Metric.mem_nhds_iff.mp hInv
  obtain ⟨R₁, hR₁⟩ := real_stable_arguments_uniform_small hμ C hδ
  let t : ℂ := ((max R R₁ + 1 : ℝ) : ℂ)
  let X : ℂ := Complex.exp (-t)
  let W : ℂ := C * Complex.exp (-(μ : ℂ) * t)
  have htR : R < t.re := by change R < max R R₁ + 1; linarith [le_max_left R R₁]
  have htR₁ : R₁ ≤ t.re := by change R₁ ≤ max R R₁ + 1; linarith [le_max_right R R₁]
  have hsmall : ‖(X, W)‖ < δ := hR₁ t htR₁
  have hsmallneg : ‖(X, -W)‖ < δ := by simpa only [Prod.norm_def, norm_neg] using hsmall
  have hpos : H (X, W) * Complex.exp (J (X, H (X, W))) = W :=
    hδInv (by simpa only [mem_ball, dist_zero_right] using hsmall)
  have hneg : H (X, -W) * Complex.exp (J (X, H (X, -W))) = -W :=
    hδInv (by simpa only [mem_ball, dist_zero_right] using hsmallneg)
  have hW : W ≠ 0 := mul_ne_zero hC (Complex.exp_ne_zero _)
  have hphaseπ : (Circle.exp Real.pi : ℂ) = -1 := by
    rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  have hfirst := S.first_eq_base_of_critical j z₀ hm (Circle.exp Real.pi) t
  rw [S.model _ t htR, S.model _ t htR] at hfirst
  have hmodel : H (X, -W) = H (X, W) := by
    have heq := OnePoint.coe_injective hfirst
    simp only [exponentialStablePhaseModel, Circle.coe_one, mul_one, hphaseπ] at heq
    have hminus : C * (-1) * Complex.exp (-(μ : ℂ) * t) = -W := by dsimp [W]; ring
    rw [hminus] at heq
    exact add_left_cancel heq
  exact stable_coordinate_opposite_ne H J X W hW hpos hneg hmodel.symm

/-- Main's actual-defect branch only needs this conclusion, rather than
rationality for every exponential pair. The critical multiplicity of the
original raw representative is transferred by punctured germ equality to
the base honest chart produced by the actual hull construction. -/
theorem ExponentialPair.not_irrational_stable_exponent_of_critical
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ)
    {μ : ℝ} (hμ : 0 < μ) (C d : ℂ) (hC : C ≠ 0)
    {H J : ℂ × ℂ → ℂ} (hH : AnalyticAt ℂ H 0) {R₀ : ℝ}
    (heq : ∀ᶠ z in codiscreteWithin {z : ℂ | R₀ < z.re},
      f z = d + H (Complex.exp (-z), C * Complex.exp (-(μ : ℂ) * z)))
    (hInv : ∀ᶠ p : ℂ × ℂ in 𝓝 0, H p * Complex.exp (J (p.1, H p)) = p.2)
    {pF qF pG qG : OnePoint ℂ} (hpFqF : pF ≠ qF) (hpGqG : pG ≠ qG)
    (hRightF : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue f z) pF ≤ ε)
    (hLeftF : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue f z) qF ≤ ε)
    (hRightG : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue g z) pG ≤ ε)
    (hLeftG : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue g z) qG ≤ ε)
    (j : Fin 3) (z : ℂ) (hm : 2 ≤ mult f (a j : Sphere) z) : ¬ Irrational μ := by
  intro hirr
  obtain ⟨R, S, hbase⟩ := exists_exponential_phase_hull_system h hμ hirr C d hH heq
    hpFqF hpGqG hRightF hLeftF hRightG hLeftG
  have hraw : f =ᶠ[codiscreteWithin univ]
      (fun w => chartFiniteMap (S.first 1 w)) := by
    rw [hbase]
    exact chartFinite_sphereGerm_eq_codiscreteWithin h.pair.nonconst_f.1
  have hmult := mult_congr_punctured
    (auxiliary_local_of_codiscreteWithin isOpen_univ hraw (mem_univ z)) (a j : Sphere)
  have hcritical : 2 ≤ mult (fun w => chartFiniteMap (S.first 1 w)) (a j : Sphere) z := by
    rw [← hmult]
    exact hm
  exact S.false_of_critical hμ hC hInv j z hcritical

/-- A genuine finite defect supplies a first-member critical point after
at most reflection and swapping. This operation preserves the original
coefficient; an unreflected swap would not do so. -/
theorem ExponentialPair.exists_critical_first_of_defect
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {j : Fin 3} {z : ℂ}
    (hd : IsDefect f g (a j : Sphere) z) :
    ∃ F G : ℂ → ℂ, ∃ w : ℂ, ExponentialPair a F G κ ∧ 2 ≤ mult F (a j : Sphere) w := by
  by_cases hf : 2 ≤ mult f (a j : Sphere) z
  · exact ⟨f, g, z, h, hf⟩
  · have hg : 2 ≤ mult g (a j : Sphere) z := by
      rcases hd with ⟨hfm, hgm, hne⟩
      omega
    refine ⟨(fun w => g (-w)), (fun w => f (-w)), -z, h.reflect_swap, ?_⟩
    have hneg : HasDerivAt (fun w : ℂ => -w) (-1) (-z) := by
      exact hasDerivAt_neg' (-z)
    have heq := mult_comp_of_deriv_ne_zero (f := g) (z := -z)
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => -w) (-z))
      (show deriv (fun w : ℂ => -w) (-z) ≠ 0 by rw [hneg.deriv]; norm_num)
      (a j : Sphere)
    have heq' : mult (fun w => g (-w)) (a j : Sphere) (-z) = mult g (a j : Sphere) z := by
      simpa only [Function.comp_def, neg_neg] using heq
    rw [heq']
    exact hg

end ThreeIM
