module

public import RequestProject.ThreeIM.ExponentialSectorDilates
public import RequestProject.ThreeIM.ExponentialSectorMarty
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Spherical derivative estimates on proper sectors

Omission of three fixed spherical values far out in every proper sector
implies the sector estimate by normality of dilates and a compactness
argument for their unit directions. No exponential expansion is assumed.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem eventually_dilate_sphericalDeriv_bounded {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ) (a : Fin 3 → OnePoint ℂ)
    (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, F t ≠ a j)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {w : ℕ → ℂ} {w₀ : ℂ} (hw : Tendsto w atTop (𝓝 w₀)) (hw₀ : 0 < w₀.re) :
    ∃ M : ℝ, ∀ᶠ n in atTop,
      r n * sphericalDeriv F ((r n : ℂ) * w n) ≤ M := by
  have hn := isNormalAt_dilates_of_sector_omission hF a ha homit hr hw₀
  have hol (H) (hH : H ∈ range (fun n z => F ((r n : ℂ) * z))) :
      SphereHolomorphicOn H univ := by
    obtain ⟨n, rfl⟩ := hH
    simpa only [preimage_univ, zero_add] using hF.comp_affine 0 (r n : ℂ)
  obtain ⟨ε, hε, M, hM⟩ := exists_sphericalDeriv_bound_of_isNormalAt
    isOpen_univ hol (mem_univ w₀) hn
  refine ⟨M, ?_⟩
  filter_upwards [hw.eventually (ball_mem_nhds w₀ hε),
    hr.eventually (eventually_ge_atTop 0)] with n hnw hnr
  have hb := hM (fun z => F ((r n : ℂ) * z)) ⟨n, rfl⟩ (w n) hnw
  have hscale := sphericalDeriv_comp_affine F 0 (r n : ℂ) (w n)
  simp only [zero_add, Complex.norm_real, Real.norm_of_nonneg hnr] at hscale
  rwa [hscale] at hb

theorem exists_sector_sphericalDeriv_bound {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ) (a : Fin 3 → OnePoint ℂ)
    (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, F t ≠ a j)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ t.re → ‖t‖ * sphericalDeriv F t ≤ M := by
  classical
  by_contra hbad
  push_neg at hbad
  have hsel (n : ℕ) : ∃ t : ℂ, (n : ℝ) + 1 ≤ ‖t‖ ∧
      δ * ‖t‖ ≤ t.re ∧ (n : ℝ) < ‖t‖ * sphericalDeriv F t :=
    hbad ((n : ℝ) + 1) (by positivity) (n : ℝ)
  choose t hnorm hsector hlarge using hsel
  have hpos (n : ℕ) : 0 < ‖t n‖ := by linarith [hnorm n, Nat.cast_nonneg (α := ℝ) n]
  have htop : Tendsto (fun n => ‖t n‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (show (n : ℝ) ≤ ‖t n‖ by linarith [hnorm n]))
      tendsto_natCast_atTop_atTop
  let d : ℕ → ℂ := fun n => t n / (‖t n‖ : ℂ)
  have hd (n : ℕ) : ‖d n‖ = 1 := by
    dsimp [d]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hpos n).ne']
  obtain ⟨d₀, _, ψ, hψ, hdir⟩ := tendsto_subseq_of_bounded
    (x := d) (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1))
    (fun n => mem_closedBall.mpr (by rw [dist_zero_right, hd n]))
  have hdre (n : ℕ) : δ ≤ (d n).re := by
    dsimp [d]
    rw [Complex.div_ofReal_re]
    exact (le_div_iff₀ (hpos n)).mpr (hsector n)
  have hδd : δ ≤ d₀.re := ge_of_tendsto
    (Complex.continuous_re.continuousAt.tendsto.comp hdir)
    (Eventually.of_forall fun n => hdre (ψ n))
  have hback (n : ℕ) : (‖t n‖ : ℂ) * d n = t n := by
    dsimp [d]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hpos n).ne')
  obtain ⟨M, hM⟩ := eventually_dilate_sphericalDeriv_bounded hF a ha homit
    (htop.comp hψ.tendsto_atTop) hdir (hδ.trans_le hδd)
  have hnat : ∀ᶠ n : ℕ in atTop, M < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop M)
  obtain ⟨n, hMn, hnn⟩ := (hM.and hnat).exists
  change ‖t (ψ n)‖ * sphericalDeriv F ((‖t (ψ n)‖ : ℂ) * d (ψ n)) ≤ M at hMn
  rw [hback] at hMn
  have hψn : (n : ℝ) ≤ (ψ n : ℝ) := by exact_mod_cast hψ.id_le n
  have hln := hlarge (ψ n)
  linarith

theorem exists_absolute_sector_sphericalDeriv_bound {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ) (a : Fin 3 → OnePoint ℂ)
    (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, F t ≠ a j)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ‖t‖ * sphericalDeriv F t ≤ M := by
  have hFn : SphereHolomorphicOn (fun z => F (-z)) univ := by
    simpa only [preimage_univ, zero_add, neg_one_mul] using hF.comp_affine 0 (-1)
  have homitn : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, F (-t) ≠ a j := by
    intro δ hδ
    obtain ⟨R, hR⟩ := homit δ hδ
    exact ⟨R, fun t ht hs j => hR (-t) (by simpa using ht) (by simpa using hs) j⟩
  obtain ⟨R₁, hR₁, M₁, hM₁⟩ := exists_sector_sphericalDeriv_bound hF a ha homit hδ
  obtain ⟨R₂, hR₂, M₂, hM₂⟩ := exists_sector_sphericalDeriv_bound hFn a ha homitn hδ
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), max M₁ M₂, ?_⟩
  intro t ht hs
  rcases le_abs'.mp hs with hneg | hpos
  · have hb := hM₂ (-t) (by simpa using (le_max_right R₁ R₂).trans ht)
      (by simp only [norm_neg, Complex.neg_re]; linarith)
    have hscale : sphericalDeriv (fun z => F (-z)) (-t) = sphericalDeriv F t := by
      simpa only [zero_add, neg_one_mul, norm_neg, norm_one, one_mul, neg_neg] using
        sphericalDeriv_comp_affine F 0 (-1) (-t)
    rw [norm_neg, hscale] at hb
    exact hb.trans (le_max_right _ _)
  · exact (hM₁ t ((le_max_left _ _).trans ht) hpos).trans (le_max_left _ _)

theorem exists_meromorphic_sector_sphericalDeriv_bound {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (a : Fin 3 → ℂ) (ha : Function.Injective a)
    (homit : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult f (a j : Sphere) t = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
        ‖t‖ * sphericalDeriv (sphereGermValue f) t ≤ M := by
  apply exists_absolute_sector_sphericalDeriv_bound
    (sphereHolomorphicOn_sphereGermValue isOpen_univ hf.1) (fun j => (a j : OnePoint ℂ))
    (fun i j h => ha (OnePoint.coe_injective h)) ?_ hδ
  intro δ hδ
  obtain ⟨R, hR⟩ := homit δ hδ
  refine ⟨R, fun t ht hs j heq => ?_⟩
  have hpos := (mult_finite_pos_iff_sphereGermValue_eq
    (hf.meromorphic t) (hf.2 t (mem_univ t) (a j))).mpr heq
  rw [hR t ht hs j] at hpos
  exact lt_irrefl (0 : ℕ) hpos

end ThreeIM
