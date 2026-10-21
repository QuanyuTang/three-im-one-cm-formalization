module

public import RequestProject.ThreeIM.ExponentialHullFibers

/-! # The common two-sided bounds exclude constant translation limits

Uniform left and right half-plane bounds are unchanged by imaginary
translations. Their closed distance bounds pass to every spherical
locally uniform limit. Two distinct limiting targets then give two
separated finite source anchors, so that the limit is nonconstant.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_translate_limit_preserves_real_region_bound
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ}
    (hshift : ∀ n, (shift n).re = 0)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    {P : ℝ → Prop} {p : OnePoint ℂ} {ε : ℝ}
    (hbound : ∀ z : ℂ, P z.re → dist (F z) p ≤ ε) :
    ∀ z : ℂ, P z.re → dist (G z) p ≤ ε := by
  intro z hz
  apply le_of_tendsto ((hconv.tendsto_at (mem_univ z)).dist tendsto_const_nhds)
  apply Eventually.of_forall
  intro n
  apply hbound
  simpa only [Complex.add_re, hshift n, add_zero] using hz

theorem sphere_translate_limit_preserves_right_bounds
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ} {p : OnePoint ℂ}
    (hshift : ∀ n, (shift n).re = 0)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re → dist (F z) p ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re → dist (G z) p ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hbound ε hε
  exact ⟨R, sphere_translate_limit_preserves_real_region_bound
    (P := fun x => R ≤ x) hshift hconv hR⟩

theorem sphere_translate_limit_nonconstant_of_halfplane_bounds
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ} {p q : OnePoint ℂ}
    (hpq : p ≠ q) (hshift : ∀ n, (shift n).re = 0)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re → dist (F z) p ≤ ε)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, z.re ≤ -R → dist (F z) q ≤ ε) :
    ¬ ∃ c : OnePoint ℂ, ∀ z : ℂ, G z = c := by
  have hd : 0 < dist p q := dist_pos.mpr hpq
  have hε : 0 < dist p q / 4 := by positivity
  obtain ⟨R, hR⟩ := hRight (dist p q / 4) hε
  obtain ⟨L, hL⟩ := hLeft (dist p q / 4) hε
  have hr : dist (G (R : ℂ)) p ≤ dist p q / 4 :=
    sphere_translate_limit_preserves_real_region_bound (P := fun x => R ≤ x) hshift hconv hR
      (R : ℂ) (by simp)
  have hl : dist (G ((-L : ℝ) : ℂ)) q ≤ dist p q / 4 :=
    sphere_translate_limit_preserves_real_region_bound (P := fun x => x ≤ -L) hshift hconv hL
      ((-L : ℝ) : ℂ) (by simp)
  rintro ⟨c, hc⟩
  rw [hc] at hr hl
  have ht := dist_triangle p c q
  rw [dist_comm p c] at ht
  linarith

/-- The needed infinite fiber follows from the actual two-sided bounds
and an actual translation limit. Holomorphy and nonconstancy of the limit
are proved here, rather than included as extra external hypotheses. -/
theorem exists_infinite_sphere_fiber_of_halfplane_translate_limit
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ} {p q : OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ) (hpq : p ≠ q)
    (hshiftRe : ∀ n, (shift n).re = 0)
    (hshiftIm : Tendsto (fun n => (shift n).im) atTop atTop)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ z.re → dist (F z) p ≤ ε)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, z.re ≤ -R → dist (F z) q ≤ ε)
    (a : Fin 3 → OnePoint ℂ) (ha : Function.Injective a) :
    ∃ j, {z : ℂ | F z = a j}.Infinite := by
  have hFn (n : ℕ) : SphereHolomorphicOn (fun w => F (w + shift n)) univ := by
    simpa only [preimage_univ] using
      sphereHolomorphicOn_comp hF (fun w => w + shift n) (by fun_prop)
  have hG : SphereHolomorphicOn G univ :=
    sphereHolomorphicOn_of_eventually isOpen_univ (Eventually.of_forall hFn) hconv
  exact exists_infinite_sphere_fiber_of_translate_limit hF hshiftIm hG
    (sphere_translate_limit_nonconstant_of_halfplane_bounds hpq hshiftRe hconv hRight hLeft)
    hconv a ha

end ThreeIM
