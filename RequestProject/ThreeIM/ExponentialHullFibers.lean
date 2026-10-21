module

public import RequestProject.ThreeIM.SphereFibers
public import RequestProject.ThreeIM.SphereZeroPersistence

/-! # A nonconstant imaginary-translation limit forces an infinite fiber

A fixed finite source set escapes every translated local disk when the
imaginary translation tends to infinity. Hurwitz then preserves omission
of each finite fiber. Three finite fibers would give a nonconstant entire
spherical limit omitting three distinct values, contrary to little Picard.
No classification of finite-order or rational functions is needed.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem eventually_imaginary_translates_avoid_finite {S : Set ℂ} (hS : S.Finite)
    {shift : ℕ → ℂ} (hshift : Tendsto (fun n => (shift n).im) atTop atTop) (z : ℂ) :
    ∀ᶠ n in atTop, ∀ w ∈ ball z 1, w + shift n ∉ S := by
  obtain ⟨C, hC⟩ := (hS.image Complex.im).bddAbove
  filter_upwards [hshift.eventually_gt_atTop (C + ‖z‖ + 1)] with n hn w hw hwS
  have hb : (w + shift n).im ≤ C := hC (mem_image_of_mem Complex.im hwS)
  have hdist : ‖w - z‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hnorm := norm_sub_norm_le w z
  have him := (abs_le.mp (Complex.abs_im_le_norm w)).1
  simp only [Complex.add_im] at hb
  linarith

/-- A nonconstant spherical limit of the actual translates omits every
value whose original fiber is finite. The holomorphy and omission needed
by Hurwitz are proved locally for those same translates. -/
theorem sphere_limit_omits_finite_fiber_of_translates
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ} {a : OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ)
    (hshift : Tendsto (fun n => (shift n).im) atTop atTop)
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, G z = p)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (hfiber : {z : ℂ | F z = a}.Finite) : ∀ z, G z ≠ a := by
  obtain ⟨A, hA⟩ := exists_sphere_coordinate_zero a
  apply sphere_limit_omits_of_mobius_zero A hA hG hnc _ hconv
  intro z
  refine ⟨ball z 1, isOpen_ball, mem_ball_self (by norm_num), ?_⟩
  filter_upwards [eventually_imaginary_translates_avoid_finite hfiber hshift z]
    with n hn
  have hholo : SphereHolomorphicOn (fun w => F (w + shift n)) univ := by
    simpa only [preimage_univ] using
      sphereHolomorphicOn_comp hF (fun w => w + shift n) (by fun_prop)
  exact ⟨sphereHolomorphicOn_mono hholo isOpen_ball (subset_univ _),
    fun w hw ha => hn w hw ha⟩

/-- One of three distinct target fibers is infinite as soon as the
imaginary translates have a genuine nonconstant entire spherical limit.
In the exponential application that limit comes from normality and the
common left and right half-plane bounds, not from an added assumption
on the original main theorem. -/
theorem exists_infinite_sphere_fiber_of_translate_limit
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ}
    (hF : SphereHolomorphicOn F univ)
    (hshift : Tendsto (fun n => (shift n).im) atTop atTop)
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, G z = p)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (a : Fin 3 → OnePoint ℂ) (ha : Function.Injective a) :
    ∃ j, {z : ℂ | F z = a j}.Infinite := by
  classical
  by_contra hnone
  have hfin (j : Fin 3) : {z : ℂ | F z = a j}.Finite := by
    by_contra hj
    exact hnone ⟨j, hj⟩
  have homit (j : Fin 3) : ∀ z, G z ≠ a j :=
    sphere_limit_omits_finite_fiber_of_translates hF hshift hG hnc hconv (hfin j)
  exact hnc (sphere_picard_constant hG (a 0) (a 1) (a 2)
    (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
    (homit 0) (homit 1) (homit 2))

theorem exists_two_sphere_preimages_of_translate_limit
    {F G : ℂ → OnePoint ℂ} {shift : ℕ → ℂ}
    (hF : SphereHolomorphicOn F univ)
    (hshift : Tendsto (fun n => (shift n).im) atTop atTop)
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, G z = p)
    (hconv : TendstoLocallyUniformlyOn (fun n w => F (w + shift n)) G atTop univ)
    (a : Fin 3 → OnePoint ℂ) (ha : Function.Injective a) :
    ∃ j x y, x ≠ y ∧ F x = a j ∧ F y = a j := by
  obtain ⟨j, hj⟩ := exists_infinite_sphere_fiber_of_translate_limit hF hshift hG hnc hconv a ha
  obtain ⟨x, hx, y, hy, hxy⟩ := hj.nontrivial
  exact ⟨j, x, y, hxy, hx, hy⟩

theorem imaginary_multiples_tendsto_atTop {ω : ℂ} (hω : 0 < ω.im) :
    Tendsto (fun n : ℕ => ((n : ℂ) * ω).im) atTop atTop := by
  simpa only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, mul_zero, zero_add, add_zero, mul_comm] using
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop hω

end ThreeIM
