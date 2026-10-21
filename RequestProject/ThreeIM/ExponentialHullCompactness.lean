module

public import RequestProject.ThreeIM.ExponentialData
public import RequestProject.ThreeIM.AuxiliaryExhaustion
public import RequestProject.ThreeIM.AuxiliaryRatioExhaustion
public import RequestProject.ThreeIM.ExponentialHullBounds

/-! # Actual translation subsequences for an exponential pair

Translations by periods of the exponential leave both prescribed auxiliary
coefficients unchanged. The proved auxiliary normality theorem therefore
applies to these actual translates, and the spherical exhaustion diagonal
extracts a joint locally uniform limit on the whole plane.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.toAuxiliaryPair {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) :
    AuxiliaryPairOn univ f g (fun z => κ * Complex.exp z)
      (fun z => κ * Complex.exp (-z)) a where
  pair := h.pair
  holo_u := by fun_prop
  holo_v := by fun_prop
  nonzero_u := fun z _ => mul_ne_zero h.κ_ne_zero (Complex.exp_ne_zero z)
  nonzero_v := fun z _ => mul_ne_zero h.κ_ne_zero (Complex.exp_ne_zero (-z))
  u_eq := h.eq_U
  v_eq := h.eq_V

theorem ExponentialPair.translate_auxiliary {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ c : ℂ}
    (h : ExponentialPair a f g κ) (hc : Complex.exp c = 1) :
    AuxiliaryPairOn univ (fun z => f (z + c)) (fun z => g (z + c))
      (fun z => κ * Complex.exp z) (fun z => κ * Complex.exp (-z)) a := by
  have ht := h.toAuxiliaryPair.comp_affine 1 c one_ne_zero
    (fun _ _ => mem_univ _ : MapsTo (fun w : ℂ => c + 1 * w) univ univ)
  have hneg : Complex.exp (-c) = 1 := by rw [Complex.exp_neg, hc, inv_one]
  simpa only [one_mul, add_comm c, Complex.exp_add, neg_add_rev, hc, hneg,
    one_mul, mul_one] using ht

theorem ExponentialPair.translate_exponential_period
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ c : ℂ}
    (h : ExponentialPair a f g κ) (hc : Complex.exp c = 1) :
    ExponentialPair a (fun z => f (z + c)) (fun z => g (z + c)) κ := by
  have ht := h.translate_auxiliary hc
  exact ⟨ht.pair, h.κ_ne_zero, ht.u_eq, ht.v_eq⟩

private theorem exponential_hull_fixed_tlu (u : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => u) u atTop univ := by
  intro e he z _
  exact ⟨univ, Filter.univ_mem, Eventually.of_forall
    (fun _ _ _ => refl_mem_uniformity he)⟩

/-- The same two nowhere-zero coefficients and their simple quotient
one-points give normality for any actual sequence of exponential pairs. -/
theorem exponential_pairs_normal
    {a : Fin 3 → ℂ} {F G : ℕ → ℂ → ℂ} {κ : ℂ}
    (h : ∀ n, ExponentialPair a (F n) (G n) κ) :
    IsNormal (range (fun n => sphereGermValue (F n))) univ ∧
      IsNormal (range (fun n => sphereGermValue (G n))) univ := by
  let u : ℂ → ℂ := fun w => κ * Complex.exp w
  let v : ℂ → ℂ := fun w => κ * Complex.exp (-w)
  have hseq (n : ℕ) : AuxiliaryPairOn univ (F n) (G n) u v a :=
    (h n).toAuxiliaryPair
  have hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) u v a :=
    fun z => ⟨univ, isOpen_univ, mem_univ z, Eventually.of_forall hseq⟩
  have hratio : (fun w => u w / v w) = fun w => Complex.exp (2 * w) := by
    funext w
    dsimp only [u, v]
    rw [mul_div_mul_left _ _ (h 0).κ_ne_zero, ← Complex.exp_sub]
    congr 1
    ring
  have hsimple (z : ℂ) (_hz : u z = v z) : deriv (fun w => u w / v w) z ≠ 0 := by
    rw [hratio]
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (2 * w))
        (Complex.exp (2 * z) * 2) z := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id z).const_mul (2 : ℂ)).cexp
    rw [hd.deriv]
    exact mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)
  have hNF : IsNormal (range (fun n => sphereGermValue (F n))) univ :=
    auxiliary_pairs_isNormal_of_locally_eventually hloc (by fun_prop) (by fun_prop)
      (fun z => mul_ne_zero (h 0).κ_ne_zero (Complex.exp_ne_zero (-z)))
      (exponential_hull_fixed_tlu u) (exponential_hull_fixed_tlu v) hsimple
  have hNG := auxiliary_pairs_companion_isNormal_of_locally_eventually hloc hNF
  exact ⟨hNF, hNG⟩

theorem exists_joint_exponential_pair_limit
    {a : Fin 3 → ℂ} {F G : ℕ → ℂ → ℂ} {κ : ℂ}
    (h : ∀ n, ExponentialPair a (F n) (G n) κ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ H K : ℂ → OnePoint ℂ,
      TendstoLocallyUniformlyOn (fun n => sphereGermValue (F (ψ n))) H atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => sphereGermValue (G (ψ n))) K atTop univ := by
  obtain ⟨hF, hG⟩ := exponential_pairs_normal h
  exact sphere_pair_subsequence_of_normal hF hG

/-- Normality of the actual spherical translates of both members. There
is no hypothesis that a limit, stable graph or phase family exists. -/
theorem ExponentialPair.exponential_translates_normal
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {shift : ℕ → ℂ}
    (hshift : ∀ n, Complex.exp (shift n) = 1) :
    IsNormal (range (fun n w => sphereGermValue f (w + shift n))) univ ∧
      IsNormal (range (fun n w => sphereGermValue g (w + shift n))) univ := by
  let F : ℕ → ℂ → ℂ := fun n w => f (w + shift n)
  let G : ℕ → ℂ → ℂ := fun n w => g (w + shift n)
  have hn : IsNormal (range (fun n => sphereGermValue (F n))) univ ∧
      IsNormal (range (fun n => sphereGermValue (G n))) univ :=
    exponential_pairs_normal (fun n => h.translate_exponential_period (hshift n))
  have hFeq (n : ℕ) : sphereGermValue (F n) = fun w => sphereGermValue f (w + shift n) := by
    funext w
    simpa only [F, one_mul, add_comm] using
      sphereGermValue_comp_affine (f := f) 1 (shift n) w one_ne_zero
        (h.pair.nonconst_f.1 _ (mem_univ _))
  have hGeq (n : ℕ) : sphereGermValue (G n) = fun w => sphereGermValue g (w + shift n) := by
    funext w
    simpa only [G, one_mul, add_comm] using
      sphereGermValue_comp_affine (f := g) 1 (shift n) w one_ne_zero
        (h.pair.nonconst_g.1 _ (mem_univ _))
  simpa only [hFeq, hGeq] using hn

theorem ExponentialPair.exists_joint_exponential_translate_limit
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {shift : ℕ → ℂ}
    (hshift : ∀ n, Complex.exp (shift n) = 1) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F G : ℂ → OnePoint ℂ,
      TendstoLocallyUniformlyOn (fun n w => sphereGermValue f (w + shift (ψ n))) F atTop univ ∧
      TendstoLocallyUniformlyOn (fun n w => sphereGermValue g (w + shift (ψ n))) G atTop univ := by
  obtain ⟨hF, hG⟩ := h.exponential_translates_normal hshift
  exact sphere_pair_subsequence_of_normal hF hG

/-- Actual half-plane bounds and escaping imaginary exponential periods
force an infinite fiber of the original first member. The convergent
subsequence, its holomorphy and its nonconstancy are all derived. -/
theorem ExponentialPair.exists_infinite_fiber_of_halfplane_bounds
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {shift : ℕ → ℂ} {p q : OnePoint ℂ}
    (hshift : ∀ n, Complex.exp (shift n) = 1)
    (hshiftRe : ∀ n, (shift n).re = 0)
    (hshiftIm : Tendsto (fun n => (shift n).im) atTop atTop)
    (hpq : p ≠ q)
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue f z) p ≤ ε)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue f z) q ≤ ε) :
    ∃ j : Fin 3, {z : ℂ | sphereGermValue f z = (a j : OnePoint ℂ)}.Infinite := by
  obtain ⟨ψ, hψ, F, G, hFconv, _hGconv⟩ := h.exists_joint_exponential_translate_limit hshift
  exact exists_infinite_sphere_fiber_of_halfplane_translate_limit
    (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1)
    hpq (fun n => hshiftRe (ψ n)) (hshiftIm.comp hψ.tendsto_atTop) hFconv hRight hLeft
    (fun j => (a j : OnePoint ℂ)) (OnePoint.coe_injective.comp h.pair.injective)

theorem exponential_nat_period (n : ℕ) :
    Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
  simpa only [Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (n : ℤ)

/-- In the application no escaping sequence is assumed: the actual
integer periods `2πin` give one. The only analytic input left here is the
two-sided bound supplied by the stable expansions. -/
theorem ExponentialPair.exists_infinite_fiber_of_two_sided_bounds
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {p q : OnePoint ℂ}
    (hpq : p ≠ q)
    (hRight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      R ≤ z.re → dist (sphereGermValue f z) p ≤ ε)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re ≤ -R → dist (sphereGermValue f z) q ≤ ε) :
    ∃ j : Fin 3, {z : ℂ | sphereGermValue f z = (a j : OnePoint ℂ)}.Infinite := by
  apply h.exists_infinite_fiber_of_halfplane_bounds
    (shift := fun n => (n : ℂ) * (2 * Real.pi * Complex.I))
    exponential_nat_period (fun n => by simp) ?_ hpq hRight hLeft
  apply imaginary_multiples_tendsto_atTop
  simpa using mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos

end ThreeIM
