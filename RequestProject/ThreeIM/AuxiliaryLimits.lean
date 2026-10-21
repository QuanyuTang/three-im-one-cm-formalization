module

public import RequestProject.ThreeIM.Holomorphic
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Passing auxiliary identities through planar holomorphic limits

Clearing the cubic denominators before passing to the limit avoids any
assumption about the assigned values at removable singularities or poles.
The hypotheses concern analytic representatives on an open chart. Spherical
compactness and the existence of these charts are separate results.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem auxiliary_continuous_cubicP (a : Fin 3 → ℂ) : Continuous (cubicP a) := by
  unfold cubicP
  fun_prop

/-- Local nonconstancy makes the three cubic factors nonzero off a discrete
set, even when the original representatives have arbitrary isolated values. -/
theorem auxiliary_cubicP_ne_zero_codiscreteWithin {Ω : Set ℂ} {F : ℂ → ℂ}
    (hf : IsNonconstMeroOn F Ω) (a : Fin 3 → ℂ) :
    ∀ᶠ z in codiscreteWithin Ω, cubicP a (F z) ≠ 0 := by
  have hne (c : ℂ) : ∀ᶠ z in codiscreteWithin Ω, F z ≠ c := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro x hx
    have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      ((hf.1 x hx).sub analyticAt_const.meromorphicAt)).mp (hf.2 x hx c)
    filter_upwards [hn] with z hz
    exact Or.inl (sub_ne_zero.mp hz)
  filter_upwards [hne (a 0), hne (a 1), hne (a 2)] with z h0 h1 h2
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h0) (sub_ne_zero.mpr h1))
    (sub_ne_zero.mpr h2)

private theorem auxiliary_eqOn_of_codiscrete {Ω : Set ℂ} {F G : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : ContinuousOn F Ω) (hG : ContinuousOn G Ω)
    (hFG : F =ᶠ[codiscreteWithin Ω] G) : EqOn F G Ω := by
  intro x hx
  have hpunctured : F =ᶠ[𝓝[≠] x] G := by
    have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hFG x hx
    have hmem : ∀ᶠ z in 𝓝[≠] x, z ∈ Ω :=
      (show ∀ᶠ z in 𝓝 x, z ∈ Ω from hΩ.mem_nhds hx).filter_mono nhdsWithin_le_nhds
    filter_upwards [h, hmem] with z hz hzΩ
    exact hz.resolve_right fun hnot => hnot hzΩ
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hF.continuousAt (hΩ.mem_nhds hx)).mono_left nhdsWithin_le_nhds)
    ((hG.continuousAt (hΩ.mem_nhds hx)).mono_left nhdsWithin_le_nhds) hpunctured

/-- A codiscrete auxiliary equation for analytic representatives gives a
cleared equation at every point, including the marked fibers. -/
theorem auxiliary_cleared_eqOn {Ω : Set ℂ} {F D u : ℂ → ℂ} (a : Fin 3 → ℂ)
    (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω)
    (hfinite : IsNonconstMeroOn F Ω) (hD : ContinuousOn D Ω)
    (hu : ContinuousOn u Ω)
    (haux : (fun z => D z * deriv F z / cubicP a (F z)) =ᶠ[codiscreteWithin Ω] u) :
    EqOn (fun z => D z * deriv F z) (fun z => u z * cubicP a (F z)) Ω := by
  apply auxiliary_eqOn_of_codiscrete hΩ (hD.mul hF.deriv.continuousOn)
    (hu.mul ((auxiliary_continuous_cubicP a).comp_continuousOn hF.continuousOn))
  filter_upwards [haux, auxiliary_cubicP_ne_zero_codiscreteWithin hfinite a]
    with z hz hden
  exact (div_eq_iff hden).mp hz

/-- The cleared U and V equations are closed under locally uniform
holomorphic convergence on an open chart. Derivative convergence is the
Weierstrass theorem, rather than an additional limit hypothesis. -/
theorem auxiliary_cleared_limit {Ω : Set ℂ} (hΩ : IsOpen Ω) (a : Fin 3 → ℂ)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {f g u v : ℂ → ℂ}
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hG : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) Ω)
    (hFconv : TendstoLocallyUniformlyOn F f atTop Ω)
    (hGconv : TendstoLocallyUniformlyOn G g atTop Ω)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop Ω)
    (hU : ∀ᶠ n in atTop, ∀ z ∈ Ω,
      (F n z - G n z) * deriv (F n) z = uₙ n z * cubicP a (F n z))
    (hV : ∀ᶠ n in atTop, ∀ z ∈ Ω,
      (F n z - G n z) * deriv (G n) z = vₙ n z * cubicP a (G n z)) :
    (∀ z ∈ Ω, (f z - g z) * deriv f z = u z * cubicP a (f z)) ∧
      (∀ z ∈ Ω, (f z - g z) * deriv g z = v z * cubicP a (g z)) := by
  have hdf := hFconv.deriv hF hΩ
  have hdg := hGconv.deriv hG hΩ
  constructor
  · intro z hz
    have hleft := ((hFconv.tendsto_at hz).sub (hGconv.tendsto_at hz)).mul
      (hdf.tendsto_at hz)
    have hright := (huconv.tendsto_at hz).mul
      (((auxiliary_continuous_cubicP a).tendsto (f z)).comp (hFconv.tendsto_at hz))
    exact tendsto_nhds_unique_of_eventuallyEq hleft hright
      (hU.mono fun n hn => hn z hz)
  · intro z hz
    have hleft := ((hFconv.tendsto_at hz).sub (hGconv.tendsto_at hz)).mul
      (hdg.tendsto_at hz)
    have hright := (hvconv.tendsto_at hz).mul
      (((auxiliary_continuous_cubicP a).tendsto (g z)).comp (hGconv.tendsto_at hz))
    exact tendsto_nhds_unique_of_eventuallyEq hleft hright
      (hV.mono fun n hn => hn z hz)

/-- Once the limiting functions are locally nonconstant, the cleared
identities recover U, V, Psi and Phi off a discrete set. -/
theorem auxiliary_identities_of_cleared {Ω : Set ℂ} {f g u v : ℂ → ℂ}
    (a : Fin 3 → ℂ) (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω)
    (hU : ∀ᶠ z in codiscreteWithin Ω,
      (f z - g z) * deriv f z = u z * cubicP a (f z))
    (hV : ∀ᶠ z in codiscreteWithin Ω,
      (f z - g z) * deriv g z = v z * cubicP a (g z)) :
    (auxU a f g =ᶠ[codiscreteWithin Ω] u) ∧
      (auxV a f g =ᶠ[codiscreteWithin Ω] v) ∧
      (auxPsi a f g =ᶠ[codiscreteWithin Ω] fun z => u z * v z) ∧
      (auxPhi a f g =ᶠ[codiscreteWithin Ω] fun z => u z / v z) := by
  have hUeq : auxU a f g =ᶠ[codiscreteWithin Ω] u := by
    filter_upwards [hU, auxiliary_cubicP_ne_zero_codiscreteWithin hf a] with z hz hden
    exact (div_eq_iff hden).2 hz
  have hVeq : auxV a f g =ᶠ[codiscreteWithin Ω] v := by
    filter_upwards [hV, auxiliary_cubicP_ne_zero_codiscreteWithin hg a] with z hz hden
    exact (div_eq_iff hden).2 hz
  exact ⟨hUeq, hVeq, hUeq.mul hVeq, hUeq.div hVeq⟩

/-- A local auxiliary identity between global meromorphic functions extends
to the whole plane as an equality of punctured germs. -/
theorem auxiliary_globalize_identity {F G : ℂ → ℂ} (hF : Meromorphic F)
    (hG : Meromorphic G) {z₀ : ℂ} (hlocal : F =ᶠ[𝓝[≠] z₀] G) :
    F =ᶠ[codiscrete ℂ] G := by
  have hD : MeromorphicOn (fun z => F z - G z) univ :=
    fun z _ => (hF z).sub (hG z)
  have htop : meromorphicOrderAt (fun z => F z - G z) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (hlocal.mono fun z hz => sub_eq_zero.mpr hz)
  have hall : ∀ z, meromorphicOrderAt (fun z => F z - G z) z = ⊤ := by
    by_contra hne
    push_neg at hne
    obtain ⟨z, hz⟩ := hne
    exact ((hD.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨z, mem_univ z⟩, hz⟩ ⟨z₀, mem_univ z₀⟩) htop
  change {z : ℂ | F z = G z} ∈ codiscrete ℂ
  rw [mem_codiscrete]
  intro z
  rw [disjoint_principal_right, compl_compl]
  exact (meromorphicOrderAt_eq_top_iff.1 (hall z)).mono fun w hw => sub_eq_zero.mp hw

/-- The prescribed limiting coefficients also give locally uniform Psi and
Phi limits. Only the limiting denominator must be nonzero. -/
theorem auxiliary_coefficient_limits {Ω : Set ℂ} {uₙ vₙ : ℕ → ℂ → ℂ}
    {u v : ℂ → ℂ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hv0 : ∀ z ∈ Ω, v z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop Ω) :
    TendstoLocallyUniformlyOn (fun n z => uₙ n z * vₙ n z)
      (fun z => u z * v z) atTop Ω ∧
      TendstoLocallyUniformlyOn (fun n z => uₙ n z / vₙ n z)
        (fun z => u z / v z) atTop Ω := by
  exact ⟨huconv.mul₀ hvconv hu hv, huconv.div₀ hvconv hu hv hv0⟩

/-- Codiscrete agreement on an open chart determines each punctured germ. -/
theorem auxiliary_local_of_codiscreteWithin {Ω : Set ℂ} {f F : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hF : f =ᶠ[codiscreteWithin Ω] F) {x : ℂ} (hx : x ∈ Ω) :
    f =ᶠ[𝓝[≠] x] F := by
  have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hF x hx
  have hmem : ∀ᶠ z in 𝓝[≠] x, z ∈ Ω :=
    (show ∀ᶠ z in 𝓝 x, z ∈ Ω from hΩ.mem_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [h, hmem] with z hz hzΩ
  exact hz.resolve_right fun hnot => hnot hzΩ

/-- U, V, Psi and Phi are invariant under changing representatives on a
discrete set of an open chart, including the derivative terms. -/
theorem auxiliary_congr_codiscreteWithin {Ω : Set ℂ} {f g F G : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : f =ᶠ[codiscreteWithin Ω] F)
    (hg : g =ᶠ[codiscreteWithin Ω] G) (a : Fin 3 → ℂ) :
    (auxU a f g =ᶠ[codiscreteWithin Ω] auxU a F G) ∧
      (auxV a f g =ᶠ[codiscreteWithin Ω] auxV a F G) ∧
      (auxPsi a f g =ᶠ[codiscreteWithin Ω] auxPsi a F G) ∧
      (auxPhi a f g =ᶠ[codiscreteWithin Ω] auxPhi a F G) := by
  have hd {f F : ℂ → ℂ} (h : f =ᶠ[codiscreteWithin Ω] F) :
      deriv f =ᶠ[codiscreteWithin Ω] deriv F := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro x hx
    filter_upwards [(auxiliary_local_of_codiscreteWithin hΩ h hx).nhdsNE_deriv]
      with z hz
    exact Or.inl hz
  have hU : auxU a f g =ᶠ[codiscreteWithin Ω] auxU a F G := by
    filter_upwards [hf, hg, hd hf] with z hzF hzG hzD
    simp only [auxU, hzF, hzG, hzD]
  have hV : auxV a f g =ᶠ[codiscreteWithin Ω] auxV a F G := by
    filter_upwards [hf, hg, hd hg] with z hzF hzG hzD
    simp only [auxV, hzF, hzG, hzD]
  exact ⟨hU, hV, hU.mul hV, hU.div hV⟩

/-- A locally nonconstant meromorphic function has a derivative which is
nonzero off a discrete set. Thus a vanishing cleared limit equation forces
the two limiting germs to coincide. No meromorphic hypothesis on g is needed. -/
theorem auxiliary_eq_of_mul_deriv_eq_zero_on {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f Ω)
    (hprod : (fun z => (f z - g z) * deriv f z)
      =ᶠ[codiscreteWithin Ω] (fun _ => 0)) :
    f =ᶠ[codiscreteWithin Ω] g := by
  have hd : ∀ᶠ z in codiscreteWithin Ω, deriv f z ≠ 0 := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro z hz
    have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hf.1 z hz).deriv).mp (order_deriv_of_nonconst hf hz).1
    filter_upwards [hne] with w hw
    exact Or.inl hw
  filter_upwards [hprod, hd] with z hz hdz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hdz)

theorem auxiliary_eq_of_mul_deriv_eq_zero {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ)
    (hprod : (fun z => (f z - g z) * deriv f z) =ᶠ[codiscrete ℂ] (fun _ => 0)) :
    f =ᶠ[codiscrete ℂ] g :=
  auxiliary_eq_of_mul_deriv_eq_zero_on hf hprod

end ThreeIM
