module

public import RequestProject.ThreeIM.ExponentialSectorNormality
public import RequestProject.ThreeIM.ExponentialSectorFiniteLimit
public import RequestProject.ThreeIM.ExponentialSectorInfinite

/-!
# The second component of every right-hand dilate limit is infinity

If the second limit is finite at a point, it stays finite near that point.
The first limit either has a finite point there, contradicting the angular
bound, or is identically infinite there, contradicting the inverse-chart
identity. Subsequence extraction then proves actual convergence to infinity.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

private theorem sector_tendsto_of_subsubsequence {Y : Type*} [TopologicalSpace Y]
    {u : ℕ → Y} {b : Y}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n))) atTop (𝓝 b)) : Tendsto u atTop (𝓝 b) := by
  apply tendsto_def.mpr
  intro s hs
  by_contra hn
  have hf : ∃ᶠ n in atTop, u n ∉ s := not_eventually.mp hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨ψ, _, hconv⟩ := h φ hφ
  obtain ⟨n, hgood⟩ := (hconv.eventually hs).exists
  exact hbad (ψ n) hgood

theorem ExponentialPair.spherical_dilate_limit_g_eq_infty
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) (hz : 0 < z.re)
    {F G : ℂ → OnePoint ℂ}
    (hFc : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue f ((r n : ℂ) * w)) F atTop U)
    (hGc : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue g ((r n : ℂ) * w)) G atTop U) :
    G z = OnePoint.infty := by
  by_contra hGfin
  have hgs (n : ℕ) : ContinuousOn
      (fun w => sphereGermValue g ((r n : ℂ) * w)) U := by
    have hg : SphereHolomorphicOn (fun w => sphereGermValue g ((r n : ℂ) * w)) univ := by
      simpa only [preimage_univ, zero_add] using
        (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_g.1).comp_affine
          0 (r n : ℂ)
    exact hg.continuousOn.mono (subset_univ U)
  have hGAt : ContinuousAt G z :=
    (hGc.continuousOn (Frequently.of_forall hgs)).continuousAt (hU.mem_nhds hzU)
  have hUm : ∀ᶠ w : ℂ in 𝓝 z, w ∈ U := hU.mem_nhds hzU
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, w ∈ U ∧ G w ≠ OnePoint.infty ∧ 0 < w.re :=
    hUm.and
      ((hGAt.eventually (eventually_ne_nhds hGfin)).and
        (Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hz)))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  by_cases hFfinite : ∃ w ∈ ball z ε, F w ≠ OnePoint.infty
  · obtain ⟨w, hw, hFw⟩ := hFfinite
    exact h.spherical_dilate_limit_not_both_finite hr hU (hεsub hw).1
      (hεsub hw).2.2 hFc hGc hFw (hεsub hw).2.1
  · have hFconst : (ball z ε).EqOn F (fun _ => OnePoint.infty) := by
      intro w hw
      by_contra hneq
      exact hFfinite ⟨w, hw, hneq⟩
    have hsub : ball z ε ⊆ U := fun w hw => (hεsub hw).1
    exact h.not_infinite_finite_dilate_limits hr isOpen_ball (mem_ball_self hε) hz
      ((hFc.mono hsub).congr_right hFconst) (hGc.mono hsub) hGfin

theorem ExponentialPair.sphereGerm_g_dilate_tendsto_infty
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n => sphereGermValue g ((r n : ℂ) * z)) atTop (𝓝 OnePoint.infty) := by
  apply sector_tendsto_of_subsubsequence
  intro φ hφ
  have hrφ : Tendsto (fun n => r (φ n)) atTop atTop := hr.comp hφ.tendsto_atTop
  obtain ⟨U, hU, hzU, ψ, hψ, F, G, _, _, hFc, hGc⟩ :=
    h.dilate_pair_subsequence hrφ hz
  have hg := h.spherical_dilate_limit_g_eq_infty
    (hrφ.comp hψ.tendsto_atTop) hU hzU hz hFc hGc
  refine ⟨ψ, hψ, ?_⟩
  simpa only [hg] using hGc.tendsto_at hzU

theorem ExponentialPair.sphereGerm_g_dilate_moving_tendsto_infty
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z : ℂ} (hz : 0 < z.re)
    {w : ℕ → ℂ} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => sphereGermValue g ((r n : ℂ) * w n)) atTop (𝓝 OnePoint.infty) := by
  have hn := (h.dilates_isNormalAt hr hz).2
  have hc : ∀ S ∈ range (fun n v => sphereGermValue g ((r n : ℂ) * v)), Continuous S := by
    rintro S ⟨n, rfl⟩
    have hg : SphereHolomorphicOn (fun v => sphereGermValue g ((r n : ℂ) * v)) univ := by
      simpa only [preimage_univ, zero_add] using
        (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_g.1).comp_affine
          0 (r n : ℂ)
    exact continuousOn_univ.mp hg.continuousOn
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, heq⟩ := hn.equicontinuousAt hc (ε / 2) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp hw δ hδ,
    Metric.tendsto_nhds.mp (h.sphereGerm_g_dilate_tendsto_infty hr hz)
      (ε / 2) (by positivity)] with n hwn hgn
  have hh := heq (fun v => sphereGermValue g ((r n : ℂ) * v)) (mem_range_self n) (w n) hwn
  exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith)

end ThreeIM
