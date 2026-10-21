module

public import RequestProject.ThreeIM.ExponentialSectorCanonical
public import RequestProject.ThreeIM.SphereLimits

/-!
# Simultaneous spherical subsequences of exponential dilates

Each component is normal near every point of the right half-plane by
the omission part of Lemma 8.4.  The two successive subsequence choices
are made on one open neighborhood, and both limits are sphere-holomorphic
there.  No stable expansion or periodicity is used.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_pair_subsequence_of_isNormalAt {F G : ℕ → ℂ → OnePoint ℂ} {z : ℂ}
    (hF : IsNormalAt (range F) z) (hG : IsNormalAt (range G) z) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f g : ℂ → OnePoint ℂ,
        TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U ∧
        TendstoLocallyUniformlyOn (fun n => G (φ n)) g atTop U := by
  obtain ⟨Uf, hUf, hFN⟩ := hF
  obtain ⟨Ug, hUg, hGN⟩ := hG
  let U : Set ℂ := interior Uf ∩ interior Ug
  have hU : IsOpen U := isOpen_interior.inter isOpen_interior
  have hz : z ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hUf,
    mem_interior_iff_mem_nhds.mpr hUg⟩
  have hFN' : IsNormal (range F) U :=
    hFN.mono (inter_subset_left.trans interior_subset)
  have hGN' : IsNormal (range G) U :=
    hGN.mono (inter_subset_right.trans interior_subset)
  obtain ⟨ψ, hψ, f, hfc⟩ := hFN' (fun n => ⟨F n, mem_range_self n⟩)
  obtain ⟨χ, hχ, g, hgc⟩ := hGN' (fun n => ⟨G (ψ n), mem_range_self (ψ n)⟩)
  refine ⟨U, hU, hz, ψ ∘ χ, hψ.comp hχ, f, g, ?_, hgc⟩
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := hfc v hv x hx
  exact ⟨t, ht, hχ.tendsto_atTop.eventually hev⟩

theorem ExponentialPair.dilates_isNormalAt
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z : ℂ} (hz : 0 < z.re) :
    IsNormalAt (range (fun n w => sphereGermValue f ((r n : ℂ) * w))) z ∧
    IsNormalAt (range (fun n w => sphereGermValue g ((r n : ℂ) * w))) z := by
  have hf : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult f (a j : Sphere) t = 0 := by
    intro δ hδ
    obtain ⟨R, hR⟩ := h.omits_shared_in_sectors hδ
    exact ⟨R, fun t ht hs j => (hR t ht hs j).1⟩
  have hg : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult g (a j : Sphere) t = 0 := by
    intro δ hδ
    obtain ⟨R, hR⟩ := h.omits_shared_in_sectors hδ
    exact ⟨R, fun t ht hs j => (hR t ht hs j).2⟩
  exact ⟨isNormalAt_meromorphic_dilates_of_sector_mult_zero
    h.pair.nonconst_f a h.pair.injective hf hr hz,
    isNormalAt_meromorphic_dilates_of_sector_mult_zero
    h.pair.nonconst_g a h.pair.injective hg hr hz⟩

theorem ExponentialPair.dilate_pair_subsequence
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {z : ℂ} (hz : 0 < z.re) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ F G : ℂ → OnePoint ℂ,
        SphereHolomorphicOn F U ∧ SphereHolomorphicOn G U ∧
        TendstoLocallyUniformlyOn
          (fun n w => sphereGermValue f ((r (φ n) : ℂ) * w)) F atTop U ∧
        TendstoLocallyUniformlyOn
          (fun n w => sphereGermValue g ((r (φ n) : ℂ) * w)) G atTop U := by
  obtain ⟨hnf, hng⟩ := h.dilates_isNormalAt hr hz
  obtain ⟨U, hU, hzU, φ, hφ, F, G, hFc, hGc⟩ :=
    sphere_pair_subsequence_of_isNormalAt hnf hng
  have hfs (n : ℕ) : SphereHolomorphicOn
      (fun w => sphereGermValue f ((r (φ n) : ℂ) * w)) U := by
    apply sphereHolomorphicOn_mono _ hU (subset_univ U)
    simpa only [preimage_univ, zero_add] using
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1).comp_affine
        0 (r (φ n) : ℂ)
  have hgs (n : ℕ) : SphereHolomorphicOn
      (fun w => sphereGermValue g ((r (φ n) : ℂ) * w)) U := by
    apply sphereHolomorphicOn_mono _ hU (subset_univ U)
    simpa only [preimage_univ, zero_add] using
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_g.1).comp_affine
        0 (r (φ n) : ℂ)
  exact ⟨U, hU, hzU, φ, hφ, F, G,
    sphereHolomorphicOn_of_eventually hU (Eventually.of_forall hfs) hFc,
    sphereHolomorphicOn_of_eventually hU (Eventually.of_forall hgs) hGc, hFc, hGc⟩

end ThreeIM
