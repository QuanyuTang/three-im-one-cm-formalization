module

public import RequestProject.ThreeIM.ExponentialSector
public import RequestProject.ThreeIM.ExponentialLocal
public import RequestProject.ThreeIM.ExponentialSectorBounds
public import RequestProject.ThreeIM.ExponentialPoleLocal

/-!
# The remaining conclusions of Lemma 8.4

The original omission theorem supplies the input to the independently
proved Montel--Marty estimate. The auxiliary invariant at a simple pole
then excludes poles far out in every proper right or left sector.
Pole exclusion is stated for the meromorphic germ, allowing arbitrary
removable values in the raw complex-valued representative.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.sector_sphericalDeriv_bound
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
      ‖t‖ * (sphericalDeriv (sphereGermValue f) t +
        sphericalDeriv (sphereGermValue g) t) ≤ M := by
  have homitf : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult f (a j : Sphere) t = 0 := by
    intro δ hδ
    obtain ⟨R, hR⟩ := h.omits_shared_in_sectors hδ
    exact ⟨R, fun t ht hs j => (hR t ht hs j).1⟩
  have homitg : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → ∀ j, mult g (a j : Sphere) t = 0 := by
    intro δ hδ
    obtain ⟨R, hR⟩ := h.omits_shared_in_sectors hδ
    exact ⟨R, fun t ht hs j => (hR t ht hs j).2⟩
  obtain ⟨Rf, hRf, Mf, hMf⟩ := exists_meromorphic_sector_sphericalDeriv_bound
    h.pair.nonconst_f a h.pair.injective homitf hδ
  obtain ⟨Rg, hRg, Mg, hMg⟩ := exists_meromorphic_sector_sphericalDeriv_bound
    h.pair.nonconst_g a h.pair.injective homitg hδ
  refine ⟨max Rf Rg, hRf.trans_le (le_max_left _ _), Mf + Mg, ?_⟩
  intro t ht hs
  have hf := hMf t ((le_max_left _ _).trans ht) hs
  have hg := hMg t ((le_max_right _ _).trans ht) hs
  nlinarith

theorem ExponentialPair.sector_mult_top_zero
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| → mult f ⊤ t = 0 ∧ mult g ⊤ t = 0 := by
  obtain ⟨R₀, hR₀, M, hM⟩ := h.sector_sphericalDeriv_bound hδ
  let C : ℝ := max 0 M
  have hk : 0 < ‖κ‖ := norm_pos_iff.mpr h.κ_ne_zero
  refine ⟨max R₀ ((C + 1) / (2 * ‖κ‖)), hR₀.trans_le (le_max_left _ _), ?_⟩
  intro t ht hs
  have hfzero : mult f ⊤ t = 0 := by
    by_contra hfne
    have hmpos : 0 < mult f ⊤ t := Nat.pos_of_ne_zero hfne
    have hm : mult f ⊤ t = 1 := by have := (h.mult_top_le_one t).1; omega
    have ho : meromorphicOrderAt f t = -1 := by
      simpa [hm] using order_eq_neg_mult_top hmpos
    have hl := kappa_norm_le_sphericalDeriv_sum_at_simple_pole h.pair ho
      (h.auxPsi_eventually_eq t)
    have hb := hM t ((le_max_left _ _).trans ht) hs
    have hthreshold : (C + 1) / (2 * ‖κ‖) ≤ ‖t‖ := (le_max_right _ _).trans ht
    rw [div_le_iff₀ (by positivity)] at hthreshold
    have hmul := mul_le_mul_of_nonneg_left hl (norm_nonneg t)
    have hMC : M ≤ C := le_max_right _ _
    nlinarith
  exact ⟨hfzero, by rw [← h.pair.cm_top t (mem_univ t)]; exact hfzero⟩

end ThreeIM
