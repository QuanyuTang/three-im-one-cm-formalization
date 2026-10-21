module

public import RequestProject.ThreeIM.ExponentialSectorAsymptotics
public import RequestProject.ThreeIM.RepresentativePairs

/-!
# Canonical representatives of exponential pairs on pole-free sectors

The original raw functions may have arbitrary values at removable points.
Taking the finite chart of their corrected spherical germs preserves the
exponential pair and gives actual analytic representatives in the sectors.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.congr_codiscrete {a : Fin 3 → ℂ} {f g F G : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) (hf : f =ᶠ[codiscrete ℂ] F) (hg : g =ᶠ[codiscrete ℂ] G) :
    ExponentialPair a F G κ := by
  have heq := auxiliary_congr_codiscreteWithin isOpen_univ hf hg a
  exact ⟨h.pair.congr_codiscreteWithin isOpen_univ hf hg, h.κ_ne_zero,
    heq.1.symm.trans h.eq_U, heq.2.1.symm.trans h.eq_V⟩

theorem ExponentialPair.canonical_representatives {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) :
    ExponentialPair a (fun z => chartFiniteMap (sphereGermValue f z))
      (fun z => chartFiniteMap (sphereGermValue g z)) κ :=
  h.congr_codiscrete (chartFinite_sphereGerm_eq_codiscreteWithin h.pair.nonconst_f.1)
    (chartFinite_sphereGerm_eq_codiscreteWithin h.pair.nonconst_g.1)

theorem analyticAt_canonical_of_no_pole {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) {z : ℂ} (hz : mult f ⊤ z = 0) :
    AnalyticAt ℂ (fun w => chartFiniteMap (sphereGermValue f w)) z := by
  apply analyticAt_chartFiniteMap_of_ne_infty
    (sphereHolomorphicOn_sphereGermValue isOpen_univ hf) (mem_univ z)
  intro hval
  have hpos := (mult_top_pos_iff_order_neg f z).mpr
    ((sphereGermValue_eq_infty_iff f z).mp hval)
  rw [hz] at hpos
  exact lt_irrefl (0 : ℕ) hpos

theorem ExponentialPair.sector_canonical_analytic {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
      AnalyticAt ℂ (fun w => chartFiniteMap (sphereGermValue f w)) t ∧
      AnalyticAt ℂ (fun w => chartFiniteMap (sphereGermValue g w)) t := by
  obtain ⟨R, hR, hzero⟩ := h.sector_mult_top_zero hδ
  refine ⟨R, hR, fun t ht hs => ?_⟩
  exact ⟨analyticAt_canonical_of_no_pole h.pair.nonconst_f.1 (hzero t ht hs).1,
    analyticAt_canonical_of_no_pole h.pair.nonconst_g.1 (hzero t ht hs).2⟩

end ThreeIM
