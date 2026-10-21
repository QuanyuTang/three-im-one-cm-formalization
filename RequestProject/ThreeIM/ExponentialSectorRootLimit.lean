module

public import RequestProject.ThreeIM.ExponentialSectorBoundedF
public import RequestProject.ThreeIM.ExponentialSectorRootGeometry

/-!
# One marked limit throughout the proper right sectors

The root label is fixed by connectedness of truncated convex sectors.
Every such sector contains a tail of the positive real axis, so the label
is independent of its aperture and of the requested approximation.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem exists_root_near_of_cubic_norm_lt {a : Fin 3 → ℂ} {z : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hp : ‖cubicP a z‖ < ε ^ 3) :
    ∃ j : Fin 3, ‖z - a j‖ < ε := by
  by_contra hbad
  push_neg at hbad
  have h01 : ε * ε ≤ ‖z - a 0‖ * ‖z - a 1‖ :=
    mul_le_mul (hbad 0) (hbad 1) hε.le (norm_nonneg _)
  have h012 : ε * ε * ε ≤ ‖z - a 0‖ * ‖z - a 1‖ * ‖z - a 2‖ :=
    mul_le_mul h01 (hbad 2) hε.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have heq : ‖cubicP a z‖ = ‖z - a 0‖ * ‖z - a 1‖ * ‖z - a 2‖ := by
    simp only [cubicP, norm_mul]
  rw [heq] at hp
  nlinarith

private theorem exists_separated_marked_radius {a : Fin 3 → ℂ}
    (ha : Function.Injective a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → 4 * ε ≤ dist (a i) (a j) := by
  have h01 : 0 < dist (a 0) (a 1) := dist_pos.mpr (ha.ne (by decide))
  have h02 : 0 < dist (a 0) (a 2) := dist_pos.mpr (ha.ne (by decide))
  have h12 : 0 < dist (a 1) (a 2) := dist_pos.mpr (ha.ne (by decide))
  let ε : ℝ := min (dist (a 0) (a 1)) (min (dist (a 0) (a 2)) (dist (a 1) (a 2))) / 8
  have hε : 0 < ε := by dsimp [ε]; exact div_pos (lt_min h01 (lt_min h02 h12)) (by norm_num)
  have hε01 : 8 * ε ≤ dist (a 0) (a 1) := by
    dsimp [ε]
    linarith [min_le_left (dist (a 0) (a 1)) (min (dist (a 0) (a 2)) (dist (a 1) (a 2)))]
  have hε02 : 8 * ε ≤ dist (a 0) (a 2) := by
    dsimp [ε]
    linarith [(min_le_right (dist (a 0) (a 1))
      (min (dist (a 0) (a 2)) (dist (a 1) (a 2)))).trans (min_le_left _ _)]
  have hε12 : 8 * ε ≤ dist (a 1) (a 2) := by
    dsimp [ε]
    linarith [(min_le_right (dist (a 0) (a 1))
      (min (dist (a 0) (a 2)) (dist (a 1) (a 2)))).trans (min_le_right _ _)]
  have hε10 : 8 * ε ≤ dist (a 1) (a 0) := by rw [dist_comm]; exact hε01
  have hε20 : 8 * ε ≤ dist (a 2) (a 0) := by rw [dist_comm]; exact hε02
  have hε21 : 8 * ε ≤ dist (a 2) (a 1) := by rw [dist_comm]; exact hε12
  refine ⟨ε, hε, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim |
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at *; linarith)

private theorem ExponentialPair.eventually_near_one_marked_value
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε)
    (hsep : ∀ i j, i ≠ j → 2 * ε ≤ dist (a i) (a j)) :
    ∃ j : Fin 3, ∀ᶠ t in rightSectorAtTop δ,
      ‖chartFiniteMap (sphereGermValue f t) - a j‖ < ε := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  have hlim : Tendsto (fun t => ‖cubicP a (F t)‖) (rightSectorAtTop δ) (𝓝 0) := by
    simpa only [norm_zero] using (h.canonical_cubic_tendsto_zero_rightSector hδ).norm
  have hsmall : ∀ᶠ t in rightSectorAtTop δ, ‖cubicP a (F t)‖ < ε ^ 3 :=
    hlim.eventually (eventually_lt_nhds (pow_pos hε 3))
  obtain ⟨R₀, hR₀⟩ := eventually_rightSectorAtTop_iff.mp
    ((h.canonical_analytic_eventually_rightSector hδ).and hsmall)
  let R : ℝ := max 1 R₀
  let S : Set ℂ := {t | R ≤ t.re ∧ δ * ‖t‖ ≤ t.re}
  have hR : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  have hSn : S.Nonempty := by
    refine ⟨(R : ℂ), ?_⟩
    change R ≤ (R : ℂ).re ∧ δ * ‖(R : ℂ)‖ ≤ (R : ℂ).re
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hR]
    exact ⟨le_rfl, mul_le_of_le_one_left hR hδone⟩
  have hdata (t : ℂ) (ht : t ∈ S) : AnalyticAt ℂ F t ∧ ‖cubicP a (F t)‖ < ε ^ 3 := by
    have hn : R₀ ≤ ‖t‖ := (le_max_right 1 R₀).trans (ht.1.trans (Complex.re_le_norm t))
    exact ⟨(hR₀ t hn ht.2).1.1, (hR₀ t hn ht.2).2⟩
  have hF : ContinuousOn F S := fun t ht => (hdata t ht).1.continuousAt.continuousWithinAt
  obtain ⟨j, hj⟩ := IsPreconnected.image_in_one_separated_ball
    (truncated_right_sector_convex R hδ.le).isPreconnected hSn hF
    (fun t ht => exists_root_near_of_cubic_norm_lt hε (hdata t ht).2) hsep
  refine ⟨j, eventually_rightSectorAtTop_iff.mpr ⟨R / δ, ?_⟩⟩
  intro t ht hs
  apply hj t
  refine ⟨?_, hs⟩
  have hh : R ≤ δ * ‖t‖ := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp ht
  exact hh.trans hs

theorem ExponentialPair.canonical_f_tendsto_marked_rightSectors
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ) :
    ∃ j : Fin 3, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun t => chartFiniteMap (sphereGermValue f t))
        (rightSectorAtTop δ) (𝓝 (a j)) := by
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_separated_marked_radius h.pair.injective
  have hsep₀ (i j : Fin 3) (hij : i ≠ j) : 2 * ε₀ ≤ dist (a i) (a j) := by
    linarith [hsep i j hij]
  obtain ⟨j, hj⟩ := h.eventually_near_one_marked_value zero_lt_one le_rfl hε₀ hsep₀
  obtain ⟨Rj, hRj⟩ := eventually_rightSectorAtTop_iff.mp hj
  refine ⟨j, ?_⟩
  intro δ hδ
  let δ₁ : ℝ := min δ 1
  have hδ₁ : 0 < δ₁ := lt_min hδ zero_lt_one
  have hmono : rightSectorAtTop δ ≤ rightSectorAtTop δ₁ := by
    dsimp only [rightSectorAtTop]
    apply inf_le_inf_left
    exact principal_mono.mpr fun t ht =>
      (mul_le_mul_of_nonneg_right (min_le_left δ 1) (norm_nonneg t)).trans ht
  refine Tendsto.mono_left (x := rightSectorAtTop δ₁) ?_ hmono
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε₁ : ℝ := min ε ε₀
  have hε₁ : 0 < ε₁ := lt_min hε hε₀
  have hsep₁ (i k : Fin 3) (hik : i ≠ k) : 2 * ε₁ ≤ dist (a i) (a k) := by
    have hh : ε₁ ≤ ε₀ := min_le_right _ _
    linarith [hsep i k hik]
  obtain ⟨i, hi⟩ := h.eventually_near_one_marked_value hδ₁ (min_le_right _ _) hε₁ hsep₁
  obtain ⟨Ri, hRi⟩ := eventually_rightSectorAtTop_iff.mp hi
  let T : ℝ := max 1 (max Rj Ri)
  have hT : 0 ≤ T := zero_le_one.trans (le_max_left _ _)
  have hTj : Rj ≤ T := (le_max_left Rj Ri).trans (le_max_right _ _)
  have hTi : Ri ≤ T := (le_max_right Rj Ri).trans (le_max_right _ _)
  have hTnorm : ‖(T : ℂ)‖ = T := by simp only [Complex.norm_real, Real.norm_of_nonneg hT]
  have hjT := hRj (T : ℂ) (by simpa only [hTnorm] using hTj)
    (by simp only [hTnorm, Complex.ofReal_re, one_mul]; exact le_rfl)
  have hiT := hRi (T : ℂ) (by simpa only [hTnorm] using hTi)
    (by
      simp only [hTnorm, Complex.ofReal_re]
      exact mul_le_of_le_one_left hT (min_le_right _ _))
  have hij : i = j := by
    by_contra hne
    have htri := dist_triangle (a i) (chartFiniteMap (sphereGermValue f (T : ℂ))) (a j)
    have hi' : dist (a i) (chartFiniteMap (sphereGermValue f (T : ℂ))) < ε₁ := by
      rw [dist_comm, dist_eq_norm]
      exact hiT
    have hj' : dist (chartFiniteMap (sphereGermValue f (T : ℂ))) (a j) < ε₀ := by
      simpa only [dist_eq_norm] using hjT
    have hh : ε₁ ≤ ε₀ := min_le_right _ _
    linarith [hsep i j hne]
  subst i
  filter_upwards [hi] with t ht
  have hh : ε₁ ≤ ε := min_le_left _ _
  simpa only [dist_eq_norm] using ht.trans_le hh

end ThreeIM
