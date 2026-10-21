module

public import RequestProject.ThreeIM.Cartan

/-! # Polynomially large radii outside a set of finite linear measure -/

@[expose] public section

open Filter Set MeasureTheory Topology

namespace ThreeIM

set_option autoImplicit false

theorem exists_outside_finite_volume_interval {E : Set ℝ} (hE : volume E < ⊤)
    (x : ℝ) {l : ℝ} (hl : (volume E).toReal < l) :
    ∃ y ∈ Icc x (x + l), y ∉ E := by
  classical
  by_contra hno
  have hsub : Icc x (x + l) ⊆ E := by
    intro y hy
    by_contra hyE
    exact hno ⟨y, hy, hyE⟩
  have hl0 : 0 ≤ l := (ENNReal.toReal_nonneg).trans hl.le
  have hbound := ENNReal.toReal_mono hE.ne (measure_mono hsub)
  rw [Real.volume_Icc, add_sub_cancel_left, ENNReal.toReal_ofReal hl0] at hbound
  linarith

theorem exists_large_power_outside_finite_volume {T : ℝ → ℝ}
    (hmono : MonotoneOn T (Ici 1))
    (hInf : ∀ k : ℕ, ∃ᶠ r in atTop, r ^ k ≤ T r)
    {E : Set ℝ} (hE : volume E < ⊤) (k : ℕ) (R : ℝ) :
    ∃ r ≥ R, r ∉ E ∧ r ^ k ≤ T r := by
  obtain ⟨x, hx, hTx⟩ := (frequently_atTop.1 (hInf (k + 1)))
    (max R (max 1 (max ((volume E).toReal + 1) ((2 : ℝ) ^ k))))
  have hxR : R ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxM : (volume E).toReal + 1 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxpow : (2 : ℝ) ^ k ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  obtain ⟨r, hxr, hrE⟩ := exists_outside_finite_volume_interval hE x
    (by linarith : (volume E).toReal < x)
  refine ⟨r, hxR.trans hxr.1, hrE, ?_⟩
  calc
    r ^ k ≤ (2 * x) ^ k := by gcongr <;> linarith [hxr.1, hxr.2]
    _ = (2 : ℝ) ^ k * x ^ k := mul_pow _ _ _
    _ ≤ x * x ^ k := mul_le_mul_of_nonneg_right hxpow (by positivity)
    _ = x ^ (k + 1) := by ring
    _ ≤ T x := hTx
    _ ≤ T r := hmono hx1 (hx1.trans hxr.1) hxr.1

theorem power_radii_outside_finite_volume {T : ℝ → ℝ}
    (hmono : MonotoneOn T (Ici 1))
    (hInf : ∀ k : ℕ, ∃ᶠ r in atTop, r ^ k ≤ T r)
    {E : Set ℝ} (hE : volume E < ⊤) (k : ℕ) :
    ∃ r : ℕ → ℝ, (∀ n, 2 ≤ r n) ∧ Tendsto r atTop atTop ∧
      (∀ n, r n ∉ E) ∧ (∀ n, r n ^ k ≤ T (r n)) := by
  classical
  have hex (n : ℕ) := exists_large_power_outside_finite_volume hmono hInf hE k (max 2 (n : ℝ))
  choose r hr hE hp using hex
  refine ⟨r, fun n => (le_max_left _ _).trans (hr n), ?_, hE, hp⟩
  exact tendsto_atTop_mono (fun n => (le_max_right _ _).trans (hr n))
    tendsto_natCast_atTop_atTop

theorem pairT_monotoneOn_Ici_one {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) :
    MonotoneOn (pairT f g) (Ici 1) := by
  intro r hr R _ hrR
  have hr1 : 1 ≤ r := hr
  exact max_le_max (charT_mono hf (by linarith) hrR)
    (charT_mono hg (by linarith) hrR)

theorem pairT_frequently_ge_nat_power {f g : ℂ → ℂ}
    (hInf : InfiniteOrder f ∨ InfiniteOrder g) (k : ℕ) :
    ∃ᶠ r in atTop, r ^ k ≤ pairT f g r := by
  rcases hInf with hf | hg
  · exact (hf (k : ℝ)).mono fun r hr =>
      (by simpa only [Real.rpow_natCast] using hr : r ^ k ≤ charT f r).trans
        (le_max_left _ _)
  · exact (hg (k : ℝ)).mono fun r hr =>
      (by simpa only [Real.rpow_natCast] using hr : r ^ k ≤ charT g r).trans
        (le_max_right _ _)

end ThreeIM
