module

public import RequestProject.ThreeIM.TwoCMOppositeExclusion

/-!
# Swapping the two CM target values

The target coordinate w ↦ 1/(w-a) exchanges the finite CM target with
infinity. All sharing assertions, counting functions and growth estimates
are transported explicitly. This reduces the two mixed cases to one.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

noncomputable def twoCMSwapTargets (a : Fin 3 → ℂ) (j i : Fin 3) : ℂ :=
  if i = j then 0 else (a i - a j)⁻¹

theorem twoCM_nonconst_targetSwap {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (c : ℂ) :
    IsNonconstMeroOn (fun w => (f w - c)⁻¹) univ := by
  refine ⟨fun z _ => meromorphicAt_mobius_comp (hf.meromorphic z) c, fun z _ d hd => ?_⟩
  apply hf.2 z (mem_univ z) (c + d⁻¹)
  apply meromorphicOrderAt_eq_top_iff.2
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hd] with w hw
  have h1 : (f w - c)⁻¹ = d := sub_eq_zero.1 hw
  have h2 : f w - c = d⁻¹ := by rw [← h1, inv_inv]
  linear_combination h2

theorem twoCM_swapTargets_injective {a : Fin 3 → ℂ}
    (ha : Function.Injective a) (j : Fin 3) : Function.Injective (twoCMSwapTargets a j) := by
  intro i k h
  by_cases hi : i = j <;> by_cases hk : k = j
  · exact hi.trans hk.symm
  · subst i
    have he : (a k - a j)⁻¹ = 0 := by simpa [twoCMSwapTargets, hk] using h.symm
    exact (hk (ha (sub_eq_zero.1 (inv_eq_zero.1 he)))).elim
  · subst k
    have he : (a i - a j)⁻¹ = 0 := by simpa [twoCMSwapTargets, hi] using h
    exact (hi (ha (sub_eq_zero.1 (inv_eq_zero.1 he)))).elim
  · have he : (a i - a j)⁻¹ = (a k - a j)⁻¹ := by
      simpa [twoCMSwapTargets, hi, hk] using h
    exact ha (sub_left_inj.1 (inv_inj.1 he))

theorem twoCM_swapTargets_coe {a : Fin 3 → ℂ}
    (ha : Function.Injective a) (j i : Fin 3) (hi : i ≠ j) :
    (twoCMSwapTargets a j i : Sphere) = mobius (a j) (a i : Sphere) := by
  rw [mobius_coe_of_ne (ha.ne hi)]
  simp [twoCMSwapTargets, hi]

theorem twoCM_sharesCM_targetSwap {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) {b : Sphere}
    (h : SharesCMOn univ f g b) (c : ℂ) :
    SharesCMOn univ (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) (mobius c b) := by
  intro z hz
  rw [mult_mobius (hf z), mult_mobius (hg z)]
  exact h z hz

theorem twoCM_normalized_targetSwap {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    NormalizedPair univ (fun w => (f w - a j)⁻¹) (fun w => (g w - a j)⁻¹)
      (twoCMSwapTargets a j) := by
  refine ⟨twoCM_nonconst_targetSwap hp.nonconst_f _,
    twoCM_nonconst_targetSwap hp.nonconst_g _, ?_, twoCM_swapTargets_injective hp.injective j,
    ?_, ?_⟩
  · intro z hz ht
    apply hp.distinct z hz
    apply meromorphicOrderAt_eq_top_iff.2
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ht] with w hw
    have he : (f w - a j)⁻¹ = (g w - a j)⁻¹ := sub_eq_zero.1 hw
    exact sub_eq_zero.2 (sub_left_inj.1 (inv_inj.1 he))
  · intro i z hz
    by_cases hi : i = j
    · subst i
      have he := twoCM_sharesCM_targetSwap hp.nonconst_f.meromorphic hp.nonconst_g.meromorphic
        hp.cm_top (a j) z hz
      simpa [twoCMSwapTargets] using (Iff.of_eq (congrArg (fun n : ℕ => 0 < n) he))
    · rw [twoCM_swapTargets_coe hp.injective j i hi,
        mult_mobius (hp.nonconst_f.meromorphic z), mult_mobius (hp.nonconst_g.meromorphic z)]
      exact hp.im i z hz
  · have he := twoCM_sharesCM_targetSwap hp.nonconst_f.meromorphic hp.nonconst_g.meromorphic hcm (a j)
    simpa using he

theorem twoCM_logCounting_targetSwap {f : ℂ → ℂ} (hf : Meromorphic f)
    (c : ℂ) (b : Sphere) :
    logCounting (fun w => (f w - c)⁻¹) (mobius c b) = logCounting f b := by
  have hnew : MeromorphicOn (fun w => (f w - c)⁻¹) univ :=
    fun z _ => meromorphicAt_mobius_comp (hf z) c
  have heq : fiberDivisor (fun w => (f w - c)⁻¹) (mobius c b) = fiberDivisor f b := by
    ext z
    rw [fiberDivisor_apply hnew, fiberDivisor_apply (fun z _ => hf z), mult_mobius (hf z)]
  rw [← fiberDivisor_logCounting, ← fiberDivisor_logCounting, heq]

theorem twoCM_charT_targetSwap_abs_le {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (c : ℂ) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      |charT (fun w => (f w - c)⁻¹) r - charT f r| ≤ K := by
  let D : ℂ → ℂ := fun w => f w - c
  have hD : Meromorphic D := fun z => (hf.meromorphic z).sub (MeromorphicAt.const c z)
  let K := max |log ‖D 0‖| |log ‖meromorphicTrailingCoeffAt D 0‖|
  refine ⟨K + (log⁺ ‖c‖ + log 2), fun r hr => ?_⟩
  have hi := characteristic_sub_characteristic_inv_le (R := r) hD
  have hs := abs_characteristic_sub_characteristic_shift_le (a₀ := c) (r := r) hf.meromorphic
  change |charT D r - charT (fun w => (f w - c)⁻¹) r| ≤ K at hi
  change |charT f r - charT D r| ≤ log⁺ ‖c‖ + log 2 at hs
  rw [abs_sub_comm] at hi hs
  linarith [abs_sub_le (charT (fun w => (f w - c)⁻¹) r) (charT D r) (charT f r)]

theorem twoCM_pairT_targetSwap_abs_le {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ) (c : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r →
      |pairT (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) r - pairT f g r| ≤ K := by
  obtain ⟨Kf, hKf⟩ := twoCM_charT_targetSwap_abs_le hf c
  obtain ⟨Kg, hKg⟩ := twoCM_charT_targetSwap_abs_le hg c
  refine ⟨|Kf| + |Kg|, by positivity, fun r hr => ?_⟩
  have hfb := abs_le.1 (hKf r hr)
  have hgb := abs_le.1 (hKg r hr)
  rw [abs_le, sub_le_iff_le_add, neg_le_sub_iff_le_add]
  constructor
  · change max _ _ ≤ max _ _ + _
    apply max_le
    · linarith [hfb.1, le_max_left (charT (fun w => (f w - c)⁻¹) r)
        (charT (fun w => (g w - c)⁻¹) r), le_abs_self Kf, abs_nonneg Kg]
    · linarith [hgb.1, le_max_right (charT (fun w => (f w - c)⁻¹) r)
        (charT (fun w => (g w - c)⁻¹) r), le_abs_self Kg, abs_nonneg Kf]
  · change max _ _ ≤ _ + max _ _
    apply max_le
    · linarith [hfb.2, le_max_left (charT f r) (charT g r), le_abs_self Kf, abs_nonneg Kg]
    · linarith [hgb.2, le_max_right (charT f r) (charT g r), le_abs_self Kg, abs_nonneg Kf]

theorem twoCM_growth_targetSwap {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ) (b : ℂ)
    (hG : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r) :
    ∃ c > 0, ∀ᶠ r in atTop,
      c * r ≤ pairT (fun w => (f w - b)⁻¹) (fun w => (g w - b)⁻¹) r := by
  obtain ⟨c, hc, hG⟩ := hG
  obtain ⟨K, hK0, hK⟩ := twoCM_pairT_targetSwap_abs_le hf hg b
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hG, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * K / c)] with r hg hr hR
  have hb := (abs_le.1 (hK r hr)).1
  have hKle : 2 * K ≤ r * c := (div_le_iff₀ hc).1 hR
  nlinarith

theorem TwoCMPeriodicCounterexample.targetSwap {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (hP : TwoCMPeriodicCounterexample a j f g) :
    TwoCMPeriodicCounterexample (twoCMSwapTargets a j) j
      (fun w => (f w - a j)⁻¹) (fun w => (g w - a j)⁻¹) := by
  refine ⟨twoCM_normalized_targetSwap hP.pair j hP.cm_finite, ?_, ?_, ?_, ?_,
    twoCM_growth_targetSwap hP.pair.nonconst_f hP.pair.nonconst_g _ hP.linear_growth⟩
  · have h := twoCM_sharesCM_targetSwap hP.pair.nonconst_f.meromorphic hP.pair.nonconst_g.meromorphic
      hP.pair.cm_top (a j)
    simpa [twoCMSwapTargets] using h
  · obtain ⟨d, z, hd⟩ := hP.defect
    have hdj : d ≠ j := by
      intro he
      subst d
      exact hd.2.2 (hP.cm_finite z (mem_univ z))
    refine ⟨d, z, ?_⟩
    unfold IsDefect
    rw [twoCM_swapTargets_coe hP.pair.injective j d hdj,
      mult_mobius (hP.pair.nonconst_f.meromorphic z),
      mult_mobius (hP.pair.nonconst_g.meromorphic z)]
    exact hd
  · intro t
    rw [hP.periodic_f]
  · intro t
    rw [hP.periodic_g]

end ThreeIM
