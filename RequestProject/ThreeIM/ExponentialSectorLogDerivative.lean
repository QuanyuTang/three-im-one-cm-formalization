module

public import RequestProject.ThreeIM.LambdaProximity
public import RequestProject.ThreeIM.FiniteExceptions

/-!
# The cubic logarithmic-derivative estimate for the sector argument

Partial fractions give small proximity for f'/P(f). Linear characteristic
growth turns its existing common logarithmic error into O(log(e+r)).
This is the upper estimate in the angular-sector contradiction of Lemma 8.5.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

noncomputable def cubicPartialCoefficient (a : Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  ((a j - a (j + 1)) * (a j - a (j + 2)))⁻¹

theorem cubic_partial_fraction_mul (a : Fin 3 → ℂ) (ha : Function.Injective a)
    (z d : ℂ) (hz : ∀ j, z ≠ a j) :
    d / cubicP a z =
      cubicPartialCoefficient a 0 * (d / (z - a 0)) +
      cubicPartialCoefficient a 1 * (d / (z - a 1)) +
      cubicPartialCoefficient a 2 * (d / (z - a 2)) := by
  have h01 : a 0 - a 1 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have h02 : a 0 - a 2 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have h10 : a 1 - a 0 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have h12 : a 1 - a 2 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have h20 : a 2 - a 0 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have h21 : a 2 - a 1 ≠ 0 := sub_ne_zero.mpr (ha.ne (by decide))
  have hz0 : z - a 0 ≠ 0 := sub_ne_zero.mpr (hz 0)
  have hz1 : z - a 1 ≠ 0 := sub_ne_zero.mpr (hz 1)
  have hz2 : z - a 2 ≠ 0 := sub_ne_zero.mpr (hz 2)
  change d / ((z - a 0) * (z - a 1) * (z - a 2)) =
    ((a 0 - a 1) * (a 0 - a 2))⁻¹ * (d / (z - a 0)) +
    ((a 1 - a 2) * (a 1 - a 0))⁻¹ * (d / (z - a 1)) +
    ((a 2 - a 0) * (a 2 - a 1))⁻¹ * (d / (z - a 2))
  field_simp
  ring

theorem cubic_logDeriv_pairProximityBound {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) :
    PairProximityBound f g (fun z => deriv f z / cubicP a (f z)) := by
  let D (j : Fin 3) : ℂ → ℂ := fun z => deriv f z / (f z - a j)
  have hm (j : Fin 3) : Meromorphic (D j) :=
    meromorphic_logDeriv_sub hp.nonconst_f.meromorphic (a j)
  have hb (j : Fin 3) : PairProximityBound f g (D j) := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a j)
    exact ⟨C, hC.mono fun _ _ h => h.1⟩
  let E (j : Fin 3) : ℂ → ℂ := fun z => cubicPartialCoefficient a j * D j z
  have he (j : Fin 3) : Meromorphic (E j) :=
    fun z => (MeromorphicAt.const _ z).mul (hm j z)
  have hbe (j : Fin 3) : PairProximityBound f g (E j) :=
    (hb j).const_mul (hm j) (cubicPartialCoefficient a j)
  have hsum := ((hbe 0).add (hbe 1) (he 0) (he 1)).add (hbe 2)
    ((he 0).add (he 1)) (he 2)
  apply hsum.congr
  have hn (j : Fin 3) : ∀ᶠ z in codiscrete ℂ, f z - a j ≠ 0 :=
    eventually_ne_zero_of_order_ne_top
      (fun z => (hp.nonconst_f.meromorphic z).sub (MeromorphicAt.const _ z))
      (fun z => hp.nonconst_f.2 z (mem_univ z) (a j))
  filter_upwards [hn 0, hn 1, hn 2] with z h0 h1 h2
  have hz : ∀ j, f z ≠ a j := by
    intro j
    fin_cases j
    · exact sub_ne_zero.mp h0
    · exact sub_ne_zero.mp h1
    · exact sub_ne_zero.mp h2
  exact (cubic_partial_fraction_mul a hp.injective (f z) (deriv f z) hz).symm

theorem pairL_eventually_le_log_of_linear_growth {f g : ℂ → ℂ} {K : ℝ}
    (hK : ∀ᶠ r : ℝ in atTop, charT f r ≤ K * r ∧ charT g r ≤ K * r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in atTop,
      pairL f g r ≤ B * log (exp 1 + r) := by
  let A : ℝ := |K| + 1
  let D : ℝ := exp 1 + A
  have hA : 0 < A := by dsimp [A]; positivity
  have he : 1 ≤ exp (1 : ℝ) := by linarith [Real.add_one_le_exp 1]
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨log D + 2, by linarith [log_nonneg hD], ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with r hrK hr
  have hr0 : 0 ≤ r := by linarith
  have hT0 : 0 ≤ pairT f g r :=
    (charT_nonneg (h := f) hr).trans (le_max_left _ _)
  have hTK : pairT f g r ≤ K * r := max_le hrK.1 hrK.2
  have hTA : pairT f g r ≤ A * r := hTK.trans
    (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [le_abs_self K]) hr0)
  have hbase : 1 ≤ exp (1 : ℝ) + r := by linarith
  have hsq : 1 ≤ (exp (1 : ℝ) + r) ^ 2 := by nlinarith
  have hrsq : r ^ 2 ≤ (exp (1 : ℝ) + r) ^ 2 := by nlinarith [exp_pos (1 : ℝ)]
  have hupper : exp 1 + r * pairT f g r ≤ D * (exp 1 + r) ^ 2 := by
    calc
      exp 1 + r * pairT f g r ≤ exp 1 + A * r ^ 2 := by nlinarith
      _ ≤ exp 1 * (exp 1 + r) ^ 2 + A * (exp 1 + r) ^ 2 :=
        add_le_add (le_mul_of_one_le_right (exp_pos _).le hsq)
          (mul_le_mul_of_nonneg_left hrsq hA.le)
      _ = D * (exp 1 + r) ^ 2 := by dsimp [D]; ring
  have hlog := log_le_log (by positivity : 0 < exp 1 + r * pairT f g r) hupper
  rw [log_mul (by linarith : D ≠ 0) (by positivity), log_pow] at hlog
  norm_num at hlog
  have hl1 : 1 ≤ log (exp (1 : ℝ) + r) := by
    calc
      1 = log (exp (1 : ℝ)) := (log_exp 1).symm
      _ ≤ log (exp (1 : ℝ) + r) := log_le_log (exp_pos _) (by linarith)
  have hscale := mul_le_mul_of_nonneg_left hl1 (log_nonneg hD)
  dsimp only [pairL]
  nlinarith

theorem cubic_logDeriv_proximity_le_log_of_linear_growth
    {f g : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a) {K : ℝ}
    (hK : ∀ᶠ r : ℝ in atTop, charT f r ≤ K * r ∧ charT g r ≤ K * r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => deriv f z / cubicP a (f z)) ⊤ r ≤ C * log (exp 1 + r) := by
  obtain ⟨C, hC⟩ := cubic_logDeriv_pairProximityBound hp
  obtain ⟨B, hB, hbound⟩ := pairL_eventually_le_log_of_linear_growth hK
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound
  refine ⟨|C| * B, (hC.conj (OutsideFiniteMeasure.eventually_ge R)).mono ?_⟩
  intro r hr h
  have hL : 0 ≤ pairL f g r := (show 0 ≤ (1 : ℝ) by norm_num).trans (one_le_pairL hr)
  calc
    _ ≤ C * pairL f g r := h.1
    _ ≤ |C| * pairL f g r := mul_le_mul_of_nonneg_right (le_abs_self C) hL
    _ ≤ |C| * (B * log (exp 1 + r)) := mul_le_mul_of_nonneg_left (hR r h.2) (abs_nonneg C)
    _ = _ := by ring

end ThreeIM
