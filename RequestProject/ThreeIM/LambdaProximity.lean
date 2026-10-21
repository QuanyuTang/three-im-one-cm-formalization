module

public import RequestProject.ThreeIM.DefectCounting
public import RequestProject.ThreeIM.ThetaProximity

/-!
# Small proximity of the Lambda differences

The difference `Λ_a - Θ_a` is a linear combination of three logarithmic
derivatives. Consequently the established estimates for `θ_a` and those
logarithmic derivatives give the proximity bound for `E_a`.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

/-- A proximity estimate with the common error term of the normalized pair. -/
def PairProximityBound (f g F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, OutsideFiniteMeasure fun r => proximity F ⊤ r ≤ C * pairL f g r

theorem PairProximityBound.add {f g F G : ℂ → ℂ}
    (hF : PairProximityBound f g F) (hG : PairProximityBound f g G)
    (hFm : Meromorphic F) (hGm : Meromorphic G) :
    PairProximityBound f g (fun z => F z + G z) := by
  obtain ⟨CF, hCF⟩ := hF
  obtain ⟨CG, hCG⟩ := hG
  refine ⟨|CF| + |CG| + log 2, (hCF.and hCG).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have e := proximity_add_top_le hFm hGm r
  simp only [Pi.add_apply] at e
  have eF := mul_le_mul_of_nonneg_right (le_abs_self CF) (by linarith : 0 ≤ pairL f g r)
  have eG := mul_le_mul_of_nonneg_right (le_abs_self CG) (by linarith : 0 ≤ pairL f g r)
  have e2 := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hL
  change proximity (F + G) ⊤ r ≤ (|CF| + |CG| + log 2) * pairL f g r
  rw [add_mul, add_mul]
  linarith

theorem PairProximityBound.const_mul {f g F : ℂ → ℂ}
    (hF : PairProximityBound f g F) (hFm : Meromorphic F) (c : ℂ) :
    PairProximityBound f g (fun z => c * F z) := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨|C| + log⁺ ‖c‖, hC.mono fun r hr h => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have e := proximity_const_mul_le c hFm r
  have eC := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith : 0 ≤ pairL f g r)
  have ec := le_mul_of_one_le_right (Real.posLog_nonneg (x := ‖c‖)) hL
  rw [add_mul]
  linarith

theorem PairProximityBound.sub {f g F G : ℂ → ℂ}
    (hF : PairProximityBound f g F) (hG : PairProximityBound f g G)
    (hFm : Meromorphic F) (hGm : Meromorphic G) :
    PairProximityBound f g (fun z => F z - G z) := by
  have heq : (fun z => F z - G z) = fun z => F z + (-1 : ℂ) * G z := by
    ext z
    ring
  rw [heq]
  exact hF.add (hG.const_mul hGm (-1)) hFm
    (fun z => (MeromorphicAt.const (-1) z).mul (hGm z))

theorem PairProximityBound.congr {f g F G : ℂ → ℂ}
    (hF : PairProximityBound f g F) (heq : F =ᶠ[codiscrete ℂ] G) :
    PairProximityBound f g G := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨C, hC.mono fun r hr h => ?_⟩
  rw [← proximity_congr_codiscrete heq (by linarith)]
  exact h

/-- The Lambda difference is the Theta difference plus logarithmic derivatives.
The identity is asserted off the discrete denominator fibers. -/
theorem EAux_eq_thetaAux_add_logDerivs (hp : NormalizedPair univ f g a) (j : Fin 3) :
    EAux a j f g =ᶠ[codiscrete ℂ] fun z => thetaAux a j f g z +
      (-4 : ℂ) * (deriv f z / (f z - a j) - deriv g z / (g z - a j)) +
      ((a (j + 1) - a j) / (a (j + 1) - a (j + 2)) + 1) *
        (deriv f z / (f z - a (j + 1)) - deriv g z / (g z - a (j + 1))) +
      ((a j - a (j + 2)) / (a (j + 1) - a (j + 2)) + 1) *
        (deriv f z / (f z - a (j + 2)) - deriv g z / (g z - a (j + 2))) := by
  have hbc : a (j + 1) ≠ a (j + 2) := fun he => by
    have hj := hp.injective he
    fin_cases j <;> simp at hj
  filter_upwards [hp.nonconst_f.eventually_ne (a (j + 1)),
    hp.nonconst_f.eventually_ne (a (j + 2)),
    hp.nonconst_g.eventually_ne (a (j + 1)),
    hp.nonconst_g.eventually_ne (a (j + 2))] with z hfb hfc hgb hgc
  simp only [EAux, LambdaFun, LambdaCore, thetaAux, ThetaFun]
  rw [LambdaCore_partial_fractions hbc (sub_ne_zero.2 hfb) (sub_ne_zero.2 hfc),
    LambdaCore_partial_fractions hbc (sub_ne_zero.2 hgb) (sub_ne_zero.2 hgc)]
  ring

/-- The proximity estimate for one Lambda difference. -/
theorem proximity_EAux_single_le (hp : NormalizedPair univ f g a) (j : Fin 3) :
    PairProximityBound f g (EAux a j f g) := by
  set D : Fin 3 → ℂ → ℂ := fun i z => deriv f z / (f z - a i) - deriv g z / (g z - a i)
  have hmF := hp.nonconst_f.meromorphic
  have hmG := hp.nonconst_g.meromorphic
  have hDm (i : Fin 3) : Meromorphic (D i) :=
    (meromorphic_logDeriv_sub hmF (a i)).sub (meromorphic_logDeriv_sub hmG (a i))
  have hDb (i : Fin 3) : PairProximityBound f g (D i) := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a i)
    have hF : PairProximityBound f g (fun z => deriv f z / (f z - a i)) :=
      ⟨C, hC.mono fun r _ h => h.1⟩
    have hG : PairProximityBound f g (fun z => deriv g z / (g z - a i)) :=
      ⟨C, hC.mono fun r _ h => h.2⟩
    exact hF.sub hG (meromorphic_logDeriv_sub hmF (a i)) (meromorphic_logDeriv_sub hmG (a i))
  have hθm : Meromorphic (thetaAux a j f g) := fun z => by
    have hf := hmF z
    have hg := hmG z
    unfold thetaAux ThetaFun
    fun_prop
  have hθb : PairProximityBound f g (thetaAux a j f g) := by
    obtain ⟨C, hC⟩ := proximity_thetaAux_le hp
    exact ⟨C, hC.mono fun r _ h => h j⟩
  set B : ℂ := (a (j + 1) - a j) / (a (j + 1) - a (j + 2)) + 1
  set C : ℂ := (a j - a (j + 2)) / (a (j + 1) - a (j + 2)) + 1
  have h0m : Meromorphic (fun z => (-4 : ℂ) * D j z) :=
    fun z => (MeromorphicAt.const (-4) z).mul (hDm j z)
  have h1m : Meromorphic (fun z => B * D (j + 1) z) :=
    fun z => (MeromorphicAt.const B z).mul (hDm (j + 1) z)
  have h2m : Meromorphic (fun z => C * D (j + 2) z) :=
    fun z => (MeromorphicAt.const C z).mul (hDm (j + 2) z)
  have h0 := hθb.add ((hDb j).const_mul (hDm j) (-4)) hθm h0m
  have h1 := h0.add ((hDb (j + 1)).const_mul (hDm (j + 1)) B) (hθm.add h0m) h1m
  have h2 := h1.add ((hDb (j + 2)).const_mul (hDm (j + 2)) C)
    ((hθm.add h0m).add h1m) h2m
  exact h2.congr (EAux_eq_thetaAux_add_logDerivs hp j).symm

end ThreeIM
