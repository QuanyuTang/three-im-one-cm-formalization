module

public import RequestProject.ThreeIM.TwoCMMixedWeighted

/-!
# The common-zero branch of the two mixed auxiliary functions
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

private theorem mixed_cubicP_eq_three {a : Fin 3 → ℂ} (j i k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k) (w : ℂ) :
    cubicP a w = (w - a j) * (w - a i) * (w - a k) := by
  fin_cases j <;> fin_cases i <;> fin_cases k
  all_goals first
  | exact (hij rfl).elim
  | exact (hkj rfl).elim
  | exact (hik rfl).elim
  | (simp only [cubicP, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring)

theorem twoCM_weightedDerivative_eq_of_aux_ratio_eq {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hratio : (fun z => auxU a f g z * (f z - a i) / (g z - a i)) =ᶠ[codiscrete ℂ]
      (fun z => auxV a f g z * (g z - a i) / (f z - a i))) :
    twoCMWeightedDerivative (a j) (a i) (a k) f =ᶠ[codiscrete ℂ]
      twoCMWeightedDerivative (a j) (a i) (a k) g := by
  filter_upwards [hratio, hp.eventually_ne,
    hp.nonconst_f.eventually_ne (a j), hp.nonconst_f.eventually_ne (a i), hp.nonconst_f.eventually_ne (a k),
    hp.nonconst_g.eventually_ne (a j), hp.nonconst_g.eventually_ne (a i), hp.nonconst_g.eventually_ne (a k)]
    with z hz hfg hfj hfi hfk hgj hgi hgk
  have hfactor : (f z - g z) *
      (twoCMWeightedDerivative (a j) (a i) (a k) f z - twoCMWeightedDerivative (a j) (a i) (a k) g z) =
      ((f z - a i) * (g z - a i)) *
        (auxU a f g z * (f z - a i) / (g z - a i) - auxV a f g z * (g z - a i) / (f z - a i)) := by
    simp only [twoCMWeightedDerivative, auxU, auxV]
    rw [mixed_cubicP_eq_three j i k hij hkj hik (f z), mixed_cubicP_eq_three j i k hij hkj hik (g z)]
    field_simp [sub_ne_zero.2 hfj, sub_ne_zero.2 hfi, sub_ne_zero.2 hfk,
      sub_ne_zero.2 hgj, sub_ne_zero.2 hgi, sub_ne_zero.2 hgk]
  rw [hz, sub_self, mul_zero] at hfactor
  exact sub_eq_zero.1 ((mul_eq_zero.1 hfactor).resolve_left (sub_ne_zero.2 hfg))

theorem twoCM_false_of_aux_ratio_eq {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hratio : (fun z => auxU a f g z * (f z - a i) / (g z - a i)) =ᶠ[codiscrete ℂ]
      (fun z => auxV a f g z * (g z - a i) / (f z - a i))) : False := by
  exact twoCM_false_of_weightedDerivative_eq hp j i k hij hkj hik hcm hdefect
    (twoCM_weightedDerivative_eq_of_aux_ratio_eq hp j i k hij hkj hik hratio)

theorem twoCM_false_of_scaled_aux_zeros {f g χ : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    {S : ℂ} (hS : S ≠ 0)
    (hη : (fun z => χ z + S * auxU a f g z * (f z - a i) / (g z - a i)) =ᶠ[codiscrete ℂ] (fun _ => 0))
    (hθ : (fun z => χ z + S * auxV a f g z * (g z - a i) / (f z - a i)) =ᶠ[codiscrete ℂ] (fun _ => 0)) : False := by
  apply twoCM_false_of_aux_ratio_eq hp j i k hij hkj hik hcm hdefect
  filter_upwards [hη, hθ] with z hη hθ
  have hprod : S * (auxU a f g z * (f z - a i) / (g z - a i) -
      auxV a f g z * (g z - a i) / (f z - a i)) = 0 := by
    linear_combination hη - hθ
  exact sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_left hS)

end ThreeIM
