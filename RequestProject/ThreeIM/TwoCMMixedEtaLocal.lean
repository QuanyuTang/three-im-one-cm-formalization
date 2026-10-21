module

public import RequestProject.ThreeIM.TwoCMChi

/-!
# The two mixed auxiliary functions

The extra target is a complex parameter, so the same definitions cover both
finite IM targets. The partial fraction below retains exactly one reciprocal
target factor in the proximity estimate.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

noncomputable def twoCMMixedEta (a : Fin 3 → ℂ) (j : Fin 3) (b : ℂ)
    (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => twoCMChi a j f g z + cAux a j * auxU a f g z * (f z - b) / (g z - b)

noncomputable def twoCMMixedTheta (a : Fin 3 → ℂ) (j : Fin 3) (b : ℂ)
    (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => twoCMChi a j f g z + cAux a j * auxV a f g z * (g z - b) / (f z - b)

theorem twoCM_meromorphic_mixedEta {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) :
    Meromorphic (twoCMMixedEta a j b f g) := by
  intro z
  have hχ := twoCM_meromorphic_chi hp j z
  have hU := hp.meromorphic_auxU z
  have hf := hp.nonconst_f.meromorphic z
  have hg := hp.nonconst_g.meromorphic z
  unfold twoCMMixedEta
  fun_prop

theorem twoCM_meromorphic_mixedTheta {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (b : ℂ) :
    Meromorphic (twoCMMixedTheta a j b f g) := by
  intro z
  have hχ := twoCM_meromorphic_chi hp j z
  have hV := hp.meromorphic_auxV z
  have hf := hp.nonconst_f.meromorphic z
  have hg := hp.nonconst_g.meromorphic z
  unfold twoCMMixedTheta
  fun_prop

theorem twoCM_cubicP_three_indices (a : Fin 3 → ℂ) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) (w : ℂ) :
    cubicP a w = (w - a j) * (w - a i) * (w - a k) := by
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    first | exact (hji rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim |
      (simp only [cubicP, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring)

theorem twoCM_mixed_partial_fraction {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    {A b c z : ℂ} (hac : A ≠ c)
    (hP : cubicP a (f z) = (f z - A) * (f z - b) * (f z - c))
    (hfA : f z ≠ A) (hfb : f z ≠ b) (hfc : f z ≠ c) (hgb : g z ≠ b) :
    auxU a f g z * (f z - b) / (g z - b) =
      -(deriv f z / (f z - A) - deriv f z / (f z - c)) / (A - c) +
      (deriv f z / (f z - A) + (c - b) *
        (deriv f z / (f z - A) - deriv f z / (f z - c)) / (A - c)) /
          (g z - b) := by
  unfold auxU
  rw [hP]
  field_simp [sub_ne_zero.mpr hac, sub_ne_zero.mpr hfA,
    sub_ne_zero.mpr hfb, sub_ne_zero.mpr hfc, sub_ne_zero.mpr hgb]
  <;> ring

theorem twoCM_mixedEta_partial_fraction {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    twoCMMixedEta a j (a i) f g =ᶠ[codiscrete ℂ] fun z =>
      (twoCMChi a j f g z - cAux a j /
        (a j - a k) * (deriv f z / (f z - a j) - deriv f z / (f z - a k))) +
      (cAux a j * (deriv f z / (f z - a j) +
        (a k - a i) / (a j - a k) *
          (deriv f z / (f z - a j) - deriv f z / (f z - a k)))) * (g z - a i)⁻¹ := by
  have hac : a j ≠ a k := fun h => hjk (hp.injective h)
  filter_upwards [hp.nonconst_f.eventually_ne (a j), hp.nonconst_f.eventually_ne (a i),
    hp.nonconst_f.eventually_ne (a k), hp.nonconst_g.eventually_ne (a i)]
    with z hfA hfb hfc hgb
  have hpf := twoCM_mixed_partial_fraction hac
    (twoCM_cubicP_three_indices a j i k hji hjk hik (f z)) hfA hfb hfc hgb
  change twoCMChi a j f g z + cAux a j * auxU a f g z * (f z - a i) / (g z - a i) = _
  calc
    _ = twoCMChi a j f g z + cAux a j *
        (auxU a f g z * (f z - a i) / (g z - a i)) := by ring
    _ = _ := by rw [hpf]; ring

theorem twoCM_mixedEta_swap (a : Fin 3 → ℂ) (j : Fin 3) (b : ℂ) (f g : ℂ → ℂ) :
    twoCMMixedEta a j b g f = fun z => -twoCMMixedTheta a j b f g z := by
  ext z
  simp only [twoCMMixedEta, twoCMMixedTheta, twoCMChi, twoCMLogDiff,
    thetaAux, ThetaFun, auxU, auxV]
  ring

theorem twoCM_WChi_swap (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) :
    twoCMWChi a j g f = twoCMWChi a j f g := by
  ext z
  simp only [twoCMWChi, twoCMChi, twoCMLogDiff, thetaAux, ThetaFun, auxPsi, auxU, auxV]
  ring

/-- The squared identity makes chi holomorphic as a germ, even if the scalar
vanishes. No selection of a square-root sign is required. -/
theorem twoCM_chi_order_nonneg_of_WChi_zero {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) (z : ℂ) :
    0 ≤ meromorphicOrderAt (twoCMChi a j f g) z := by
  have heq : (fun w => twoCMChi a j f g w ^ 2) =ᶠ[𝓝[≠] z]
      (fun w => cAux a j ^ 2 * auxPsi a f g w) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp (hW z)] with w hw
    exact sub_eq_zero.mp hw
  have hconst : 0 ≤ meromorphicOrderAt (fun _ : ℂ => cAux a j ^ 2) z :=
    analyticAt_const.meromorphicOrderAt_nonneg
  have hnn : 0 ≤ meromorphicOrderAt (fun w => twoCMChi a j f g w ^ 2) z := by
    rw [meromorphicOrderAt_congr heq]
    change 0 ≤ meromorphicOrderAt ((fun _ : ℂ => cAux a j ^ 2) * auxPsi a f g) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const _ z) (hp.meromorphic_auxPsi z)]
    exact add_nonneg hconst (hp.order_aux (mem_univ z)).2.2.1
  have hsq : meromorphicOrderAt (fun w => twoCMChi a j f g w ^ 2) z =
      2 * meromorphicOrderAt (twoCMChi a j f g) z := by
    exact_mod_cast meromorphicOrderAt_pow (twoCM_meromorphic_chi hp j z) (n := 2)
  rw [hsq] at hnn
  generalize meromorphicOrderAt (twoCMChi a j f g) z = o at hnn ⊢
  induction o using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    rw [show (2 : WithTop ℤ) * (n : WithTop ℤ) = ((2 * n : ℤ) : WithTop ℤ) by norm_cast] at hnn
    have hn : (0 : ℤ) ≤ 2 * n := by exact_mod_cast hnn
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

end ThreeIM
