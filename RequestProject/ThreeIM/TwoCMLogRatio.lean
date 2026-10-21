module

public import RequestProject.ThreeIM.TwoCMAffine
public import RequestProject.ThreeIM.ThetaLocal

/-!
# Equal logarithmic derivatives at a CM value

The quotient of the shifted functions has order zero at every point. Its
regular representative is an entire unit; equal logarithmic derivatives
make it constant and yield an affine germ relation. This proves one branch
of the two-CM argument without any sharing theorem.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

/-- CM sharing at infinity and at a finite target equates the full signed
orders of the two shifted functions, including poles and points off the fiber. -/
theorem twoCM_order_shift_eq (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z : ℂ) :
    meromorphicOrderAt (fun w => f w - a j) z =
      meromorphicOrderAt (fun w => g w - a j) z := by
  by_cases hpole : 0 < mult f ⊤ z
  · have hpoleg : 0 < mult g ⊤ z := by rwa [← hp.cm_top z (mem_univ z)]
    have hf := order_eq_neg_mult_top hpole
    have hg := order_eq_neg_mult_top hpoleg
    have hfneg : meromorphicOrderAt f z < 0 := by rw [hf]; exact_mod_cast (by omega : -(mult f ⊤ z : ℤ) < 0)
    have hgneg : meromorphicOrderAt g z < 0 := by rw [hg]; exact_mod_cast (by omega : -(mult g ⊤ z : ℤ) < 0)
    rw [order_sub_const_of_neg hfneg, order_sub_const_of_neg hgneg,
      hf, hg, hp.cm_top z (mem_univ z)]
  · have hf0 : mult f ⊤ z = 0 := by omega
    have hg0 : mult g ⊤ z = 0 := by rw [← hp.cm_top z (mem_univ z)]; exact hf0
    have hfnn := order_nonneg_of_mult_top_eq_zero hf0
      (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z))
    have hgnn := order_nonneg_of_mult_top_eq_zero hg0
      (order_ne_top_of_nonconst hp.nonconst_g (mem_univ z))
    by_cases hval : 0 < mult f (a j : Sphere) z
    · have hvalg : 0 < mult g (a j : Sphere) z := by rwa [← hcm z (mem_univ z)]
      rw [order_sub_eq_mult hval, order_sub_eq_mult hvalg, hcm z (mem_univ z)]
    · have hfz : mult f (a j : Sphere) z = 0 := by omega
      have hgz : mult g (a j : Sphere) z = 0 := by rw [← hcm z (mem_univ z)]; exact hfz
      rw [order_sub_const_eq_zero_generic hp.nonconst_f (mem_univ z) hfnn hfz,
        order_sub_const_eq_zero_generic hp.nonconst_g (mem_univ z) hgnn hgz]

/-- The shifted quotient is a meromorphic unit at every point. -/
theorem twoCM_order_quotient_eq_zero (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z : ℂ) :
    meromorphicOrderAt (fun w => (g w - a j) / (f w - a j)) z = 0 := by
  have hfm : MeromorphicAt (fun w => f w - a j) z :=
    (hp.nonconst_f.1 z (mem_univ z)).sub (MeromorphicAt.const (a j) z)
  have hgm : MeromorphicAt (fun w => g w - a j) z :=
    (hp.nonconst_g.1 z (mem_univ z)).sub (MeromorphicAt.const (a j) z)
  have heq : (fun w => (g w - a j) / (f w - a j)) =
      (fun w => g w - a j) * (fun w => f w - a j)⁻¹ := by ext w; simp [div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul hgm hfm.inv, meromorphicOrderAt_inv,
    ← twoCM_order_shift_eq hp j hcm z]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.nonconst_f.2 z (mem_univ z) (a j))
  rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel]
  rfl

private theorem twoCM_punctured_of_codiscrete {P : ℂ → Prop}
    (h : ∀ᶠ w in codiscrete ℂ, P w) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, P w :=
  codiscrete_iff_nhdsNE.1 h z

private theorem twoCM_germEq_of_codiscrete {F G : ℂ → ℂ}
    (h : F =ᶠ[codiscrete ℂ] G) (z : ℂ) : F =ᶠ[𝓝[≠] z] G :=
  codiscrete_iff_nhdsNE.1 h z

/-- Equal logarithmic derivatives at the finite CM value give an invertible
affine germ relation; no point values at singularities are identified. -/
theorem twoCM_affine_of_log_deriv_eq (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hlog : (fun z => deriv f z / (f z - a j)) =ᶠ[codiscrete ℂ]
      (fun z => deriv g z / (g z - a j))) :
    ∃ A B : ℂ, A ≠ 0 ∧ ∀ z, g =ᶠ[𝓝[≠] z] fun w => A * f w + B := by
  let Q : ℂ → ℂ := fun w => (g w - a j) / (f w - a j)
  have hQm : MeromorphicOn Q univ := by
    intro z _
    exact ((hp.nonconst_g.1 z (mem_univ z)).sub (MeromorphicAt.const _ _)).div
      ((hp.nonconst_f.1 z (mem_univ z)).sub (MeromorphicAt.const _ _))
  let H := toMeromorphicNFOn Q univ
  have hQH : Q =ᶠ[codiscrete ℂ] H := toMeromorphicNFOn_eqOn_codiscrete hQm
  have hHa : ∀ z, AnalyticAt ℂ H z := by
    intro z
    apply (meromorphicNFOn_toMeromorphicNFOn Q univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hQm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z))]
    rw [twoCM_order_quotient_eq_zero hp j hcm]
  have hQd : deriv Q =ᶠ[codiscrete ℂ] (fun _ => 0) := by
    filter_upwards [eventually_analyticAt_of_meromorphic hp.nonconst_f.meromorphic,
      eventually_analyticAt_of_meromorphic hp.nonconst_g.meromorphic,
      hp.nonconst_f.eventually_ne (a j), hp.nonconst_g.eventually_ne (a j), hlog]
      with z hf hg hfne hgne hl
    have hfsub : DifferentiableAt ℂ (fun w => f w - a j) z :=
      hf.differentiableAt.sub_const _
    have hgsub : DifferentiableAt ℂ (fun w => g w - a j) z :=
      hg.differentiableAt.sub_const _
    have hf0 : f z - a j ≠ 0 := sub_ne_zero.2 hfne
    have hg0 : g z - a j ≠ 0 := sub_ne_zero.2 hgne
    have hc : deriv g z * (f z - a j) - (g z - a j) * deriv f z = 0 := by
      have hl' := (div_eq_div_iff hf0 hg0).1 hl
      linear_combination -hl'
    change deriv (fun w => (g w - a j) / (f w - a j)) z = 0
    rw [deriv_fun_div hgsub hfsub hf0]
    simp only [deriv_sub_const]
    rw [hc, zero_div]
  have hHd : ∀ z, deriv H z = 0 := by
    intro z
    have hlocal : deriv H =ᶠ[𝓝[≠] z] (fun _ => 0) := by
      filter_upwards [(twoCM_germEq_of_codiscrete hQH z).nhdsNE_deriv,
        twoCM_punctured_of_codiscrete hQd z] with w hder hzero
      exact hder.symm.trans hzero
    exact tendsto_nhds_unique
      ((hHa z).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hlocal.symm)
  have hHconst : ∀ z, H z = H 0 :=
    fun z => is_const_of_deriv_eq_zero (fun w => (hHa w).differentiableAt) hHd z 0
  have hQconst : ∀ z, Q =ᶠ[𝓝[≠] z] fun _ => H 0 := by
    intro z
    exact (twoCM_germEq_of_codiscrete hQH z).trans
      (Eventually.of_forall hHconst)
  have hA : H 0 ≠ 0 := by
    intro hz
    have htop : meromorphicOrderAt Q 0 = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      simpa only [hz, Filter.EventuallyEq] using hQconst 0
    have hzero := twoCM_order_quotient_eq_zero hp j hcm 0
    change meromorphicOrderAt Q 0 = 0 at hzero
    rw [hzero] at htop
    exact WithTop.zero_ne_top htop
  refine ⟨H 0, a j - H 0 * a j, hA, fun z => ?_⟩
  filter_upwards [hQconst z,
    twoCM_punctured_of_codiscrete (hp.nonconst_f.eventually_ne (a j)) z] with w hw hn
  have hc := (div_eq_iff (sub_ne_zero.2 hn)).1 hw
  linear_combination hc

/-- The equal-logarithmic-derivative branch gives CM sharing of every
IM-shared sphere value. -/
theorem twoCM_allCM_of_log_deriv_eq (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hlog : (fun z => deriv f z / (f z - a j)) =ᶠ[codiscrete ℂ]
      (fun z => deriv g z / (g z - a j))) {b : Sphere}
    (him : SharesIMOn univ f g b) : SharesCMOn univ f g b := by
  obtain ⟨A, B, hA, hfg⟩ := twoCM_affine_of_log_deriv_eq hp j hcm hlog
  exact twoCM_sharesCM_of_affine_germs hp.nonconst_f.1 hA hfg him

end ThreeIM
