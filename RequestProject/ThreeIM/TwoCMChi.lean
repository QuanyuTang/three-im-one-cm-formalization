module

public import RequestProject.ThreeIM.TwoCMTheta
public import RequestProject.ThreeIM.TwoCMLogRatio
public import RequestProject.ThreeIM.LambdaProximity

/-!
# The second logarithmic auxiliary function in the two-CM argument

The correction to theta is an entire germ because its logarithmic residues
cancel at the two CM values. The two squared identities split globally into
one fixed sign. The same-sign branch already gives all CM sharing.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

noncomputable def twoCMLogDiff (c : ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv f z / (f z - c) - deriv g z / (g z - c)

noncomputable def twoCMChi (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => thetaAux a j f g z - 4 * twoCMLogDiff (a j) f g z

noncomputable def twoCMWChi (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => twoCMChi a j f g z ^ 2 - cAux a j ^ 2 * auxPsi a f g z

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

theorem twoCM_meromorphic_logDiff (hp : NormalizedPair univ f g a) (c : ℂ) :
    Meromorphic (twoCMLogDiff c f g) :=
  (meromorphic_logDeriv_sub hp.nonconst_f.meromorphic c).sub
    (meromorphic_logDeriv_sub hp.nonconst_g.meromorphic c)

theorem twoCM_meromorphic_chi (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (twoCMChi a j f g) := by
  intro z
  have hθ := twoCM_meromorphic_thetaAux hp j z
  have hD := twoCM_meromorphic_logDiff hp (a j) z
  unfold twoCMChi
  fun_prop

theorem twoCM_meromorphic_WChi (hp : NormalizedPair univ f g a) (j : Fin 3) :
    Meromorphic (twoCMWChi a j f g) := by
  intro z
  have hχ := twoCM_meromorphic_chi hp j z
  have hΨ := hp.meromorphic_auxPsi z
  unfold twoCMWChi
  fun_prop

/-- Cancellation of the two equal logarithmic residues is asserted at the
level of analytic punctured germs. -/
theorem twoCM_logDiff_local (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z₀ : ℂ) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧ twoCMLogDiff (a j) f g =ᶠ[𝓝[≠] z₀] E := by
  have hfm : MeromorphicAt (fun w => f w - a j) z₀ :=
    (hp.nonconst_f.1 z₀ (mem_univ z₀)).sub (MeromorphicAt.const _ _)
  have hgm : MeromorphicAt (fun w => g w - a j) z₀ :=
    (hp.nonconst_g.1 z₀ (mem_univ z₀)).sub (MeromorphicAt.const _ _)
  obtain ⟨Ef, hEfa, hf⟩ := logDeriv_local_ordZ hfm (hp.nonconst_f.2 z₀ (mem_univ z₀) (a j))
  obtain ⟨Eg, hEga, hg⟩ := logDeriv_local_ordZ hgm (hp.nonconst_g.2 z₀ (mem_univ z₀) (a j))
  have ho : ordZ (fun w => f w - a j) z₀ = ordZ (fun w => g w - a j) z₀ :=
    congrArg WithTop.untop₀ (twoCM_order_shift_eq hp j hcm z₀)
  refine ⟨fun w => Ef w - Eg w, hEfa.sub hEga, ?_⟩
  filter_upwards [hf, hg] with w hwf hwg
  simp only [deriv_sub_const] at hwf hwg
  simp only [twoCMLogDiff, hwf, hwg, ho]
  ring

theorem twoCM_logDiff_order_nonneg (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z : ℂ) :
    0 ≤ meromorphicOrderAt (twoCMLogDiff (a j) f g) z := by
  obtain ⟨E, hEa, heq⟩ := twoCM_logDiff_local hp j hcm z
  rw [meromorphicOrderAt_congr heq]
  exact hEa.meromorphicOrderAt_nonneg

/-- Chi has the same Laurent residue as theta at every point. -/
theorem twoCM_chi_local (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z₀ : ℂ) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀,
      twoCMChi a j f g z = ((thetaRes a j f z₀ - thetaRes a j g z₀ : ℤ) : ℂ) /
        (z - z₀) + E z := by
  obtain ⟨Ef, hEf, hf⟩ := ThetaFun_local hp.nonconst_f a j z₀ (mem_univ z₀)
  obtain ⟨Eg, hEg, hg⟩ := ThetaFun_local hp.nonconst_g a j z₀ (mem_univ z₀)
  obtain ⟨D, hD, hdeq⟩ := twoCM_logDiff_local hp j hcm z₀
  refine ⟨fun z => Ef z - Eg z - 4 * D z,
    (hEf.sub hEg).sub (analyticAt_const.mul hD), ?_⟩
  filter_upwards [hf, hg, hdeq] with z hzf hzg hzd
  simp only [twoCMChi, thetaAux, hzf, hzg, hzd]
  push_cast
  ring

theorem twoCM_chi_order_support (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (z : ℂ) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (twoCMChi a j f g) z ∧
      (meromorphicOrderAt (twoCMChi a j f g) z < 0 →
        0 < meromorphicOrderAt (auxPsi a f g) z) := by
  obtain ⟨E, hE, heq⟩ := twoCM_chi_local hp j hcm z
  obtain ⟨hord, hzero, _⟩ := order_of_local_form hE heq
  refine ⟨hord, fun hneg => ?_⟩
  have hres : thetaRes a j f z - thetaRes a j g z ≠ 0 := by
    intro h
    exact not_lt_of_ge (hzero (by rw [h]; simp)) hneg
  rcases (thetaRes_sub_spec hp j z (mem_univ z)).1 hres with hd | hψ
  · exact (hd.2.2 (hcm z (mem_univ z))).elim
  · exact hψ

theorem twoCM_negPart_chi_le_psi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    (MeromorphicOn.divisor (twoCMChi a j f g) univ)⁻ ≤
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  simp only [Function.locallyFinsuppWithin.negPart_apply,
    Function.locallyFinsuppWithin.posPart_apply]
  rw [MeromorphicOn.divisor_apply (fun x _ => twoCM_meromorphic_chi hp j x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.meromorphic_auxPsi x) (mem_univ z)]
  obtain ⟨hord, hsupp⟩ := twoCM_chi_order_support hp j hcm z
  have hP0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  induction hχ : meromorphicOrderAt (twoCMChi a j f g) z using WithTop.recTopCoe with
  | top => simpa using hP0
  | coe n =>
    rw [hχ] at hord hsupp
    have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 hord
    simp only [WithTop.untop₀_coe, negPart_def]
    by_cases hn0 : 0 ≤ n
    · omega
    · have hneg : ((n : ℤ) : WithTop ℤ) < 0 := by exact_mod_cast (by omega : n < 0)
      have hψ := hsupp hneg
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
      rw [← hm] at hψ ⊢
      have hmpos : (0 : ℤ) < m := by exact_mod_cast hψ
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hmpos.le]
      omega

theorem twoCM_proximity_logDiff_le (hp : NormalizedPair univ f g a) (c : ℂ) :
    PairProximityBound f g (twoCMLogDiff c f g) := by
  obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp c
  have hF : PairProximityBound f g (fun z => deriv f z / (f z - c)) :=
    ⟨C, hC.mono fun r _ h => h.1⟩
  have hG : PairProximityBound f g (fun z => deriv g z / (g z - c)) :=
    ⟨C, hC.mono fun r _ h => h.2⟩
  exact hF.sub hG (meromorphic_logDeriv_sub hp.nonconst_f.meromorphic c)
    (meromorphic_logDeriv_sub hp.nonconst_g.meromorphic c)

theorem twoCM_proximity_chi_le (hp : NormalizedPair univ f g a) (j : Fin 3) :
    PairProximityBound f g (twoCMChi a j f g) := by
  have hθ : PairProximityBound f g (thetaAux a j f g) := by
    obtain ⟨C, hC⟩ := proximity_thetaAux_le hp
    exact ⟨C, hC.mono fun r _ h => h j⟩
  exact hθ.sub ((twoCM_proximity_logDiff_le hp (a j)).const_mul
      (twoCM_meromorphic_logDiff hp (a j)) 4)
    (twoCM_meromorphic_thetaAux hp j)
    (fun z => (MeromorphicAt.const (4 : ℂ) z).mul (twoCM_meromorphic_logDiff hp (a j) z))

theorem twoCM_charT_chi_le_pairL (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT (twoCMChi a j f g) r ≤ C * pairL f g r := by
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨Cχ, hCχ⟩ := twoCM_proximity_chi_le hp j
  refine ⟨Cχ + CP, (hCχ.and hCP).mono fun r hr ⟨hχ, hP⟩ => ?_⟩
  have hN := Function.locallyFinsuppWithin.logCounting_le (twoCM_negPart_chi_le_psi hp j hcm) hr
  simp only [← logCounting_top, ← logCounting_zero] at hN
  change proximity (twoCMChi a j f g) ⊤ r + logCounting (twoCMChi a j f g) ⊤ r ≤ _
  rw [add_mul]
  linarith

/-- Equal squares of two meromorphic functions choose one fixed sign on the
connected plane. The conclusion is independent of exceptional point values. -/
theorem twoCM_sign_of_square_eq {F G : ℂ → ℂ} (hF : Meromorphic F) (hG : Meromorphic G)
    (hsq : (fun z => F z ^ 2) =ᶠ[codiscrete ℂ] (fun z => G z ^ 2)) :
    F =ᶠ[codiscrete ℂ] G ∨ F =ᶠ[codiscrete ℂ] (fun z => -G z) := by
  have hprod : (fun z => (F z - G z) * (F z + G z)) =ᶠ[codiscrete ℂ] (fun _ => 0) := by
    filter_upwards [hsq] with z hz
    linear_combination hz
  have htop : meromorphicOrderAt ((fun z => F z - G z) * (fun z => F z + G z)) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact codiscrete_iff_nhdsNE.1 hprod 0
  have hDm : MeromorphicOn (fun z => F z - G z) univ := fun z _ => (hF z).sub (hG z)
  have hSm : MeromorphicOn (fun z => F z + G z) univ := fun z _ => (hF z).add (hG z)
  rw [meromorphicOrderAt_mul (hDm 0 (mem_univ 0)) (hSm 0 (mem_univ 0)), WithTop.add_eq_top] at htop
  have hpropagate {K : ℂ → ℂ} (hKm : MeromorphicOn K univ)
      (hK0 : meromorphicOrderAt K 0 = ⊤) : ∀ z, meromorphicOrderAt K z = ⊤ := by
    intro z
    by_contra hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hKm
      isPreconnected_univ (mem_univ z) (mem_univ 0) hz hK0
  rcases htop with hd | hs
  · left
    apply codiscrete_iff_nhdsNE.2
    intro z
    exact (meromorphicOrderAt_eq_top_iff.1 (hpropagate hDm hd z)).mono
      fun w hw => sub_eq_zero.1 hw
  · right
    apply codiscrete_iff_nhdsNE.2
    intro z
    exact (meromorphicOrderAt_eq_top_iff.1 (hpropagate hSm hs z)).mono
      fun w hw => by linear_combination hw

/-- The same-sign branch reduces directly to the proved logarithmic-ratio
branch, hence gives all CM sharing. -/
theorem twoCM_allCM_of_theta_eq_chi (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hsign : thetaAux a j f g =ᶠ[codiscrete ℂ] twoCMChi a j f g) {b : Sphere}
    (him : SharesIMOn univ f g b) : SharesCMOn univ f g b := by
  apply twoCM_allCM_of_log_deriv_eq hp j hcm _ him
  filter_upwards [hsign] with z hz
  have hD : twoCMLogDiff (a j) f g z = 0 := by
    dsimp [twoCMChi] at hz
    linear_combination (1 / 4 : ℂ) * hz
  exact sub_eq_zero.1 hD

/-- Two squared identities leave only the opposite-sign case unless all
shared IM values are already CM. No analytic exclusion is assumed here. -/
theorem twoCM_both_squared_identities_case (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hθ : ∀ z, meromorphicOrderAt (WAux a j f g) z = ⊤)
    (hχ : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    (∀ b : Sphere, SharesIMOn univ f g b → SharesCMOn univ f g b) ∨
      thetaAux a j f g =ᶠ[codiscrete ℂ] (fun z => -twoCMChi a j f g z) := by
  have hsq : (fun z => thetaAux a j f g z ^ 2) =ᶠ[codiscrete ℂ]
      (fun z => twoCMChi a j f g z ^ 2) := by
    apply codiscrete_iff_nhdsNE.2
    intro z
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hθ z),
      meromorphicOrderAt_eq_top_iff.1 (hχ z)] with w hwθ hwχ
    change thetaAux a j f g w ^ 2 - cAux a j ^ 2 * auxPsi a f g w = 0 at hwθ
    change twoCMChi a j f g w ^ 2 - cAux a j ^ 2 * auxPsi a f g w = 0 at hwχ
    linear_combination hwθ - hwχ
  rcases twoCM_sign_of_square_eq (twoCM_meromorphic_thetaAux hp j)
      (twoCM_meromorphic_chi hp j) hsq with hs | hn
  · exact Or.inl fun b him => twoCM_allCM_of_theta_eq_chi hp j hcm hs him
  · exact Or.inr hn

end ThreeIM
