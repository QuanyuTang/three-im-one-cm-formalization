module

public import RequestProject.ThreeIM.TwoCMChi

/-!
# Counting the finite CM fiber with the second auxiliary function

At a common simple point over the CM target, the Lambda difference vanishes.
Subtracting its regular correction gives the squared-chi identity there.
Higher multiplicities are charged to zeros of the Mues function.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

private lemma twoCM_cubicP_cyclic (a : Fin 3 → ℂ) (j : Fin 3) (w : ℂ) :
    cubicP a w = (w - a j) * (w - a (j + 1)) * (w - a (j + 2)) := by
  fin_cases j <;> simp [cubicP] <;> ring

noncomputable def twoCMRegularTerm (a : Fin 3 → ℂ) (j : Fin 3) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv h z * (3 * h z - a j - a (j + 1) - a (j + 2)) /
    ((h z - a (j + 1)) * (h z - a (j + 2)))

/-- The Lambda expansion removes the second derivative from the finite-fiber
limit calculation. Only the two other denominator fibers are excluded. -/
theorem twoCM_chi_eq_EAux_sub_regular (hp : NormalizedPair univ f g a) (j : Fin 3) :
    twoCMChi a j f g =ᶠ[codiscrete ℂ]
      (fun z => EAux a j f g z -
        (twoCMRegularTerm a j f z - twoCMRegularTerm a j g z)) := by
  filter_upwards [hp.nonconst_f.eventually_ne (a (j + 1)),
    hp.nonconst_f.eventually_ne (a (j + 2)),
    hp.nonconst_g.eventually_ne (a (j + 1)),
    hp.nonconst_g.eventually_ne (a (j + 2))] with z hfb hfc hgb hgc
  have hidentity (h p : ℂ) (hb : h ≠ a (j + 1)) (hc : h ≠ a (j + 2)) :
      p * (h - a j) / ((h - a (j + 1)) * (h - a (j + 2))) +
        p / (h - a (j + 1)) + p / (h - a (j + 2)) =
      p * (3 * h - a j - a (j + 1) - a (j + 2)) /
        ((h - a (j + 1)) * (h - a (j + 2))) := by
    field_simp [sub_ne_zero.2 hb, sub_ne_zero.2 hc]
    ring
  have hF := hidentity (f z) (deriv f z) hfb hfc
  have hG := hidentity (g z) (deriv g z) hgb hgc
  simp only [twoCMChi, twoCMLogDiff, twoCMRegularTerm, thetaAux, ThetaFun,
    EAux, LambdaFun, LambdaCore]
  linear_combination -hF + hG

private lemma twoCM_simple_models {h : ℂ → ℂ} {z₀ c : ℂ}
    (hh : MeromorphicAt h z₀)
    (ho : meromorphicOrderAt (fun w => h w - c) z₀ = (1 : ℤ)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ F z₀ ≠ 0 ∧
      h =ᶠ[𝓝[≠] z₀] (fun w => c + (w - z₀) * F w) ∧
      deriv h =ᶠ[𝓝[≠] z₀] (fun w => F w + (w - z₀) * deriv F w) := by
  obtain ⟨F, hFa, hF0, heq⟩ := local_rep hh (m := 1) (by decide) ho
  refine ⟨F, hFa, hF0, ?_, ?_⟩
  · exact heq.mono fun w hw => by simpa only [pow_one] using hw.1
  · exact heq.mono fun w hw => by
      simpa only [Nat.sub_self, pow_zero, Nat.cast_one, one_mul] using hw.2

private lemma twoCM_simple_limits {h F : ℂ → ℂ} {z₀ c : ℂ}
    (hFa : AnalyticAt ℂ F z₀)
    (hh : h =ᶠ[𝓝[≠] z₀] (fun w => c + (w - z₀) * F w))
    (hd : deriv h =ᶠ[𝓝[≠] z₀] (fun w => F w + (w - z₀) * deriv F w)) :
    Tendsto h (𝓝[≠] z₀) (𝓝 c) ∧ Tendsto (deriv h) (𝓝[≠] z₀) (𝓝 (F z₀)) := by
  have hs : ContinuousAt (fun w : ℂ => w - z₀) z₀ := by fun_prop
  have ht : Tendsto (fun w : ℂ => w - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using hs.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
  have hF : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) :=
    hFa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFd : Tendsto (deriv F) (𝓝[≠] z₀) (𝓝 (deriv F z₀)) :=
    hFa.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun _ : ℂ => c) (𝓝[≠] z₀) (𝓝 c) := tendsto_const_nhds
  constructor
  · simpa using (hC.add (ht.mul hF)).congr' hh.symm
  · simpa using (hF.add (ht.mul hFd)).congr' hd.symm

/-- The second squared auxiliary vanishes at every common simple point over
the marked target. It uses germs throughout and allows coincident leading terms. -/
theorem twoCM_tendsto_WChi_shared_simple (hp : NormalizedPair univ f g a) (j : Fin 3)
    {z₀ : ℂ} (hf1 : meromorphicOrderAt (fun w => f w - a j) z₀ = (1 : ℤ))
    (hg1 : meromorphicOrderAt (fun w => g w - a j) z₀ = (1 : ℤ)) :
    Tendsto (twoCMWChi a j f g) (𝓝[≠] z₀) (𝓝 0) := by
  obtain ⟨F, hFa, hF0, hF, hFd⟩ := twoCM_simple_models (hp.nonconst_f.meromorphic z₀) hf1
  obtain ⟨G, hGa, hG0, hG, hGd⟩ := twoCM_simple_models (hp.nonconst_g.meromorphic z₀) hg1
  obtain ⟨hflim, hfdlim⟩ := twoCM_simple_limits hFa hF hFd
  obtain ⟨hglim, hgdlim⟩ := twoCM_simple_limits hGa hG hGd
  have hjb : j ≠ j + 1 := by fin_cases j <;> decide
  have hjc : j ≠ j + 2 := by fin_cases j <;> decide
  let K : ℂ := (a j - a (j + 1)) * (a j - a (j + 2))
  have hK : K ≠ 0 := mul_ne_zero (sub_ne_zero.2 (hp.injective.ne hjb))
    (sub_ne_zero.2 (hp.injective.ne hjc))
  have hFt : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hFa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGt : Tendsto G (𝓝[≠] z₀) (𝓝 (G z₀)) := hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFne : ∀ᶠ w in 𝓝[≠] z₀, F w ≠ 0 :=
    nhdsWithin_le_nhds (hFa.continuousAt.eventually_ne hF0)
  have hGne : ∀ᶠ w in 𝓝[≠] z₀, G w ≠ 0 :=
    nhdsWithin_le_nhds (hGa.continuousAt.eventually_ne hG0)
  have hratioF : (fun w => (f w - g w) / (f w - a j)) =ᶠ[𝓝[≠] z₀]
      (fun w => (F w - G w) / F w) := by
    filter_upwards [hF, hG, hFne, self_mem_nhdsWithin] with w hwf hwg hfn hwz
    rw [hwf, hwg]
    field_simp [hfn, sub_ne_zero.2 hwz]
    ring
  have hratioG : (fun w => (f w - g w) / (g w - a j)) =ᶠ[𝓝[≠] z₀]
      (fun w => (F w - G w) / G w) := by
    filter_upwards [hF, hG, hGne, self_mem_nhdsWithin] with w hwf hwg hgn hwz
    rw [hwf, hwg]
    field_simp [hgn, sub_ne_zero.2 hwz]
    ring
  have hrFlim := ((hFt.sub hGt).div hFt hF0).congr' hratioF.symm
  have hrGlim := ((hFt.sub hGt).div hGt hG0).congr' hratioG.symm
  have hUf (w : ℂ) : auxU a f g w = (f w - g w) / (f w - a j) * deriv f w /
      ((f w - a (j + 1)) * (f w - a (j + 2))) := by
    simp only [auxU, twoCM_cubicP_cyclic a j, div_eq_mul_inv, mul_inv_rev]
    ring
  have hVg (w : ℂ) : auxV a f g w = (f w - g w) / (g w - a j) * deriv g w /
      ((g w - a (j + 1)) * (g w - a (j + 2))) := by
    simp only [auxV, twoCM_cubicP_cyclic a j, div_eq_mul_inv, mul_inv_rev]
    ring
  have hUlim : Tendsto (auxU a f g) (𝓝[≠] z₀) (𝓝 ((F z₀ - G z₀) / K)) := by
    have h := ((hrFlim.mul hfdlim).div
      ((hflim.sub_const (a (j + 1))).mul (hflim.sub_const (a (j + 2)))) hK).congr'
        (Eventually.of_forall fun w => (hUf w).symm)
    convert h using 1
    congr 1
    dsimp [K]
    field_simp [hF0, hK]
  have hVlim : Tendsto (auxV a f g) (𝓝[≠] z₀) (𝓝 ((F z₀ - G z₀) / K)) := by
    have h := ((hrGlim.mul hgdlim).div
      ((hglim.sub_const (a (j + 1))).mul (hglim.sub_const (a (j + 2)))) hK).congr'
        (Eventually.of_forall fun w => (hVg w).symm)
    convert h using 1
    congr 1
    dsimp [K]
    field_simp [hG0, hK]
  have hΨlim : Tendsto (auxPsi a f g) (𝓝[≠] z₀) (𝓝 (((F z₀ - G z₀) / K) ^ 2)) := by
    have hfun : auxPsi a f g = (fun w => auxU a f g w * auxV a f g w) := by
      funext w
      rfl
    rw [hfun]
    simpa only [pow_two] using hUlim.mul hVlim
  have hRF : Tendsto (twoCMRegularTerm a j f) (𝓝[≠] z₀)
      (𝓝 (F z₀ * cAux a j / K)) := by
    have h := (hfdlim.mul ((((hflim.const_mul 3).sub_const (a j)).sub_const (a (j + 1))).sub_const (a (j + 2)))).div
        ((hflim.sub_const (a (j + 1))).mul (hflim.sub_const (a (j + 2)))) hK
    convert h using 1
    congr 1
    dsimp [K, cAux]
    ring
  have hRG : Tendsto (twoCMRegularTerm a j g) (𝓝[≠] z₀)
      (𝓝 (G z₀ * cAux a j / K)) := by
    have h := (hgdlim.mul ((((hglim.const_mul 3).sub_const (a j)).sub_const (a (j + 1))).sub_const (a (j + 2)))).div
        ((hglim.sub_const (a (j + 1))).mul (hglim.sub_const (a (j + 2)))) hK
    convert h using 1
    congr 1
    dsimp [K, cAux]
    ring
  have hEpos : 0 < meromorphicOrderAt (EAux a j f g) z₀ :=
    lt_of_lt_of_le (by decide : (0 : WithTop ℤ) < 1)
      (EAux_order_ge_one_at_shared_simple (hp.nonconst_f.meromorphic z₀)
        (hp.nonconst_g.meromorphic z₀) hp.injective j hf1 hg1)
  have hElim := (tendsto_zero_iff_meromorphicOrderAt_pos
    (meromorphicAt_EAux (hp.nonconst_f.meromorphic z₀) (hp.nonconst_g.meromorphic z₀) a j)).2 hEpos
  have hχlim : Tendsto (twoCMChi a j f g) (𝓝[≠] z₀)
      (𝓝 (-(F z₀ - G z₀) * cAux a j / K)) := by
    have heqχ : twoCMChi a j f g =ᶠ[𝓝[≠] z₀]
        (fun z => EAux a j f g z - (twoCMRegularTerm a j f z - twoCMRegularTerm a j g z)) :=
      codiscrete_iff_nhdsNE.1 (twoCM_chi_eq_EAux_sub_regular hp j) z₀
    have h := (hElim.sub (hRF.sub hRG)).congr' heqχ.symm
    convert h using 1 <;> ring
  have hW := (hχlim.pow 2).sub (hΨlim.const_mul (cAux a j ^ 2))
  change Tendsto (twoCMWChi a j f g) (𝓝[≠] z₀)
    (𝓝 ((-(F z₀ - G z₀) * cAux a j / K) ^ 2 - cAux a j ^ 2 * ((F z₀ - G z₀) / K) ^ 2)) at hW
  convert hW using 1
  simp only [div_eq_mul_inv]
  ring

end ThreeIM
