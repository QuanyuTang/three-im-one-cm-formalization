module

public import RequestProject.ThreeIM.RationalAffine
public import RequestProject.ThreeIM.Normalization

/-!
# Proposition 9.28 (rational functions on the punctured plane)

Two nonconstant rational functions sharing four distinct values on `ℂ*`, three IM and one CM,
share all four values CM on `ℂ*`.

The proof follows the paper.  After a common Möbius transformation of the target the CM value is
`∞`, so that the pair is a normalized pair on `ℂ*` (a *rational sharing datum*).  Suppose a
finite shared value has a defect.  The finite endpoint case (Lemma 9.4) is excluded; Lemmas
9.5–9.6 give, after interchanging and rescaling, the balanced opposite-endpoint configuration;
Lemma 9.25 descends it to endpoint pole order one with a retained defect; an affine change of the
target and possibly `t ↦ -t` give the normalization of Lemmas 9.26–9.27, which then show that all
four values are shared CM, contradicting the defect.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

lemma IsDefect.symm {f g : ℂ → ℂ} {b : Sphere} {z : ℂ} (h : IsDefect f g b z) :
    IsDefect g f b z :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

lemma IsDefect.ratScale {R S : RatFunc ℂ} {c : ℂ} (hc : c ≠ 0) {b : Sphere} {z : ℂ}
    (h : IsDefect (ratEval R) (ratEval S) b z) :
    IsDefect (ratEval (ThreeIM.ratScale c R)) (ratEval (ThreeIM.ratScale c S)) b (c⁻¹ * z) := by
  have hh : AnalyticAt ℂ (fun t : ℂ => c * t) (c⁻¹ * z) := analyticAt_const.mul analyticAt_id
  have hh' : deriv (fun t : ℂ => c * t) (c⁻¹ * z) ≠ 0 := by
    rw [deriv_const_mul_field']; simpa using hc
  have e : ∀ F : RatFunc ℂ,
      mult (ratEval (ThreeIM.ratScale c F)) b (c⁻¹ * z) = mult (ratEval F) b z := by
    intro F
    rw [ratEval_ratScale_fun hc F]
    have := mult_comp_of_deriv_ne_zero (f := ratEval F) hh hh' b
    simp only [Function.comp_def] at this
    rw [this, mul_inv_cancel_left₀ hc]
  rw [IsDefect, e R, e S]; exact h

/-- **Lemmas 9.26–9.27 and the end of the proof of Proposition 9.28**, in the form used here:
the normalized configuration with endpoint pole order one, values `0, 1, c` (`c < 0`) and real
positive coefficient `κ`. -/
theorem OppositeData.cm_of_rho_one {R S : RatFunc ℂ} {c κ : ℝ} (hc : c < 0) (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) ![0, 1, (c : ℂ)])
    (hd : OppositeData ![0, 1, (c : ℂ)] R S 0 0 1 κ κ) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![((0 : ℂ) : Sphere), ((1 : ℂ) : Sphere), ((c : ℂ) : Sphere), ⊤] i) := by
  obtain ⟨hR0, hdeg, hlc, hS0, hres, hSinf⟩ := hd.rho_one_conditions hpair
  refine rational_cm_rho_one_of_pair hc hκ hpair ?_ ?_ hR0 hdeg hlc hS0 hres hSinf
  · filter_upwards [hd.aux_U] with t ht; rw [ht]; norm_num
  · filter_upwards [hd.aux_V] with t ht; rw [ht]; norm_num

/-- **Proposition 9.28 for a rational sharing datum**: if `R, S ∈ ℂ(t)` form a normalized pair on
`ℂ*` (distinct, nonconstant, sharing three finite values IM and `∞` CM on `ℂ*`), then the three
finite values are shared CM on `ℂ*`. -/
theorem rational_cm_of_normalizedPair {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    ∀ k : Fin 3, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a k : Sphere) := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨k, hk⟩ := hnot
  simp only [SharesCMOn, not_forall] at hk
  obtain ⟨z, hz, hne⟩ := hk
  have hiff := hpair.im k z hz
  have hdef : IsDefect (ratEval R) (ratEval S) (a k : Sphere) z := by
    refine ⟨?_, ?_, hne⟩
    · by_contra h0
      have h1 : mult (ratEval R) (a k : Sphere) z = 0 := by omega
      have h2 : mult (ratEval S) (a k : Sphere) z = 0 := by
        by_contra h3; exact h0 (hiff.2 (Nat.pos_of_ne_zero h3))
      exact hne (h1.trans h2.symm)
    · by_contra h0
      have h1 : mult (ratEval S) (a k : Sphere) z = 0 := by omega
      have h2 : mult (ratEval R) (a k : Sphere) z = 0 := by
        by_contra h3; exact h0 (hiff.1 (Nat.pos_of_ne_zero h3))
      exact hne (h2.trans h1.symm)
  -- the finite endpoint case (Lemma 9.4)
  by_cases hfin : (R.denom.eval 0 ≠ 0 ∧ S.denom.eval 0 ≠ 0) ∨
      (infVal R.num R.denom ≠ ⊤ ∧ infVal S.num S.denom ≠ ⊤)
  · have h := rational_finite_endpoint_cm hpair hfin k.castSucc
    have e : (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] k.castSucc) = (a k : Sphere) := by
      fin_cases k <;> rfl
    rw [e] at h
    exact hne (h z hz)
  -- Lemmas 9.5–9.6: opposite endpoints, balanced constants
  obtain ⟨R₁, S₁, hswap, c, hc, hp1, j, ρ, γ, hd1, -⟩ := rational_residue_normalization hpair hfin
  have hdef1 : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ),
      IsDefect (ratEval (ratScale c R₁)) (ratEval (ratScale c S₁)) (a k : Sphere) z := by
    have hz0 : z ≠ 0 := hz
    refine ⟨k, c⁻¹ * z, mul_ne_zero (inv_ne_zero hc) hz0, IsDefect.ratScale hc ?_⟩
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdef
    · exact hdef.symm
  -- Lemma 9.25: descent to endpoint pole order one
  obtain ⟨r, s, -, -, hp2, hd2, hdef2⟩ := hd1.descent hp1 hdef1
  -- Lemma 9.6 for the descended pair
  obtain ⟨-, -, -, -, -, -, hnorm⟩ := hd2.residue_normalization hp2
  obtain ⟨i, l, hij, hlj, hli, hcover⟩ : ∃ i l : Fin 3, i ≠ j ∧ l ≠ j ∧ l ≠ i ∧
      ∀ k, k = j ∨ k = i ∨ k = l :=
    ⟨j + 1, j + 2, by fin_cases j <;> decide, by fin_cases j <;> decide,
      by fin_cases j <;> decide, fun k => by fin_cases j <;> fin_cases k <;> decide⟩
  obtain ⟨him, c', hc', hcc⟩ := hnorm i l hij hlj hli
  -- affine change of the target to `0, 1, c'`
  obtain ⟨hp3, hd3⟩ := hd2.affine hij hlj hli hcc hp2
  have hd0 : a i - a j ≠ 0 := sub_ne_zero.2 (hp2.injective.ne hij)
  obtain ⟨k₂, z₂, hz₂, hdef₂⟩ := hdef2
  have hdef3 := hdef₂.ratAff hd0 (a j) (a k₂)
  set r' := ratAff (a j) (a i - a j) r
  set s' := ratAff (a j) (a i - a j) s
  set K := (a i - a j) * (γ / ρ) with hKdef
  have hK0 : K ≠ 0 := hd3.alpha_ne
  have hKr : K = (K.re : ℂ) := Complex.ext rfl (by simpa [hKdef] using him)
  have hKre : K.re ≠ 0 := fun h => hK0 (by rw [hKr, h, Complex.ofReal_zero])
  -- the value of the defect is one of `0, 1, c'`
  have hv : ∃ m : Fin 4, (((a k₂ - a j) / (a i - a j) : ℂ) : Sphere) =
      ![((0 : ℂ) : Sphere), ((1 : ℂ) : Sphere), ((c' : ℂ) : Sphere), ⊤] m := by
    rcases hcover k₂ with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [div_self hd0]⟩
    · exact ⟨2, by simp [hcc]⟩
  obtain ⟨m, hm⟩ := hv
  rw [hm] at hdef3
  rcases lt_or_gt_of_ne hKre with hneg | hpos
  · -- replace `t` by `-t`
    have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
    have hp4 := hp3.ratScale hm1
    have hd4 := hd3.ratScale hm1
    have e1 : K * (-1 : ℂ) ^ (-((1 : ℕ) : ℤ)) = ((-K.re : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, ← hKr]; norm_num
    have e2 : K * (-1 : ℂ) ^ ((1 : ℕ) : ℤ) = ((-K.re : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, ← hKr]; norm_num
    rw [e1, e2] at hd4
    have hall := hd4.cm_of_rho_one hc' (by linarith) hp4
    have hdef4 := hdef3.ratScale hm1
    exact hdef4.2.2 (hall m _ (mul_ne_zero (inv_ne_zero hm1) hz₂))
  · rw [hKr] at hd3
    have hall := hd3.cm_of_rho_one hc' hpos hp3
    exact hdef3.2.2 (hall m z₂ hz₂)

/-! ### Removing the normalization of the CM value -/

/-- Proposition 9.28 with the CM value `∞` and three finite IM values. -/
theorem rational_cm_top {R S : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c)
    (hS : ∀ c : ℂ, S ≠ RatFunc.C c) {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (him : ∀ j, SharesIMOn {0}ᶜ (ratEval R) (ratEval S) (a j : Sphere))
    (hcm : SharesCMOn {0}ᶜ (ratEval R) (ratEval S) ⊤) :
    ∀ j, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a j : Sphere) := by
  by_cases hdist : ∃ z, meromorphicOrderAt (fun w => ratEval R w - ratEval S w) z = ⊤
  · obtain ⟨z₀, hz₀⟩ := hdist
    have hmer : MeromorphicOn (fun w => ratEval R w - ratEval S w) univ := fun z _ =>
      (meromorphicAt_ratEval R z).sub (meromorphicAt_ratEval S z)
    have hall : ∀ z, meromorphicOrderAt (fun w => ratEval R w - ratEval S w) z = ⊤ := by
      intro z
      by_contra hne
      exact hmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z)
        (mem_univ z₀) hne hz₀
    intro j z _
    have hev : ∀ᶠ w in 𝓝[≠] z, ratEval R w = ratEval S w :=
      (meromorphicOrderAt_eq_top_iff.1 (hall z)).mono fun w hw => sub_eq_zero.1 hw
    exact mult_congr_nhdsNE hev _
  · push_neg at hdist
    exact rational_cm_of_normalizedPair ⟨isNonconstMeroOn_ratEval hR _,
      isNonconstMeroOn_ratEval hS _, fun z _ => hdist z, ha, him, hcm⟩

/-- The rational function `1/(R - c)`. -/
noncomputable def ratMob (c : ℂ) (R : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) R.denom / algebraMap ℂ[X] (RatFunc ℂ) (R.num - C c * R.denom)

lemma isCoprime_ratMob (c : ℂ) (R : RatFunc ℂ) : IsCoprime R.denom (R.num - C c * R.denom) := by
  have := (RatFunc.isCoprime_num_denom R).add_mul_left_left (-C c)
  exact (by convert this using 1; ring : IsCoprime (R.num - C c * R.denom) R.denom).symm

lemma ratEval_ratMob_of_ne {c : ℂ} {R : RatFunc ℂ} (hR : R ≠ RatFunc.C c) {t : ℂ}
    (ht : R.denom.eval t ≠ 0) : ratEval (ratMob c R) t = (ratEval R t - c)⁻¹ := by
  unfold ratMob
  rw [ratEval_div_of_coprime (num_sub_ne_zero hR) (isCoprime_ratMob c R), ratEval_eq]
  simp only [eval_sub, eval_mul, eval_C]
  rw [div_sub' ht, inv_div]
  ring

lemma ratEval_ratMob_nhdsNE {c : ℂ} {R : RatFunc ℂ} (hR : R ≠ RatFunc.C c) (z : ℂ) :
    ratEval (ratMob c R) =ᶠ[𝓝[≠] z] fun w => (ratEval R w - c)⁻¹ :=
  eventually_nhdsNE_of_cofinite (by
    filter_upwards [IsRatFun.eventually_ne R.denom_ne_zero] with t ht
    exact ratEval_ratMob_of_ne hR ht) z

lemma mult_ratMob {c : ℂ} {R : RatFunc ℂ} (hR : R ≠ RatFunc.C c) (b : Sphere) (z : ℂ) :
    mult (ratEval (ratMob c R)) (mobius c b) z = mult (ratEval R) b z := by
  rw [mult_congr_nhdsNE (ratEval_ratMob_nhdsNE hR z), mult_mobius (meromorphicAt_ratEval R z)]

lemma ratMob_ne_C {c : ℂ} {R : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c) (c' : ℂ) :
    ratMob c R ≠ RatFunc.C c' := by
  intro hc
  have hnc := isNonconstMeroOn_ratEval hR ({0}ᶜ : Set ℂ)
  have hval : ∀ᶠ w in 𝓝[≠] (1 : ℂ), (ratEval R w - c)⁻¹ = c' := by
    filter_upwards [ratEval_ratMob_nhdsNE (hR c) 1] with w hw
    rw [← hw, hc]; simp [ratEval]
  by_cases h0 : c' = 0
  · apply hnc.2 1 one_ne_zero c
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hval] with w hw
    rw [h0, inv_eq_zero] at hw; exact hw
  · apply hnc.2 1 one_ne_zero (c + c'⁻¹)
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hval] with w hw
    have : ratEval R w - c = c'⁻¹ := by rw [← hw, inv_inv]
    rw [← this]; ring

end ThreeIM

namespace ThreeIM

/-- **Proposition 9.28.**  Let `R, S ∈ ℂ(t)` be nonconstant.  If they share four distinct values
on `ℂ*`, three IM and one CM, then all four are shared CM on `ℂ*`.  No sharing condition is
imposed at `0` or `∞`. -/
theorem rational_four_values {R S : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c)
    (hS : ∀ c : ℂ, S ≠ RatFunc.C c) (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i : Fin 3, SharesIMOn {0}ᶜ (ratEval R) (ratEval S) (a i.castSucc))
    (hcm : SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a 3)) :
    ∀ i, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a i) := by
  suffices H : ∀ j : Fin 3, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) (a j.castSucc) by
    intro i
    by_cases hi : i = 3
    · subst hi; exact hcm
    · have : i = (⟨i.1, by omega⟩ : Fin 3).castSucc := by ext; simp
      rw [this]; exact H _
  have hne : ∀ j : Fin 3, a j.castSucc ≠ a 3 := fun j h => by
    have := ha h; simp [Fin.ext_iff] at this; omega
  induction h3 : a 3 using WithTop.recTopCoe with
  | top =>
    have hne' : ∀ j : Fin 3, a j.castSucc ≠ ⊤ := fun j => h3 ▸ hne j
    set a' : Fin 3 → ℂ := fun j => (a j.castSucc).untop (hne' j) with ha'
    have hcoe : ∀ j, (a' j : Sphere) = a j.castSucc := fun j => by simp [ha']
    have hinj : Function.Injective a' := fun i j hij => by
      have : a i.castSucc = a j.castSucc := by rw [← hcoe, ← hcoe, hij]
      exact Fin.castSucc_injective _ (ha this)
    have := rational_cm_top hR hS hinj (fun j => hcoe j ▸ him j) (h3 ▸ hcm)
    intro j; rw [← hcoe]; exact this j
  | coe c =>
    have hIM : ∀ b, SharesIMOn {0}ᶜ (ratEval R) (ratEval S) b →
        SharesIMOn {0}ᶜ (ratEval (ratMob c R)) (ratEval (ratMob c S)) (mobius c b) :=
      fun b h z hz => by rw [mult_ratMob (hR c), mult_ratMob (hS c)]; exact h z hz
    have hCM' : ∀ b, SharesCMOn {0}ᶜ (ratEval (ratMob c R)) (ratEval (ratMob c S))
        (mobius c b) → SharesCMOn {0}ᶜ (ratEval R) (ratEval S) b :=
      fun b h z hz => by rw [← mult_ratMob (hR c), ← mult_ratMob (hS c)]; exact h z hz
    have hCM : ∀ b, SharesCMOn {0}ᶜ (ratEval R) (ratEval S) b →
        SharesCMOn {0}ᶜ (ratEval (ratMob c R)) (ratEval (ratMob c S)) (mobius c b) :=
      fun b h z hz => by rw [mult_ratMob (hR c), mult_ratMob (hS c)]; exact h z hz
    have hne' : ∀ j : Fin 3, mobius c (a j.castSucc) ≠ ⊤ := fun j h => by
      rw [← mobius_self c] at h
      exact hne j ((mobius_injective c h).trans h3.symm)
    set a' : Fin 3 → ℂ := fun j => (mobius c (a j.castSucc)).untop (hne' j) with ha'
    have hcoe : ∀ j, (a' j : Sphere) = mobius c (a j.castSucc) := fun j => by simp [ha']
    have hinj : Function.Injective a' := fun i j hij => by
      have : mobius c (a i.castSucc) = mobius c (a j.castSucc) := by
        rw [← hcoe, ← hcoe, hij]
      exact Fin.castSucc_injective _ (ha (mobius_injective c this))
    have := rational_cm_top (ratMob_ne_C hR) (ratMob_ne_C hS) hinj
      (fun j => hcoe j ▸ hIM _ (him j)) (by rw [← mobius_self c]; exact hCM _ (h3 ▸ hcm))
    intro j
    exact hCM' _ (hcoe j ▸ this j)

end ThreeIM
