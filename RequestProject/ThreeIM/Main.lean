module

public import RequestProject.ThreeIM.Normalization
public import RequestProject.ThreeIM.Periodic
public import RequestProject.ThreeIM.Exclusion

/-!
# Theorem 1.3: three IM values and one CM value

Let `f, g` be nonconstant meromorphic functions on `ℂ` and `a₁, a₂, a₃, a₄ ∈ ℂ̂` pairwise
distinct.  If `a₁, a₂, a₃` are shared IM and `a₄` is shared CM, then all four values are
shared CM.

The proof follows the paper's final argument (Section 10): normalize the CM value to `∞`
(Lemma 3.4); if some finite value has a defect, pass to a periodic counterexample
(Lemma 4.12), select marked inverse branches (Proposition 6.3), and exclude the resulting
selected configuration (Lemmas 10.4–10.6).
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- If `f - g` vanishes identically near every point, all local degrees of `f` and `g`
agree. -/
lemma mult_eq_of_forall_order_sub_eq_top {f g : ℂ → ℂ}
    (h : ∀ z, meromorphicOrderAt (fun w => f w - g w) z = ⊤) (b : Sphere) (z : ℂ) :
    mult f b z = mult g b z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, f w = g w :=
    (meromorphicOrderAt_eq_top_iff.1 (h z)).mono fun w hw => sub_eq_zero.1 hw
  induction b using WithTop.recTopCoe with
  | top =>
    simp only [mult_top]
    rw [meromorphicOrderAt_congr hev]
  | coe c =>
    simp only [mult_coe]
    rw [meromorphicOrderAt_congr (f₂ := fun w => g w - c) (hev.mono fun w hw => by rw [hw])]

/-- **Theorem 1.3, normalized form**: the CM value is `∞` and the three IM values are finite. -/
theorem main_normalized {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (ha : Function.Injective a) (him : ∀ j, SharesIMOn univ f g (a j : Sphere))
    (hcm : SharesCMOn univ f g ⊤) :
    ∀ j, SharesCMOn univ f g (a j : Sphere) := by
  by_cases hdist : ∃ z, meromorphicOrderAt (fun w => f w - g w) z = ⊤
  · obtain ⟨z₀, hz₀⟩ := hdist
    have hall : ∀ z, meromorphicOrderAt (fun w => f w - g w) z = ⊤ := by
      intro z
      by_contra hne
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf.1.sub hg.1)
        isPreconnected_univ (mem_univ z) (mem_univ z₀) hne hz₀
    intro j z _
    exact mult_eq_of_forall_order_sub_eq_top hall _ z
  · push_neg at hdist
    have hpair : NormalizedPair univ f g a := ⟨hf, hg, fun z _ => hdist z, ha, him, hcm⟩
    by_contra hnot
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    simp only [SharesCMOn, mem_univ, forall_const, not_forall] at hj
    obtain ⟨z, hz⟩ := hj
    have hiff := him j z (mem_univ z)
    have hd : IsDefect f g (a j : Sphere) z := by
      refine ⟨?_, ?_, hz⟩
      · by_contra h0
        have h1 : mult f (a j : Sphere) z = 0 := by omega
        have h2 : mult g (a j : Sphere) z = 0 := by
          by_contra h3; exact h0 (hiff.2 (Nat.pos_of_ne_zero h3))
        exact hz (h1.trans h2.symm)
      · by_contra h0
        have h1 : mult g (a j : Sphere) z = 0 := by omega
        have h2 : mult f (a j : Sphere) z = 0 := by
          by_contra h3; exact h0 (hiff.1 (Nat.pos_of_ne_zero h3))
        exact hz (h2.trans h1.symm)
    obtain ⟨f₁, g₁, hP⟩ := exists_periodicCounterexample hpair ⟨j, z, hd⟩
    obtain ⟨S⟩ := hP.selectedConfiguration
    exact S.false

/-- Nonconstancy is preserved by the Möbius map `w ↦ 1/(w - c)`. -/
lemma IsNonconstMeroOn.mobius {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (c : ℂ) :
    IsNonconstMeroOn (fun w => (f w - c)⁻¹) univ := by
  refine ⟨fun z _ => meromorphicAt_mobius_comp (hf.1 z (mem_univ z)) c, fun z _ d hd => ?_⟩
  have hev := meromorphicOrderAt_eq_top_iff.1 hd
  by_cases hd0 : d = 0
  · subst hd0
    apply hf.2 z (mem_univ z) c
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hev] with w hw
    simpa using hw
  · apply hf.2 z (mem_univ z) (c + d⁻¹)
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hev] with w hw
    have h1 : (f w - c)⁻¹ = d := sub_eq_zero.1 hw
    have h2 : f w - c = d⁻¹ := by rw [← h1, inv_inv]
    rw [← h2]; ring

/-- **Theorem 1.3** (main theorem).  Let `f, g` be nonconstant meromorphic functions on `ℂ`,
and let `a 0, a 1, a 2, a 3 ∈ ℂ̂` be pairwise distinct.  If `a 0, a 1, a 2` are shared IM and
`a 3` is shared CM, then all four values are shared CM. -/
theorem three_IM_one_CM {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i : Fin 3, SharesIMOn univ f g (a i.castSucc))
    (hcm : SharesCMOn univ f g (a 3)) :
    ∀ i, SharesCMOn univ f g (a i) := by
  -- reduce the statement over `Fin 4` to the three values `a 0, a 1, a 2`
  suffices H : ∀ j : Fin 3, SharesCMOn univ f g (a j.castSucc) by
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
    have := main_normalized hf hg hinj (fun j => hcoe j ▸ him j) (h3 ▸ hcm)
    intro j; rw [← hcoe]; exact this j
  | coe c =>
    have hfm : ∀ z, MeromorphicAt f z := fun z => hf.1 z (mem_univ z)
    have hgm : ∀ z, MeromorphicAt g z := fun z => hg.1 z (mem_univ z)
    -- transfer of sharing through the Möbius map
    have hIM : ∀ b, SharesIMOn univ f g b →
        SharesIMOn univ (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) (mobius c b) :=
      fun b h z hz => by rw [mult_mobius (hfm z), mult_mobius (hgm z)]; exact h z hz
    have hCM' : ∀ b, SharesCMOn univ (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹)
        (mobius c b) → SharesCMOn univ f g b :=
      fun b h z hz => by rw [← mult_mobius (hfm z) c, ← mult_mobius (hgm z) c]; exact h z hz
    have hCM : ∀ b, SharesCMOn univ f g b →
        SharesCMOn univ (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) (mobius c b) :=
      fun b h z hz => by rw [mult_mobius (hfm z), mult_mobius (hgm z)]; exact h z hz
    have hne' : ∀ j : Fin 3, mobius c (a j.castSucc) ≠ ⊤ := fun j h => by
      rw [← mobius_self c] at h
      exact hne j ((mobius_injective c h).trans h3.symm)
    set a' : Fin 3 → ℂ := fun j => (mobius c (a j.castSucc)).untop (hne' j) with ha'
    have hcoe : ∀ j, (a' j : Sphere) = mobius c (a j.castSucc) := fun j => by simp [ha']
    have hinj : Function.Injective a' := fun i j hij => by
      have : mobius c (a i.castSucc) = mobius c (a j.castSucc) := by
        rw [← hcoe, ← hcoe, hij]
      exact Fin.castSucc_injective _ (ha (mobius_injective c this))
    have := main_normalized (hf.mobius c) (hg.mobius c) hinj
      (fun j => hcoe j ▸ hIM _ (him j)) (by rw [← mobius_self c]; exact hCM _ (h3 ▸ hcm))
    intro j
    exact hCM' _ (hcoe j ▸ this j)

end ThreeIM
