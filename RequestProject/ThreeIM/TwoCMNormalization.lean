module

public import RequestProject.ThreeIM.TwoCMReduction

/-!
# Sphere normalization for the two-CM theorem

This proves the complete reduction to a periodic normalized counterexample.
The analytic exclusion of such a counterexample is an explicit parameter,
so this file does not assert that the two-CM theorem has already been proved.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- The analytic statement still needed after the unconditional reductions. -/
def TwoCMPeriodicExcluded : Prop :=
  ∀ (a : Fin 3 → ℂ) (j : Fin 3) (F G : ℂ → ℂ),
    TwoCMPeriodicCounterexample a j F G → False

private lemma twoCM_mult_eq_of_order_sub_top {f g : ℂ → ℂ}
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
    rw [meromorphicOrderAt_congr (f₂ := fun w => g w - c)
      (hev.mono fun w hw => by rw [hw])]

/-- Excluding periodic counterexamples suffices for the normalized two-CM
statement. No growth condition is imposed on the input functions. -/
theorem twoCM_normalized_of_periodic_exclusion (hexclude : TwoCMPeriodicExcluded)
    {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (ha : Function.Injective a) (him : ∀ j, SharesIMOn univ f g (a j : Sphere))
    (htop : SharesCMOn univ f g ⊤) (jCM : Fin 3)
    (hcm : SharesCMOn univ f g (a jCM : Sphere)) :
    ∀ j, SharesCMOn univ f g (a j : Sphere) := by
  by_cases hdist : ∃ z, meromorphicOrderAt (fun w => f w - g w) z = ⊤
  · obtain ⟨z₀, hz₀⟩ := hdist
    have hall : ∀ z, meromorphicOrderAt (fun w => f w - g w) z = ⊤ := by
      intro z
      by_contra hne
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf.1.sub hg.1)
        isPreconnected_univ (mem_univ z) (mem_univ z₀) hne hz₀
    intro j z _
    exact twoCM_mult_eq_of_order_sub_top hall _ z
  · push_neg at hdist
    have hp : NormalizedPair univ f g a :=
      ⟨hf, hg, fun z _ => hdist z, ha, him, htop⟩
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
          by_contra h3
          exact h0 (hiff.2 (Nat.pos_of_ne_zero h3))
        exact hz (h1.trans h2.symm)
      · by_contra h0
        have h1 : mult g (a j : Sphere) z = 0 := by omega
        have h2 : mult f (a j : Sphere) z = 0 := by
          by_contra h3
          exact h0 (hiff.1 (Nat.pos_of_ne_zero h3))
        exact hz (h2.trans h1.symm)
    obtain ⟨F, G, hcounter⟩ := exists_twoCM_periodicCounterexample hp jCM hcm ⟨j, z, hd⟩
    exact hexclude a jCM F G hcounter

private lemma twoCM_nonconst_mobius {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (c : ℂ) :
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
    rw [← h2]
    ring

/-- Sphere normalization when the last target is one of the CM values. -/
theorem twoCM_at_last_of_periodic_exclusion (hexclude : TwoCMPeriodicExcluded)
    {f g : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i, SharesIMOn univ f g (a i))
    (htop : SharesCMOn univ f g (a 3)) (jCM : Fin 3)
    (hcm : SharesCMOn univ f g (a jCM.castSucc)) :
    ∀ i, SharesCMOn univ f g (a i) := by
  suffices H : ∀ j : Fin 3, SharesCMOn univ f g (a j.castSucc) by
    intro i
    by_cases hi : i = 3
    · subst hi
      exact htop
    · have hi' : i = (⟨i.1, by omega⟩ : Fin 3).castSucc := by ext; simp
      rw [hi']
      exact H _
  have hne : ∀ j : Fin 3, a j.castSucc ≠ a 3 := fun j h => by
    have := ha h
    simp [Fin.ext_iff] at this
    omega
  induction h3 : a 3 using WithTop.recTopCoe with
  | top =>
    have hne' : ∀ j : Fin 3, a j.castSucc ≠ ⊤ := fun j => h3 ▸ hne j
    let a' : Fin 3 → ℂ := fun j => (a j.castSucc).untop (hne' j)
    have hcoe : ∀ j, (a' j : Sphere) = a j.castSucc := fun j => by simp [a']
    have hinj : Function.Injective a' := fun i j hij => by
      have : a i.castSucc = a j.castSucc := by rw [← hcoe, ← hcoe, hij]
      exact Fin.castSucc_injective _ (ha this)
    have H := twoCM_normalized_of_periodic_exclusion hexclude hf hg hinj
      (fun j => hcoe j ▸ him j.castSucc) (h3 ▸ htop) jCM (hcoe jCM ▸ hcm)
    intro j
    rw [← hcoe]
    exact H j
  | coe c =>
    have hfm : ∀ z, MeromorphicAt f z := fun z => hf.1 z (mem_univ z)
    have hgm : ∀ z, MeromorphicAt g z := fun z => hg.1 z (mem_univ z)
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
    let a' : Fin 3 → ℂ := fun j => (mobius c (a j.castSucc)).untop (hne' j)
    have hcoe : ∀ j, (a' j : Sphere) = mobius c (a j.castSucc) := fun j => by simp [a']
    have hinj : Function.Injective a' := fun i j hij => by
      have : mobius c (a i.castSucc) = mobius c (a j.castSucc) := by rw [← hcoe, ← hcoe, hij]
      exact Fin.castSucc_injective _ (ha (mobius_injective c this))
    have H := twoCM_normalized_of_periodic_exclusion hexclude
      (twoCM_nonconst_mobius hf c) (twoCM_nonconst_mobius hg c) hinj
      (fun j => hcoe j ▸ hIM _ (him j.castSucc))
      (by rw [← mobius_self c]; exact hCM _ (h3 ▸ htop)) jCM
      (hcoe jCM ▸ hCM _ hcm)
    intro j
    exact hCM' _ (hcoe j ▸ H j)

/-- Permuting the CM targets and applying sphere normalization reduces the
full two-CM theorem to exclusion of periodic normalized counterexamples. -/
theorem twoCM_of_periodic_exclusion (hexclude : TwoCMPeriodicExcluded)
    {f g : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a : Fin 4 → Sphere) (ha : Function.Injective a)
    (him : ∀ i, SharesIMOn univ f g (a i)) {i₁ i₂ : Fin 4} (hi : i₁ ≠ i₂)
    (hcm₁ : SharesCMOn univ f g (a i₁)) (hcm₂ : SharesCMOn univ f g (a i₂)) :
    ∀ i, SharesCMOn univ f g (a i) := by
  classical
  let e : Equiv.Perm (Fin 4) := Equiv.swap i₁ 3
  let b : Fin 4 → Sphere := a ∘ e
  have he3 : e 3 = i₁ := by simp [e]
  have hek : e i₂ ≠ 3 := by
    intro hk
    have : i₂ = i₁ := e.injective (hk.trans (by simp [e]))
    exact hi this.symm
  let j : Fin 3 := ⟨(e i₂).val, by have := (e i₂).isLt; simp [Fin.ext_iff] at hek; omega⟩
  have hj : j.castSucc = e i₂ := by ext; rfl
  have hb : Function.Injective b := ha.comp e.injective
  have H := twoCM_at_last_of_periodic_exclusion hexclude hf hg b hb
    (fun i => him (e i)) (by simpa [b, Function.comp_def, he3] using hcm₁) j
    (by simpa [b, Function.comp_def, hj, e] using hcm₂)
  intro i
  simpa [b, Function.comp_def, e] using H (e i)

end ThreeIM
