module

public import RequestProject.ThreeIM.PicardBasic

/-!
# Little Picard for meromorphic functions

Move one omitted spherical value to infinity. The resulting meromorphic germ
has no pole; its canonical representative is entire. The entire two-omitted-
values result then gives a contradiction. The changes of representatives and
of target coordinates preserve all local multiplicities.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

private theorem mult_eq_of_germ_eq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝[≠] z] g) (b : Sphere) : mult f b z = mult g b z := by
  induction b using WithTop.recTopCoe with
  | top => simp only [mult_top]; rw [meromorphicOrderAt_congr h]
  | coe c =>
    simp only [mult_coe]
    rw [meromorphicOrderAt_congr (f₂ := fun w => g w - c)
      (h.mono fun w hw => by rw [hw])]

private theorem order_nonneg_of_omits_top {f : ℂ → ℂ} {z : ℂ}
    (hfinite : meromorphicOrderAt f z ≠ ⊤) (homit : mult f ⊤ z = 0) :
    0 ≤ meromorphicOrderAt f z := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfinite
  simp only [mult_top, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
    WithTop.untop₀_coe] at homit
  have hn0 : 0 ≤ n := by omega
  rw [← hn]
  exact_mod_cast hn0

private theorem nonconst_inverse_shift {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (c : ℂ) :
    IsNonconstMeroOn (fun w => (f w - c)⁻¹) univ := by
  refine ⟨fun z _ => meromorphicAt_mobius_comp (hf.1 z (mem_univ z)) c,
    fun z _ d hd => ?_⟩
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
    have h₁ : (f w - c)⁻¹ = d := sub_eq_zero.1 hw
    have h₂ : f w - c = d⁻¹ := by rw [← h₁, inv_inv]
    rw [← h₂]
    ring

private theorem two_finite_targets_of_top {f : ℂ → ℂ}
    (b : Fin 3 → Sphere) (hb : Function.Injective b) (h₀ : b 0 = ⊤)
    (homit : ∀ i z, mult f (b i) z = 0) :
    ∃ a : Fin 2 → ℂ, Function.Injective a ∧ ∀ i z, mult f (a i : Sphere) z = 0 := by
  have hfinite : ∀ i : Fin 2, b i.succ ≠ ⊤ := by
    intro i hi
    have hindex : i.succ = 0 := hb (hi.trans h₀.symm)
    simpa using congrArg Fin.val hindex
  choose a ha using fun i => WithTop.ne_top_iff_exists.1 (hfinite i)
  refine ⟨a, ?_, ?_⟩
  · intro i j hij
    have hindex : i.succ = j.succ := hb (by rw [← ha i, ← ha j, hij])
    apply Fin.ext
    have hval := congrArg Fin.val hindex
    simp only [Fin.val_succ] at hval
    omega
  · intro i z
    rw [ha i]
    exact homit i.succ z

private theorem omitted_chart {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    (b : Fin 3 → Sphere) (hb : Function.Injective b)
    (homit : ∀ i z, mult f (b i) z = 0) :
    ∃ (F : ℂ → ℂ) (a : Fin 2 → ℂ), IsNonconstMeroOn F univ ∧ Function.Injective a ∧
      (∀ z, mult F ⊤ z = 0) ∧ ∀ i z, mult F (a i : Sphere) z = 0 := by
  classical
  by_cases htop : b 0 = ⊤
  · obtain ⟨a, ha, homit'⟩ := two_finite_targets_of_top b hb htop homit
    exact ⟨f, a, hf, ha, fun z => by simpa only [htop] using homit 0 z, homit'⟩
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 htop
    let F : ℂ → ℂ := fun w => (f w - c)⁻¹
    let B : Fin 3 → Sphere := fun i => mobius c (b i)
    have hB : Function.Injective B := (mobius_injective c).comp hb
    have hB₀ : B 0 = ⊤ := by simp only [B, ← hc, mobius_self]
    have homitB : ∀ i z, mult F (B i) z = 0 := by
      intro i z
      rw [show mult F (B i) z = mult f (b i) z from
        mult_mobius (hf.1 z (mem_univ z)) c (b i)]
      exact homit i z
    obtain ⟨a, ha, homit'⟩ := two_finite_targets_of_top B hB hB₀ homitB
    exact ⟨F, a, nonconst_inverse_shift hf c, ha,
      fun z => by simpa only [hB₀] using homitB 0 z, homit'⟩

theorem little_picard {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    (b : Fin 3 → Sphere) (hb : Function.Injective b) : ∃ i z, 0 < mult f (b i) z := by
  classical
  by_contra hnone
  have homit : ∀ i z, mult f (b i) z = 0 := by
    intro i z
    by_contra hne
    exact hnone ⟨i, z, Nat.pos_of_ne_zero hne⟩
  obtain ⟨F, a, hF, ha, htop, hfinite⟩ := omitted_chart hf b hb homit
  let H := toMeromorphicNFOn F univ
  have hEq : ∀ z, H =ᶠ[𝓝[≠] z] F :=
    fun z => hF.1.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hHm : MeromorphicOn H univ :=
    (meromorphicNFOn_toMeromorphicNFOn F univ).meromorphicOn
  have hHa : ∀ z, AnalyticAt ℂ H z := by
    intro z
    apply ((meromorphicNFOn_toMeromorphicNFOn F univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt).1
    rw [meromorphicOrderAt_congr (hEq z)]
    exact order_nonneg_of_omits_top (order_ne_top_of_nonconst hF (mem_univ z)) (htop z)
  have hHn : IsNonconstMeroOn H univ := by
    refine ⟨hHm, fun z _ c => ?_⟩
    rw [meromorphicOrderAt_congr (f₂ := fun w => F w - c)
      ((hEq z).mono fun w hw => by rw [hw])]
    exact hF.2 z (mem_univ z) c
  apply entire_omits_two_impossible (fun z => (hHa z).differentiableAt) hHn a ha
  intro i z
  rw [mult_eq_of_germ_eq (hEq z)]
  exact hfinite i z

end ThreeIM
