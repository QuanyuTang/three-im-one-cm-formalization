module

public import RequestProject.ThreeIM.TwoCMMixedZeroCounting

/-!
# A reciprocal difference detects the remaining shared fibers
-/

@[expose] public section

open Filter Set Topology ValueDistribution

namespace ThreeIM

theorem twoCM_reciprocalDifference_nonconst_of_defect {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (hdefect : ∃ j z, IsDefect f g (a j : Sphere) z)
    (c : ℂ) {k : ℂ} (hk : k ≠ 0) :
    IsNonconstMeroOn (twoCMReciprocalDifference c k f g) univ := by
  have hH := twoCM_meromorphic_reciprocalDifference hp.nonconst_f.meromorphic hp.nonconst_g.meromorphic c k
  refine ⟨fun z _ => hH z, fun z₀ _ d ht => ?_⟩
  have hm : MeromorphicOn (fun w => twoCMReciprocalDifference c k f g w - d) univ :=
    fun z _ => (hH z).sub (MeromorphicAt.const d z)
  have hall : ∀ z, meromorphicOrderAt (fun w => twoCMReciprocalDifference c k f g w - d) z = ⊤ := by
    intro z
    by_contra hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hm isPreconnected_univ
      (mem_univ z) (mem_univ z₀) hz ht
  let F : ℂ → ℂ := fun w => (f w - c)⁻¹
  let G : ℂ → ℂ := fun w => (g w - c)⁻¹
  have halg (x y : ℂ) (hxy : x - k * y - d = 0) : y = k⁻¹ * x + (-k⁻¹ * d) := by
    field_simp [hk]
    linear_combination -hxy
  have hfg : ∀ z, G =ᶠ[𝓝[≠] z] fun w => k⁻¹ * F w + (-k⁻¹ * d) := by
    intro z
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hall z)] with w hw
    exact halg (F w) (G w) hw
  obtain ⟨j, z, hd⟩ := hdefect
  have him : SharesIMOn univ F G (mobius c (a j : Sphere)) := by
    intro w hw
    rw [mult_mobius (hp.nonconst_f.meromorphic w), mult_mobius (hp.nonconst_g.meromorphic w)]
    exact hp.im j w hw
  have hcm := twoCM_sharesCM_of_affine_germs
    (fun w _ => meromorphicAt_mobius_comp (hp.nonconst_f.meromorphic w) c)
    (inv_ne_zero hk) hfg him z (mem_univ z)
  rw [mult_mobius (hp.nonconst_f.meromorphic z), mult_mobius (hp.nonconst_g.meromorphic z)] at hcm
  exact hd.2.2 hcm

theorem twoCM_reciprocalDifference_mult_pos {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {a b k z : ℂ}
    (hH : IsNonconstMeroOn (twoCMReciprocalDifference a k f g) univ) (hba : b ≠ a)
    (hpf : 0 < mult f (b : Sphere) z) (hpg : 0 < mult g (b : Sphere) z) :
    0 < mult (twoCMReciprocalDifference a k f g) (((b - a)⁻¹ - k * (b - a)⁻¹ : ℂ) : Sphere) z := by
  have hfm : MeromorphicAt (fun w => f w - b) z := (hf.meromorphic z).sub (MeromorphicAt.const b z)
  have hgm : MeromorphicAt (fun w => g w - b) z := (hg.meromorphic z).sub (MeromorphicAt.const b z)
  have hfl : Tendsto (fun w => f w - b) (𝓝[≠] z) (𝓝 0) :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hfm).2 (by rw [order_sub_eq_mult hpf]; exact_mod_cast hpf)
  have hgl : Tendsto (fun w => g w - b) (𝓝[≠] z) (𝓝 0) :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hgm).2 (by rw [order_sub_eq_mult hpg]; exact_mod_cast hpg)
  have hflim : Tendsto f (𝓝[≠] z) (𝓝 b) := by simpa using hfl.add_const b
  have hglim : Tendsto g (𝓝[≠] z) (𝓝 b) := by simpa using hgl.add_const b
  have hFi := (hflim.sub_const a).inv₀ (sub_ne_zero.2 hba)
  have hGi := (hglim.sub_const a).inv₀ (sub_ne_zero.2 hba)
  let v : ℂ := (b - a)⁻¹ - k * (b - a)⁻¹
  have hlim : Tendsto (twoCMReciprocalDifference a k f g) (𝓝[≠] z) (𝓝 v) :=
    hFi.sub (hGi.const_mul k)
  have hlim0 : Tendsto (fun w => twoCMReciprocalDifference a k f g w - v) (𝓝[≠] z) (𝓝 0) := by
    simpa using hlim.sub_const v
  have hsub : MeromorphicAt (fun w => twoCMReciprocalDifference a k f g w - v) z :=
    (hH.meromorphic z).sub (MeromorphicAt.const v z)
  have hpos : 0 < meromorphicOrderAt (fun w => twoCMReciprocalDifference a k f g w - v) z :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hsub).1 hlim0
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hH.2 z (mem_univ z) v)
  have hnpos : 0 < n := by rw [← hn] at hpos; exact_mod_cast hpos
  change 0 < (meromorphicOrderAt (fun w => twoCMReciprocalDifference a k f g w - v) z).untop₀.toNat
  rw [← hn, WithTop.untop₀_coe]
  omega

theorem twoCM_reducedFiberDivisor_le_reciprocalDifference {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {a b k : ℂ} (hH : IsNonconstMeroOn (twoCMReciprocalDifference a k f g) univ)
    (hba : b ≠ a) (him : SharesIMOn univ f g (b : Sphere)) :
    reducedFiberDivisor f (b : Sphere) ≤
      fiberDivisor (twoCMReciprocalDifference a k f g) (((b - a)⁻¹ - k * (b - a)⁻¹ : ℂ) : Sphere) := by
  intro z
  rw [reducedFiberDivisor_apply hf.1, fiberDivisor_apply hH.1]
  split_ifs with hpos
  · have hHpos := twoCM_reciprocalDifference_mult_pos hf hg hH hba hpos (him z (mem_univ z) |>.1 hpos)
    norm_num only [Nat.cast_one]
    have hz : (1 : ℤ) ≤ (mult (twoCMReciprocalDifference a k f g) (((b - a)⁻¹ - k * (b - a)⁻¹ : ℂ) : Sphere) z : ℤ) := by
      exact_mod_cast (show (1 : ℕ) ≤ mult (twoCMReciprocalDifference a k f g) (((b - a)⁻¹ - k * (b - a)⁻¹ : ℂ) : Sphere) z from hHpos)
    exact hz
  · positivity

theorem twoCM_reducedCounting_le_reciprocalDifference {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {a b k : ℂ} (hH : IsNonconstMeroOn (twoCMReciprocalDifference a k f g) univ)
    (hba : b ≠ a) (him : SharesIMOn univ f g (b : Sphere)) {r : ℝ} (hr : 1 ≤ r) :
    reducedCounting f (b : Sphere) r ≤
      logCounting (twoCMReciprocalDifference a k f g) (((b - a)⁻¹ - k * (b - a)⁻¹ : ℂ) : Sphere) r := by
  rw [reducedCounting_eq_reducedFiberDivisor hf.1 _ (by linarith), ← fiberDivisor_logCounting]
  exact Function.locallyFinsuppWithin.logCounting_le
    (twoCM_reducedFiberDivisor_le_reciprocalDifference hf hg hH hba him) hr

end ThreeIM
