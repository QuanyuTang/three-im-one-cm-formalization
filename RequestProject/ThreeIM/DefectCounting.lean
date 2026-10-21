module

public import RequestProject.ThreeIM.Counting
public import RequestProject.ThreeIM.LambdaLocal

/-!
# Reduced multiplicity defects and poles of the Lambda differences

The divisor of defects records one at each point where the two fiber
multiplicities differ. Under IM sharing this is precisely the reduced defect
divisor. The local Laurent estimates imply that every pole of `E_a` is simple
and is charged to a defect or a zero of the entire auxiliary function `Ψ`.

Only the pure local and divisor modules are imported here.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Classical

namespace ThreeIM

/-- The reduced divisor of unequal fiber multiplicities. Under IM sharing it
is exactly the indicator divisor of the defects. -/
noncomputable def defectDivisor (f g : ℂ → ℂ) (b : Sphere) :
    Function.locallyFinsupp ℂ ℤ :=
  truncatePositiveDivisor |fiberDivisor f b - fiberDivisor g b|

/-- Integrated reduced multiplicity defects. -/
noncomputable def defectCounting (f g : ℂ → ℂ) (b : Sphere) : ℝ → ℝ :=
  (defectDivisor f g b).logCounting

/-- The total reduced defect divisor over the three marked finite values. -/
noncomputable def totalDefectDivisor (a : Fin 3 → ℂ) (f g : ℂ → ℂ) :
    Function.locallyFinsupp ℂ ℤ :=
  ∑ j, defectDivisor f g (a j : Sphere)

/-- The sum of the three reduced defect counting functions. -/
noncomputable def totalDefectCounting (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∑ j, defectCounting f g (a j : Sphere) r

private lemma defectCounting_sum_apply {α : Type*} (s : Finset α)
    (D : α → Function.locallyFinsupp ℂ ℤ) (z : ℂ) :
    (∑ i ∈ s, D i) z = ∑ i ∈ s, D i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      ih, Finset.sum_insert hi]

@[simp] theorem defectDivisor_apply {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) (b : Sphere) (z : ℂ) :
    defectDivisor f g b z = if mult f b z ≠ mult g b z then 1 else 0 := by
  rw [defectDivisor, truncatePositiveDivisor_apply]
  change (if 0 < |fiberDivisor f b z - fiberDivisor g b z| then 1 else 0) = _
  rw [fiberDivisor_apply hf, fiberDivisor_apply hg]
  have hcast : ((mult f b z : ℤ) ≠ (mult g b z : ℤ)) ↔ mult f b z ≠ mult g b z := by
    constructor
    · intro h he
      exact h (by rw [he])
    · intro h he
      exact h (by exact_mod_cast he)
  simp only [abs_pos, sub_ne_zero, hcast]

theorem defectDivisor_nonneg (f g : ℂ → ℂ) (b : Sphere) :
    0 ≤ defectDivisor f g b := truncatePositiveDivisor_nonneg _

/-- With IM sharing, unequal multiplicities are positive on both sides. -/
theorem defectDivisor_apply_of_im {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) {b : Sphere}
    (him : SharesIMOn univ f g b) (z : ℂ) :
    defectDivisor f g b z = if IsDefect f g b z then 1 else 0 := by
  rw [defectDivisor_apply hf hg]
  have hequiv : mult f b z ≠ mult g b z ↔ IsDefect f g b z := by
    refine ⟨?_, fun h => h.2.2⟩
    intro hne
    have hposf : 0 < mult f b z := by
      by_contra h
      have hf0 : mult f b z = 0 := by omega
      have hg0 : mult g b z = 0 := by
        by_contra h'
        have := (him z (mem_univ z)).2 (Nat.pos_of_ne_zero h')
        omega
      exact hne (hf0.trans hg0.symm)
    exact ⟨hposf, (him z (mem_univ z)).1 hposf, hne⟩
  simp only [hequiv]

theorem defectCounting_nonneg (f g : ℂ → ℂ) (b : Sphere) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ defectCounting f g b r :=
  Function.locallyFinsuppWithin.logCounting_nonneg (defectDivisor_nonneg f g b) hr

@[simp] theorem totalDefectDivisor_apply (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (z : ℂ) :
    totalDefectDivisor a f g z = ∑ j, defectDivisor f g (a j : Sphere) z := by
  rw [totalDefectDivisor, defectCounting_sum_apply]

theorem totalDefectDivisor_nonneg (a : Fin 3 → ℂ) (f g : ℂ → ℂ) :
    0 ≤ totalDefectDivisor a f g := by
  intro z
  rw [totalDefectDivisor_apply]
  exact Finset.sum_nonneg fun j _ => defectDivisor_nonneg f g (a j : Sphere) z

theorem totalDefectCounting_nonneg (a : Fin 3 → ℂ) (f g : ℂ → ℂ) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ totalDefectCounting a f g r :=
  Finset.sum_nonneg fun j _ => defectCounting_nonneg f g (a j : Sphere) hr

/-- The total count is the logarithmic count of the sum divisor. -/
theorem totalDefectDivisor_logCounting (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (r : ℝ) :
    (totalDefectDivisor a f g).logCounting r = totalDefectCounting a f g r := by
  simp only [totalDefectDivisor, totalDefectCounting, defectCounting,
    map_sum, Finset.sum_apply]

private lemma defectCounting_negPart_le_one {o : WithTop ℤ} (ho : (-1 : WithTop ℤ) ≤ o) :
    o.untop₀⁻ ≤ 1 ∧ (0 < o.untop₀⁻ → o < 0) := by
  induction h : o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [h] at ho
    have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 ho
    simp only [WithTop.untop₀_coe, negPart_def]
    refine ⟨by omega, fun hpos => ?_⟩
    exact_mod_cast (show n < 0 by omega)

/-- Pointwise divisor bound for each Lambda difference. A single copy of the
zero divisor of `Ψ` suffices for all exceptional locations of one `E_a`. -/
theorem negPart_divisor_EAux_le (hp : NormalizedPair univ f g a) (j : Fin 3) :
    (MeromorphicOn.divisor (EAux a j f g) univ)⁻ ≤
      totalDefectDivisor a f g + (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  have hEm : MeromorphicOn (EAux a j f g) univ := fun z _ =>
    meromorphicAt_EAux (hp.nonconst_f.1 z (mem_univ z))
      (hp.nonconst_g.1 z (mem_univ z)) a j
  have hPm : MeromorphicOn (auxPsi a f g) univ := by
    intro z _
    have hfm := hp.nonconst_f.1 z (mem_univ z)
    have hgm := hp.nonconst_g.1 z (mem_univ z)
    unfold auxPsi auxU auxV cubicP
    fun_prop
  intro z
  simp only [Function.locallyFinsuppWithin.negPart_apply,
    Function.locallyFinsuppWithin.posPart_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [MeromorphicOn.divisor_apply hEm (mem_univ z),
    MeromorphicOn.divisor_apply hPm (mem_univ z)]
  have hD0 : (0 : ℤ) ≤ totalDefectDivisor a f g z := totalDefectDivisor_nonneg a f g z
  have hP0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  have hE0 := negPart_nonneg (meromorphicOrderAt (EAux a j f g) z).untop₀
  obtain ⟨hE1, hEneg⟩ := defectCounting_negPart_le_one (EAux_order_on hp j z (mem_univ z)).1
  by_cases hEpos : 0 < (meromorphicOrderAt (EAux a j f g) z).untop₀⁻
  · rcases EAux_pole_support_on hp j z (mem_univ z) (hEneg hEpos) with hdef | hpsi
    · obtain ⟨k, hk⟩ := hdef
      have hk1 : defectDivisor f g (a k : Sphere) z = 1 := by
        rw [defectDivisor_apply hp.nonconst_f.1 hp.nonconst_g.1, if_pos hk.2.2]
      have hD1 : 1 ≤ totalDefectDivisor a f g z := by
        rw [totalDefectDivisor_apply]
        have hsingle := Finset.single_le_sum (f := fun i => defectDivisor f g (a i : Sphere) z)
          (fun i _ => defectDivisor_nonneg f g (a i : Sphere) z) (Finset.mem_univ k)
        change defectDivisor f g (a k : Sphere) z ≤ ∑ i, defectDivisor f g (a i : Sphere) z
          at hsingle
        rwa [hk1] at hsingle
      omega
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
      rw [← hn] at hpsi ⊢
      have hnpos : (0 : ℤ) < n := by exact_mod_cast hpsi
      rw [WithTop.untop₀_coe, posPart_eq_self.2 hnpos.le]
      omega
  · have hEzero : (meromorphicOrderAt (EAux a j f g) z).untop₀⁻ = 0 := by omega
    rw [hEzero]
    exact add_nonneg hD0 hP0

/-- Integrated pole bound `N(r,E_a) ≤ D_total(r) + N(r,1/Ψ)`. -/
theorem logCounting_EAux_top_le (hp : NormalizedPair univ f g a) (j : Fin 3)
    {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.logCounting (EAux a j f g) ⊤ r ≤
      totalDefectCounting a f g r + ValueDistribution.logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_EAux_le hp j) hr
  rw [map_add] at h
  simpa only [Pi.add_apply, totalDefectDivisor_logCounting,
    ← ValueDistribution.logCounting_top, ← ValueDistribution.logCounting_zero] using h

private lemma defectCounting_posPart_ge_one {o : WithTop ℤ} (hfinite : o ≠ ⊤)
    (hpos : 0 < o) : 1 ≤ o.untop₀⁺ := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfinite
  rw [← hn] at hpos ⊢
  have hnpos : (0 : ℤ) < n := WithTop.coe_lt_coe.1 hpos
  simp only [WithTop.untop₀_coe, posPart_def]
  omega

/-- A finite shared fiber is charged to defects, zeros of its selected `E_a`,
or zeros of `Ψ`. The explicit defect witness ensures that `E_a` is not the
zero germ, so its positive divisor really counts its zeros. -/
theorem reducedFiberDivisor_le_defect_EAux (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hdefect : ∃ z₀, IsDefect f g (a j : Sphere) z₀) :
    reducedFiberDivisor f (a j : Sphere) ≤
      defectDivisor f g (a j : Sphere) +
        (MeromorphicOn.divisor (EAux a j f g) univ)⁺ +
          (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  have hEm : MeromorphicOn (EAux a j f g) univ := fun z _ =>
    meromorphicAt_EAux (hp.nonconst_f.1 z (mem_univ z))
      (hp.nonconst_g.1 z (mem_univ z)) a j
  have hPm : MeromorphicOn (auxPsi a f g) univ := by
    intro z _
    have hfm := hp.nonconst_f.1 z (mem_univ z)
    have hgm := hp.nonconst_g.1 z (mem_univ z)
    unfold auxPsi auxU auxV cubicP
    fun_prop
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.posPart_apply]
  rw [reducedFiberDivisor_apply hp.nonconst_f.1,
    MeromorphicOn.divisor_apply hEm (mem_univ z),
    MeromorphicOn.divisor_apply hPm (mem_univ z)]
  have hD0 : (0 : ℤ) ≤ defectDivisor f g (a j : Sphere) z :=
    defectDivisor_nonneg f g (a j : Sphere) z
  have hE0 := posPart_nonneg (meromorphicOrderAt (EAux a j f g) z).untop₀
  have hP0 := posPart_nonneg (meromorphicOrderAt (auxPsi a f g) z).untop₀
  by_cases hpos : 0 < mult f (a j : Sphere) z
  · rw [if_pos hpos]
    have hposg := (hp.im j z (mem_univ z)).1 hpos
    by_cases hcm : mult f (a j : Sphere) z = mult g (a j : Sphere) z
    · by_cases hpsi : 0 < meromorphicOrderAt (auxPsi a f g) z
      · have hP1 := defectCounting_posPart_ge_one (hp.order_aux (mem_univ z)).2.2.2 hpsi
        omega
      · have hpsi0 : meromorphicOrderAt (auxPsi a f g) z = 0 :=
          le_antisymm (not_lt.1 hpsi) (hp.order_aux (mem_univ z)).2.2.1
        have hmone := hp.min_mult_eq_one_of_psi (mem_univ z) hpos hpsi0
        rw [← hcm, min_self] at hmone
        have hnone : mult g (a j : Sphere) z = 1 := by rw [← hcm]; exact hmone
        have hford : meromorphicOrderAt (fun w => f w - a j) z = (1 : ℤ) := by
          simpa only [hmone, Nat.cast_one] using order_sub_eq_mult hpos
        have hgord : meromorphicOrderAt (fun w => g w - a j) z = (1 : ℤ) := by
          simpa only [hnone, Nat.cast_one] using order_sub_eq_mult hposg
        have hEge := EAux_order_ge_one_at_shared_simple (hp.nonconst_f.1 z (mem_univ z))
          (hp.nonconst_g.1 z (mem_univ z)) hp.injective j hford hgord
        have hEfinite := EAux_order_ne_top_of_defect
          (fun w => hp.nonconst_f.1 w (mem_univ w))
          (fun w => hp.nonconst_g.1 w (mem_univ w)) hp.injective j hdefect z
        have hE1 := defectCounting_posPart_ge_one hEfinite
          (lt_of_lt_of_le (by decide : (0 : WithTop ℤ) < 1) hEge)
        omega
    · have hD1 : defectDivisor f g (a j : Sphere) z = 1 := by
        rw [defectDivisor_apply hp.nonconst_f.1 hp.nonconst_g.1, if_pos hcm]
      omega
  · rw [if_neg hpos]
    omega

/-- Integrated reduced-fiber estimate from the local zero properties of `E_a`. -/
theorem reducedCounting_le_defect_EAux (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hdefect : ∃ z₀, IsDefect f g (a j : Sphere) z₀) {r : ℝ} (hr : 1 ≤ r) :
    reducedCounting f (a j : Sphere) r ≤ defectCounting f g (a j : Sphere) r +
      ValueDistribution.logCounting (EAux a j f g) 0 r +
        ValueDistribution.logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (reducedFiberDivisor_le_defect_EAux hp j hdefect) hr
  rw [map_add, map_add] at h
  simpa only [Pi.add_apply, defectCounting, ← ValueDistribution.logCounting_zero,
    ← reducedCounting_eq_reducedFiberDivisor hp.nonconst_f.1 (a j : Sphere)
      (le_trans zero_le_one hr)] using h

/-- Summing the three finite reduced-fiber bounds, with the required
nonvanishing witnesses for all three selected auxiliary functions. -/
theorem sum_reducedCounting_finite_le_defect_EAux (hp : NormalizedPair univ f g a)
    (hdefects : ∀ j, ∃ z₀, IsDefect f g (a j : Sphere) z₀) {r : ℝ} (hr : 1 ≤ r) :
    (∑ j, reducedCounting f (a j : Sphere) r) ≤ totalDefectCounting a f g r +
      (∑ j, ValueDistribution.logCounting (EAux a j f g) 0 r) +
        3 * ValueDistribution.logCounting (auxPsi a f g) 0 r := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    reducedCounting_le_defect_EAux hp j (hdefects j) hr)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, totalDefectCounting] using h

end ThreeIM
