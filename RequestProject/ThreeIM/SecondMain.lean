module

public import RequestProject.ThreeIM.SecondMainFinite

/-!
# Nevanlinna's second main theorem for distinct spherical targets

If infinity is a target, remove its unique index before applying the finite
target inequality. If it is not, bound the additional reduced pole count by
the characteristic. Both cases give the coefficient `q - 2`.
-/

@[expose] public section

open Set

namespace ThreeIM

theorem second_main_theorem {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ) {q : ℕ}
    (hq : 3 ≤ q) (b : Fin q → Sphere) (hb : Function.Injective b) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ((q : ℝ) - 2) * charT f r ≤ ∑ i, reducedCounting f (b i) r +
        C * Real.log (Real.exp 1 + r * charT f r) := by
  classical
  by_cases htop : ∃ k, b k = ⊤
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    obtain ⟨k, hk⟩ := htop
    have hfinite : ∀ i : Fin n, ∃ c : ℂ, (c : Sphere) = b (k.succAbove i) := by
      intro i
      apply WithTop.ne_top_iff_exists.1
      intro hi
      exact Fin.succAbove_ne k i (hb (hi.trans hk.symm))
    choose a ha using hfinite
    have hainj : Function.Injective a := by
      intro i j hij
      apply Fin.succAbove_right_injective (p := k)
      apply hb
      rw [← ha i, ← ha j, hij]
    obtain ⟨C, hC⟩ := second_main_finite hf a hainj
    refine ⟨C, hC.map ?_⟩
    intro r hr
    rw [Fin.sum_univ_succAbove (fun i => reducedCounting f (b i) r) k, hk]
    have hsum : (∑ i, reducedCounting f (a i) r) =
        ∑ i : Fin n, reducedCounting f (b (k.succAbove i)) r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ha i]
    rw [hsum] at hr
    push_cast
    linarith
  · push_neg at htop
    have hfinite : ∀ i, ∃ c : ℂ, (c : Sphere) = b i :=
      fun i => WithTop.ne_top_iff_exists.1 (htop i)
    choose a ha using hfinite
    have hainj : Function.Injective a := by
      intro i j hij
      apply hb
      rw [← ha i, ← ha j, hij]
    obtain ⟨C, hC⟩ := second_main_finite hf a hainj
    refine ⟨C, (hC.conj (OutsideFiniteMeasure.eventually_ge 1)).map ?_⟩
    intro r h
    obtain ⟨hfinite, hr⟩ := h
    have hpole := reducedCounting_top_le_charT hf.1 hr
    have hsum : (∑ i, reducedCounting f (a i) r) =
        ∑ i, reducedCounting f (b i) r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ha i]
    rw [hsum] at hfinite
    linarith

end ThreeIM
