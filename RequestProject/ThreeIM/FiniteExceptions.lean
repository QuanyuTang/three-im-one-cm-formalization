module

public import RequestProject.ThreeIM.Counting

/-!
# Finite combinations of exceptional sets

The second main theorem uses finitely many logarithmic-derivative estimates.
A finite union of their measurable exceptional sets still has finite linear
measure, and a maximum of their starting radii works for every estimate.
-/

@[expose] public section

open Set MeasureTheory

namespace ThreeIM

theorem OutsideFiniteMeasure.of_forall {P : ℝ → Prop} (h : ∀ r, P r) :
    OutsideFiniteMeasure P := by
  refine ⟨∅, MeasurableSet.empty, by simp, 0, ?_⟩
  intro r _ _
  exact h r

theorem OutsideFiniteMeasure.map {P Q : ℝ → Prop}
    (hP : OutsideFiniteMeasure P) (hPQ : ∀ r, P r → Q r) :
    OutsideFiniteMeasure Q := by
  obtain ⟨E, hEm, hEv, r₀, hP⟩ := hP
  exact ⟨E, hEm, hEv, r₀, fun r hr hrE => hPQ r (hP r hr hrE)⟩

theorem OutsideFiniteMeasure.conj {P Q : ℝ → Prop}
    (hP : OutsideFiniteMeasure P) (hQ : OutsideFiniteMeasure Q) :
    OutsideFiniteMeasure (fun r => P r ∧ Q r) := by
  obtain ⟨E, hEm, hEv, r₀, hP⟩ := hP
  obtain ⟨F, hFm, hFv, r₁, hQ⟩ := hQ
  refine ⟨E ∪ F, hEm.union hFm,
    (measure_union_le E F).trans_lt (ENNReal.add_lt_top.2 ⟨hEv, hFv⟩),
    max r₀ r₁, ?_⟩
  intro r hr hrEF
  have hnot := not_or.1 hrEF
  exact ⟨hP r (le_of_max_le_left hr) hnot.1,
    hQ r (le_of_max_le_right hr) hnot.2⟩

theorem OutsideFiniteMeasure.eventually_ge (r₀ : ℝ) :
    OutsideFiniteMeasure (fun r => r₀ ≤ r) :=
  ⟨∅, MeasurableSet.empty, by simp, r₀, fun _ hr _ => hr⟩

theorem OutsideFiniteMeasure.finset_all {ι : Type*} (s : Finset ι)
    {P : ι → ℝ → Prop} (h : ∀ i ∈ s, OutsideFiniteMeasure (P i)) :
    OutsideFiniteMeasure (fun r => ∀ i ∈ s, P i r) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact .of_forall (by simp)
  | @insert i s hi ih =>
    have hiP := h i (Finset.mem_insert_self _ _)
    have hsP := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact (hiP.conj hsP).map (by simp only [Finset.mem_insert, forall_eq_or_imp]; tauto)

theorem OutsideFiniteMeasure.fintype_all {ι : Type*} [Fintype ι]
    {P : ι → ℝ → Prop} (h : ∀ i, OutsideFiniteMeasure (P i)) :
    OutsideFiniteMeasure (fun r => ∀ i, P i r) := by
  simpa only [Finset.mem_univ, forall_true_left] using
    OutsideFiniteMeasure.finset_all Finset.univ (fun i _ => h i)

end ThreeIM
