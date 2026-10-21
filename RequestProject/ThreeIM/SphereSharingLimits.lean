module

public import RequestProject.ThreeIM.SphereHurwitz
public import RequestProject.ThreeIM.SpherePicard

/-!
# A constant companion forces omitted values

If one member of a sharing pair converges spherically to a constant p,
the nonconstant entire limit of the other must omit each shared target
different from p. Three such targets contradict little Picard.
-/

@[expose] public section

open Filter Set Metric Topology Matrix NoWanderingDomains

namespace ThreeIM

theorem sphere_const_limit_local_omission {F : ℕ → ℂ → OnePoint ℂ}
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {p a : OnePoint ℂ}
    (hconv : TendstoLocallyUniformlyOn F (fun _ => p) atTop U) (hpa : p ≠ a) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∀ᶠ n in atTop, ∀ w ∈ V, F n w ≠ a := by
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hconv
    (dist p a) (dist_pos.mpr hpa) z hz
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hz)] at ht
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz) ht)
  refine ⟨V, hVo, hzV, fun _ hw => (hVsub hw).1, ?_⟩
  filter_upwards [hev] with n hn w hw heq
  have hd := hn w (hVsub hw).2
  rw [heq] at hd
  exact lt_irrefl (dist p a) hd

theorem sphere_nonconstant_limit_omits_shared_target {F G : ℕ → ℂ → OnePoint ℂ}
    {f : ℂ → OnePoint ℂ} {p a : OnePoint ℂ} (A : GL (Fin 2) ℂ)
    (hAa : A • a = ((0 : ℂ) : OnePoint ℂ)) (hpa : p ≠ a)
    (hf : SphereHolomorphicOn f univ) (hnc : ¬ ∃ q : OnePoint ℂ, ∀ z, f z = q)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (hG : TendstoLocallyUniformlyOn G (fun _ => p) atTop univ)
    (hpair : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧
        ∀ w ∈ U, (F n w = a ↔ G n w = a)) : ∀ z, f z ≠ a := by
  apply sphere_limit_omits_of_mobius_zero A hAa hf hnc
  · intro z
    obtain ⟨U, hU, hzU, hp⟩ := hpair z
    obtain ⟨V, hV, hzV, _, hv⟩ :=
      sphere_const_limit_local_omission isOpen_univ (mem_univ z) hG hpa
    refine ⟨U ∩ V, hU.inter hV, ⟨hzU, hzV⟩, ?_⟩
    filter_upwards [hp, hv] with n hn hnv
    refine ⟨sphereHolomorphicOn_mono hn.1 (hU.inter hV) inter_subset_left, ?_⟩
    intro w hw hwa
    exact hnv w hw.2 ((hn.2 w hw.1).1 hwa)
  · exact hF

theorem sphere_constant_companion_impossible {F G : ℕ → ℂ → OnePoint ℂ}
    {f : ℂ → OnePoint ℂ} {p : OnePoint ℂ}
    (hf : SphereHolomorphicOn f univ) (hnc : ¬ ∃ q : OnePoint ℂ, ∀ z, f z = q)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (hG : TendstoLocallyUniformlyOn G (fun _ => p) atTop univ)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hpair : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧
        ∀ w ∈ U, (F n w = a ↔ G n w = a) ∧
          (F n w = b ↔ G n w = b) ∧ (F n w = c ↔ G n w = c)) : False := by
  obtain ⟨A, hAa, _, _⟩ := exists_gl_smul_eq_zero_one_infty hab hac hbc
  obtain ⟨B, hBb, _, _⟩ := exists_gl_smul_eq_zero_one_infty hab.symm hbc hac
  obtain ⟨C, hCc, _, _⟩ := exists_gl_smul_eq_zero_one_infty hac.symm hbc.symm hab
  have ha : ∀ z, f z ≠ a := sphere_nonconstant_limit_omits_shared_target A hAa hpa hf hnc hF hG
    (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hpair z
      exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.1, fun w hw => (hn.2 w hw).1⟩⟩)
  have hb : ∀ z, f z ≠ b := sphere_nonconstant_limit_omits_shared_target B hBb hpb hf hnc hF hG
    (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hpair z
      exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.1, fun w hw => (hn.2 w hw).2.1⟩⟩)
  have hc : ∀ z, f z ≠ c := sphere_nonconstant_limit_omits_shared_target C hCc hpc hf hnc hF hG
    (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hpair z
      exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.1, fun w hw => (hn.2 w hw).2.2⟩⟩)
  exact hnc (sphere_picard_constant hf a b c hab hac hbc ha hb hc)

end ThreeIM
