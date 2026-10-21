module

public import RequestProject.ThreeIM.SphereZeroPersistence
public import RequestProject.ThreeIM.SphereLocalOmission

/-!
# Shared spherical fibers persist under nonconstant limits

A limit preimage is approximated by preimages of the members. If the
companion limit had a different value, local omission would contradict
sharing. This applies to infinity as well as finite values.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_limit_shared_fiber_imp {F G : ℕ → ℂ → OnePoint ℂ}
    {f g : ℂ → OnePoint ℂ} {a : OnePoint ℂ}
    (hf : SphereHolomorphicOn f univ) (hg : SphereHolomorphicOn g univ)
    (hfnc : ¬ ∃ p : OnePoint ℂ, ∀ z, f z = p)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (hG : TendstoLocallyUniformlyOn G g atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧
        ∀ w ∈ U, F n w = a → G n w = a) :
    ∀ z, f z = a → g z = a := by
  intro z hfz
  by_contra hgz
  have hgc : ContinuousAt g z := hg.continuousOn.continuousAt (isOpen_univ.mem_nhds (mem_univ z))
  obtain ⟨V, hV, hzV, _, homit⟩ :=
    sphere_limit_local_omission isOpen_univ hG (mem_univ z) hgc hgz
  obtain ⟨U, hU, hzU, hpair⟩ := hloc z
  have hpre := sphere_eventually_exists_preimage hf hfnc
    (fun w => by
      obtain ⟨W, hW, hwW, hev⟩ := hloc w
      exact ⟨W, hW, hwW, hev.mono fun n hn => hn.1⟩)
    hF hfz (hU.inter hV) ⟨hzU, hzV⟩
  have hfalse : ∀ᶠ (n : ℕ) in atTop, False := by
    filter_upwards [hpre, hpair, homit] with n hn hp ho
    obtain ⟨w, hw, hwF⟩ := hn
    exact ho w hw.2 (hp.2 w hw.1 hwF)
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

theorem sphere_limit_shared_fiber_iff {F G : ℕ → ℂ → OnePoint ℂ}
    {f g : ℂ → OnePoint ℂ} {a : OnePoint ℂ}
    (hf : SphereHolomorphicOn f univ) (hg : SphereHolomorphicOn g univ)
    (hfnc : ¬ ∃ p : OnePoint ℂ, ∀ z, f z = p)
    (hgnc : ¬ ∃ p : OnePoint ℂ, ∀ z, g z = p)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (hG : TendstoLocallyUniformlyOn G g atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧ SphereHolomorphicOn (G n) U ∧
        ∀ w ∈ U, (F n w = a ↔ G n w = a)) :
    ∀ z, (f z = a ↔ g z = a) := by
  have hfg := sphere_limit_shared_fiber_imp hf hg hfnc hF hG (fun z => by
    obtain ⟨U, hU, hzU, hp⟩ := hloc z
    exact ⟨U, hU, hzU, hp.mono fun n hn =>
      ⟨hn.1, fun w hw => (hn.2.2 w hw).1⟩⟩)
  have hgf := sphere_limit_shared_fiber_imp hg hf hgnc hG hF (fun z => by
    obtain ⟨U, hU, hzU, hp⟩ := hloc z
    exact ⟨U, hU, hzU, hp.mono fun n hn =>
      ⟨hn.2.1, fun w hw => (hn.2.2 w hw).2⟩⟩)
  exact fun z => ⟨hfg z, hgf z⟩

end ThreeIM
