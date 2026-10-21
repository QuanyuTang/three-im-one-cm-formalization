module

public import RequestProject.ThreeIM.CMPersistence
public import RequestProject.ThreeIM.SphereLimits
public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-! # CM persistence in finite spherical charts -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_chart_orders_eq_of_spherical_cm {F G : ℕ → ℂ → OnePoint ℂ}
    {f g : ℂ → OnePoint ℂ} (hf : SphereHolomorphicOn f univ)
    (hg : SphereHolomorphicOn g univ)
    (hfnc : ¬ ∃ p : OnePoint ℂ, ∀ w, f w = p)
    (hgnc : ¬ ∃ p : OnePoint ℂ, ∀ w, g w = p)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (hG : TendstoLocallyUniformlyOn G g atTop univ)
    {z : ℂ} (hfz : f z ≠ OnePoint.infty) (hgz : g z ≠ OnePoint.infty)
    (hloc : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧ SphereHolomorphicOn (G n) U ∧
        (∀ w ∈ U, mult (fun x => chartFiniteMap (F n x)) ((0 : ℂ) : Sphere) w =
          mult (fun x => chartFiniteMap (G n x)) ((0 : ℂ) : Sphere) w) ∧
        ∀ w ∈ U, meromorphicOrderAt (fun x => chartFiniteMap (F n x)) w ≠ ⊤ ∧
          meromorphicOrderAt (fun x => chartFiniteMap (G n x)) w ≠ ⊤) :
    meromorphicOrderAt (fun w => chartFiniteMap (f w)) z =
      meromorphicOrderAt (fun w => chartFiniteMap (g w)) z := by
  obtain ⟨U, hU, hzU, hseq⟩ := hloc
  obtain ⟨rf, hrf, hrfU, _, _, hfd, hfc⟩ := exists_finite_chart_convergence_eventually
    hU (hseq.mono fun n hn => hn.1) (hF.mono (subset_univ U)) hzU hfz
  obtain ⟨rg, hrg, _, _, _, hgd, hgc⟩ := exists_finite_chart_convergence_eventually
    hU (hseq.mono fun n hn => hn.2.1) (hG.mono (subset_univ U)) hzU hgz
  let R : ℝ := min rf rg
  have hR : 0 < R := lt_min hrf hrg
  have hRf : ball z R ⊆ closedBall z rf :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_left _ _))
  have hRg : ball z R ⊆ closedBall z rg :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))
  have hRU : ball z R ⊆ U := hRf.trans hrfU
  have hdata : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z R) ∧
      DifferentiableOn ℂ (fun w => chartFiniteMap (G n w)) (ball z R) ∧
      (∀ w ∈ ball z R, mult (fun x => chartFiniteMap (F n x)) ((0 : ℂ) : Sphere) w =
        mult (fun x => chartFiniteMap (G n x)) ((0 : ℂ) : Sphere) w) ∧
      ∀ w ∈ ball z R, meromorphicOrderAt (fun x => chartFiniteMap (F n x)) w ≠ ⊤ ∧
        meromorphicOrderAt (fun x => chartFiniteMap (G n x)) w ≠ ⊤ := by
    filter_upwards [hseq, hfd, hgd] with n hn hnf hng
    exact ⟨hnf.mono (ball_subset_ball (min_le_left _ _)),
      hng.mono (ball_subset_ball (min_le_right _ _)),
      fun w hw => hn.2.2.1 w (hRU hw), fun w hw => hn.2.2.2 w (hRU hw)⟩
  exact orders_eq_of_locally_uniform_zero_mult hR hdata
    (hfc.tendstoLocallyUniformlyOn.mono hRf) (hgc.tendstoLocallyUniformlyOn.mono hRg)
    (analyticAt_chartFiniteMap_of_ne_infty hf (mem_univ z) hfz)
    (analyticAt_chartFiniteMap_of_ne_infty hg (mem_univ z) hgz)
    (by simpa only [sub_zero] using (isNonconstMeroOn_chartFiniteMap hf hfnc).2 z (mem_univ z) 0)
    (by simpa only [sub_zero] using (isNonconstMeroOn_chartFiniteMap hg hgnc).2 z (mem_univ z) 0)

end ThreeIM
