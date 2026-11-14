import LongTails.Proofs.GeneralizedMirrorStep
import LongTails.Proofs.GeneralizedMirrorTuning

open Set
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorStep
open LongTails.Proofs.GeneralizedMirrorTuning

namespace LongTails.Proofs.GeneralizedMirrorInvariant

lemma query_distance (q : Public) (hq : spec.valid q) {ell A : ℝ}
    (hell : 0 < ell) (hA : 0 < A) (x z u : q.E)
    (hx : ‖x - u‖ ≤ 2 * q.R) (hz : ‖z - u‖ ≤ 2 * q.R) :
    ‖x - mix A (stepWeight q ell A) x z‖ ≤ 4 * q.R * stepWeight q ell A / (A + stepWeight q ell A) := by
  have ha := stepWeight_pos q hq hell hA
  have hn : ‖z - x‖ ≤ 4 * q.R := by
    have h := norm_add_le (z - u) (u - x)
    rw [sub_add_sub_cancel, norm_sub_rev u x] at h
    linarith
  rw [mix_query_distance hA.le ha]
  have h := mul_le_mul_of_nonneg_left hn (show 0 ≤ stepWeight q ell A / (A + stepWeight q ell A) by positivity)
  exact h.trans_eq (by ring)

lemma query_locality (q : Public) (hq : spec.valid q) {ell A : ℝ}
    (hell : 0 < ell) (hA : 0 < A) (x z u : q.E)
    (hx : ‖x - u‖ ≤ 2 * q.R) (hz : ‖z - u‖ ≤ 2 * q.R) :
    q.L1 * ‖x - mix A (stepWeight q ell A) x z‖ ≤ 1 / 256 := by
  have ha := stepWeight_pos q hq hell hA
  have hlin := stepWeight_linear q hq hell hA
  have hd := query_distance q hq hell hA x z u hx hz
  have hden : 0 < A + stepWeight q ell A := by positivity
  have hd' := (le_div_iff₀ hden).mp hd
  have hprod := mul_le_mul_of_nonneg_left hd' hq.2.1
  nlinarith

set_option maxHeartbeats 1000000 in
lemma admissible_energy_step (q : Public) (hq : spec.valid q) (I : Instance q)
    (O : OracleTemplate.Oracle (Query q) (Reply q)) (hI : spec.admissible q I O)
    {ell A : ℝ} (hell : 1 ≤ ell) (hA : 0 < A)
    (x z u : q.E) (hx : x ∈ I.Q ∩ I.U) (hz : z ∈ I.Q ∩ I.U) (hu : u ∈ I.Q)
    (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (henergy : A * (objective I x - objective I u) + divergence I u z ≤ q.R ^ 2)
    (hxradius : ‖x - u‖ ≤ 2 * q.R) (v : Dual q)
    (herr : ‖v - I.df (mix A (stepWeight q ell A) x z)‖ ≤ 3 * clipRadius q / 2) :
    let a := stepWeight q ell A
    let p := I.prox a z v
    let xnew := mix A a x p
    p ∈ I.Q ∩ I.U ∧ xnew ∈ I.Q ∩ I.U ∧
      (A + a) * (objective I xnew - objective I u) + divergence I u p ≤
        A * (objective I x - objective I u) + divergence I u z +
          a * (v - I.df (mix A a x z)) (u - z) + a ^ 2 * ‖v - I.df (mix A a x z)‖ ^ 2 := by
  have hell0 : 0 < ell := by linarith
  have ha := stepWeight_pos q hq hell0 hA
  have hbase := stepWeight_base q hq hell0 hA
  have hlinear := stepWeight_linear q hq hell0 hA
  have herror := stepWeight_error q hq hell hA (v - I.df (mix A (stepWeight q ell A) x z)) herr
  rcases hq with ⟨hL0, hL1, hR, hΔ, hG0, hσ, hα, hα2, hε, hδ, hδ1⟩
  rcases hI with ⟨_, _, _, _, _, hf, hdf, hc, hgl, hQ, _, hψ, _, _, hU, hdh,
    hstrong, _, hprox, _⟩
  let a := stepWeight q ell A
  let y := mix A a x z
  let p := I.prox a z v
  have haq : 0 < a := ha
  have hB : 0 ≤ q.L0 + q.L1 * q.G := by positivity
  have hgap0 : 0 ≤ objective I x - objective I u := sub_nonneg.mpr (hmin hx.1)
  have hD := hstrong z hz u hu
  have hD0 : 0 ≤ divergence I u z := by nlinarith [sq_nonneg ‖u - z‖]
  have hgap : A * (objective I x - objective I u) ≤ q.R ^ 2 := by linarith
  have hDupper : divergence I u z ≤ q.R ^ 2 := by
    nlinarith [mul_nonneg hA.le hgap0]
  have hzr : ‖z - u‖ ≤ 2 * q.R := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (u - z)]
  have hself := GeneralizedMirrorCurvature.composite_self_bound hL0 hL1 hG0 hf hψ hc hdf hgl
    hu hx.1 hmin hG
  have hgrad := GeneralizedMirrorCurvature.weighted_gradient_bound ha.le hB hL1 hgap0 hR
    hself hgap hbase hlinear
  have hcurv := GeneralizedMirrorCurvature.curvature_from_self_bound
    (norm_nonneg (I.df x - I.df u)) hB hL1 hgap0 hself
  have hins := norm_le_insert (I.df u) (I.df x)
  rw [norm_sub_rev (I.df u)] at hins
  have hCx : q.L0 + q.L1 * ‖I.df x‖ ≤
      2 * (q.L0 + q.L1 * q.G) + 64 * q.L1 ^ 2 * (objective I x - objective I u) := by
    have hh := mul_le_mul_of_nonneg_left hins hL1
    have hg := mul_le_mul_of_nonneg_left hG hL1
    nlinarith
  have hweighted := GeneralizedMirrorCurvature.weighted_curvature_bound hA ha.le hL1 hgap0 hR
    hCx hgap hbase hlinear
  have hvalid : spec.valid q := ⟨hL0, hL1, hR, hΔ, hG0, hσ, hα, hα2, hε, hδ, hδ1⟩
  have hdistance := query_distance q hvalid hell0 hA x z u hxradius hzr
  have hlocal := query_locality q hvalid hell0 hA x z u hxradius hzr
  have hdir := localized_direction_bound hL0.le hL1 hA.le ha hR.le hc hgl x y u v
    hdistance (by linarith) (by dsimp [a] at *; linarith) hgrad herror
  obtain ⟨hp, hpm⟩ := hprox a haq z hz v
  have hDpz := hstrong z hz p hp.1
  have hDup := hstrong p hp u hu
  have hpr := GeneralizedMirrorGeometry.prox_localization I haq (show 0 < 2 * q.R by positivity)
    hψ hp.1 hu (hdh p hp.2) hpm (hdf u) hmin
    (by nlinarith [sq_nonneg ‖p - z‖]) hDup (by nlinarith) (by dsimp [a] at *; linarith)
  have hpz : ‖p - z‖ ≤ 5 * q.R := by
    have hh := norm_add_le (p - u) (u - z)
    rw [sub_add_sub_cancel, norm_sub_rev p u, norm_sub_rev u z] at hh
    linarith
  have hden : 0 < A + a := by positivity
  have hnewlocal : q.L1 * ‖mix A a x z - mix A a x p‖ ≤ 1 / 2 := by
    rw [norm_sub_rev, mix_displacement, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg haq.le hden.le)]
    have hh := mul_le_mul_of_nonneg_left hpz (div_nonneg haq.le hden.le)
    have hh' := mul_le_mul_of_nonneg_left hh hL1
    apply (mul_le_mul_iff_left₀ hden).mp
    have he : q.L1 * (a / (A + a) * (5 * q.R)) * (A + a) = 5 * q.L1 * q.R * a := by
      field_simp
    have ht := mul_le_mul_of_nonneg_right hh' hden.le
    rw [he] at ht
    dsimp [a] at *
    nlinarith
  have hCy := GeneralizedMirrorCurvature.local_curvature hL0.le hL1 hc hgl x y (by linarith)
  have hstep : 8 * (q.L0 + q.L1 * ‖I.df y‖) * a ^ 2 ≤ A + a := by
    have hh := mul_le_mul_of_nonneg_right hCy (sq_nonneg a)
    dsimp [a] at *
    nlinarith
  refine ⟨hp, ⟨mix_mem hQ hA.le haq hx.1 hp.1, mix_mem hU hA.le haq hx.2 hp.2⟩, ?_⟩
  exact energy_step I hA.le haq hL0.le hL1 (hf.subset (subset_univ _) hQ) hψ hdf hc hgl
    x z p u hx.1 hz.1 hp.1 hu v (hdh p hp.2) hpm hDpz hnewlocal hstep

end LongTails.Proofs.GeneralizedMirrorInvariant
