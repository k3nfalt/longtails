import LongTails.Proofs.FeasibleGapModel
import LongTails.Proofs.FeasibleGapTuning

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FeasibleGapPhase

open LongTails.Setups.FeasibleHessianGapComposite
open OracleTemplate.FeasibleGapAccelerated
open LongTails.Proofs.CompositeGapGeometry FeasibleGapModel

variable {p : Params} {I : Instance p} {s center : p.E} {Δ : ℝ}

structure Invariant (p : Params) (I : Instance p) (s center : p.E) (Δ : ℝ)
    (q : State p.E) : Prop where
  positive : 0 < q.A
  capped : q.A ≤ target p Δ
  feasible_x : q.x ∈ I.Q
  feasible_z : q.z ∈ I.Q
  radius_x : ‖q.x - s‖ ≤ p.R
  gradient_sum : ‖q.v - q.A • I.grad s‖ ≤ q.A * (gradientCap p Δ)
  certificate : ∃ c : ℝ,
    IsMinOn (model (regularizerShift I s) center q.A (q.v - q.A • I.grad s) c) I.Q q.z ∧
    q.A * (objective I q.x - objective I s) ≤
      model (regularizerShift I s) center q.A (q.v - q.A • I.grad s) c q.z ∧
    ∀ u ∈ I.Q, model (regularizerShift I s) center q.A (q.v - q.A • I.grad s) c u ≤
      ‖u - center‖ ^ 2 / 2 + q.A * (objective I u - objective I s)

lemma invariant_energy (h : Conditions p I s) {q : State p.E}
    (hq : Invariant p I s center Δ q) {u : p.E} (hu : u ∈ I.Q) :
    q.A * (objective I q.x - objective I u) + ‖q.z - u‖ ^ 2 / 2 ≤
      ‖u - center‖ ^ 2 / 2 := by
  obtain ⟨c, hm, hl, hupp⟩ := hq.certificate
  exact model_energy h hq.positive.le hq.feasible_z hu hm hl (hupp u hu)

lemma invariant_gap (h : Conditions p I s) {q : State p.E}
    (hq : Invariant p I s center Δ q) (hc : center ∈ I.Q)
    (hgap : objective I center - objective I s ≤ Δ) :
    objective I q.x - objective I s ≤ Δ := by
  have he := invariant_energy h hq hc
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at he
  have hh : objective I q.x ≤ objective I center := by
    nlinarith [sq_nonneg ‖q.z - center‖, hq.positive]
  linarith

lemma invariant_radius (h : Conditions p I s) {q : State p.E}
    (hq : Invariant p I s center Δ q) (hR : 0 ≤ p.R) (hc : ‖center - s‖ ≤ p.R) :
    ‖q.z - s‖ ≤ p.R := by
  have he := invariant_energy h hq h.minimizer_feasible
  have hg := h.minimizer hq.feasible_x
  have hn := mul_nonneg hq.positive.le (sub_nonneg.mpr hg)
  rw [norm_sub_rev s center] at he
  have hs := (sq_le_sq₀ (norm_nonneg _) hR).mpr hc
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  nlinarith only [he, hn, hs]

lemma invariant_regularizer (h : Conditions p I s) {q : State p.E}
    (hq : Invariant p I s center Δ q) (hR : 0 ≤ p.R) (hc : center ∈ I.Q)
    (hr : ‖center - s‖ ≤ p.R) (hgap : objective I center - objective I s ≤ Δ)
    (hG : 0 ≤ gradientCap p Δ) :
    regularizerShift I s q.z ≤ Δ + 2 * p.R * gradientCap p Δ := by
  obtain ⟨c, hm, _, _⟩ := hq.certificate
  have hz := invariant_radius h hq hR hr
  have hd : ‖q.z - center‖ ≤ 2 * p.R := by
    have hh := norm_sub_le_norm_sub_add_norm_sub q.z s center
    rw [norm_sub_rev s center] at hh
    linarith
  have hj := (regularizerShift_le_gap h hc).trans hgap
  have hh := LongTails.Proofs.CompositeGapGeometry.nonsmooth_bound hq.positive
    hG hc hm hj hq.gradient_sum hd
  nlinarith only [hh]

lemma phase_gradient_cap (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hΔ : p.ε ≤ Δ)
    {x : p.E} (hx : x ∈ I.Q) (hr : ‖x - s‖ ≤ p.R)
    (hgap : objective I x - objective I s ≤ 4 * Δ) :
    ‖I.grad x - I.grad s‖ ≤ gradientCap p Δ := by
  have hd : 0 < Δ := hε.trans_le hΔ
  have hM := FeasibleGapTuning.curvature_pos p h0 h1 hR hd
  have hU := FeasibleGapTuning.globalScale_ge_one p h0 h1 hε
  have hscale := FeasibleGapTuning.scale_le_global p h0 hR hε hΔ
  have hs : curvature p Δ * p.R ^ 2 ≤ globalScale p * Δ := by
    exact (div_le_iff₀ hd).mp hscale
  apply FeasibleGapTuning.logarithmic_gradient_bound hU hM hd hR.le hs
  intro K
  have hc : p.H0 + p.H1 * (4 * Δ) ≤ 4 * curvature p Δ := by
    dsimp [curvature]
    have hn : 0 ≤ Δ / p.R ^ 2 := by positivity
    nlinarith
  have hh := sublevel_gradient_bound h h1 (show 0 ≤ 4 * Δ by positivity)
    (show 0 < 4 * curvature p Δ by positivity) hc hx hgap hr K
  have he : Real.sqrt ((4 * curvature p Δ) * (4 * Δ)) =
      4 * Real.sqrt (curvature p Δ * Δ) := by
    rw [show (4 * curvature p Δ) * (4 * Δ) = 16 * (curvature p Δ * Δ) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  rw [he] at hh
  nlinarith only [hh]

lemma initial_invariant (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) :
    let a := 1 / (131072 * logarithm p ^ 2 * curvature p Δ)
    let z := I.prox a center (I.grad center)
    Invariant p I s center Δ ⟨a, z, z, a • I.grad center⟩ := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  have hL := FeasibleGapTuning.logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  let G := gradientCap p Δ
  let M := curvature p Δ
  let a := 1 / (131072 * logarithm p ^ 2 * M)
  let g := I.grad center - I.grad s
  let z := I.prox a center (I.grad center)
  let c := a * smoothShift I s center
  have hM : 0 < M := FeasibleGapTuning.curvature_pos p h0 h1 hR hΔ
  have ha : 0 < a := by dsimp [a]; positivity
  have hgc : (1 / a) • (a • I.grad center) = I.grad center := by
    rw [smul_smul, one_div_mul_cancel ha.ne', one_smul]
  have hp := prox_is_model_min h ha center (a • I.grad center) c
  rw [hgc] at hp
  have hv : a • I.grad center - a • I.grad s = a • g := by dsimp [g]; module
  have hmin : IsMinOn (model (regularizerShift I s) center a (a • g) c) I.Q z := by
    have hh := shifted_model_min (s := s) hp.2
    rw [hv] at hh
    exact hh
  have hcurv : p.H0 + p.H1 * Δ ≤ M := by
    dsimp [M, curvature]
    have hh : 0 ≤ Δ / p.R ^ 2 := by positivity
    linarith
  have hG : 0 < G := by dsimp [G, gradientCap]; positivity
  have hgs := phase_gradient_cap h h0 h1 hR hε hεΔ hc hr (by linarith)
  have hGsq : G ^ 2 = 1024 * logarithm p ^ 2 * M * Δ := by
    dsimp [G, gradientCap, M]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hscale : 128 * a * G ^ 2 = Δ := by
    rw [hGsq]
    dsimp [a]
    field_simp
    ring
  have hGM : M * Δ ≤ G ^ 2 := by
    have hh : 1 ≤ 1024 * logarithm p ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ M * Δ by positivity)]
  have hlower : a * (objective I z - objective I s) ≤
      model (regularizerShift I s) center a (a • g) c z := by
    exact FeasibleGapModel.initial_model_lower h h0 h1 hc hp.1 hΔ hG ha
      hscale hGM hcurv hgap hgs hmin
  have hupper (u : p.E) (hu : u ∈ I.Q) : model (regularizerShift I s) center a (a • g) c u ≤
      ‖u - center‖ ^ 2 / 2 + a * (objective I u - objective I s) := by
    have hh := mul_le_mul_of_nonneg_left (shifted_support h hu hc) ha.le
    rw [← shift_sum]
    dsimp [model, c]
    rw [real_inner_smul_left]
    nlinarith only [hh]
  have he := model_energy h ha.le hp.1 h.minimizer_feasible hmin hlower (hupper s h.minimizer_feasible)
  have hzrad : ‖z - s‖ ≤ p.R := by
    have hg := mul_nonneg ha.le (sub_nonneg.mpr (h.minimizer hp.1))
    rw [norm_sub_rev s center] at he
    have hs := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hr
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    nlinarith only [he, hg, hs]
  have hacap : a ≤ target p Δ := by
    have hh := FeasibleGapTuning.scale_ge_one p h0 h1 hR hΔ
    have hMd : Δ ≤ M * p.R ^ 2 := by
      simpa only [one_mul] using (le_div_iff₀ hΔ).mp hh
    have ham : a * M ≤ 1 / 128 := by
      have ht := mul_le_mul_of_nonneg_left hGM (show 0 ≤ 128 * a by positivity)
      nlinarith
    have ht := mul_le_mul_of_nonneg_left hMd ha.le
    have ht' := mul_le_mul_of_nonneg_right ham (sq_nonneg p.R)
    apply (le_div_iff₀ hΔ).mpr
    nlinarith only [ht, ht', sq_nonneg p.R]
  have hgcap := phase_gradient_cap h h0 h1 hR hε hεΔ hc hr (by linarith)
  refine ⟨ha, hacap, hp.1, hp.1, hzrad, ?_, ?_⟩
  · change ‖a • I.grad center - a • I.grad s‖ ≤ a * (gradientCap p Δ)
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hgcap ha.le
  · refine ⟨c, ?_, ?_, ?_⟩
    · simpa only [← hv] using hmin
    · simpa only [← hv] using hlower
    · intro u hu
      simpa only [← hv] using hupper u hu


end LongTails.Proofs.FeasibleGapPhase
