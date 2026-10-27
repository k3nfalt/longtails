import LongTails.Proofs.CompositeGapModel
import LongTails.Proofs.CompositeGapTuning

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapPhase

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapAccelerated
open CompositeGapGeometry CompositeGapModel

variable {p : Params} {I : Instance p} {s center : p.E} {Δ : ℝ}

structure Invariant (p : Params) (I : Instance p) (s center : p.E) (Δ : ℝ)
    (q : State p.E) : Prop where
  positive : 0 < q.A
  capped : q.A ≤ target p Δ
  feasible_x : q.x ∈ I.Q
  feasible_z : q.z ∈ I.Q
  radius_x : ‖q.x - s‖ ≤ p.R
  gradient_sum : ‖q.v - q.A • I.grad s‖ ≤ q.A * (8 * Real.sqrt (curvature p Δ * Δ))
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
    (hr : ‖center - s‖ ≤ p.R) (hgap : objective I center - objective I s ≤ Δ) :
    regularizerShift I s q.z ≤ Δ + 16 * p.R * Real.sqrt (curvature p Δ * Δ) := by
  obtain ⟨c, hm, _, _⟩ := hq.certificate
  have hz := invariant_radius h hq hR hr
  have hd : ‖q.z - center‖ ≤ 2 * p.R := by
    have hh := norm_sub_le_norm_sub_add_norm_sub q.z s center
    rw [norm_sub_rev s center] at hh
    linarith
  have hj := (regularizerShift_le_gap h center).trans hgap
  have hh := nonsmooth_bound hq.positive
    (show 0 ≤ 8 * Real.sqrt (curvature p Δ * Δ) by positivity) hc hm hj hq.gradient_sum hd
  nlinarith only [hh]

lemma phase_gradient_cap (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) {x : p.E} (hx : x ∈ I.Q)
    (hgap : objective I x - objective I s ≤ 2 * Δ) :
    ‖I.grad x - I.grad s‖ ≤ 8 * Real.sqrt (curvature p Δ * Δ) := by
  have hM := CompositeGapTuning.curvature_pos p h0 h1 hR hΔ
  have hc : p.H0 + p.H1 * (2 * Δ) ≤ 2 * curvature p Δ := by
    unfold curvature
    have hh : 0 ≤ Δ / p.R ^ 2 := by positivity
    nlinarith
  have hg := shifted_gradient_sq h h0 h1 hx (show 0 < 2 * Δ by positivity) hgap hc
  have hs := Real.sq_sqrt (show 0 ≤ curvature p Δ * Δ by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hg, hs]

lemma query_localization (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) {x z : p.E} (hx : x ∈ I.Q) (hz : z ∈ I.Q)
    (hrx : ‖x - s‖ ≤ p.R) (hrz : ‖z - s‖ ≤ p.R)
    (hgap : objective I x - objective I s ≤ Δ)
    (hjz : regularizerShift I s z ≤ Δ + 16 * p.R * Real.sqrt (curvature p Δ * Δ))
    {τ : ℝ} (hτ : 0 ≤ τ) (hτθ : τ ≤ fraction p Δ) :
    let y := (1 - τ) • x + τ • z
    y ∈ I.Q ∧ objective I y - objective I s ≤ 2 * Δ := by
  let y := (1 - τ) • x + τ • z
  have hτ1 : τ ≤ 1 / 128 := hτθ.trans (CompositeGapTuning.fraction_le p Δ)
  have hy : y ∈ I.Q := h.convex_domain hx hz (by linarith) hτ (by ring)
  refine ⟨hy, ?_⟩
  have hM := CompositeGapTuning.curvature_pos p h0 h1 hR hΔ
  have hg := phase_gradient_cap h h0 h1 hR hΔ hx (by linarith)
  have hdist : ‖y - x‖ ≤ 2 * p.R * τ := by
    have he : y - x = τ • (z - x) := by dsimp [y]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    have hh := norm_sub_le_norm_sub_add_norm_sub z s x
    rw [norm_sub_rev s x] at hh
    nlinarith [mul_le_mul_of_nonneg_left (show ‖z - x‖ ≤ 2 * p.R by linarith) hτ]
  have hr : Real.sqrt p.H1 * ‖y - x‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg p.H1)
    have ht := mul_le_mul_of_nonneg_right hτθ (show 0 ≤ Real.sqrt p.H1 * p.R by positivity)
    have hf := CompositeGapTuning.fraction_radius p h0 h1 hR hΔ
    nlinarith only [hh, ht, hf]
  have hc : p.H0 + p.H1 * (objective I x - objective I s) ≤ curvature p Δ := by
    unfold curvature
    have hh : 0 ≤ Δ / p.R ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hgap h1]
  have hquad : curvature p Δ * p.R ^ 2 * τ ^ 2 ≤ Δ / 16384 := by
    have hs := (sq_le_sq₀ hτ (CompositeGapTuning.fraction_pos p Δ).le).mpr hτθ
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ curvature p Δ * p.R ^ 2 by positivity)
    exact hh.trans (CompositeGapTuning.fraction_quadratic p h0 h1 hR hΔ)
  have hlinear : τ * p.R * (8 * Real.sqrt (curvature p Δ * Δ)) ≤ Δ / 16 := by
    have hh := mul_le_mul_of_nonneg_right hτθ
      (show 0 ≤ p.R * Real.sqrt (curvature p Δ * Δ) by positivity)
    have ht := CompositeGapTuning.fraction_geometry p h0 h1 hR hΔ
    nlinarith only [hh, ht]
  have hquery : smoothShift I s y ≤ smoothShift I s x +
      2 * p.R * τ * (8 * Real.sqrt (curvature p Δ * Δ)) +
      4 * curvature p Δ * p.R ^ 2 * τ ^ 2 := by
    have hh := shifted_upper h hx hr
    have hi := (real_inner_le_norm (I.grad x - I.grad s) (y - x)).trans
      (mul_le_mul hg hdist (norm_nonneg _) (by positivity))
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hdist
    have hm := mul_le_mul_of_nonneg_left hs hM.le
    have hm' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖y - x‖)
    nlinarith only [hh, hi, hm, hm']
  have hj := (shifted_regularizer_convex h).2 hx hz (show 0 ≤ 1 - τ by linarith) hτ
    (show 1 - τ + τ = 1 by ring)
  simp only [smul_eq_mul] at hj
  rw [← shift_sum]
  apply localized_query_gap hτ hτ1 hΔ (by rw [shift_sum]; exact hgap)
    (by nlinarith only [hjz]) (regularizerShift_nonneg h hx) hquery hj hlinear hquad

lemma initial_invariant (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) :
    let a := 1 / (16 * curvature p Δ)
    let z := I.prox a center (I.grad center)
    Invariant p I s center Δ ⟨a, z, z, a • I.grad center⟩ := by
  let M := curvature p Δ
  let a := 1 / (16 * M)
  let g := I.grad center - I.grad s
  let z := I.prox a center (I.grad center)
  let c := a * smoothShift I s center
  have hM : 0 < M := CompositeGapTuning.curvature_pos p h0 h1 hR hΔ
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
  have hgs : ‖g‖ ^ 2 ≤ 16 * M * Δ := shifted_gradient_sq h h0 h1 hc hΔ hgap hcurv
  have hlocal : ∀ y, Real.sqrt p.H1 * ‖y - center‖ ≤ 1 →
      smoothShift I s y ≤ smoothShift I s center + ⟪g, y - center⟫ + M * ‖y - center‖ ^ 2 := by
    intro y hy
    have hh := shifted_upper h hc hy
    have ht : p.H0 + p.H1 * (objective I center - objective I s) ≤ M := by
      nlinarith [mul_le_mul_of_nonneg_left hgap h1]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg ‖y - center‖)])
  have hlower : a * (objective I z - objective I s) ≤
      model (regularizerShift I s) center a (a • g) c z := by
    rw [← shift_sum]
    exact initial_model_lower hM h1 hΔ (by linarith) hc
      (regularizerShift_nonneg h hp.1) ((regularizerShift_le_gap h center).trans hgap)
      hgs hmin (hlocal z)
  have hupper (u : p.E) : model (regularizerShift I s) center a (a • g) c u ≤
      ‖u - center‖ ^ 2 / 2 + a * (objective I u - objective I s) := by
    have hh := mul_le_mul_of_nonneg_left (shifted_support h u center) ha.le
    rw [← shift_sum]
    dsimp [model, c]
    rw [real_inner_smul_left]
    nlinarith only [hh]
  have he := model_energy h ha.le hp.1 h.minimizer_feasible hmin hlower (hupper s)
  have hzrad : ‖z - s‖ ≤ p.R := by
    have hg := mul_nonneg ha.le (sub_nonneg.mpr (h.minimizer hp.1))
    rw [norm_sub_rev s center] at he
    have hs := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hr
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    nlinarith only [he, hg, hs]
  have hacap : a ≤ target p Δ := by
    have hh := CompositeGapTuning.scale_ge_one p h0 h1 hR hΔ
    dsimp [scale] at hh
    have ht := (le_div_iff₀ hΔ).mp hh
    dsimp [a, target]
    apply (div_le_div_iff₀ (show 0 < 16 * M by positivity) hΔ).mpr
    simp only [one_mul]
    change Δ ≤ p.R ^ 2 * (16 * M)
    simp only [one_mul] at ht
    change Δ ≤ curvature p Δ * p.R ^ 2 at ht
    dsimp [M]
    nlinarith only [ht, hΔ]
  have hgcap := phase_gradient_cap h h0 h1 hR hΔ hc (by linarith)
  refine ⟨ha, hacap, hp.1, hp.1, hzrad, ?_, ?_⟩
  · change ‖a • I.grad center - a • I.grad s‖ ≤ a * (8 * Real.sqrt (curvature p Δ * Δ))
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hgcap ha.le
  · refine ⟨c, ?_, ?_, ?_⟩
    · simpa only [← hv] using hmin
    · simpa only [← hv] using hlower
    · intro u _
      simpa only [← hv] using hupper u

end LongTails.Proofs.CompositeGapPhase
