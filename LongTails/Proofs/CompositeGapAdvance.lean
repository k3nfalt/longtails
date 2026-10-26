import LongTails.Proofs.CompositeGapPhase
import LongTails.Proofs.CompositeGeneralizedStep

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapAdvance

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapAccelerated
open CompositeGapGeometry CompositeGapModel CompositeGapPhase CompositeGapTuning

variable {p : Params} {I : Instance p} {s center : p.E} {Δ : ℝ}

lemma active_invariant (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) {q : State p.E}
    (hq : Invariant p I s center Δ q) (hactive : q.A < target p Δ) :
    let y := queryPoint p Δ q
    let a := weight p Δ q.A
    let z := I.prox (q.A + a) center ((1 / (q.A + a)) • (q.v + a • I.grad y))
    Invariant p I s center Δ (update p Δ q (I.grad y) z) := by
  let a := weight p Δ q.A
  let B := q.A + a
  let τ := a / B
  let y := queryPoint p Δ q
  let g := I.grad y - I.grad s
  let z := I.prox B center ((1 / B) • (q.v + a • I.grad y))
  let w := (q.A / B) • q.x + (a / B) • z
  let v := q.v - q.A • I.grad s
  let G := 8 * Real.sqrt (curvature p Δ * Δ)
  obtain ⟨ha, hcap, hratio⟩ := weight_bounds p hq.positive hactive
  change 0 < a at ha
  have hA := hq.positive
  have hB : 0 < B := by dsimp [B]; linarith [hq.positive]
  have hsum : 0 < q.A + a := hB
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτθ : τ ≤ fraction p Δ := (div_le_iff₀ hB).mpr hratio
  have hyrepr : y = (1 - τ) • q.x + τ • q.z := by
    have he : q.A / B = 1 - τ := by dsimp [τ, B]; field_simp [hsum.ne']; ring
    dsimp [y, queryPoint]
    change (q.A / B) • q.x + τ • q.z = _
    rw [he]
  have hqx := invariant_gap h hq hc hgap
  have hqz := invariant_radius h hq hR.le hr
  have hjq := invariant_regularizer h hq hR.le hc hr hgap
  have hy := query_localization h h0 h1 hR hΔ hq.feasible_x hq.feasible_z
    hq.radius_x hqz hqx hjq hτ hτθ
  rw [← hyrepr] at hy
  have hg : ‖g‖ ≤ G := phase_gradient_cap h h0 h1 hR hΔ hy.1 hy.2
  obtain ⟨c, hm, hl, hu⟩ := hq.certificate
  let cnew := c + a * (smoothShift I s y - ⟪g, y - center⟫)
  have hvnew : q.v + a • I.grad y - B • I.grad s = v + a • g := by
    dsimp [v, g, B]
    module
  have hp := prox_is_model_min h hB center (q.v + a • I.grad y) cnew
  have hmin : IsMinOn (model (regularizerShift I s) center B (v + a • g) cnew) I.Q z := by
    have hh := shifted_model_min (s := s) hp.2
    rw [hvnew] at hh
    exact hh
  have hgrowth := model_growth h.convex_domain (shifted_regularizer_convex h)
    hq.positive.le hq.feasible_z hp.1 hm
  have happend (u : p.E) :
      model (regularizerShift I s) center B (v + a • g) cnew u =
      model (regularizerShift I s) center q.A v c u +
        a * (smoothShift I s y + ⟪g, u - y⟫ + regularizerShift I s u) :=
    model_append _ center v g y u q.A a c (smoothShift I s y)
  have hdisp : ‖z - q.z‖ ≤ p.R := by
    have hnew (u : p.E) : model (regularizerShift I s) center B (v + a • g) cnew u =
        model (regularizerShift I s) center q.A v c u +
          a * ((smoothShift I s y - ⟪g, y⟫) + ⟪g, u⟫ + regularizerShift I s u) := by
      rw [happend, inner_sub_right]
      ring
    have hh := cumulative_displacement_sq ha.le hgrowth (hmin hq.feasible_z) hnew
      (regularizerShift_nonneg h hp.1) hjq hg
    obtain ⟨hG, hJ⟩ := weight_displacement_bounds p h0 h1 hR hΔ hq.positive hactive
    exact short_displacement hR (norm_nonneg _) hh hG hJ
  have hwy : w - y = τ • (z - q.z) := by
    dsimp [w, y, queryPoint, τ, B, a]
    module
  have hlocal : Real.sqrt p.H1 * ‖w - y‖ ≤ 1 := by
    rw [hwy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    have hh := mul_le_mul_of_nonneg_left hdisp hτ
    have ht := mul_le_mul_of_nonneg_right hτθ hR.le
    have hr' := mul_le_mul_of_nonneg_left (hh.trans ht) (Real.sqrt_nonneg p.H1)
    have hf := fraction_radius p h0 h1 hR hΔ
    nlinarith only [hr', hf]
  have hM := curvature_pos p h0 h1 hR hΔ
  have hdesc : smoothShift I s w ≤ smoothShift I s y + ⟪g, w - y⟫ +
      (2 * curvature p Δ) * ‖w - y‖ ^ 2 := by
    have hh := shifted_upper h hy.1 hlocal
    have ht : p.H0 + p.H1 * (objective I y - objective I s) ≤ 2 * curvature p Δ := by
      have he : 0 ≤ Δ / p.R ^ 2 := by positivity
      dsimp [curvature]
      nlinarith [mul_le_mul_of_nonneg_left hy.2 h1]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg ‖w - y‖)])
  have hweights : q.A / B + a / B = 1 := by dsimp [B]; field_simp [hsum.ne']
  have hw : w ∈ I.Q := h.convex_domain hq.feasible_x hp.1
    (by positivity) (by positivity) hweights
  have hyid : B • y = q.A • q.x + a • q.z := by
    dsimp [y, queryPoint]
    change B • ((q.A / B) • q.x + (a / B) • q.z) = _
    rw [smul_add, smul_smul, smul_smul]
    field_simp
  have hwid : B • w = q.A • q.x + a • z := by
    dsimp [w]
    rw [smul_add, smul_smul, smul_smul]
    field_simp
  have hjmix : B * regularizerShift I s w ≤
      q.A * regularizerShift I s q.x + a * regularizerShift I s z := by
    have hh := (shifted_regularizer_convex h).2 hq.feasible_x hp.1
      (show 0 ≤ q.A / B by positivity) (show 0 ≤ a / B by positivity) hweights
    simp only [smul_eq_mul] at hh
    have ht := mul_le_mul_of_nonneg_left hh hB.le
    dsimp [w] at ⊢
    field_simp at ht
    exact ht
  have hlow : B * (objective I w - objective I s) ≤
      model (regularizerShift I s) center B (v + a • g) cnew z := by
    rw [← shift_sum]
    apply cumulative_step hq.positive.le hB hyid hwid (shifted_support h q.x y)
      hjmix hdesc (by rw [shift_sum]; exact hl) hgrowth (happend z)
    have hh := weight_condition p h0 h1 hR hΔ hq.positive hactive
    nlinarith only [hh]
  have hupp (u : p.E) (huf : u ∈ I.Q) :
      model (regularizerShift I s) center B (v + a • g) cnew u ≤
        ‖u - center‖ ^ 2 / 2 + B * (objective I u - objective I s) := by
    rw [happend]
    have hh := mul_le_mul_of_nonneg_left (shifted_support h u y) ha.le
    have ht := hu u huf
    rw [← shift_sum] at ht ⊢
    dsimp [B]
    nlinarith only [hh, ht]
  have he := model_energy h hB.le hp.1 h.minimizer_feasible hmin hlow (hupp s h.minimizer_feasible)
  have hzrad : ‖z - s‖ ≤ p.R := by
    have hh := mul_nonneg hB.le (sub_nonneg.mpr (h.minimizer hw))
    rw [norm_sub_rev s center] at he
    have hs := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hr
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    nlinarith only [he, hh, hs]
  have hwrad : ‖w - s‖ ≤ p.R :=
    OracleTemplate.CompositeGeneralized.mix_dist hq.positive.le ha.le hB q.x z s hq.radius_x hzrad
  have hvs : ‖v + a • g‖ ≤ B * G := by
    have hh := norm_add_le v (a • g)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hh
    have ht := mul_le_mul_of_nonneg_left hg ha.le
    have hv := hq.gradient_sum
    change ‖v‖ ≤ q.A * G at hv
    dsimp [B]
    nlinarith only [hh, ht, hv]
  change Invariant p I s center Δ ⟨B, w, z, q.v + a • I.grad y⟩
  refine ⟨hB, hcap, hw, hp.1, hwrad, ?_, ?_⟩
  · simpa only [← hvnew] using hvs
  · refine ⟨cnew, ?_, ?_, ?_⟩
    · simpa only [← hvnew] using hmin
    · simpa only [← hvnew] using hlow
    · intro u huf
      simpa only [← hvnew] using hupp u huf

end LongTails.Proofs.CompositeGapAdvance
