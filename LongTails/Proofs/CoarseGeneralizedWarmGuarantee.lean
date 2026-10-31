import LongTails.Proofs.CoarseGeneralizedSearch
import LongTails.Proofs.NonlinearTemporalConvergence
import LongTails.Proofs.CoarseGeneralizedFailures
import LongTails.Proofs.CoarseGeneralizedBatchExecution

open MeasureTheory

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
open StochasticGeneralized (blockTrace blockCalls blockAdvance accumulated)

lemma coarse_trace_error (p : Params) (f : p.E → ℝ) (oracle : p.E → p.Ω → p.E)
    (s : Search p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (h : accumulated (fun _ => warmBatch p) (coarseNext p oracle)
      (coarseFailure p f oracle) n s ξ < 1) (i : ℕ) (hi : i < n) :
    let q := blockTrace (fun _ => warmBatch p) (coarseNext p oracle) s ξ i
    ‖warmEstimate p (RobustGeneralized.sampleReplies oracle (searchPoint q.1) (fun j : Fin (warmBatch p) => q.2 j)) -
      gradient f (searchPoint q.1)‖ ≤ coarseTolerance p := by
  have hh := coarseFailure_zero_of_accumulated_lt p f oracle s ξ n h i hi
  dsimp only at hh ⊢
  unfold coarseFailure at hh
  split_ifs at hh with hb
  · norm_num at hh
  · exact le_of_not_gt hb

lemma coarse_warm_good (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u : p.E) (hu : gradient f u = 0) (hmin : ∀ x, f u ≤ f x) (hdist : ‖p.x0 - u‖ ≤ p.R)
    (oracle : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (hR : 1 ≤ p.L1 * p.R)
    (herr : accumulated (fun _ => warmBatch p) (coarseNext p oracle) (coarseFailure p f oracle)
      (warmCalls p) (resume (warmTuning p) ⟨p.x0, p.x0, 0, 0⟩) ξ < 1) :
    let q := (blockTrace (fun _ => warmBatch p) (coarseNext p oracle)
      (resume (warmTuning p) ⟨p.x0, p.x0, 0, 0⟩) ξ (warmCalls p)).1
    ‖warmOutput q - u‖ ≤ p.R ∧ f (warmOutput q) - f u ≤ restartGap p := by
  have hL := warmCurvature_pos p hp
  have hζ := coarseTolerance_pos p hp
  have hL1 : 0 < p.L1 := by nlinarith [hp.2.1, hp.2.2.1]
  have hLam : p.L0 ≤ warmCurvature p := by
    unfold warmCurvature
    have hh : 0 ≤ 2 ^ 20 * p.L1 ^ 2 * p.R * coarseTolerance p := by have hRp := hp.2.2.1; positivity
    linarith
  have hH' : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ warmCurvature p + p.L1 * ‖gradient f x‖ := by
    intro x
    linarith [hH x]
  have hcalls : warmCalls p = (warmTuning p).rounds * ((warmTuning p).depth + 2) := by
    simp [warmCalls, not_lt.mpr hR]
  let reply := fun k x => warmEstimate p (fun j => oracle x (ξ (k * warmBatch p + j)))
  have he : ∀ k < (warmTuning p).rounds * ((warmTuning p).depth + 2),
      let q := StochasticGradient.advance
        (fun i s => searchUpdate (warmTuning p) s (reply i (searchPoint s))) k 0
        (resume (warmTuning p) ⟨p.x0, p.x0, 0, 0⟩)
      ‖reply k (searchPoint q) - gradient f (searchPoint q)‖ ≤ (warmTuning p).ζ := by
    intro k hk
    have hh := coarse_trace_error p f oracle _ ξ (warmCalls p) herr k (by omega)
    dsimp only at hh ⊢
    simp_rw [coarse_trace_tail] at hh
    rw [warmEstimate_stream, coarse_trace_state] at hh
    exact hh
  have hgeom := warm_depth_geometry p hp
  simp only [div_pow, one_pow] at hgeom
  have hh := warm_pathwise (warmTuning p) reply hL hL1 hζ.le hR (warmCurvature_inflation p hp)
    hc hf hg hH' hu hmin hdist (warm_rounds_large p hR) (warm_depth_pos p) hgeom.1 hgeom.2 he
  dsimp only [warmAlgorithm] at hh
  dsimp only
  rw [coarse_trace_state, hcalls]
  exact ⟨hh.1, hh.2.trans (low_gap_le_restart p hp hR)⟩

lemma warmPoint_good (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hdist : ‖p.x0 - u‖ ≤ p.R)
    (oracle : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (herr : accumulated (fun _ => warmBatch p) (coarseNext p oracle) (coarseFailure p f oracle)
      (warmCalls p) (resume (warmTuning p) ⟨p.x0, p.x0, 0, 0⟩) ξ < 1) :
    ‖warmPoint p oracle ξ - u‖ ≤ p.R ∧ f (warmPoint p oracle ξ) - f u ≤ restartGap p := by
  have hu := NonlinearTemporalDiscrepancy.minimizer_gradient_zero hmin
  have hm : ∀ x, f u ≤ f x := fun x => hmin (Set.mem_univ x)
  unfold warmPoint
  split_ifs with hskip
  · refine ⟨hdist, ?_⟩
    exact (small_radius_gap hp.1.le hp.2.1 hc hf hg hH hu hdist hskip.le).trans
      (basic_gap_le_restart p hp)
  · exact coarse_warm_good p hp hc hf hg hH u hu hm hdist oracle ξ (le_of_not_gt hskip) herr

lemma warmPoint_failure_probability (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hdist : ‖p.x0 - u‖ ≤ p.R)
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} {ξ : ℕ → Ξ → p.Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P) :
    P {ω | p.R < ‖warmPoint p oracle (fun k => ξ k ω) - u‖ ∨
      restartGap p < f (warmPoint p oracle (fun k => ξ k ω)) - f u} ≤ ENNReal.ofReal (p.δ / 4) := by
  apply (measure_mono (show _ ⊆ {ω | 1 ≤ accumulated (fun _ => warmBatch p)
    (coarseNext p oracle) (coarseFailure p f oracle) (warmCalls p)
    (resume (warmTuning p) ⟨p.x0, p.x0, 0, 0⟩) (fun k => ξ k ω)} from ?_)).trans
    (coarseFailure_tail_iid p hp hg.continuous.measurable ho hξ _)
  intro ω hbad
  by_contra hn
  have hh := warmPoint_good p hp hc hf hg hH u hmin hdist oracle (fun k => ξ k ω) (lt_of_not_ge hn)
  rcases hbad with hbad | hbad
  · exact (not_lt_of_ge hh.1) hbad
  · exact (not_lt_of_ge hh.2) hbad

end OracleTemplate.CoarseGeneralized
