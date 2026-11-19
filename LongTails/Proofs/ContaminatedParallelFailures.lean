import LongTails.Proofs.ContaminatedParallelHistory
import LongTails.Proofs.ContaminatedCalendarBudget
import LongTails.Proofs.DistributedSmoothNonconvex

namespace LongTails.Proofs.ContaminatedParallelFailures

open MeasureTheory ProbabilityTheory
open scoped Classical
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution iterations height)
open ContaminatedParallelHistory ContaminatedParallelSampling ContaminatedParallelObservations

structure Data (p : Params) where
  f : Functions p
  g : Fin p.n → Point p → p.Ω → Point p
  μ : Fin p.n → ProbabilityMeasure p.Ω
  ν : Fin p.n → ProbabilityMeasure p.Ω
  P : ProbabilityMeasure (Samples p)
  valid : spec.valid p
  differentiable : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  smooth : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x-y‖
  gap : ∃ a : ℝ, (∀ x, a ≤ objective p f x) ∧ objective p f p.x0-a ≤ p.Δ
  workers : iIndepFun (fun i (s : Samples p) => s i) (P : Measure _)
  streams : ∀ i, IID (fun k (s : Samples p) => s i k) (mixture (p.η i) (μ i) (ν i)) (P : Measure _)
  clean : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)

variable {p : Params}

noncomputable def Data.G (D : Data p) := gradient (objective p D.f)

lemma Data.gradient (D : Data p) (x) : HasGradientAt (objective p D.f) (D.G x) x := by
  have h := OracleTemplate.FiniteSum.objective_gradient (f := D.f)
    (oracle := fun ix : Fin p.n × Point p => _root_.gradient (D.f ix.1) ix.2) D.differentiable x
  rw [← h.gradient] at h
  exact h

lemma Data.measurable_G (D : Data p) : Measurable D.G :=
  (show LipschitzWith p.L.toNNReal D.G by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Data.G,dist_eq_norm,Real.coe_toNNReal _ D.valid.2.1.le] using D.smooth x y).continuous.measurable

lemma Data.start_bound (D : Data p) :
    ‖D.G p.x0‖ ≤ (4:ℝ)^(height (network p))*resolution (network p) := by
  obtain ⟨a,ha,hgap⟩ := D.gap
  have hL := D.valid.2.1
  have hε := D.valid.2.2.2.1
  have h0 := DistributedSmoothNonconvex.initial_gradient_bound (p := network p) hL D.gradient D.smooth a ha hgap
  have hs := LeonBatchTuning.resolution_pos (network p) hε
  have hK : 1 ≤ (4:ℝ)^(height (network p)) := one_le_pow₀ (by norm_num)
  have hk := (div_le_iff₀ (sq_pos_of_pos hs)).mp (LeonBatchTuning.iterations_lower (network p))
  have he : (iterations (network p) : ℝ) = (4:ℝ)^(height (network p)) := by simp [iterations]
  rw [he] at hk
  change ‖D.G p.x0‖^2 ≤ 2*p.L*p.Δ at h0
  nlinarith [mul_nonneg (sub_nonneg.mpr hK)
    (show 0 ≤ (4:ℝ)^height (network p) * resolution (network p)^2 by positivity),
    norm_nonneg (D.G p.x0), show 0 ≤ (4:ℝ)^height (network p)*resolution (network p) by positivity]

noncomputable def trainOp (p : Params) (t : ℕ) :=
  Operation.train ((levels (height (network p)))[t]?.getD 0)

noncomputable def bad (D : Data p) (o : ℕ → Operation) (t : ℕ) : Set (Samples p) :=
  {s | resolution (network p) < noise p D.g D.f (used p o t) (state p D.g o s t) (o t) s}

lemma bad_measurable (D : Data p) (o : ℕ → Operation) (t : ℕ) :
    MeasurableSet[past p (used p o (t+1))] (bad D o t) := by
  let _ := past p (used p o (t+1))
  have hm := (measurable_state p D.g (fun i => (D.clean i).measurable) o t).mono
    (ν := past p (used p o (t+1))) (past_mono p (used_mono p o (Nat.le_succ t)))
  let x := fun s => location p (state p D.g o s t) (o t)
  have hx : Measurable x := hm.location _
  have hh := measurable_average p ((o t).precision p) D.g (fun i => (D.clean i).measurable)
    x hx (freshSamples p (used p o t)) (fun i j hj => past_eval p _ i _ (Nat.add_lt_add_left hj _))
  exact measurableSet_lt measurable_const (hh.sub (D.measurable_G.comp hx)).norm

lemma weighted_failure (D : Data p) (o : ℕ → Operation) (t : ℕ) (hq : 1 ≤ (o t).precision p)
    (W : Samples p → ℝ) (hmW : Measurable[past p (used p o t)] W)
    (hW : Integrable W (D.P : Measure _)) (h0 : ∀ s, 0 ≤ W s) :
    (∫ s, (if s ∈ bad D o t then W s else 0) ∂(D.P : Measure _)) ≤
      (∫ s, W s ∂(D.P : Measure _)) * (2 * Real.exp (-((o t).precision p : ℝ))) := by
  let u := used p o t
  let x := fun s => location p (state p D.g o s t) (o t)
  let a := fun s => (x s, W s)
  let q := (o t).precision p
  let T : Samples p → Samples p := LeonAdaptiveSampling.shifted (network p) u
  let ν (i : Fin p.n) : ProbabilityMeasure p.Ω := ⟨mixture (p.η i) (D.μ i) (D.ν i),
    DistributedContaminationMoments.mixture_probability (D.valid.2.2.2.2.1 i).2.1
      (by linarith [(D.valid.2.2.2.2.1 i).2.2])⟩
  have hind := DistributedSampling.independent_coordinates (network p) D.P ν D.workers D.streams
  have hT := LeonAdaptiveSampling.shift_law (network p) u D.P ν D.workers D.streams
  have hx : Measurable[past p u] x :=
    @MeasurableModel.location (Samples p) (past p u) p _ (measurable_state p D.g (fun i => (D.clean i).measurable) o t) _
  have ha : Measurable[past p u] a := by let _ := past p u; exact hx.prodMk hmW
  have hma : Measurable a := ha.mono (past_le p u) le_rfl
  have hi := fresh p D.P u hind a ha
  let E := {z : (Point p × ℝ) × Samples p | resolution (network p) <
    ‖localAverage p q D.g z.1.1 z.2 - D.G z.1.1‖}
  have he : MeasurableSet E := measurableSet_lt measurable_const
    ((measurable_average p q D.g (fun i => (D.clean i).measurable) _ measurable_fst.fst _
      (fun i j _ => (show Measurable (fun z : (Point p × ℝ) × Samples p => z.2 i j) by fun_prop))).sub
      (D.measurable_G.comp measurable_fst.fst)).norm
  let w (z : Point p × ℝ) := max 0 z.2
  have hw : Measurable w := measurable_const.max measurable_snd
  have hwa (s) : w (a s) = W s := max_eq_right (h0 s)
  have hwi : Integrable w ((D.P : Measure _).map a) := by
    apply (integrable_map_measure hw.aestronglyMeasurable hma.aemeasurable).mpr
    simpa only [Function.comp_def,hwa] using hW
  have hh := conditional_event (Ω := Samples p) (A := Point p × ℝ) (D.P : Measure (Samples p)) a T hma hT hi E he w hw
    (fun _ => le_max_left _ _) hwi (2*Real.exp (-(q:ℝ))) (fun z => by
      change (D.P : Measure _).real {s | resolution (network p) < ‖localAverage p q D.g z.1 s - D.G z.1‖} ≤ _
      simp_rw [Data.G, average_error p q D.g D.f D.differentiable]
      exact one_batch p D.valid q hq D.P D.μ D.ν D.workers D.streams D.g D.f D.clean z.1)
  have hev (s : Samples p) : ((a s,T s) ∈ E) = (s ∈ bad D o t) := rfl
  simpa only [hev,hwa] using hh

end LongTails.Proofs.ContaminatedParallelFailures
