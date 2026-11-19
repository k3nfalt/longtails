import LongTails.Proofs.MultirateEstimator
import LongTails.Proofs.LeonAccuracy
import LongTails.Algorithms.MultirateProtocol

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultirateAccuracy

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateCalendar
open LongTails.Algorithms.MultiscaleAggregate (precision)
open MultirateDrift MultirateFiltration MultirateNoise

variable {p : Params}

lemma grad_measurable {F : Point p → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x-y‖) : Measurable (gradient F) := by
  have hb : LipschitzWith L.toNNReal (gradient F) := lipschitzWith_iff_norm_sub_le.mpr (by
    simpa only [Real.coe_toNNReal _ hL] using h)
  exact hb.continuous.measurable

lemma flat_accuracy (F : Point p → ℝ) (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hl : ∀ x y, ‖gradient F x - gradient F y‖ ≤ 0) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (a : ℝ) (ha : ∀ x, a ≤ F x) (hgap : F p.x0 - a ≤ p.Δ) (x : Point p) :
    ‖gradient F x‖ ^ 2 ≤ p.ε ^ 2 := by
  let L := p.ε^2 / (2 * (p.Δ+1))
  have hL : 0 < L := by dsimp [L]; positivity
  let q := { MultiscaleAggregateSampling.streamParams (aggregate p) with L := L }
  have hb := DistributedSmoothNonconvex.initial_gradient_bound (p := q) (f := F) hL hF
    (fun x y => (hl x y).trans (mul_nonneg hL.le (norm_nonneg _))) a ha hgap
  have he := sub_eq_zero.mp (norm_le_zero_iff.mp (hl x p.x0))
  rw [he]
  have ht : L * (2 * (p.Δ+1)) = p.ε^2 := div_mul_cancel₀ _ (by positivity)
  change ‖gradient F p.x0‖ ^ 2 ≤ 2 * L * p.Δ at hb
  nlinarith

set_option maxHeartbeats 650000 in
lemma accuracy (hh : ∀ i, 0 < p.h i) (hLi : ∀ i, 0 ≤ p.L i) (hΔ : 0 ≤ p.Δ)
    (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) (P : ProbabilityMeasure (Samples p))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) (P : Measure _))
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (a : ℝ) (ha : ∀ x, a ≤ objective p f x) (hgap : objective p f p.x0 - a ≤ p.Δ)
    (T : DistributedTemplate.Time) :
    spec.successful p f (fun z : (Fin (steps p) × Fin (steps p)) × Samples p =>
      output p (trajectory p g z.2 (steps p)) z.1.1 z.1.2)
      (DistributedTemplate.law (Setups.DistributedAggregateSmoothNonconvex.system (aggregate p) g P)
        (Algorithms.MultirateProtocol.algorithm p T)) := by
  let K := steps p
  let F := objective p f
  let x := fun (i : Fin K) (s : Samples p) => point g s i
  let v := fun (i : Fin K) (s : Samples p) => estimate g s i
  let G := fun i s => gradient F (x i s)
  let δ := precision (aggregate p)
  let out := fun (ij : Fin K × Fin K) (s : Samples p) =>
    if ‖v ij.1 s‖ ≤ ‖v ij.2 s‖ then x ij.1 s else x ij.2 s
  have hout (ij : Fin K × Fin K) (s : Samples p) :
      output p (trajectory p g s K) ij.1 ij.2 = out ij s := by
    simp only [output, out, past_estimate g s ij.1.isLt, past_estimate g s ij.2.isLt,
      past_point g s ij.1.isLt.le, past_point g s ij.2.isLt.le, x, v]
  have hstate (t j) := measurable_state g (fun i => (hsg i).measurable) t inferInstance
    (fun _ _ i _ _ => sample_coordinate p i _) j
  have hx (i : Fin K) : Measurable (x i) := (hstate i i).1
  have hv (i : Fin K) : Measurable (v i) := (hstate (i+1 : ℕ) i).2
  have hm (ij : Fin K × Fin K) : Measurable (out ij) :=
    Measurable.ite (measurableSet_le (hv _).norm (hv _).norm) (hx _) (hx _)
  have houtm : Measurable (fun z : (Fin K × Fin K) × Samples p => out z.1 z.2) := measurable_from_prod_countable_right hm
  have hF (z) : HasGradientAt F (gradient F z) z := by
    have h := MultiscaleAggregateSampling.objective_gradient (p := aggregate p) f hf z
    rw [← h.gradient] at h
    exact h
  have hlF := average_lipschitz f hf hl
  have hL₀ : 0 ≤ (aggregate p).L := div_nonneg (Finset.sum_nonneg fun i _ => hLi i) (Nat.cast_nonneg _)
  have hFm := grad_measurable hL₀ hlF
  have hG (i : Fin K) : Measurable (G i) := hFm.comp (hx i)
  let : NeZero K := ⟨(MultirateCalendar.steps_pos p).ne'⟩
  let Q := (PMF.uniformOfFintype (Fin K × Fin K)).toMeasure.prod (P : Measure (Samples p))
  let Y := fun z : (Fin K × Fin K) × Samples p => output p (trajectory p g z.2 K) z.1.1 z.1.2
  change Measurable Y ∧ Integrable (fun z => ‖gradient F (Y z)‖^2) Q ∧ (∫ z, ‖gradient F (Y z)‖^2 ∂Q) ≤ p.ε^2
  have hY : Y = fun z => out z.1 z.2 := funext (fun z => hout z.1 z.2)
  rw [hY]
  refine ⟨houtm, ?_⟩
  rcases hL₀.eq_or_lt with hzero | hL
  · have hflat (x y : Point p) : ‖gradient F x - gradient F y‖ ≤ 0 := by
      have h := hlF x y
      change _ ≤ (aggregate p).L * _ at h
      rwa [← hzero, zero_mul] at h
    have hb (y) := flat_accuracy F hF hflat hε hΔ a ha hgap y
    have hi : Integrable (fun z : (Fin K × Fin K) × Samples p => ‖gradient F (out z.1 z.2)‖ ^ 2) Q :=
      (integrable_const (p.ε^2)).mono' ((hFm.comp houtm).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hb (out z.1 z.2))
    exact ⟨hi, (integral_mono hi (integrable_const (p.ε^2)) fun z => hb (out z.1 z.2)).trans_eq (by simp)⟩
  have herr (i : Fin K) := MultirateEstimator.expected_error (p := p) (P : Measure (Samples p)) μ hw hIID
    g f hsg hh hLi hL hσ hε hf hl a ha hgap i.isLt.le (hv i) (hG i)
  have hs (s) := MultirateDescent.estimated_sum g s F hF hlF hL hε a ha hgap
  have hp := LeonPairAccuracy.expected (P : Measure _) v G δ hv hG (fun i => (herr i).1) (fun i => (herr i).2) hs
  have hval (z : (Fin K × Fin K) × Samples p) : gradient F (out z.1 z.2) =
      if ‖v z.1.1 z.2‖ ≤ ‖v z.1.2 z.2‖ then G z.1.1 z.2 else G z.1.2 z.2 := by
    dsimp only [out, G]; split <;> rfl
  simp_rw [hval]
  exact ⟨hp.1, hp.2.trans_eq (by unfold δ precision; ring)⟩

end LongTails.Proofs.MultirateAccuracy
