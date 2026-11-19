import LongTails.Proofs.MultirateDescent
import LongTails.Proofs.MultirateOrthogonality

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultirateEstimator

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateCalendar
open LongTails.Algorithms.MultiscaleAggregate (precision radius unpack localCode width congruent)
open MultirateDrift MultirateFiltration MultirateNoise

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)

lemma estimator_error (s : Samples p) (hh : ∀ i, 0 < p.h i) (hLi : ∀ i, 0 ≤ p.L i)
    (hL : 0 < (aggregate p).L) (hε : 0 < p.ε)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (a : ℝ) (ha : ∀ x, a ≤ objective p f x) (hgap : objective p f p.x0 - a ≤ p.Δ)
    {k : ℕ} (hk : k ≤ steps p) :
    ‖estimate g s k - gradient (objective p f) (point g s k)‖ ^ 2 ≤
      50 * ((8 * precision (aggregate p)) ^ 2 + ‖(p.n : ℝ)⁻¹ • ∑ i, noise g f k i s‖ ^ 2) := by
  let u := aggregate p
  let X := fun i => batchMean p g s i (epoch p i k) (query g k i s)
  let Y := fun i => gradient (f i) (query g k i s)
  let G := gradient (objective p f) (point g s k)
  let z := fun i => localCode u (X i)
  let r := ∑ i, read p (pack p (z i))
  let δ := precision u
  have hcon : congruent (width u 0) (∑ i, z i) r := by
    intro j
    simp only [r, Algorithms.MultirateTrajectory.read, pack, MultiscaleAggregateCodec.read_packet_self, Finset.sum_apply]
    exact (DashaModular.sum_residue_mod Finset.univ _ (fun i => z i j)).symm
  have hF (x) : HasGradientAt (objective p f) (gradient (objective p f) x) x := by
    have h := MultiscaleAggregateSampling.objective_gradient (p := u) f hf x
    rw [← h.gradient] at h
    exact h
  have hg : ‖G‖ ≤ 2 * radius u 0 :=
    MultirateDescent.gradient_range g s _ hF (average_lipschitz f hf hl) hL hε a ha hgap hk
  have hstep : estimate g s k = liftCode p r := by
    simp only [estimate, trajectory, advance, Function.update_self]; rfl
  have hr := MultiscaleAggregateError.rounding_error (p := u) hε X
  have hb := bias g s hh hLi hL hε f hf hl hk
  change ‖(p.n : ℝ)⁻¹ • ∑ i, Y i - G‖ ≤ 7 * δ at hb
  let Z := (p.n : ℝ)⁻¹ • ∑ i, noise g f k i s
  have hZ : (p.n : ℝ)⁻¹ • ∑ i, X i - (p.n : ℝ)⁻¹ • ∑ i, Y i = Z := by
    simp only [Z, noise_eq, ← smul_sub, Finset.sum_sub_distrib, X, Y]
  have ht := norm_sub_le_norm_sub_add_norm_sub (unpack u (∑ i, z i)) ((p.n : ℝ)⁻¹ • ∑ i, X i) G
  have ht' := norm_sub_le_norm_sub_add_norm_sub ((p.n : ℝ)⁻¹ • ∑ i, X i) ((p.n : ℝ)⁻¹ • ∑ i, Y i) G
  rw [hZ] at ht'
  have h := MultirateEncoding.lift_error hε _ r hcon G hg
  change ‖unpack u (∑ i, z i) - (p.n : ℝ)⁻¹ • ∑ i, X i‖ ≤ δ at hr
  have heu : ‖liftCode p r - G‖ ≤ 5 * (8 * δ + ‖Z‖) := by linarith
  rw [hstep]
  change ‖liftCode p r - G‖ ^ 2 ≤ 50 * ((8 * δ)^2 + ‖Z‖ ^ 2)
  nlinarith only [mul_self_le_mul_self (norm_nonneg _) heu, sq_nonneg (8 * δ - ‖Z‖)]

lemma expected_error (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hh : ∀ i, 0 < p.h i) (hLi : ∀ i, 0 ≤ p.L i) (hL : 0 < (aggregate p).L)
    (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (a : ℝ) (ha : ∀ x, a ≤ objective p f x) (hgap : objective p f p.x0 - a ≤ p.Δ)
    {k : ℕ} (hk : k ≤ steps p) (hv : Measurable (fun s => estimate g s k))
    (hG : Measurable (fun s => gradient (objective p f) (point g s k))) :
    let E := fun s => ‖estimate g s k - gradient (objective p f) (point g s k)‖^2
    Integrable E P ∧ (∫ s, E s ∂P) ≤ 7142 * precision (aggregate p)^2 := by
  let δ := precision (aggregate p)
  let Z := fun s => (p.n : ℝ)⁻¹ • ∑ j, noise g f k j s
  have hm (i : Fin p.n) : Measurable (gradient (f i)) := by
    have h : LipschitzWith (p.L i).toNNReal (gradient (f i)) := lipschitzWith_iff_norm_sub_le.mpr (by
      simpa only [Real.coe_toNNReal _ (hLi i)] using hl i)
    exact h.continuous.measurable
  have hZ := MultirateOrthogonality.aggregate_variance (p := p) P μ hw hIID g f hsg hm k hh hσ hε
  have hi : Integrable (fun s => 50 * ((8*δ)^2 + ‖Z s‖^2)) P :=
    ((integrable_const _).add hZ.1).const_mul _
  have hb (s) := estimator_error g f s hh hLi hL hε hf hl a ha hgap hk
  have he : Integrable (fun s => ‖estimate g s k - gradient (objective p f) (point g s k)‖ ^ 2) P := hi.mono' ((hv.sub hG).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs, abs_pow, abs_norm, Pi.sub_apply] using hb s)
  refine ⟨he, (integral_mono he hi hb).trans ?_⟩
  rw [integral_const_mul, integral_add (integrable_const _) hZ.1, integral_const, probReal_univ, one_smul]
  have hδ : Algorithms.MultirateAllocation.precision p = δ/2 := by
    unfold Algorithms.MultirateAllocation.precision δ precision; change _ = p.ε / 512 / 2; ring
  have hv' := hZ.2
  change (∫ s, ‖Z s‖^2 ∂P) ≤ _ at hv'
  rw [hδ] at hv'
  change _ ≤ 7142*δ^2
  nlinarith [sq_nonneg δ]

end LongTails.Proofs.MultirateEstimator
