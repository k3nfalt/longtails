import LongTails.Proofs.BirchAveragingPaths
import LongTails.Proofs.NormSubGaussianBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

/-- The controls use the mean of queried gradients, not a free global-gradient oracle. -/
theorem objective_gradient_mean {workers d : ℕ} (I : Instance workers d)
    (hg : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (x : Point d) : gradient (objective I) x = pointMean (fun i => gradient (I.localObjective i) x) := by
  have hh : HasGradientAt (objective I) (pointMean (fun i => gradient (I.localObjective i) x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hd := (HasFDerivAt.sum (u := Finset.univ)
      (fun i _ => (hg i x).hasFDerivAt)).const_mul (workers : ℝ)⁻¹
    simp only [Finset.sum_apply] at hd
    simp only [pointMean, map_smul, map_sum]
    exact hd
  exact hh.gradient

theorem zeroVariance_exact {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {f : Point d → ℝ} {g : Point d → Ω → Point d}
    (hg : IsStochasticGradient (Point d) Ω (μ : Measure Ω) f g 0) (x : Point d) :
    ∀ᵐ ω ∂(μ : Measure Ω), g x ω = gradient f x := by
  have hb : (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(μ : Measure Ω)) ≤ 0 := by
    simpa using hg.variance x
  have hz := OracleTemplate.LightTail.ae_zero_of_integral_sq_norm_nonpos
    (hg.variance_integrable x) hb
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

/-- All queries of a countable deterministic reference schedule are exact together. -/
theorem zeroVariance_schedule_exact {workers d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {P : ProbabilityMeasure (ℕ → Ω)}
    {I : Instance workers d} {g : Fin workers → Point d → Ω → Point d}
    (hiid : IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hg : ∀ i, IsStochasticGradient (Point d) Ω (μ : Measure Ω) (I.localObjective i) (g i) 0)
    (q : ℕ → Fin workers × Point d) :
    ∀ᵐ ξ ∂(P : Measure (ℕ → Ω)), ∀ k,
      g (q k).1 (q k).2 (ξ k) = gradient (I.localObjective (q k).1) (q k).2 := by
  apply ae_all_iff.mpr
  intro k
  have h := zeroVariance_exact (hg (q k).1) (q k).2
  rw [← hiid.marginal k] at h
  exact ae_of_ae_map (hiid.measurable k).aemeasurable h

end LongTails.Setups.BirchNonIID

open MeasureTheory
open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

/-- Reconstruction from replies alone; the anchor replies are reused as controls. -/
noncomputable def replayLocal {workers d : ℕ} (anchor : Point d) (η : ℝ)
    (reply : ℕ → Fin workers → Point d) (i : Fin workers) : ℕ → Point d
  | 0 => anchor
  | k + 1 => replayLocal anchor η reply i k -
      η • (reply k i - reply 0 i + pointMean (reply 0))

noncomputable def replayServer {workers d : ℕ} (x0 : Point d) (η : ℝ) (K : ℕ)
    (reply : ℕ → ℕ → Fin workers → Point d) : ℕ → Point d
  | 0 => x0
  | r + 1 => pointMean (fun i => replayLocal (replayServer x0 η K reply r) η (reply r) i K)

theorem replayLocal_exact {workers d : ℕ} (I : Instance workers d)
    (hg : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (anchor : Point d) (η : ℝ) (i : Fin workers) (k : ℕ) :
    replayLocal anchor η (fun k j => gradient (I.localObjective j) (localPath I j anchor η k)) i k =
      localPath I i anchor η k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [replayLocal, ih, localPath, ← objective_gradient_mean I hg, correctedDirection]

theorem replayServer_exact {workers d : ℕ} (I : Instance workers d)
    (hg : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (x0 : Point d) (η : ℝ) (K r : ℕ) :
    replayServer x0 η K (fun r k i =>
      gradient (I.localObjective i) (localPath I i (serverPath I x0 η K r) η k)) r =
      serverPath I x0 η K r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [replayServer, ih, replayLocal_exact I hg, serverPath]

theorem replayLocal_congr {workers d : ℕ} (anchor : Point d) (η : ℝ)
    {reply reply' : ℕ → Fin workers → Point d} (i : Fin workers) (k : ℕ)
    (h : ∀ j, j < k → ∀ a, reply j a = reply' j a) :
    replayLocal anchor η reply i k = replayLocal anchor η reply' i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih (fun j hj => h j (by omega))
    have hzero : reply 0 = reply' 0 := funext (h 0 (by omega))
    simp only [replayLocal, hprev, h k (by omega), hzero]

theorem replayServer_congr {workers d : ℕ} (x0 : Point d) (η : ℝ) (K r : ℕ)
    {reply reply' : ℕ → ℕ → Fin workers → Point d}
    (h : ∀ s, s < r → ∀ k, k < K → ∀ i, reply s k i = reply' s k i) :
    replayServer x0 η K reply r = replayServer x0 η K reply' r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hprev := ih (fun s hs => h s (by omega))
    simp only [replayServer, hprev]
    congr 1
    funext i
    exact replayLocal_congr _ η i K (h r (by omega))

theorem measurable_pointMean {workers d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Fin workers → Point d} (hy : ∀ i, Measurable (fun ω => y ω i)) :
    Measurable (fun ω => pointMean (y ω)) := by
  unfold pointMean
  exact (Finset.measurable_sum _ (fun i _ => hy i)).const_smul (workers : ℝ)⁻¹

theorem measurable_replayLocal {workers d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {anchor : Ω → Point d} {reply : Ω → ℕ → Fin workers → Point d}
    (ha : Measurable anchor) (hr : ∀ k i, Measurable (fun ω => reply ω k i))
    (η : ℝ) (i : Fin workers) (k : ℕ) :
    Measurable (fun ω => replayLocal (anchor ω) η (reply ω) i k) := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    exact ih.sub (((hr k i).sub (hr 0 i)).add
      (measurable_pointMean (fun j => hr 0 j)) |>.const_smul η)

theorem measurable_replayServer {workers d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {reply : Ω → ℕ → ℕ → Fin workers → Point d}
    (hr : ∀ r k i, Measurable (fun ω => reply ω r k i))
    (x0 : Point d) (η : ℝ) (K r : ℕ) :
    Measurable (fun ω => replayServer x0 η K (reply ω) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    exact measurable_pointMean (fun i => measurable_replayLocal ih (hr r) η i K)

end LongTails.Setups.BirchNonIID
