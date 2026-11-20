import LongTails.Proofs.MultirateCausality
import LongTails.Proofs.TwoSidedPLSampling
import LongTails.Proofs.FiniteVarianceBatch

namespace LongTails.Proofs.MultirateMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateSchedule
open MultirateCausality MultirateTrajectory MultiratePackets

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {f : Functions p}
  {P : Measure (Samples p)} [IsProbabilityMeasure P] {μ : Fin p.n → ProbabilityMeasure p.Ω}
  (hw : iIndepFun (fun i (s : Samples p) => s i) P)
  (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
  (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
  (hm : ∀ i, Measurable (gradient (f i)))

noncomputable def basePoint (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) (a : Index p)
    (s : Samples p) := x g s (anchor p a.1 (block p a.1 k))

noncomputable def noiseAt (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (k : ℕ) (a : Index p) (s : Samples p) : Point p :=
  g a.1 (basePoint g k a s) (atCoord (coord k a) s) - gradient (f a.1) (basePoint g k a s)

include hsg in
lemma base_measurable (k : ℕ) (a : Index p) : Measurable (basePoint g k a) :=
  point_measurable g id (fun i => (hsg i).measurable) _ fun _ _ _ => coord_measurable _

include hsg hm in
lemma noise_measurable (k : ℕ) (a : Index p) : Measurable (noiseAt g f k a) :=
  (((hsg a.1).measurable).comp ((base_measurable hsg k a).prodMk (coord_measurable _))).sub
    ((hm a.1).comp (base_measurable hsg k a))

include hw hi in
lemma coord_law {Y : Type*} [MeasurableSpace Y] (a : Coord p) (z : Samples p → Y)
    (hz : Measurable z) (hzo : Measurable[others a] z) :
    HasLaw (fun s => (z s, atCoord a s)) ((P.map z).prod (μ a.1 : Measure _)) P := by
  have hh := independent_other P μ hw hi a z hzo
  refine ⟨(hz.prodMk (coord_measurable a)).aemeasurable, ?_⟩
  rw [hh.map_prod_eq_prod_map_map hz.aemeasurable (coord_measurable a).aemeasurable]
  exact congrArg _ ((hi a.1).marginal a.2)

include hw hi hsg hm in
lemma diagonal (k : ℕ) (a : Index p) :
    Integrable (fun s => ‖noiseAt g f k a s‖^2) P ∧
    (∫ s, ‖noiseAt g f k a s‖^2 ∂P) ≤ p.σ a.1 ^ 2 := by
  let z := basePoint g k a
  have hz := base_measurable hsg k a
  have law := coord_law hw hi (coord k a) z hz
    (point_without g (fun i => (hsg i).measurable) _ _ (anchor_release k a))
  let F := fun w : Point p × p.Ω => ‖g a.1 w.1 w.2 - gradient (f a.1) w.1‖^2
  have hF : Measurable F :=
    (((hsg a.1).measurable.sub ((hm a.1).comp measurable_fst)).norm.pow_const 2)
  have : IsProbabilityMeasure (P.map z) :=
    (Measure.isProbabilityMeasure_map_iff hz.aemeasurable).mpr inferInstance
  obtain ⟨hI,hB⟩ := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := P.map z) (Q := (μ a.1 : Measure _)) hF.stronglyMeasurable (fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall (hsg a.1).variance_integrable)
    (integrable_const (p.σ a.1 ^ 2)) (Filter.Eventually.of_forall (hsg a.1).variance)
  exact ⟨law.integrable_comp hI, by simpa [noiseAt,F,z,coord,atCoord] using (law.integral_comp hI.aestronglyMeasurable).trans_le hB⟩

include hw hi hsg hm in
lemma inner_integrable (k : ℕ) (a b : Index p) :
    Integrable (fun s => ⟪noiseAt g f k a s, noiseAt g f k b s⟫) P := by
  have h2 (u) := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq
    (noise_measurable hsg hm k u).aestronglyMeasurable).mpr (diagonal hw hi hsg hm k u).1
  exact OracleTemplate.TwoSidedPL.integrable_inner_of_memLp (h2 a) (h2 b)

include hw hi hsg hm in
lemma inner_zero_le (k : ℕ) (a b : Index p) (hne : a ≠ b)
    (hr : release (coord k a) ≤ release (coord k b)) :
    (∫ s, ⟪noiseAt g f k a s, noiseAt g f k b s⟫ ∂P) = 0 := by
  let z := fun s => (noiseAt g f k a s, basePoint g k b s)
  have ho (u : Index p) (hu : release (coord k u) ≤ release (coord k b)) :
      Measurable[others (coord k b)] (basePoint g k u) :=
    point_without g (fun i => (hsg i).measurable) _ _ ((anchor_release k u).trans hu)
  have hna : Measurable[others (coord k b)] (noiseAt g f k a) :=
    ((hsg a.1).measurable.comp ((ho a hr).prodMk
      (other_measurable (fun he => hne (coord_inj k he))))).sub ((hm a.1).comp (ho a hr))
  have law := coord_law hw hi (coord k b) z
    ((noise_measurable hsg hm k a).prodMk (base_measurable hsg k b)) (hna.prodMk (ho b le_rfl))
  change HasLaw (fun s => (z s, atCoord (coord k b) s)) ((P.map z).prod (μ b.1 : Measure _)) P at law
  let F := fun w : (Point p × Point p) × p.Ω =>
    ⟪w.1.1, g b.1 w.1.2 w.2 - gradient (f b.1) w.1.2⟫
  have hF : Measurable F := (measurable_fst.comp measurable_fst).inner
    (((hsg b.1).measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).sub
      ((hm b.1).comp (measurable_snd.comp measurable_fst)))
  have hI : Integrable F ((P.map z).prod (μ b.1 : Measure _)) := by
    rw [← law.map_eq]
    exact (integrable_map_measure hF.aestronglyMeasurable law.aemeasurable).mpr
      (inner_integrable hw hi hsg hm k a b)
  have : IsProbabilityMeasure (P.map z) := (Measure.isProbabilityMeasure_map_iff
    ((noise_measurable hsg hm k a).prodMk (base_measurable hsg k b)).aemeasurable).mpr inferInstance
  refine (law.integral_comp hF.aestronglyMeasurable).trans ?_
  rw [integral_prod F hI]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro w
  dsimp only [F]
  rw [integral_inner (𝕜 := ℝ) (f := fun y => g b.1 w.2 y - gradient (f b.1) w.2)
    (((hsg b.1).integrable w.2).sub (integrable_const _)) w.1,
    integral_sub ((hsg b.1).integrable _) (integrable_const _), (hsg b.1).unbiased]
  simp

include hw hi hsg hm in
lemma inner_zero (k : ℕ) (a b : Index p) (hne : a ≠ b) :
    (∫ s, ⟪noiseAt g f k a s, noiseAt g f k b s⟫ ∂P) = 0 := by
  rcases le_total (release (coord k a)) (release (coord k b)) with hab | hba
  · exact inner_zero_le hw hi hsg hm k a b hne hab
  · simpa only [real_inner_comm (noiseAt g f k b _) (noiseAt g f k a _)] using
      inner_zero_le hw hi hsg hm k b a hne.symm hba

end LongTails.Proofs.MultirateMoments
