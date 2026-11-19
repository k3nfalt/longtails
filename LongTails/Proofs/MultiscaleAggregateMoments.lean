import LongTails.Proofs.MultiscaleAggregateSampling

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateMoments

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateHistory MultiscaleAggregateTrajectory MultiscaleAggregateBudget
open MultiscaleAggregateSampling MultiscaleAggregateCodec

variable {p : Params}

lemma past_independent (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (k : ℕ) :
    IndepFun (fun s => point g s k) (DistributedSampling.tail (streamParams p) (streamConfig p) k) P := by
  let m : Fin p.n × ℕ → MeasurableSpace (Samples p) := fun v =>
    MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ
  let past : Set (Fin p.n × ℕ) := {v | v.2 < k * batch p v.1}
  let future : Set (Fin p.n × ℕ) := {v | k * batch p v.1 ≤ v.2}
  have hm (v : Fin p.n × ℕ) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) := by
    have hl : Measurable (fun s : Samples p => s v.1 v.2) := by fun_prop
    exact hl.comap_le
  have hind : iIndep m P := DistributedSampling.independent_coordinates (streamParams p) P μ hw hIID
  have hpair := indep_iSup_of_disjoint hm hind
    (show Disjoint past future from Set.disjoint_left.mpr (fun _ hv hf => Nat.not_lt_of_ge hf hv))
  have hh := coordinates_measurable p g hg k (⨆ v ∈ past, m v)
    (fun i j hj => Measurable.of_comap_le
      (le_iSup_of_le (i, j) (le_iSup_of_le hj le_rfl)))
  let : MeasurableSpace (History p) := ⊤
  let : DiscreteMeasurableSpace (History p) := ⟨fun _ => trivial⟩
  have hx := (measurable_of_countable (f := fun h : History p => (replay p h).point)).comp hh
  simp only [Function.comp_def, replay_history] at hx
  apply indep_of_indep_of_le hpair hx.comap_le
  change (inferInstance : MeasurableSpace (Samples p)).comap (DistributedSampling.tail (streamParams p) (streamConfig p) k) ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, DistributedSampling.tail]
  exact iSup_le (fun i => iSup_le (fun j =>
    le_iSup_of_le (i, k * batch p i + j) (le_iSup_of_le (Nat.le_add_right _ _) le_rfl)))

lemma measurable_batch (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) (i : Fin p.n) :
    Measurable (fun z : Point p × Samples p => batchMean p g z.2 k i z.1) := by
  apply Measurable.fun_const_smul
  exact Finset.measurable_sum _ fun j _ => (hg i).comp (measurable_fst.prodMk
    ((measurable_pi_apply (k * batch p i + j)).comp ((measurable_pi_apply i).comp measurable_snd)))

lemma adaptive_variance (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 < p.L) (k : ℕ) :
    let e := fun s => ‖unrounded p g s k (point g s k) - gradient (objective p f) (point g s k)‖ ^ 2
    Integrable e P ∧ (∫ s, e s ∂P) ≤ precision p ^ 2 := by
  let F := fun z : Point p × Samples p =>
    ‖unrounded p g z.2 0 z.1 - gradient (objective p f) z.1‖ ^ 2
  have hG : LipschitzWith ⟨p.L, hL.le⟩ (gradient (objective p f)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      change dist _ _ ≤ p.L * dist _ _
      simpa only [dist_eq_norm] using hlip x y
  have hg' := fun i => (hsg i).measurable
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub _ (hG.continuous.measurable.comp measurable_fst)
    apply Measurable.fun_const_smul
    exact Finset.measurable_sum _ fun i _ => measurable_batch g hg' 0 i
  have hfix := fun x => aggregate_variance P μ hw hIID g f hsg hg hh hε x 0
  have hb := DistributedBatchedSgd.independent_finite_range_bound (p := streamParams p) P
    (fun s => point g s k)
    (measurable_trajectory_image p g hg' k Model.point)
    (finite_trajectory_image p g k Model.point)
    _ (DistributedSampling.tail_preserving (streamParams p) (streamConfig p) P μ hw hIID k)
    (past_independent P μ hw hIID g hg' k) F (fun _ => precision p ^ 2) hF measurable_const
    (fun _ => sq_nonneg _) (fun x => (hfix x).1) (fun x => (hfix x).2)
  simpa only [F, unrounded, batchMean, DistributedSampling.tail, streamConfig, Nat.zero_mul,
    Nat.zero_add, integral_const, probReal_univ, one_smul] using hb

end LongTails.Proofs.MultiscaleAggregateMoments
