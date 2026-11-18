import LongTails.Proofs.WeightedInterpolationExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationSampling

open ProbabilityTheory MeasureTheory Set
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.WeightedInterpolationSgd WeightedInterpolationExecution
open LongTails.Algorithms.WeakInterpolationDesign

variable {p : Params}

lemma transformed_measurable (g : LocalOracle p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (i : Fin p.n) : Measurable (Function.uncurry (transformed g i)) := by
  have hs : Measurable (fun z : Point p × (ℕ × p.Ω) => factor p i z.2.1) :=
    (measurable_of_countable (factor p i)).comp (measurable_fst.comp measurable_snd)
  exact hs.smul ((hg i).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

lemma iterate_measurable_from (T : DistributedTemplate.Time) (g : LocalOracle p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) (m : MeasurableSpace (Samples p))
    (hcoord : ∀ i j, j < k * batch p i →
      @Measurable _ _ m p.measurableΩ (fun s : Samples p => s i j)) :
    @Measurable _ _ m _ (fun s : Samples p => iterate p T g s k) := by
  let tag := @tagged p
  have hh := DistributedBatchedSgd.measurable_trajectory_of_coordinates
    (config p T) (transformed g) (transformed_measurable g hg) k (m.map tag)
    (fun i j hj => show @Measurable _ _ (m.map tag) _ (fun s => s i j) from
      fun _ hS => (measurable_const (a := j) |>.prodMk (hcoord i j hj)) hS)
  have ht : @Measurable _ _ m (m.map tag) tag := Measurable.of_le_map le_rfl
  simpa only [tag, Function.comp_def, trajectory_identity] using hh.comp ht

lemma iterate_measurable (T : DistributedTemplate.Time) (g : LocalOracle p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (fun s : Samples p => iterate p T g s k) :=
  iterate_measurable_from T g hg k _ (fun i j _ => (measurable_pi_apply j).comp (measurable_pi_apply i))

lemma iterate_finite (T : DistributedTemplate.Time) (g : LocalOracle p) (k : ℕ) :
    (range (fun s : Samples p => iterate p T g s k)).Finite :=
  (DistributedBatchedSgd.finite_range_trajectory (config p T) (transformed g) k).subset
    (by rintro _ ⟨s,rfl⟩; exact ⟨tagged s, trajectory_identity T g s k⟩)

lemma iterate_independent (T : DistributedTemplate.Time) (g : LocalOracle p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun j (s : Samples p) => s i j) (ν i : Measure _) P) :
    IndepFun (fun s : Samples p => iterate p T g s k)
      (DistributedSampling.tail (rawParams p) (rawConfig p T) k) P := by
  let m (v : Fin p.n × ℕ) := p.measurableΩ.comap (fun s : Samples p => s v.1 v.2)
  let past : Set (Fin p.n × ℕ) := {v | v.2 < k * batch p v.1}
  let future : Set (Fin p.n × ℕ) := {v | k * batch p v.1 ≤ v.2}
  have hm (v) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) := by
    have h : Measurable (fun s : Samples p => s v.1 v.2) := by fun_prop
    exact h.comap_le
  have hd : Disjoint past future := disjoint_left.mpr (fun _ ha hb => Nat.not_lt_of_ge hb ha)
  have hind : iIndep m P := DistributedSampling.independent_coordinates (rawParams p) P ν hw hi
  have hpair := indep_iSup_of_disjoint hm hind hd
  have hx := iterate_measurable_from T g hg k (⨆ v ∈ past, m v) (fun i j hj =>
    Measurable.of_comap_le (le_iSup_of_le (i,j) (le_iSup_of_le hj le_rfl)))
  apply indep_of_indep_of_le hpair hx.comap_le
  change (inferInstance : MeasurableSpace (Samples p)).comap
    (DistributedSampling.tail (rawParams p) (rawConfig p T) k) ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def, DistributedSampling.tail]
  exact iSup_le (fun i => iSup_le (fun j =>
    le_iSup_of_le (i, k * batch p i + j) (le_iSup_of_le (Nat.le_add_right _ _) le_rfl)))

end LongTails.Proofs.WeightedInterpolationSampling
