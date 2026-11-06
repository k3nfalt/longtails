import LongTails.Algorithms.SpikedSoftCutMethod
import LongTails.Proofs.SpikedSoftCutCoordinates
import LongTails.Proofs.SpikedSoftCutSelection
import LongTails.Proofs.CovarianceSoftCutTrajectory
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory

namespace LongTails.Proofs.SpikedSoftCutMeasurable

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutCoordinates
open CovarianceSoftCutTrajectory

lemma measurable_tail_stream (q : Params) :
    Measurable (fun r : ℕ → Space q => fun i => tail q (r i)) :=
  Measurable.of_eval fun i => (continuous_tail q).measurable.comp (measurable_pi_apply i)

lemma measurable_supportPoints (q : Params) (c : Config) (hR : 0 < q.R) :
    Measurable (supportPoints q c) := by
  apply Measurable.of_eval
  intro i
  have hp := (continuous_generatorPoint (innerParams q c.α)
    (by dsimp [innerParams]; positivity) c.α (2/c.α) c.b i).measurable.comp
      (measurable_tail_stream q)
  exact hp

lemma measurable_innerEstimates (q : Params) (c : Config) :
    Measurable (fun r : ℕ → Space q => innerEstimates q c.α c.T c.b (fun i => tail q (r i))) := by
  apply Measurable.of_eval
  intro i
  exact (continuous_batchMean (innerParams q c.α) c.b i).measurable.comp (measurable_tail_stream q)

lemma measurable_weights (q : Params) (c : Config) (hR : 0 < q.R) :
    Measurable (weights q c) := by
  have hh := (SpikedSoftCutSelection.measurable_certificateWeights q c.α c.T c.n).comp
    ((measurable_supportPoints q c hR).prodMk (measurable_innerEstimates q c))
  change Measurable (weights q c) at hh
  exact hh

lemma measurable_sampleCount (q : Params) (c : Config) (hR : 0 < q.R) (k i : ℕ) :
    Measurable (fun r => sampleCount q c k r i) := by
  unfold sampleCount
  by_cases hi : i < c.T
  · simp only [hi, dite_true]
    exact (((measurable_pi_apply (⟨i, hi⟩ : Fin c.T)).comp
      (measurable_weights q c hR)).const_mul (c.N k : ℝ)).nat_ceil
  · simp only [hi, dite_false]
    exact measurable_const

lemma measurable_sampleStart (q : Params) (c : Config) (hR : 0 < q.R) (k i : ℕ) :
    Measurable (fun r => sampleStart q c k r i) := by
  unfold sampleStart
  exact Finset.measurable_sum _ (fun j _ => measurable_sampleCount q c hR k j)

lemma measurable_dynamic_reply (q : Params) :
    Measurable (fun z : (ℕ → Space q) × ℕ => z.1 z.2) :=
  measurable_from_prod_countable_left (fun i => measurable_pi_apply i)

lemma measurable_reply_range_sum (q : Params) :
    Measurable (fun z : (ℕ → Space q) × (ℕ × ℕ) =>
      ∑ j ∈ Finset.range z.2.2, head q (z.1 (z.2.1+j))) := by
  apply measurable_from_prod_countable_left
  intro a
  change Measurable (fun r : ℕ → Space q => ∑ j ∈ Finset.range a.2, head q (r (a.1+j)))
  apply Finset.measurable_sum
  intro j _
  exact (continuous_head q).measurable.comp (measurable_pi_apply (a.1+j))

lemma measurable_scalarEstimate (q : Params) (c : Config) (hR : 0 < q.R) (k : ℕ) :
    Measurable (scalarEstimate q c k) := by
  unfold scalarEstimate
  apply Finset.measurable_sum
  intro i _
  have hw := (measurable_pi_apply i).comp (measurable_weights q c hR)
  have hc := measurable_sampleCount q c hR k i
  have ha := measurable_sampleStart q c hR k i
  have hd : Measurable (fun r => (sampleCount q c k r i : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hc
  have hs : Measurable (fun r => c.T*c.b+sampleStart q c k r i) := measurable_const.add ha
  exact (hw.div hd).mul ((measurable_reply_range_sum q).comp
    (measurable_id.prodMk (hs.prodMk hc)))

lemma measurable_primalOutput (q : Params) (c : Config) (hR : 0 < q.R) :
    Measurable (fun z : OuterState q × (ℕ → Space q) => primalOutput q c z.1 z.2) := by
  have hw : Measurable (fun z : OuterState q × (ℕ → Space q) => weights q c z.2) :=
    (measurable_weights q c hR).comp measurable_snd
  have hp : Measurable (fun z : OuterState q × (ℕ → Space q) => supportPoints q c z.2) :=
    (measurable_supportPoints q c hR).comp measurable_snd
  have hm : Measurable (fun z : OuterState q × (ℕ → Space q) =>
      ∑ i, weights q c z.2 i • supportPoints q c z.2 i) := by fun_prop
  change Measurable (fun z : OuterState q × (ℕ → Space q) =>
    join q (center q z.1) (∑ i, weights q c z.2 i • supportPoints q c z.2 i))
  have hc : Measurable (fun z : OuterState q × (ℕ → Space q) => center q z.1) := measurable_fst.fst
  exact (continuous_join q).measurable.comp (hc.prodMk hm)

lemma measurable_find_output {A I E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (l : List I) (p : A → I → Prop) [∀ x, DecidablePred (p x)]
    (F : A → I → E) (z : A → E) (hp : ∀ i, MeasurableSet {x | p x i})
    (hF : ∀ i, Measurable (fun x => F x i)) (hz : Measurable z) :
    Measurable (fun x => match l.find? (fun i => decide (p x i)) with
      | some i => F x i
      | none => z x) := by
  induction l with
  | nil => simpa using hz
  | cons i l ih =>
    have he : (fun x => match (i::l).find? (fun j => decide (p x j)) with
        | some j => F x j | none => z x) =
        fun x => if p x i then F x i else
          match l.find? (fun j => decide (p x j)) with | some j => F x j | none => z x := by
      funext x
      by_cases hx : p x i <;> simp [hx]
    rw [he]
    exact Measurable.ite (hp i) (hF i) ih

lemma measurable_scalarQuery (q : Params) (c : Config) (hR : 0 < q.R) (k t : ℕ) :
    Measurable (fun z : OuterState q × (ℕ → Space q) => scalarQuery q c k z.1 z.2 t) := by
  have hp (i : Fin c.T) : MeasurableSet {z : OuterState q × (ℕ → Space q) |
      t < sampleStart q c k z.2 (i.val+1)} :=
    measurableSet_lt measurable_const ((measurable_sampleStart q c hR k (i.val+1)).comp measurable_snd)
  have hF (i : Fin c.T) : Measurable (fun z : OuterState q × (ℕ → Space q) =>
      join q (center q z.1) (supportPoints q c z.2 i)) :=
    (continuous_join q).measurable.comp
      ((show Measurable (fun z : OuterState q × (ℕ → Space q) => center q z.1) from measurable_fst.fst).prodMk
        (((measurable_pi_apply i).comp (measurable_supportPoints q c hR)).comp measurable_snd))
  have hh := measurable_find_output (List.finRange c.T)
    (fun z : OuterState q × (ℕ → Space q) => fun i => t < sampleStart q c k z.2 (i.val+1))
    (fun z i => join q (center q z.1) (supportPoints q c z.2 i)) (fun _ => (0 : Space q))
    hp hF measurable_const
  convert! hh using 1
  funext z
  simp only [scalarQuery]
  split <;> split <;> simp_all

lemma measurable_nextState (q : Params) (c : Config) (hR : 0 < q.R) (k : ℕ) :
    Measurable (fun z : OuterState q × (ℕ → Space q) => nextState q c k z.1 z.2) := by
  let E := OuterState q × (ℕ → Space q)
  have he : Measurable (fun z : E => scalarEstimate q c k z.2) :=
    (measurable_scalarEstimate q c hR k).comp measurable_snd
  have hc : Measurable (fun z : E => center q z.1) := measurable_fst.fst
  have hr : Measurable (fun z : E => radius q z.1) := measurable_fst.snd.fst
  have hs : Measurable (fun z : E => saved q z.1) := measurable_fst.snd.snd.fst
  have hf : Measurable (fun z : E => frozen q z.1) := measurable_fst.snd.snd.snd
  have ha : Measurable (fun z : E => if 0 ≤ scalarEstimate q c k z.2 then
      center q z.1-3*radius q z.1/8 else center q z.1+3*radius q z.1/8) :=
    Measurable.ite (measurableSet_le measurable_const he) (by fun_prop) (by fun_prop)
  have hfreeze : MeasurableSet {z : E | frozen q z.1 = true} := by
    change MeasurableSet ((fun z : E => frozen q z.1) ⁻¹' {true})
    exact hf (measurableSet_singleton true)
  have hb : Measurable (fun z : E => if frozen q z.1 then saved q z.1 else primalOutput q c z.1 z.2) :=
    Measurable.ite hfreeze hs (measurable_primalOutput q c hR)
  have ht : Measurable (fun z : E => decide (|scalarEstimate q c k z.2| ≤ q.ε/(2*radius q z.1))) := by
    apply measurable_to_bool
    have hineq : MeasurableSet {z : E | |scalarEstimate q c k z.2| ≤ q.ε/(2*radius q z.1)} :=
      measurableSet_le (continuous_abs.measurable.comp he)
        ((measurable_const : Measurable (fun _ : E => q.ε)).div (hr.const_mul 2))
    have heq : ((fun z : E => decide (|scalarEstimate q c k z.2| ≤ q.ε/(2*radius q z.1))) ⁻¹' {true}) =
        {z : E | |scalarEstimate q c k z.2| ≤ q.ε/(2*radius q z.1)} := by ext z; simp
    rw [heq]
    exact hineq
  have ho : Measurable (fun z : E => frozen q z.1 || decide (|scalarEstimate q c k z.2| ≤ q.ε/(2*radius q z.1))) :=
    (measurable_of_countable (fun z : Bool × Bool => z.1 || z.2)).comp (hf.prodMk ht)
  exact ha.prodMk ((by fun_prop : Measurable (fun z : E => 5*radius q z.1/8)).prodMk (hb.prodMk ho))

lemma measurable_queryFrom (q : Params) (c : Config) (hR : 0 < q.R)
    (remaining k t : ℕ) :
    Measurable (fun z : OuterState q × (ℕ → Space q) => queryFrom q c k remaining z.1 z.2 t) := by
  induction remaining generalizing k t with
  | zero => exact measurable_const
  | succ remaining ih =>
    by_cases hg : t < c.T*c.b
    · simp only [queryFrom, hg, ite_true]
      have hp := (continuous_generatorPoint (innerParams q c.α)
        (by dsimp [innerParams]; positivity) c.α (2/c.α) c.b (t/c.b)).measurable.comp
          (measurable_tail_stream q)
      exact (continuous_join q).measurable.comp
        ((show Measurable (fun z : OuterState q × (ℕ → Space q) => center q z.1) from measurable_fst.fst).prodMk
          (hp.comp measurable_snd))
    · by_cases he : t < epochCost c k
      · simpa only [queryFrom, hg, ite_false, he, ite_true] using measurable_scalarQuery q c hR k (t-c.T*c.b)
      · simp only [queryFrom, hg, ite_false, he]
        have hs : Measurable (fun z : OuterState q × (ℕ → Space q) => fun i => z.2 (epochCost c k+i)) := by
          exact Measurable.of_eval fun i => (measurable_pi_apply (epochCost c k+i)).comp measurable_snd
        exact (ih (k+1) (t-epochCost c k)).comp ((measurable_nextState q c hR k).prodMk hs)

lemma measurable_outputFrom (q : Params) (c : Config) (hR : 0 < q.R)
    (remaining k : ℕ) :
    Measurable (fun z : OuterState q × (ℕ → Space q) => outputFrom q c k remaining z.1 z.2) := by
  induction remaining generalizing k with
  | zero => exact measurable_fst.snd.snd.fst
  | succ remaining ih =>
    have hs : Measurable (fun z : OuterState q × (ℕ → Space q) => fun i => z.2 (epochCost c k+i)) :=
      Measurable.of_eval fun i => (measurable_pi_apply (epochCost c k+i)).comp measurable_snd
    exact (ih (k+1)).comp ((measurable_nextState q c hR k).prodMk hs)

end LongTails.Proofs.SpikedSoftCutMeasurable
