import LongTails.Proofs.BirchCollectionNoise
import LongTails.Proofs.BirchCollectionBlocks

namespace LongTails.Proofs.BirchCollectionTrajectory

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionSampling
open LongTails.Proofs.BirchCollectionWeights
open LongTails.Proofs.BirchCollectionEvaluation
open LongTails.Proofs.BirchCollectionBlocks
open LongTails.Proofs.BirchNonEuclideanEnergy
open LongTails.Proofs.BirchCausalTransport
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)

noncomputable def sharpVector (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) : Point p.d :=
  (executed p lmo response).vectors ((compiled p).registers.sharp (p.ordering.label n))

noncomputable def sourcePoint (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) : Point p.d :=
  (executed p lmo response).points ((compiled p).registers.point
    ((compiled p).trace.directions (p.ordering.label n)).source)

noncomputable def mainPoint (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (k : ℕ) : Point p.d :=
  (executed p lmo response).points ((compiled p).registers.point
    ((compiled p).trace.markers[k]?.getD 0))

lemma logical_source_point (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    sourcePoint p lmo response n = p.x0 + (1 / (20 * p.L)) •
      ∑ j ∈ p.ordering.history (compiled p).trace n,
        p.ordering.movement (compiled p).trace j • sharpVector p lmo response j := by
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hm : ∀ a ∈ (compiled p).trace.markers, a < (compiled p).trace.nextState := by
    simpa only [compiled, compile_trace] using markers_bound_run p.workers p.events he
  have hd := hh.direction _ (ho.2.2.2.2.2.2.1 n hn)
  have hhistory := ordering_query_history (compiled p).trace p.ordering K hh ho hm n hn
  have hindex (j : ℕ) (hj : j ∈ p.ordering.history (compiled p).trace n) :
      j < p.ordering.labels.length :=
    (mem_range.mp (ho.2.2.2.2.2.2.2.2 n hj)).trans hn
  have hs := executed_point p lmo response he _ hd.1
  dsimp only at hs
  erw [← hd.2.1, hhistory, sum_image] at hs
  · unfold sourcePoint
    rw [hs, smul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    simp [Ordering.movement, hindex j hj, sharpVector, smul_smul]
  · intro i hi j hj heq
    exact label_injective p.ordering ho.2.1 (hindex i hi) (hindex j hj) heq

lemma logical_main_point (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (k : ℕ) (hk : k ≤ K) :
    mainPoint p lmo response k = p.x0 + (1 / (20 * p.L)) •
      ∑ j ∈ range (p.ordering.cut k),
        p.ordering.movement (compiled p).trace j • sharpVector p lmo response j := by
  have hm : ∀ a ∈ (compiled p).trace.markers, a < (compiled p).trace.nextState := by
    simpa only [compiled, compile_trace] using markers_bound_run p.workers p.events he
  have hklen : k < (compiled p).trace.markers.length := by rw [ho.2.2.1]; omega
  have hkmem : (compiled p).trace.markers[k]?.getD 0 ∈ (compiled p).trace.markers := by
    simp [hklen]
  have hcut := cut_mono (compiled p).trace p.ordering K ho k K hk le_rfl
  rw [ho.2.2.2.2.1] at hcut
  have hindex (j : ℕ) (hj : j ∈ range (p.ordering.cut k)) : j < p.ordering.labels.length :=
    (mem_range.mp hj).trans_le hcut
  have hs := executed_point p lmo response he _ (hm _ hkmem)
  dsimp only at hs
  erw [ho.2.2.2.2.2.2.2.1 k hk, sum_image] at hs
  · unfold mainPoint
    rw [hs, smul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    simp [Ordering.movement, hindex j hj, sharpVector, smul_smul]
  · intro i hi j hj heq
    exact label_injective p.ordering ho.2.1 (hindex i hi) (hindex j hj) heq

lemma logical_main_initial (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K) :
    mainPoint p lmo response 0 = p.x0 := by
  rw [logical_main_point p lmo response he K ho 0 (Nat.zero_le _), ho.2.2.2.1]
  simp

lemma logical_main_chain (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (k : ℕ) (hk : k < K) :
    mainPoint p lmo response (k + 1) = mainPoint p lmo response k + (1 / (20 * p.L)) •
      ∑ j ∈ (range p.ordering.labels.length).filter (fun j => owner p.ordering K j = k),
        p.ordering.movement (compiled p).trace j •
          (dualNorm p.N (estimatorVector p lmo response j) • lmo (estimatorVector p lmo response j)) := by
  rw [owner_filter (compiled p).trace p.ordering K ho k hk]
  have hsharp (j : ℕ) (hj : j ∈ Ico (p.ordering.cut k) (p.ordering.cut (k + 1))) :
      sharpVector p lmo response j =
        dualNorm p.N (estimatorVector p lmo response j) • lmo (estimatorVector p lmo response j) := by
    have hcut := cut_mono (compiled p).trace p.ordering K ho (k + 1) K (by omega) le_rfl
    rw [ho.2.2.2.2.1] at hcut
    exact executed_sharp p lmo response he _ (ho.2.2.2.2.2.2.1 j
      ((mem_Ico.mp hj).2.trans_le hcut))
  have heq : (∑ j ∈ Ico (p.ordering.cut k) (p.ordering.cut (k + 1)),
      p.ordering.movement (compiled p).trace j •
        (dualNorm p.N (estimatorVector p lmo response j) • lmo (estimatorVector p lmo response j))) =
      ∑ j ∈ Ico (p.ordering.cut k) (p.ordering.cut (k + 1)),
        p.ordering.movement (compiled p).trace j • sharpVector p lmo response j := by
    exact sum_congr rfl (fun j hj => by rw [hsharp j hj])
  rw [heq, logical_main_point p lmo response he K ho (k + 1) (by omega),
    logical_main_point p lmo response he K ho k hk.le,
    sum_Ico_eq_sub _ (ho.2.2.2.2.2.1 k hk).le, smul_sub]
  abel

lemma sum_subset_indicator {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s t : Finset ℕ) (hst : s ⊆ t) (w : ℕ → ℝ) (v : ℕ → E) :
    (∑ j ∈ s, w j • v j) = ∑ j ∈ t, (if j ∈ s then w j else 0) • v j := by
  classical
  calc
    _ = ∑ j ∈ s, (if j ∈ s then w j else 0) • v j :=
      sum_congr rfl (fun j hj => by simp [hj])
    _ = _ := sum_subset hst (fun j _ hj => by simp [hj])

lemma logical_displacement (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K : ℕ) (ho : p.ordering.Valid (compiled p).trace K)
    (n q : ℕ) (hn : n < p.ordering.labels.length) (hq : q ≤ n) :
    sourcePoint p lmo response q - mainPoint p lmo response (owner p.ordering K n) =
      (1 / (20 * p.L)) • ∑ t ∈ range p.ordering.labels.length,
        (p.ordering.movement (compiled p).trace t *
          ((if t ∈ p.ordering.history (compiled p).trace q then (1 : ℝ) else 0) -
            (if t < start p.ordering K n then 1 else 0))) • sharpVector p lmo response t := by
  have hb := owner_bounds (compiled p).trace p.ordering K ho n hn
  have hqN : q < p.ordering.labels.length := hq.trans_lt hn
  have hhist : p.ordering.history (compiled p).trace q ⊆ range p.ordering.labels.length :=
    (ho.2.2.2.2.2.2.2.2 q).trans (range_mono hqN.le)
  have hprefix : range (p.ordering.cut (owner p.ordering K n)) ⊆
      range p.ordering.labels.length := range_mono (hb.2.1.trans hn.le)
  rw [logical_source_point p lmo response he K ho q hqN,
    logical_main_point p lmo response he K ho _ hb.1.le,
    sum_subset_indicator _ _ hhist, sum_subset_indicator _ _ hprefix]
  simp only [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib, ← sub_smul]
  congr 1
  apply sum_congr rfl
  intro t _
  simp only [mem_range, start, hn, ite_true]
  congr 1
  split_ifs <;> ring

lemma logical_gradient_drift (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hL : 0 < p.L)
    (hlmo : IsBallLMO p.N 1 lmo) (f : Point p.d → ℝ)
    (hlip : ∀ x y, dualNorm p.N (gradient f x - gradient f y) ≤ p.L * p.N (x - y))
    (n : ℕ) (hn : n < p.ordering.labels.length) :
    let W := row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2
    dualNorm p.N (∑ q ∈ range (n + 1), W n q •
      (gradient f (sourcePoint p lmo response q) -
        gradient f (mainPoint p lmo response (owner p.ordering K n)))) ≤
      (1 / (20 * p.L)) * p.L * ∑ t ∈ range p.ordering.labels.length,
        (p.ordering.movement (compiled p).trace t *
          transportMass (p.ordering.history (compiled p).trace) (start p.ordering K n) n t 0 (W n)) *
          dualNorm p.N (estimatorVector p lmo response t) := by
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hw := ordering_parameters _ _ K hp hc hs.1
  have hr := structural_row_bounds _ _ _ K B hp hc hh hs
  let W := row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2
  have hsharp (t : ℕ) (ht : t ∈ range p.ordering.labels.length) :
      p.N (sharpVector p lmo response t) ≤ dualNorm p.N (estimatorVector p lmo response t) := by
    have h := executed_sharp p lmo response he _ (hs.1.2.2.2.2.2.2.1 t (mem_range.mp ht))
    change sharpVector p lmo response t = _ at h
    rw [h]
    exact sharp_direction_bound hR hlmo _
  have hd := gradient_transport hR hL.le (by positivity : 0 ≤ (1 / (20 * p.L))) hlip
    (range (n + 1)) (range p.ordering.labels.length) (W n)
    (fun q t => p.ordering.movement (compiled p).trace t *
      ((if t ∈ p.ordering.history (compiled p).trace q then (1 : ℝ) else 0) -
        (if t < start p.ordering K n then 1 else 0)))
    (sourcePoint p lmo response) (mainPoint p lmo response (owner p.ordering K n))
    (sharpVector p lmo response) (fun t => dualNorm p.N (estimatorVector p lmo response t)) hsharp
    (fun q hq => logical_displacement p lmo response he K hs.1 n q hn
      (by have := mem_range.mp hq; omega))
  dsimp only
  convert hd using 1
  congr 1
  apply sum_congr rfl
  intro t _
  congr 1
  simp only [transportMass, zero_mul, zero_add, abs_mul, abs_of_nonneg ((hw t).1),
    ← displacement_eq_abs, mul_sum]
  apply sum_congr rfl
  intro q _
  rw [abs_of_nonneg (hr.1 n q)]
  ring

lemma row_sum_extend {E : Type*} [AddCommMonoid E]
    (s : TraceState) (o : CollectionOrdering) (hpast : ∀ n, o.history s n ⊆ range n)
    (n : ℕ) (hn : n < o.labels.length) (F : ℝ → ℕ → E) (hzero : ∀ q, F 0 q = 0) :
    (∑ q ∈ range (n + 1), F (row s o hpast n q) q) =
      ∑ q ∈ range o.labels.length, F (row s o hpast n q) q := by
  apply sum_subset (range_mono (by omega))
  intro q _ hq
  have hqn : ¬q ≤ n := by simp only [mem_range] at hq; omega
  simp only [row, hn, ite_true, hqn, ite_false, hzero]

lemma logical_energy (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B)
    (I : OracleTemplate.Rennala.Instance p.d)
    (hf : LongTails.Setups.BirchNonEuclidean.Objective (native p) I)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hL : 0 < p.L) (hlmo : IsBallLMO p.N 1 lmo) :
    let W := row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2
    (∑ k ∈ range K, mass (compiled p).trace p.ordering k *
      dualNorm p.N (gradient I.f (mainPoint p lmo response k)) ^ 2) ≤
      6 * p.Δ / (1 / (20 * p.L)) +
        16 * ∑ n ∈ range p.ordering.labels.length, p.ordering.movement (compiled p).trace n *
          dualNorm p.N (∑ q ∈ range (n + 1), W n q •
            (meanVector p lmo response q - gradient I.f (sourcePoint p lmo response q))) ^ 2 := by
  have hp : CollectionParameters (compiled p).trace := by
    simpa only [compiled, compile_trace] using collectionParameters_run p.workers p.events he
  have hc : CompletedLedger (compiled p).trace := by
    simpa only [compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hh : Histories (compiled p).trace := by
    simpa only [compiled, compile_trace] using histories_run p.workers p.events he
  have hw := ordering_parameters _ _ K hp hc hs.1
  have hr := structural_row_bounds _ _ _ K B hp hc hh hs
  have ht := structural_transport _ _ _ K B hp hc hh hs
  let W := row (compiled p).trace p.ordering hs.1.2.2.2.2.2.2.2.2
  let C := fun n t => p.ordering.movement (compiled p).trace t *
    transportMass (p.ordering.history (compiled p).trace) (start p.ordering K n) n t 0 (W n)
  have hstep : (1 / (20 * p.L)) * p.L * p.controls.upperMass ≤ 1 / 2 := by
    have hc1 := hs.2.1.2.2.1
    field_simp
    nlinarith
  have hsmall : (1 / (20 * p.L)) * p.L * 5 ≤ 1 / 4 := by
    field_simp
    norm_num
  have henergy := LongTails.Proofs.BirchRetainedEnergy.trajectory_energy (Δ := p.Δ) hR hdef hlmo hL.le
    (by positivity : 0 < (1 / (20 * p.L))) (by norm_num : (0 : ℝ) ≤ 5)
    (hs.2.1.1.le.trans hs.2.1.2.1) hstep hsmall hf.differentiable hf.smooth
    (range p.ordering.labels.length) (range p.ordering.labels.length) K (owner p.ordering K)
    (p.ordering.movement (compiled p).trace) (mass (compiled p).trace p.ordering) W C
    (meanVector p lmo response) (sourcePoint p lmo response) (mainPoint p lmo response)
    (estimatorVector p lmo response) (fun j _ => (hw j).1)
    (fun j hj => (owner_bounds _ _ K hs.1 j (mem_range.mp hj)).1)
    (fun k hk => by rw [owner_filter _ _ K hs.1 k hk]; rfl)
    (fun k hk => hs.2.2.2.2.2.1 k hk) (logical_main_chain p lmo response he K hs.1)
    (by
      rw [logical_main_initial p lmo response he K hs.1]
      exact (sub_le_sub_left (hf.lower _) _).trans hf.gap)
    (fun n hn => by
      rw [logical_estimator_expansion p lmo response he K B hs n (mem_range.mp hn)]
      exact row_sum_extend _ _ _ n (mem_range.mp hn) (fun a q => a • meanVector p lmo response q)
        (fun _ => zero_smul _ _))
    (fun n hn => by
      rw [← row_sum_extend _ _ _ n (mem_range.mp hn) (fun a _ => a) (fun _ => rfl)]
      exact hr.2.2.1 n)
    (fun n _ t _ => ht.1 n t)
    (fun n hn => by
      rw [← row_sum_extend _ _ _ n (mem_range.mp hn)
        (fun a q => a • (gradient I.f (sourcePoint p lmo response q) -
          gradient I.f (mainPoint p lmo response (owner p.ordering K n)))) (fun _ => zero_smul _ _)]
      exact logical_gradient_drift p lmo response he K B hs hR hL hlmo I.f hf.smooth n
        (mem_range.mp hn)) ht.2
  dsimp only
  convert henergy using 1
  congr 2
  apply sum_congr rfl
  intro n hn
  rw [← row_sum_extend _ _ _ n (mem_range.mp hn)
    (fun a q => a • (meanVector p lmo response q - gradient I.f (sourcePoint p lmo response q)))
    (fun _ => zero_smul _ _)]

end LongTails.Proofs.BirchCollectionTrajectory
