import LongTails.Proofs.BirchCausalDerivation
import LongTails.Proofs.BirchNonEuclideanUnused

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanUnused
open LongTails.Proofs.BirchCausalRecords
open LongTails.Proofs.BirchCausalOutputs
open LongTails.Proofs.BirchCausalConstruction
open LongTails.Proofs.BirchCausalProgram
open LongTails.Proofs.BirchCausalEncoding

namespace LongTails.Proofs.BirchCausalDiscarded

def RawAffine (v : LinearValue) : Prop := v.2 = 0 ∧ coefficientMass v.1 = 1

lemma ema_affine (α : ℝ) (q : ℕ) (v : LinearValue) (hv : RawAffine v) :
    RawAffine (α • (Finsupp.single q 1, 0) + (1 - α) • v) := by
  constructor
  · change α • (0 : ℕ →₀ ℝ) + (1 - α) • v.2 = 0
    rw [hv.1]
    simp
  · change coefficientMass (α • Finsupp.single q 1 + (1 - α) • v.1) = 1
    rw [map_add, map_smul, map_smul, coefficientMass_single, hv.2]
    simp

lemma merge_affine (l r c : LinearValue) (hl : RawAffine l) (hr : RawAffine r)
    (hc : RawAffine c) : RawAffine (l + r - c) := by
  constructor
  · change l.2 + r.2 - c.2 = 0
    rw [hl.1, hr.1, hc.1]
    simp
  · change coefficientMass (l.1 + r.1 - c.1) = 1
    rw [map_sub, map_add, hl.2, hr.2, hc.2]
    norm_num

structure AffineState (v : GraphValues LinearValue) : Prop where
  point : ∀ i, (v.points i).1 = 0
  momentum : ∀ i, RawAffine (v.momenta i)
  queryPoint : ∀ i < v.atoms, (v.queryPoints i).1 = 0
  queryMomentum : ∀ i < v.atoms, RawAffine (v.queryMomenta i)

lemma affine_initial (x v : LinearValue) (hx : x.1 = 0) (hv : RawAffine v) :
    AffineState (initialValues x v) := by
  exact ⟨fun _ => hx, fun _ => hv, fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim⟩

lemma affine_step (α γ : ℝ) (raw sharp : ℕ → ℕ) (node : GraphNode)
    (v : GraphValues LinearValue) (hv : AffineState v) :
    AffineState (valueStep α γ (fun i => (Finsupp.single (raw i) 1, 0))
      (fun i => (0, Finsupp.single (sharp i) 1)) node v) := by
  cases node with
  | query worker source =>
      constructor
      · intro i
        by_cases hi : i = v.next
        · subst i
          simp only [valueStep, Function.update_self]
          change (v.points source).1 + γ • (0 : ℕ →₀ ℝ) = 0
          rw [hv.point source]
          simp
        · simpa only [valueStep, Function.update_of_ne hi] using hv.point i
      · intro i
        by_cases hi : i = v.next
        · subst i
          simpa only [valueStep, Function.update_self] using
            ema_affine α (raw v.atoms) (v.momenta source) (hv.momentum source)
        · simpa only [valueStep, Function.update_of_ne hi] using hv.momentum i
      · intro i hi
        by_cases he : i = v.atoms
        · subst i
          simpa only [valueStep, Function.update_self] using hv.point source
        · have hi' : i < v.atoms := by change i < v.atoms + 1 at hi; omega
          simpa only [valueStep, Function.update_of_ne he] using hv.queryPoint i hi'
      · intro i hi
        by_cases he : i = v.atoms
        · subst i
          simpa only [valueStep, Function.update_self] using hv.momentum source
        · have hi' : i < v.atoms := by change i < v.atoms + 1 at hi; omega
          simpa only [valueStep, Function.update_of_ne he] using hv.queryMomentum i hi'
  | merge worker left right common =>
      constructor
      · intro i
        by_cases hi : i = v.next
        · subst i
          simp only [valueStep, Function.update_self]
          change (v.points left).1 + (v.points right).1 - (v.points common).1 = 0
          rw [hv.point left, hv.point right, hv.point common]
          simp
        · simpa only [valueStep, Function.update_of_ne hi] using hv.point i
      · intro i
        by_cases hi : i = v.next
        · subst i
          simpa only [valueStep, Function.update_self] using
            merge_affine _ _ _ (hv.momentum left) (hv.momentum right) (hv.momentum common)
        · simpa only [valueStep, Function.update_of_ne hi] using hv.momentum i
      · exact hv.queryPoint
      · exact hv.queryMomentum

lemma affine_fold (α γ : ℝ) (raw sharp : ℕ → ℕ) (nodes : List GraphNode)
    (v : GraphValues LinearValue) (hv : AffineState v) :
    AffineState (nodes.foldl (flip (valueStep α γ (fun i => (Finsupp.single (raw i) 1, 0))
      (fun i => (0, Finsupp.single (sharp i) 1)))) v) := by
  induction nodes generalizing v with
  | nil => exact hv
  | cons node rest ih => exact ih _ (affine_step α γ raw sharp node v hv)

lemma clean_from_trace_support (t : Tuning) (s r : CodeState) (α : ℝ)
    (values : GraphValues LinearValue) (raw sharp : ℕ → ℕ)
    (hc : Clean (codeSymbolic t s)) (he : CodeExtends s r)
    (hv : AffineState values) (ht : Trace t r values raw sharp α)
    (hs : Support t r values.atoms raw sharp
      (codeSymbolic t s).queries (codeSymbolic t s).sharps (codeSymbolic t s).units) :
    Clean (codeSymbolic t r) := by
  refine ⟨hs.unit_set.trans hc.units, ?_, ?_⟩
  · intro q hq
    rw [hs.query_set] at hq
    rcases mem_union.mp hq with hold | hnew
    · rw [(codeExtends_symbolic t s r he q ((code_beforeNext t s).1 q hold)).2.2.1]
      exact hc.queries q hold
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hnew
      rw [ht.point i (mem_range.mp hi)]
      exact hv.queryPoint i (mem_range.mp hi)
  · intro e he'
    rw [hs.sharp_set] at he'
    rcases mem_union.mp he' with hold | hnew
    · rw [(codeExtends_symbolic t s r he e ((code_beforeNext t s).2 e hold)).2.2.2]
      exact hc.sharps e hold
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hnew
      rw [ht.input i (mem_range.mp hi)]
      exact ema_affine α (raw i) (values.queryMomenta i) (hv.queryMomentum i (mem_range.mp hi))


lemma graphCode_extends (H round : ℕ) (nodes : List GraphNode) (output coordinator x m : ℕ) :
    BuildExtends (graphCode H round nodes output coordinator x m) := by
  intro s
  let initial : GraphState := ⟨fun _ => ⟨coordinator, x, m⟩, 1, 0⟩
  let z := graphRun H round nodes initial s
  change CodeExtends s (sendState (z.1.states output).worker coordinator
    (z.1.states output).point (z.1.states output).momentum z.2).2
  exact codeExtends_trans s z.2 _ (graphRun_extends H round nodes initial s)
    (sendState_extends _ _ _ _ z.2)

lemma valueFold_atoms {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α γ : ℝ) (raw sharp : ℕ → E) (nodes : List GraphNode) (v : GraphValues E) :
    (nodes.foldl (flip (valueStep α γ raw sharp)) v).atoms = v.atoms + (nodes.map GraphNode.calls).sum := by
  induction nodes generalizing v with
  | nil => simp
  | cons node rest ih =>
      rw [List.foldl_cons, ih]
      cases node <;> simp [flip, valueStep, GraphNode.calls, Nat.add_assoc]

lemma graphCode_clean (workers H round B output coordinator x m : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (nodes : List GraphNode)
    (hw : ∀ node ∈ nodes, node.worker < workers) (s : CodeState)
    (hs : CodeValid workers (canonicalTuning η B) s) (hc : coordinator < workers)
    (hx : x ∈ (codeLayout (canonicalTuning η B) s).points coordinator)
    (hm : m ∈ (codeLayout (canonicalTuning η B) s).vectors coordinator)
    (hclean : Clean (codeSymbolic (canonicalTuning η B) s))
    (hpx : ((codeSymbolic (canonicalTuning η B) s).points x).1 = 0)
    (hpm : RawAffine ((codeSymbolic (canonicalTuning η B) s).vectors m)) :
    Clean (codeSymbolic (canonicalTuning η B) (graphCode H round nodes output coordinator x m s).2) := by
  let t := canonicalTuning η B
  let initial : GraphState := ⟨fun _ => ⟨coordinator, x, m⟩, 1, 0⟩
  let labels0 : GraphLabels := ⟨s.next, 0, fun _ => 0, fun _ => 0⟩
  let labels := labelFold nodes labels0
  let values0 := initialValues ((codeSymbolic t s).points x) ((codeSymbolic t s).vectors m)
  let values := nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
    (fun i => (Finsupp.single (labels.raw i) 1, 0))
    (fun i => (0, Finsupp.single (labels.sharp i) 1)))) values0
  let z := graphRun H round nodes initial s
  let final := (graphCode H round nodes output coordinator x m s).2
  have htrace : Trace t final values labels.raw labels.sharp (1 / (B : ℝ)) :=
    (graphCode_runtime workers H round B output coordinator x m η ht nodes hw s hs hc hx hm).2.2
  have hvalues : AffineState values := affine_fold _ _ labels.raw labels.sharp nodes values0
    (affine_initial _ _ hpx hpm)
  have hs0 : Support t s labels0.atoms labels.raw labels.sharp
      (codeSymbolic t s).queries (codeSymbolic t s).sharps (codeSymbolic t s).units := by
    constructor <;> simp only [labels0, range_zero, image_empty, union_empty]
  have hsupport := graphFold_support H round nodes initial s t labels0 labels.raw labels.sharp
    _ _ _ (codeValid_symbolic_next workers t s hs) rfl hs0 (labelsMatch_final nodes labels0)
  have ha : values.atoms = labels.atoms := by
    rw [valueFold_atoms, labelFold_atoms]
    rfl
  have hsend := sendState_symbolic t (z.1.states output).worker coordinator
    (z.1.states output).point (z.1.states output).momentum z.2
  have hf : Support t final values.atoms labels.raw labels.sharp
      (codeSymbolic t s).queries (codeSymbolic t s).sharps (codeSymbolic t s).units := by
    constructor
    · change (codeSymbolic t (sendState (z.1.states output).worker coordinator
        (z.1.states output).point (z.1.states output).momentum z.2).2).queries = _
      rw [hsend, ha]
      exact hsupport.query_set
    · change (codeSymbolic t (sendState (z.1.states output).worker coordinator
        (z.1.states output).point (z.1.states output).momentum z.2).2).sharps = _
      rw [hsend, ha]
      exact hsupport.sharp_set
    · change (codeSymbolic t (sendState (z.1.states output).worker coordinator
        (z.1.states output).point (z.1.states output).momentum z.2).2).units = _
      rw [hsend]
      exact hsupport.unit_set
  exact clean_from_trace_support t s final _ values labels.raw labels.sharp hclean
    (graphCode_extends H round nodes output coordinator x m s) hvalues htrace hf

lemma batchMomentum_affine (B : ℕ) (hB : 0 < B) : RawAffine (batchMomentum B) := by
  refine ⟨batchMomentum_sharp B, ?_⟩
  simp only [batchMomentum, linearValue_fst_smul, linearValue_fst_sum, rawBasis,
    map_smul, map_sum, coefficientMass_single, sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact one_div_mul_cancel (by exact_mod_cast (Nat.ne_zero_of_lt hB))

lemma initialized_states_affine (workers H B : ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid)
    (hw : 0 < workers) (hB : 0 < B) (nodes : List GraphNode) (hvalid : GraphValidFrom workers {} nodes) :
    let init := (localBatch 0 0 B).run {}
    let z := graphRun H 0 nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
    ∀ i, ((codeSymbolic (canonicalTuning η B) z.2).points (z.1.states i).point).1 = 0 ∧
      RawAffine ((codeSymbolic (canonicalTuning η B) z.2).vectors (z.1.states i).momentum) := by
  let init := (localBatch 0 0 B).run {}
  let labels := labelFold nodes ⟨init.2.next, 0, fun _ => 0, fun _ => 0⟩
  have hr := (initialized_runtime workers H B η ht hw nodes hvalid).1
  have hv := affine_fold (1 / (B : ℝ)) (1 / (H : ℝ) * η) labels.raw labels.sharp nodes
    (initialValues 0 (batchMomentum B)) (affine_initial 0 (batchMomentum B) rfl (batchMomentum_affine B hB))
  dsimp only
  intro i
  rw [hr.reads.1 i, hr.reads.2 i]
  exact ⟨hv.point i, hv.momentum i⟩

end LongTails.Proofs.BirchCausalDiscarded
