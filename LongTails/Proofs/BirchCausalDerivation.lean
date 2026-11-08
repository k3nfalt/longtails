import LongTails.Proofs.BirchCausalOutputs
import LongTails.Proofs.BirchCausalCertificate

namespace LongTails.Proofs.BirchCausalDerivation

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchCausalMerges
open LongTails.Proofs.BirchCausalStates
open LongTails.Proofs.BirchCausalRecords
open LongTails.Proofs.BirchCausalProgram
open LongTails.Proofs.BirchCausalPlans
open LongTails.Proofs.BirchCausalOutputs
open LongTails.Proofs.BirchCausalEncoding
open LongTails.Proofs.BirchCausalCertificate

lemma plan_encoding (workers H R K B : ℕ) (η : ℝ) (plan : GraphPlan)
    (ht : (canonicalTuning η B).Valid) (hw : 0 < workers) (hK : 0 < K)
    (hplan : PlanInvariant workers H R K plan) :
    let history := graphHistory plan.nodes
    let hpast := completeHistory_past history (graphHistory_invariant plan.nodes)
    let init := (localBatch 0 0 B).run {}
    let labels := labelFold plan.nodes ⟨init.2.next, 0, fun _ => 0, fun _ => 0⟩
    let main := (graphProgramCode H K B plan.nodes plan.main {}).1
    Encoding ((graphProgramTemplate H K B plan.nodes plan.main).instantiate (canonicalTuning η B))
      (completeHistory history) hpast H K B η main labels.raw labels.sharp := by
  let t := canonicalTuning η B
  let history := graphHistory plan.nodes
  let hh := graphHistory_invariant plan.nodes
  let hpast := completeHistory_past history hh
  let init := (localBatch 0 0 B).run {}
  let labels0 : GraphLabels := ⟨init.2.next, 0, fun _ => 0, fun _ => 0⟩
  let labels := labelFold plan.nodes labels0
  let initial : GraphState := ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩
  let z := graphRun H 0 plan.nodes initial init.2
  let values := plan.nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
    (fun i => rawBasis (labels.raw i)) (fun i => sharpBasis (labels.sharp i))))
    (initialValues 0 (batchMomentum B))
  let a := (graphProgramTemplate H K B plan.nodes plan.main).instantiate t
  let main := (graphProgramCode H K B plan.nodes plan.main {}).1
  have hr : RuntimeInvariant workers B η z.1 z.2 labels values labels.raw labels.sharp :=
    (initialized_runtime workers H B η ht hw plan.nodes hplan.valid).1
  have hm : ModelInvariant history values 0 (batchMomentum B) (1 / (B : ℝ))
      (1 / (H : ℝ) * η) (fun i => rawBasis (labels.raw i)) (fun i => sharpBasis (labels.sharp i)) :=
    (initialized_runtime workers H B η ht hw plan.nodes hplan.valid).2
  have ha : values.atoms = K * H := hm.atoms.trans hplan.atoms
  have hl : labels.atoms = K * H := hr.label_atoms.trans ha
  have hi := initialBatch_valid workers B t hw
  have hsets := initialBatch_sets B t
  have hn : init.2.next = (codeSymbolic t init.2).next := codeValid_symbolic_next workers t init.2 hi.1
  have hsym : a.symbolic = { codeSymbolic t z.2 with next := (codeSymbolic t z.2).next + (K + 1) } := by
    change codeSymbolic t (sendPoints z.1 plan.main (List.range (K + 1)) z.2).2 = _
    simpa only [List.length_range] using sendPoints_symbolic t z.1 plan.main (List.range (K + 1)) z.2
  have hs0 : Support t init.2 labels0.atoms labels.raw labels.sharp
      ((range B).image (fun j => 1 + j)) ∅ ∅ := by
    constructor
    · simpa only [labels0, range_zero, image_empty, union_empty] using hsets.1
    · simpa only [labels0, range_zero, image_empty, empty_union] using hsets.2.1
    · exact hsets.2.2
  have hs : Support t z.2 labels.atoms labels.raw labels.sharp
      ((range B).image (fun j => 1 + j)) ∅ ∅ :=
    graphFold_support H 0 plan.nodes initial init.2 t labels0 labels.raw labels.sharp
      _ ∅ ∅ hn rfl hs0 (labelsMatch_final plan.nodes labels0)
  have hf : LabelInvariant init.2.next labels := labelFold_fresh init.2.next plan.nodes
  have hraw : Set.InjOn labels.raw (Set.Iio (K * H)) := by
    intro i hi j hj he
    exact hf.2.1.injective i j (by rwa [hl]) (by rwa [hl]) he
  have hsharp : Set.InjOn labels.sharp (Set.Iio (K * H)) := by
    intro i hi j hj he
    exact hf.2.2.injective i j (by rwa [hl]) (by rwa [hl]) he
  have hsep : ∀ q, q < K * H → labels.raw q ∉ (range B).image (fun j => 1 + j) := by
    intro q hq hbad
    obtain ⟨j, hj, he⟩ := mem_image.mp hbad
    have hlow := hf.2.1.lower q (by rwa [hl])
    have hnext : init.2.next = 1 + B + 1 := localBatch_next 0 0 B {}
    rw [hnext, ← he] at hlow
    have := mem_range.mp hj
    omega
  refine ⟨hraw, hsharp, hsep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change a.symbolic.queries = _
    rw [hsym]
    exact hs.query_set.trans (by rw [hl])
  · change a.symbolic.sharps = _
    rw [hsym]
    simpa only [hl, empty_union] using hs.sharp_set
  · change a.symbolic.units = _
    rw [hsym]
    exact hs.unit_set
  · intro n hn'
    change a.symbolic.sharpInputs (labels.sharp n) = _
    rw [hsym]
    change (codeSymbolic t z.2).sharpInputs (labels.sharp n) = _
    rw [hr.trace.input n (by rwa [ha])]
    rw [model_query_coefficients history values 0 (batchMomentum B) _ _ _ _ hh hm n (by rwa [hplan.atoms])]
    rfl
  · intro j hj
    change a.symbolic.queryPoints (1 + j) = _
    rw [hsym]
    change (codeSymbolic t z.2).queryPoints (1 + j) = _
    have hbound : 1 + j < (codeSymbolic t init.2).next := by
      rw [← hn]
      have hn' : init.2.next = 1 + B + 1 := localBatch_next 0 0 B {}
      rw [hn']
      omega
    rw [(codeExtends_symbolic t init.2 z.2 (graphRun_extends H 0 plan.nodes initial init.2) _ hbound).2.2.1]
    exact initialBatch_queryPoints B t j hj
  · intro q hq
    change a.symbolic.queryPoints (labels.raw q) = _
    rw [hsym]
    change (codeSymbolic t z.2).queryPoints (labels.raw q) = _
    rw [hr.trace.point q (by rwa [ha]), hm.queryPoints q (by rwa [hplan.atoms])]
    simp only [completeHistory, show q < (graphHistory plan.nodes).atoms by rwa [hplan.atoms], ite_true, zero_add]
    rfl
  · intro k hk
    change a.symbolic.points ((z.1.states (plan.main k)).point) = _
    rw [hsym]
    change (codeSymbolic t z.2).points ((z.1.states (plan.main k)).point) = _
    rw [hr.reads.1, hm.points, hplan.main_history k hk, zero_add]
    rfl
  · exact graphProgram_output_zero H K B plan.nodes plan.main hplan.main_zero
  · change K - 1 + 1 = K
    omega
  · intro j
    rfl

noncomputable def planCertificate (workers H R K B : ℕ) (η : ℝ) (plan : GraphPlan)
    (ht : (canonicalTuning η B).Valid) (hw : 0 < workers) (hH : 0 < H) (hK : 0 < K)
    (hη : η ≠ 0) (hB : 2 ≤ B) (hr : 4 * (H * (R + 1)) ≤ B)
    (hplan : PlanInvariant workers H R K plan) :
    ProgramCertificate
      ((graphProgramTemplate H K B plan.nodes plan.main).instantiate (canonicalTuning η B)) K η
      ((((max (H - 1) (2 * (H * (R + 1)) + 1) : ℕ) : ℝ) + B) / H) (1 / (B : ℝ)) := by
  let history := graphHistory plan.nodes
  let hh := graphHistory_invariant plan.nodes
  have he := plan_encoding workers H R K B η plan ht hw hK hplan
  exact Encoding.certificate _ (completeHistory history) (completeHistory_past history hh)
    H K B (H * (R + 1)) η _ _ _ he hH hK hη hB hr
    (plan_complete_recent workers H R K plan hplan) (completeHistory_closed history hh)

lemma planTemplate_constructed (workers H R K B : ℕ) (η : ℝ)
    (packet : ℕ → PacketExpr) (source : ℕ → ℕ)
    (ht : (canonicalTuning η B).Valid) (hw : 0 < workers) (hH : 0 < H) (hK : 0 < K)
    (hη : η ≠ 0) (hB : 2 ≤ B) (hr : 4 * (H * (R + 1)) ≤ B)
    (hp : ∀ k, (packet k).Valid workers) (hc : ∀ k, (packet k).calls = H)
    (hs : ∀ k, source k ≤ k) (hage : ∀ k, k - source k ≤ R) :
    let a := (planTemplate H K B packet source).instantiate (canonicalTuning η B)
    a.Legal workers ∧ a.oracleCalls = B + K * H ∧
      Nonempty (ProgramCertificate a K η
        ((((max (H - 1) (2 * (H * (R + 1)) + 1) : ℕ) : ℝ) + B) / H) (1 / (B : ℝ))) := by
  let plan := planRun packet source K
  have hi := planRun_invariant workers H R K packet source hw hp hc hs hage
  refine ⟨graphProgram_legal workers H K B η ht hw plan.nodes plan.main hi.valid, ?_,
    ⟨planCertificate workers H R K B η plan ht hw hH hK hη hB hr hi⟩⟩
  change ((graphProgramTemplate H K B plan.nodes plan.main).instantiate _).oracleCalls = _
  rw [graphProgram_calls, ← graphHistory_atoms, hi.atoms]

end LongTails.Proofs.BirchCausalDerivation
