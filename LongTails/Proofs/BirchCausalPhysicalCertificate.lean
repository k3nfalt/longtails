import LongTails.Proofs.BirchCausalLedger

namespace LongTails.Proofs.BirchCausalPhysicalCertificate

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Algorithms.BirchCausalPhysical
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanUnused
open LongTails.Proofs.BirchNonEuclideanExtensions
open LongTails.Proofs.BirchCausalConstruction
open LongTails.Proofs.BirchCausalProgram
open LongTails.Proofs.BirchCausalOutputs
open LongTails.Proofs.BirchCausalPlans
open LongTails.Proofs.BirchCausalDerivation
open LongTails.Proofs.BirchCausalDiscarded
open LongTails.Proofs.BirchCausalLedger

lemma physicalGraph_properties {m : ℕ} (workers H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) (η : ℝ) (hw : 0 < workers) (hB : 0 < B)
    (ht : (canonicalTuning η B).Valid) (hp : ∀ job, (recipe job).Valid workers)
    (hc : ∀ job, (recipe job).calls = H)
    (hclean : Clean (codeSymbolic (canonicalTuning η B)
      (graphProgramCode H K B (physicalPlan H K B word recipe).nodes
        (physicalPlan H K B word recipe).main {}).2)) :
    let plan := physicalPlan H K B word recipe
    let base := (graphProgramCode H K B plan.nodes plan.main {}).2
    let final := ((physicalGraphCode H K B word recipe).run {}).2
    CodeValid workers (canonicalTuning η B) final ∧ Retains (canonicalTuning η B) base final ∧
      CodeExtends base final ∧ Clean (codeSymbolic (canonicalTuning η B) final) := by
  let t := canonicalTuning η B
  let plan := physicalPlan H K B word recipe
  let init := (localBatch 0 0 B).run {}
  let state := graphRun H 0 plan.nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
  let base := (graphProgramCode H K B plan.nodes plan.main {}).2
  have hi := physicalPlan_invariant workers H K B word recipe hw hp hc
  have hr := (initialized_runtime workers H B η ht hw plan.nodes hi.valid).1
  have hs := sendPoints_valid workers t state.1 plan.main (List.range (K + 1)) state.2 hw hr.valid hr.owned
  have ha := initialized_states_affine workers H B η ht hw hB plan.nodes hi.valid
  have hsym : codeSymbolic t base =
      { codeSymbolic t state.2 with next := (codeSymbolic t state.2).next + (K + 1) } := by
    change codeSymbolic t (sendPoints state.1 plan.main (List.range (K + 1)) state.2).2 = _
    simpa only [List.length_range] using sendPoints_symbolic t state.1 plan.main (List.range (K + 1)) state.2
  have ho : ∀ i, OwnedValid workers t base (state.1.states i) :=
    fun i => OwnedValid.retains workers t state.2 base _ (hr.owned i) hs.2.1
  have hax : ∀ i, ((codeSymbolic t base).points (state.1.states i).point).1 = 0 := by
    intro i
    rw [hsym]
    exact (ha i).1
  have hav : ∀ i, RawAffine ((codeSymbolic t base).vectors (state.1.states i).momentum) := by
    intro i
    rw [hsym]
    exact (ha i).2
  exact drainGraphs_properties workers H B η recipe state.1 plan.main
    (ignored (finalSchedule H K B word)) base ht hs.1 hclean
    (fun job _ => hp job) (fun job _ => ho _) (fun job _ => hax _) (fun job _ => hav _)

lemma physicalGraph_extension {m : ℕ} (workers H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) (η D V : ℝ) (hw : 0 < workers) (hB : 0 < B)
    (ht : (canonicalTuning η B).Valid) (hp : ∀ job, (recipe job).Valid workers)
    (hc : ∀ job, (recipe job).calls = H)
    (C : ProgramCertificate
      ((graphProgramTemplate H K B (physicalPlan H K B word recipe).nodes
        (physicalPlan H K B word recipe).main).instantiate (canonicalTuning η B)) K η D V)
    (hmain : C.main = (graphProgramCode H K B (physicalPlan H K B word recipe).nodes
      (physicalPlan H K B word recipe).main {}).1) :
    let a := (makeTemplate K (physicalGraphCode H K B word recipe)).instantiate (canonicalTuning η B)
    a.Legal workers ∧ Nonempty (ProgramCertificate a K η D V) := by
  let t := canonicalTuning η B
  let plan := physicalPlan H K B word recipe
  let base := graphProgramCode H K B plan.nodes plan.main {}
  let final := (physicalGraphCode H K B word recipe).run {}
  let a := (graphProgramTemplate H K B plan.nodes plan.main).instantiate t
  let b := (makeTemplate K (physicalGraphCode H K B word recipe)).instantiate t
  have hclean : Clean (codeSymbolic t base.2) := by
    refine ⟨C.sharp_only, C.query_linear, ?_⟩
    intro e he
    refine ⟨C.estimator_linear e he, ?_⟩
    rw [codeSymbolic_sharp_mass]
    exact C.estimator_mass e he
  have hprop := physicalGraph_properties workers H K B word recipe η hw hB ht hp hc hclean
  have hi := physicalPlan_invariant workers H K B word recipe hw hp hc
  let init := (localBatch 0 0 B).run {}
  let state := graphRun H 0 plan.nodes ⟨fun _ => ⟨0, 0, init.1⟩, 1, 0⟩ init.2
  have hr := (initialized_runtime workers H B η ht hw plan.nodes hi.valid).1
  have hs := sendPoints_valid workers t state.1 plan.main (List.range (K + 1)) state.2 hw hr.valid hr.owned
  have hmemb (k : ℕ) (hk : k ≤ K) : base.1 k ∈ (codeLayout t base.2).points 0 :=
    hs.2.2 k (List.mem_range.mpr (by omega))
  have hbound (k : ℕ) (hk : k ≤ K) : C.main k < (codeSymbolic t base.2).next := by
    rw [hmain]
    rw [← codeValid_symbolic_next workers t base.2 hs.1]
    exact (codeValid_register_bound workers t base.2 hs.1).1 0 _ (hmemb k hk)
  have hext : CertificateExtension a b C.main K :=
    clean_append_extension base.2 final.2 t a b C.main K rfl rfl hprop.2.2.1 hbound hprop.2.2.2 rfl (fun _ => rfl)
  refine ⟨⟨hprop.1.2, hw, ?_⟩, ⟨extendCertificate C hext⟩⟩
  intro j
  apply (hprop.2.1 0).1
  exact hmemb j.val (by have hj : j.val < K - 1 + 1 := j.isLt; omega)

lemma physicalGraph_certificate {m : ℕ} (workers H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) (η : ℝ)
    (hw : 0 < workers) (hH : 0 < H) (hK : 0 < K) (hη : η ≠ 0)
    (ht : (canonicalTuning η B).Valid) (hB : 2 ≤ B)
    (hgate : 4 * (H * (packetCutoff H B + 1)) ≤ B)
    (hp : ∀ job, (recipe job).Valid workers) (hc : ∀ job, (recipe job).calls = H) :
    let a := (makeTemplate K (physicalGraphCode H K B word recipe)).instantiate (canonicalTuning η B)
    a.Legal workers ∧ a.oracleCalls = B + H * (K + (ignored (finalSchedule H K B word)).length) ∧
      Nonempty (ProgramCertificate a K η
        ((((max (H - 1) (2 * (H * (packetCutoff H B + 1)) + 1) : ℕ) : ℝ) + B) / H) (1 / (B : ℝ))) := by
  let plan := physicalPlan H K B word recipe
  have hi := physicalPlan_invariant workers H K B word recipe hw hp hc
  let C := planCertificate workers H (packetCutoff H B) K B η plan ht hw hH hK hη hB hgate hi
  have he := physicalGraph_extension workers H K B word recipe η _ _ hw (by omega) ht hp hc C rfl
  refine ⟨he.1, ?_, he.2⟩
  rw [template_tuning_oracleCalls _ (canonicalTuning η B) (canonicalTuning 0 1)]
  exact physicalGraphCode_calls workers H K B word recipe hw hp hc

end LongTails.Proofs.BirchCausalPhysicalCertificate
