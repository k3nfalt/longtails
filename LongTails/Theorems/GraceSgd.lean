import LongTails.Setups.GraphBandwidthSmoothNonconvex
import LongTails.Proofs.GraceSgdBudget

namespace LongTails.Theorems.GraceSgd

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceGraph (Link)

noncomputable def budget (p : Params) : Time :=
  let B := max 1 ⌈256 * p.σ^2 / p.ε⌉₊
  let t := clockBits + Nat.size B
  let w := 32 + 4 * Nat.log2 (2 + p.d + ⌈2 * p.L * p.Δ / p.ε⌉₊ + ⌈p.σ^2 / p.ε⌉₊)
  let α (S : Finset (Fin p.n)) : Time :=
    ⨅ C : {C : Finset (Fin p.n) // (S ∩ C).Nonempty ∧ (S \ C).Nonempty},
      ∑ e : Link p, if (e.val.1 ∈ C.val ↔ e.val.2 ∈ C.val) then 0 else p.b e.val.1 e.val.2
  let m := Fintype.card (Link p)
  let P : Time := 16 * (p.d * (w + t) + t * (m + 1) * p.n : ℕ)
  (⌈32 * p.L * p.Δ / p.ε⌉₊ - 1 : ℕ) * ⨅ S : {S : Finset (Fin p.n) // S.Nonempty},
    ((B + S.val.card : ℕ) : Time) / (∑ i ∈ S.val, (p.h i)⁻¹) +
      if S.val.card ≤ 1 then 0 else
        (P : Time) / α S.val

theorem result : DistributedTemplate.TimedConvergence
    LongTails.Setups.GraphBandwidthSmoothNonconvex.spec budget := by
  classical
  choose S r A h using Proofs.GraceSgdBudget.select_routes
  let alg := fun (p : Params) => if hp : spec.valid p then Algorithms.GraceSgd.algorithm (A p hp) (budget p)
    else Algorithms.GraceSgd.algorithm (Proofs.GraceSgdBudget.solo p 0) (budget p)
  refine ⟨alg,?_⟩
  intro p hp
  change Params at p
  change spec.allowedAlgorithm p (alg p) ∧ _
  have he : alg p = Algorithms.GraceSgd.algorithm (A p hp) (budget p) := by simp [alg,hp]
  change spec.allowedAlgorithm p (alg p) ∧ ∀ f O, spec.admissible p f O →
    (∀ᵐ seed ∂(law O (alg p) : Measure _), FiniteEvents O (alg p) (budget p) seed) ∧
      spec.successful p f (fun seed => execute O (alg p) (budget p) seed.1 seed.2) (law O (alg p))
  rw [he]
  let U := (S p hp).val
  let route := A p hp
  have hU := (S p hp).property
  obtain ⟨hr,ht⟩ := h p hp
  obtain ⟨_,hb,hh,hL,hΔ,_,hε⟩ := hp
  have hs (i j) (hadj : p.G.Adj i j) := (hb i j hadj).2
  have htime : (((Algorithms.GraceBatch.tuning p U).iterations : ℕ) - 1 : ℕ) *
      Proofs.GraceSampleSchedule.time route ≤ budget p := by
    rw [Proofs.GraceSgdBudget.iterations_sub_one p U]
    unfold budget
    apply mul_le_mul_of_nonneg_left _ zero_le
    refine ht.trans_eq (iInf_congr fun V => ?_)
    by_cases hc : V.val.card ≤ 1
    · simp [Proofs.GraceSgdBudget.cost,hc,Algorithms.GraceBatch.batchTime,Algorithms.GraceBatch.B,
        Algorithms.DistributedBatchedSgd.targetBatch]
    · simp only [Proofs.GraceSgdBudget.cost,hc,ite_false,
        Proofs.GraceSgdBudget.cut_formula p V.val (lt_of_not_ge hc),Algorithms.GraceGraph.cut,
        Algorithms.GraceGraph.capacity,Algorithms.GraceBatch.batchTime,Nat.cast_add,
        Proofs.GraceSgdBudget.width,Algorithms.GracePacket.limbWidth,Algorithms.GraceBatch.B,
        Algorithms.DistributedBatchedSgd.targetBatch]
  refine ⟨Proofs.GraceSgdGuarantee.family route hU hr hh hs (budget p) htime hL hε,?_⟩
  intro f O ho
  obtain ⟨hg,hlip,⟨lower,hl,hgap⟩,g,μ,P,rfl,hsg,hworkers,hIID⟩ := ho
  refine ⟨Filter.Eventually.of_forall (fun seed => Proofs.GraceExecution.finite route g P (budget p) seed.1 seed.2),?_⟩
  have hout : (fun seed => execute (system p g P) (Algorithms.GraceSgd.algorithm route (budget p))
      (budget p) seed.1 seed.2) = Algorithms.DistributedBatchedSgd.output (Algorithms.GraceBatch.statistical p)
        (Algorithms.GraceBatch.tuning p U) (fun _ => g) := by
    funext seed
    exact Proofs.GraceSgdGuarantee.actual_output route hU hr hh hs _ htime g P seed.2 seed.1
  change Measurable _ ∧ Integrable _ _ ∧ _ ≤ p.ε
  erw [hout]
  exact Proofs.GraceBatchTuning.quantized_output_accuracy hU hh hL hΔ hε P μ hworkers hIID g f
    hsg hg hlip lower hl hgap

end LongTails.Theorems.GraceSgd
