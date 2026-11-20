import LongTails.Setups.DistributedMeanSquaredSmooth
import LongTails.Proofs.MultilevelAccuracy

namespace LongTails.Theorems.MultilevelPipelineStationarity

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelPipeline

noncomputable def budget (p : Params) : Time :=
  let K := max 1 ⌈524288 * p.L * p.Δ / p.ε ^ 2⌉₊
  let S := max 1 ⌈(512 * p.σ / p.ε) ^ 2⌉₊
  let J := min (Nat.log2 K) (Nat.log 4 (S / (1 + Nat.log 4 S)))
  let c := fun i => 2 * p.h i + 2 * p.l + p.b * (129 + 3 * p.d * (14 + 4 * Nat.log2 (2 + p.d + K + S)) : ℕ)
  let B := fun (m : ℕ) => 4 * Finset.univ.inf' Finset.univ_nonempty (fun i => max (c i) ((m : Time) / ∑ u, if c u ≤ c i then (c u)⁻¹ else 0))
  B S + K * (Finset.range (J + 1)).sup (fun j => B (2 * (J + 1) * 4 ^ j + if j = J then S else 0) / 2 ^ j)

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.DistributedMeanSquaredSmooth.spec budget := by
  refine ⟨fun p => algorithm p (duration p), ?_⟩
  intro p hp
  obtain ⟨hh,hL,_,_,hε⟩ := hp
  refine ⟨trivial,?_⟩
  have hK : 524288 * p.L * p.Δ / p.ε^2 = 2 * p.L * p.Δ / (p.ε / 512)^2 := by
    field_simp
    ring
  have hT : budget p = duration p := by
    unfold budget
    rw [hK]
    let B := fun (m : ℕ) => 4 * Finset.univ.inf' Finset.univ_nonempty (fun i =>
      max ((physical p).h i) ((m : Time) / speed (physical p) i))
    change B (fullBatch p) + (wanted p : Time) * (Finset.range (height p + 1)).sup
      (fun j => B (2 * (height p + 1) * 4^j + if j = height p then fullBatch p else 0) / 2^j) = _
    have hB (m : ℕ) : B m = 2 * batchDuration (physical p) m := by
      unfold B batchDuration
      rw [← mul_assoc]
      norm_num
    simp_rw [hB,Nat.mul_assoc]
    rfl
  intro f O had
  obtain ⟨hf,⟨a,ha,hgap⟩,g,μ,P,rfl,hw,hi⟩ := had
  rw [hT]
  refine ⟨Filter.Eventually.of_forall (fun z =>
    LongTails.Proofs.MultilevelExecution.finite ⟨script p,duration p,g,P,z.2,z.1⟩
      (LongTails.Proofs.MultilevelTimetable.certified p hh) hh), ?_⟩
  let A := algorithm p (duration p)
  let O := system p g P
  let F := fun z : LongTails.Algorithms.MultilevelTransport.Selection p × Samples p =>
    output p z.1 (LongTails.Proofs.MultilevelDraws.row (script p) g
      (LongTails.Proofs.MultilevelDraws.actual (script p) z.2))
  have he : (fun z : A.Seed × O.Seed => execute O A (duration p) z.1 z.2) = F :=
    funext fun z => LongTails.Proofs.MultilevelAccuracy.execution_output (g := g) hh P z.1 z.2
  apply (congrArg (fun X => spec.successful p f X (law O A)) he).mpr
  exact LongTails.Proofs.MultilevelAccuracy.successful
    ⟨hL,hε,hf,ha,hgap,fun i => (hi i).2.1,fun i => (hi i).2.2⟩ hh P hw (fun i => (hi i).1)

end LongTails.Theorems.MultilevelPipelineStationarity
