import LongTails.Algorithms.SparseGroupSampling
import LongTails.Proofs.FiniteRiskMesh
import LongTails.Proofs.SparseConvexCertificate
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open scoped BigOperators

namespace LongTails.Proofs.SparseGroupGeometry

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling

lemma coordinateScale_pos (q : Public) (hε : 0 < q.ε) (hG : 0 ≤ q.G) :
    0 < coordinateScale q := by
  unfold coordinateScale
  positivity

lemma primalMesh_valid (q : Public) (hε : 0 < q.ε) (hG : 0 ≤ q.G)
    (hx : q.x0 ∈ q.domain) (hbound : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R) :
    IsPrimalMesh q (primalMesh q) := by
  have hex : ∃ H, IsPrimalMesh q H :=
    FiniteRiskMesh.exists_euclidean_mesh q.domain q.x0 q.R (coordinateScale q)
      (coordinateScale_pos q hε hG) ⟨q.x0, hx⟩ hbound
  classical
  simpa only [primalMesh, dite_eq_left hex] using hex.choose_spec

lemma sparseSimplex_coordinate_le_one (q : Public) {w : Fin q.K → ℝ}
    (hw : w ∈ SparseSimplex q) (i : Fin q.K) : w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
    _ = 1 := hw.2.1

lemma sparseSimplex_closed (q : Public) : IsClosed (SparseSimplex q) := by
  classical
  let C : Finset (Finset (Fin q.K)) := Finset.univ.filter (fun S => S.card ≤ q.d + 1)
  have hface (S : Finset (Fin q.K)) :
      IsClosed {w : Fin q.K → ℝ | ∀ i, i ∉ S → w i = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply i) continuous_const
  have heq : SparseSimplex q =
      {w : Fin q.K → ℝ | ∀ i, 0 ≤ w i} ∩
      {w : Fin q.K → ℝ | ∑ i, w i = 1} ∩
      ⋃ S ∈ C, {w : Fin q.K → ℝ | ∀ i, i ∉ S → w i = 0} := by
    ext w
    simp [SparseSimplex, C, and_assoc]
  rw [heq]
  apply IsClosed.inter
  · apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (by fun_prop) continuous_const
  · exact C.finite_toSet.isClosed_biUnion (fun S _ => hface S)

lemma sparseSimplex_compact (q : Public) : IsCompact (SparseSimplex q) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : Fin q.K → ℝ) 1)
    isCompact_Icc (sparseSimplex_closed q)
  intro w hw
  exact ⟨hw.1, fun i => sparseSimplex_coordinate_le_one q hw i⟩

lemma sparseSimplex_nonempty (q : Public) : (SparseSimplex q).Nonempty := by
  classical
  refine ⟨Pi.single 0 1, ?_, ?_, {0}, ?_, ?_⟩
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp
  · simp
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [hi]

lemma dualMeshRadius_pos (q : Public) (hε : 0 < q.ε) : 0 < dualMeshRadius q := by
  have hK : 0 < q.K := Nat.pos_of_ne_zero (NeZero.ne q.K)
  unfold dualMeshRadius
  positivity

lemma dualMesh_valid (q : Public) (hε : 0 < q.ε) : IsDualMesh q (dualMesh q) := by
  classical
  obtain ⟨W, hWsub, hWfin, hcover⟩ := (sparseSimplex_compact q).finite_cover_balls
    (dualMeshRadius_pos q hε)
  have hcover' : ∀ w ∈ SparseSimplex q, ∃ v ∈ hWfin.toFinset,
      dist w v ≤ dualMeshRadius q := by
    intro w hw
    obtain ⟨v, hv, hd⟩ := Set.mem_iUnion₂.mp (hcover hw)
    exact ⟨v, by simpa using hv, hd.le⟩
  have hex : ∃ W, IsDualMesh q W := by
    refine ⟨hWfin.toFinset, ?_, ?_, hcover'⟩
    · obtain ⟨w, hw⟩ := sparseSimplex_nonempty q
      obtain ⟨v, hv, _⟩ := hcover' w hw
      exact ⟨v, hv⟩
    · intro w hw
      exact hWsub (by simpa using hw)
  simpa only [dualMesh, dite_eq_left hex] using hex.choose_spec

end LongTails.Proofs.SparseGroupGeometry
