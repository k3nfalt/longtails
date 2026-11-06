import LongTails.Proofs.FiniteSparseSaddle
import LongTails.Proofs.SparseGroupGeometry
import LongTails.Proofs.SparseConfidenceCertificate

open scoped BigOperators

namespace LongTails.Proofs.SparseGroupCertificate

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling
open SparseGroupGeometry SparseGroupChoices

lemma state_saddle_bound (q : Public) (s : State q) (u : Fin q.K → Space q.d → ℝ)
    (hε : 0 < q.ε) (hG : 0 ≤ q.G) (hx0 : q.x0 ∈ q.domain)
    (hbound : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R) (hQ : Convex ℝ q.domain)
    (hu : ∀ i, ConvexOn ℝ q.domain (u i))
    (hl : ∀ i, ∀ x ∈ q.domain, ∀ y ∈ q.domain, |u i x - u i y| ≤ q.G * dist x y)
    (hb : ∀ i, ∀ x ∈ q.domain, |u i x| ≤ 2)
    (hs : ∀ i h, upper q s i h = u i h.val) :
    ∀ x ∈ q.domain,
      upper q s (finiteMaximizer (fun i => upper q s i (primalChoice q s))) (primalChoice q s) ≤
      (∑ i, (dualChoice q s).val i * u i x) +
        (2 * q.G * ((q.d + 1 : ℝ) * coordinateScale q) +
          q.ε / (64 * (q.d + 1 : ℝ)) + 2 * q.K * dualMeshRadius q) := by
  have hmesh := primalMesh_valid q hε hG hx0 hbound
  have hdual := dualMesh_valid q hε
  have h := FiniteSparseSaddle.finite_sparse_saddle q.domain u
    (fun h : PrimalIndex q => h.val) (fun w : DualIndex q => w.val)
    q.G ((q.d + 1 : ℝ) * coordinateScale q) (dualMeshRadius q)
    (q.ε / (64 * (q.d + 1 : ℝ))) hQ hu
    (fun h => hmesh.2.2.1 h.val h.property)
    (by intro x hx; obtain ⟨y, hy, hd⟩ := hmesh.2.2.2 x hx; exact ⟨⟨y, hy⟩, hd⟩)
    hG (by positivity) hl (fun i h => hb i h.val (hmesh.2.2.1 h.val h.property))
    (fun w => ⟨(hdual.2.1 w.val w.property).1, (hdual.2.1 w.val w.property).2.1⟩)
    (by
      intro w hw hsum hsupport
      have hsp : w ∈ SparseSimplex q := by
        refine ⟨hw, hsum, ?_⟩
        simpa only [Space, finrank_euclideanSpace_fin] using hsupport
      obtain ⟨v, hv, hd⟩ := hdual.2.2 w hsp
      refine ⟨⟨v, hv⟩, fun i => ?_⟩
      simpa only [Real.dist_eq] using (dist_le_pi_dist w v i).trans hd)
  have he : upper q s = fun i h => u i h.val := by funext i h; exact hs i h
  simpa only [FiniteSparseSaddle.primalValue, FiniteSparseSaddle.dualValue,
    primalChoice, dualChoice, he, Fintype.card_fin] using h

lemma discretization_error_le (q : Public) (hε : 0 < q.ε) (hG : 0 ≤ q.G) :
    4 * q.G * ((q.d + 1 : ℝ) * coordinateScale q) +
      q.ε / (64 * (q.d + 1 : ℝ)) + 2 * q.K * dualMeshRadius q ≤
      q.ε / (8 * (q.d + 1 : ℝ)) := by
  have hs : (0 : ℝ) < q.d + 1 := by positivity
  have hg : 0 < 1 + q.G := by linarith
  have hk : (0 : ℝ) < q.K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q.K)
  unfold coordinateScale dualMeshRadius
  apply (le_div_iff₀ (by positivity : 0 < 8 * (q.d + 1 : ℝ))).mpr
  field_simp
  nlinarith [sq_nonneg (q.d : ℝ), mul_nonneg hG (Nat.cast_nonneg q.d : (0 : ℝ) ≤ q.d)]

end LongTails.Proofs.SparseGroupCertificate
