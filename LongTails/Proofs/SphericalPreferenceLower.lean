import LongTails.Proofs.SphericalPreferenceRisk

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SphericalPreferenceLower
attribute [local instance 2000] WithLp.measurableSpace

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceGaussian
open LongTails.Proofs.SphericalPreferenceHypercube LongTails.Proofs.SphericalPreferenceTranscript
open LongTails.Proofs.SphericalPreferenceTranscriptLaw LongTails.Proofs.SphericalPreferenceRisk
open OracleTemplate

noncomputable def stream (p : Params) : Measure (ℕ → Point p.d) :=
  Measure.infinitePi fun _ : ℕ => mixture p.d p.B

instance (p : Params) : IsProbabilityMeasure (stream p) := by unfold stream; infer_instance

abbrev Method (p : Params) := Algorithm (Feasible p × Feasible p) Bool (Feasible p)

noncomputable def loss (p : Params) [NeZero p.d] (v : Vertex p.d) (A : Method p) (k : ℕ)
    (q : A.Seed × (ℕ → Point p.d)) : ℝ :=
  linear p v (execute (oracle p v) A (fun _ => k) q.1 q.2).val-linear p v (optimal p v).val

lemma conditional_loss (p : Params) [NeZero p.d] (v : Vertex p.d) (A : Method p) (k : ℕ)
    (seed : A.Seed) :
    let t := state (A.initial seed) A.update k
    let m := weight (A.initial seed) A.update (fun s => yes p v (A.query s).2) k
    (∫ ξ, loss p v A k (seed,ξ) ∂stream p) =
      ∑ w, m w*(linear p v (A.output (t w)).val-linear p v (optimal p v).val) := by
  let μ := mixture p.d p.B
  let test := fun s : A.State => comparePair (linear p v) (A.query s).2
  have ht (s : A.State) : Measurable (test s) := by
    unfold test comparePair sampleUtility
    apply measurable_to_bool
    simp only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq]
    apply measurableSet_le <;> fun_prop
  let t := state (A.initial seed) A.update k
  let L := fun w => linear p v (A.output (t w)).val-linear p v (optimal p v).val
  have hl := finite_loss μ (A.initial seed) A.update test ht k L
  have hex (ξ : ℕ → Point p.d) : loss p v A k (seed,ξ) =
      L (observed (A.initial seed) A.update test k (fun i => ξ i)) := by
    unfold loss
    have hx := StochasticGradient.execute_advance (oracle p v).law (comparePair (linear p v)) A k seed ξ
    change execute (oracle p v) A _ seed ξ = _ at hx
    rw [hx]
    rw [show StochasticGradient.advance (fun i s => A.update s (comparePair (linear p v) (A.query s).2 (ξ i))) k 0 (A.initial seed) =
      state (A.initial seed) A.update k (observed (A.initial seed) A.update test k (fun i => ξ i)) from
        state_observed (A.initial seed) A.update test ξ k]
  simp_rw [hex]
  exact ((StochasticGeneralized.prefix_preserving μ k).hasLaw.integral_comp hl.1.aestronglyMeasurable).trans hl.2

lemma hard_vertex (p : Params) [NeZero p.d] (hR : 0 < p.R) (hB : 0 < p.B)
    (he : 0 < p.ε) (hacc : p.ε ≤ p.B*p.R/16) (A : Method p) (k : ℕ)
    (hk : (k : ℝ) ≤ p.d*(p.B*p.R/p.ε)^2/524288) :
    ∃ v : Vertex p.d, ¬ spec.successful p (linear p v)
      (fun q : A.Seed × (ℕ → Point p.d) => execute (oracle p v) A (fun _ => k) q.1 q.2)
      ⟨(A.law : Measure A.Seed).prod (stream p),inferInstance⟩ := by
  classical
  by_contra! hall
  let μ := stream p
  let P := (A.law : Measure A.Seed).prod μ
  have hg (v : Vertex p.d) : Integrable (loss p v A k) P ∧ ∫ q, loss p v A k q ∂P ≤ p.ε := by
    obtain ⟨x,hx,hI,hE⟩ := hall v
    have heq : linear p v x.val = linear p v (optimal p v).val := le_antisymm (hx (optimal p v).property) (optimality p v hR he x.property)
    rw [heq] at hI hE
    exact ⟨hI,hE⟩
  let F := fun (v : Vertex p.d) (s : A.Seed) => ∫ ξ, loss p v A k (s,ξ) ∂μ
  have hsum (seed : A.Seed) : 5/4*(Fintype.card (Vertex p.d) : ℝ)*p.ε ≤ ∑ v, F v seed := by
    have h := history_risk p hR hB he hacc hk (A.initial seed) A.update (fun s => (A.query s).2) A.output
    simpa only [F,μ,conditional_loss] using h
  have hFi (v : Vertex p.d) : Integrable (F v) (A.law : Measure A.Seed) := (hg v).1.integral_prod_left
  have hin := integral_mono (integrable_const _) (integrable_finsetSum _ (fun v _ => hFi v)) hsum
  rw [integral_const,probReal_univ,one_smul,integral_finsetSum _ (fun v _ => hFi v)] at hin
  have hupper (v : Vertex p.d) : (∫ s, F v s ∂(A.law : Measure A.Seed)) ≤ p.ε :=
    (integral_prod _ (hg v).1).symm.trans_le (hg v).2
  have hh := hin.trans (Finset.sum_le_sum fun v _ => hupper v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hV : 0 < (Fintype.card (Vertex p.d) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith only [hh,mul_pos hV he]

end LongTails.Proofs.SphericalPreferenceLower
