import LongTails.Proofs.FixedBatchConfidenceNormalized
import LongTails.Proofs.FixedBatchConfidenceExecution

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma two_atom_admissible (q : Params) (p : unitInterval) (u a v : Space)
    (ha : ‖a‖ ^ 2 ≤ q.L) (hv : ‖v‖ ^ 2 ≤ q.L)
    (hu : ‖q.x0 - u‖ ≤ q.R) :
    spec.admissible q
      (fun x => (p : ℝ) * (⟪a, x - u⟫ ^ 2 / 2) +
        (1 - p) * (⟪v, x - u⟫ ^ 2 / 2))
      { Seed := fun _ => Space
        law := ⟨Measure.infinitePi fun _ : ℕ => bernoulliMeasure a v p, inferInstance⟩
        answer := fun _ (_, x) z => ⟪z, x - u⟫ • z } := by
  exact ⟨⟨bernoulliMeasure a v p, inferInstance⟩,
    ⟨Measure.infinitePi fun _ : ℕ => bernoulliMeasure a v p, inferInstance⟩, u,
    two_atom_model q p u a v ha hv hu, StochasticGeneralized.infinitePi_iid (bernoulliMeasure a v p), rfl⟩

lemma two_atom_stream_law (p : unitInterval) (a v : Space) :
    (Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p).map
      (fun ξ k => if ξ k then a else v) =
        Measure.infinitePi fun _ : ℕ => bernoulliMeasure a v p := by
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (z : Bool) => if z then a else v)
    (fun _ => Measurable.of_discrete)]
  simp only [map_bernoulliMeasure, ↓reduceIte, Bool.false_eq_true]

lemma scaled_two_atom_risk (p : unitInterval) (a v u z : Space) (r s : ℝ) :
    (p : ℝ) * (⟪s • a, (u + r • z) - u⟫ ^ 2 / 2) +
      (1 - p) * (⟪s • v, (u + r • z) - u⟫ ^ 2 / 2) =
        s ^ 2 * r ^ 2 * ((p : ℝ) * (⟪a, z⟫ ^ 2 / 2) +
          (1 - p) * (⟪v, z⟫ ^ 2 / 2)) := by
  simp only [add_sub_cancel_left, inner_smul_left, inner_smul_right, conj_trivial]
  ring

lemma scaled_feature_bound {L : ℝ} (hL : 0 ≤ L) {a : Space} (ha : ‖a‖ ^ 2 ≤ 1) :
    ‖Real.sqrt L • a‖ ^ 2 ≤ L := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hL]
  nlinarith

lemma shifted_initial_radius (q : Params) (hR : 0 ≤ q.R) :
    ‖q.x0 - (q.x0 - q.R • pair 1 0)‖ ≤ q.R := by
  have hnorm : ‖pair 1 0‖ = 1 := by
    have h := pair_norm_sq 1 0
    nlinarith [norm_nonneg (pair 1 0)]
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, hnorm, mul_one]

lemma boolean_batch_affine_iterate {b : ℕ} (u a v : Space)
    (η r s : ℝ) (ξ : ℕ → Bool) (K : ℕ) :
    MarkovQuadratic.iterate
      (fun (x : Space) (z : Fin b → Space) => (b : ℝ)⁻¹ •
        ∑ i, ⟪z i, x - u⟫ • z i)
      η (u + r • pair 1 0)
      (fun k i => if ξ (k * b + i.val) then s • a else s • v) K =
        u + r • MarkovQuadratic.iterate
          (fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
            ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v))
          (η * s ^ 2) (pair 1 0) (fun k i => ξ (k * b + i.val)) K := by
  have he : (fun k (i : Fin b) => if ξ (k * b + i.val) then s • a else s • v) =
      (fun k i => s • (if ξ (k * b + i.val) then a else v)) := by
    funext k i
    split_ifs <;> rfl
  rw [he, rank_one_batch_iterate_affine]
  rw [iterate_oracle_map
    (fun (x : Space) (z : Fin b → Space) => (b : ℝ)⁻¹ • ∑ i, ⟪z i, x⟫ • z i)
    (fun (z : Fin b → Bool) i => if z i then a else v)]

end OracleTemplate.FixedBatchConfidence
