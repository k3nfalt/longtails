import LongTails.Proofs.FixedBatchConfidenceInstance

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma lift_normalized_failure (q : Params) (hL : 0 < q.L) (hR : 0 < q.R)
    (hδ : 0 ≤ q.δ) (η : ℝ) {b : ℕ} (hb : 0 < b) (N : ℕ)
    (p : unitInterval) (a v : Space) (ha : ‖a‖ ^ 2 ≤ 1) (hv : ‖v‖ ^ 2 ≤ 1)
    (hfail :
      let P := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
      let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v)
      let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G (η * q.L) (pair 1 0)
        (fun k i => ξ (k * b + i.val)) (N / b)
      q.δ < P.real {ξ | q.ε / (q.L * q.R ^ 2) <
        (p : ℝ) * (⟪a, X ξ⟫ ^ 2 / 2) + (1 - p) * (⟪v, X ξ⟫ ^ 2 / 2)}) :
    ∃ (f : Space → ℝ) (O : Oracle Space Space), spec.admissible q f O ∧
      ∃ u : Space, IsMinOn f Set.univ u ∧
        Measurable (fun ω => (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () ω)) ∧
        ENNReal.ofReal q.δ < (O.law : Measure _) {ω |
          q.ε < f (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () ω) - f u} := by
  let u := q.x0 - q.R • pair 1 0
  let s := Real.sqrt q.L
  let A := s • a
  let V := s • v
  let f := fun x : Space => (p : ℝ) * (⟪A, x - u⟫ ^ 2 / 2) +
    (1 - p) * (⟪V, x - u⟫ ^ 2 / 2)
  let P : ProbabilityMeasure (ℕ → Space) :=
    ⟨Measure.infinitePi fun _ : ℕ => bernoulliMeasure A V p, inferInstance⟩
  let O : Oracle Space Space :=
    { Seed := fun _ => Space, law := P, answer := fun _ (_, x) z => ⟪z, x - u⟫ • z }
  have hA : ‖A‖ ^ 2 ≤ q.L := scaled_feature_bound hL.le ha
  have hV : ‖V‖ ^ 2 ≤ q.L := scaled_feature_bound hL.le hv
  have hu : ‖q.x0 - u‖ ≤ q.R := shifted_initial_radius q hR.le
  have hm := two_atom_model q p u A V hA hV hu
  have hmin := model_minimum hm
  have hmeas : Measurable (fun ξ => (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () ξ)) :=
    measurable_fixedBatchSgd hb P (fun x z => ⟪z, x - u⟫ • z) (by fun_prop) η q.x0 N
  refine ⟨f, O, two_atom_admissible q p u A V hA hV hu, u, hmin.1, hmeas, ?_⟩
  · let T := fun (ξ : ℕ → Bool) k => if ξ k then A else V
    let PB := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
    have hT : Measurable T := by
      apply Measurable.of_eval
      intro k
      exact (show Measurable (fun z : Bool => if z then A else V) from
        Measurable.of_discrete).comp (measurable_pi_apply k)
    have hlaw : PB.map T = (P : Measure _) := two_atom_stream_law p A V
    let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ •
      ∑ i, ⟪(if z i then a else v), x⟫ • (if z i then a else v)
    let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G (η * q.L) (pair 1 0)
      (fun k i => ξ (k * b + i.val)) (N / b)
    have hs : s ^ 2 = q.L := Real.sq_sqrt hL.le
    have hstart : q.x0 = u + q.R • pair 1 0 := by dsimp [u]; abel
    have hex (ξ : ℕ → Bool) :
        (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () (T ξ)) = u + q.R • X ξ := by
      dsimp only [O]
      rw [execute_fixedBatchSgd_calls hb P (fun x z => ⟪z, x - u⟫ • z)]
      rw [hstart]
      change MarkovQuadratic.iterate _ η (u + q.R • pair 1 0)
        (fun k (i : Fin b) => if ξ (k * b + i.val) then s • a else s • v) (N / b) = _
      rw [boolean_batch_affine_iterate, hs]
    have hrisk (ξ : ℕ → Bool) :
        f (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () (T ξ)) - f u =
          q.L * q.R ^ 2 * ((p : ℝ) * (⟪a, X ξ⟫ ^ 2 / 2) +
            (1 - p) * (⟪v, X ξ⟫ ^ 2 / 2)) := by
      rw [hex]
      have hfzero : f u = 0 := hmin.2
      rw [hfzero, sub_zero]
      change (p : ℝ) * (⟪s • a, (u + q.R • X ξ) - u⟫ ^ 2 / 2) +
        (1 - p) * (⟪s • v, (u + q.R • X ξ) - u⟫ ^ 2 / 2) = _
      rw [scaled_two_atom_risk, hs]
    have hf : Measurable f := by dsimp [f]; fun_prop
    have hset : MeasurableSet {ω | q.ε < f (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () ω) - f u} :=
      measurableSet_lt measurable_const ((hf.comp hmeas).sub_const _)
    apply (ENNReal.ofReal_lt_iff_lt_toReal hδ (measure_ne_top _ _)).mpr
    change q.δ < ((P : Measure _) {ω | q.ε < f (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () ω) - f u}).toReal
    rw [← hlaw, Measure.map_apply hT hset]
    apply hfail.trans_le
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ξ hξ
    change q.ε < f (execute O (fixedBatchSgd hb η q.x0) (fun _ => N) () (T ξ)) - f u
    rw [hrisk]
    have hh := (div_lt_iff₀ (by positivity : 0 < q.L * q.R ^ 2)).mp hξ
    nlinarith

end OracleTemplate.FixedBatchConfidence
