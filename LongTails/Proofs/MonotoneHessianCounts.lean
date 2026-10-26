import LongTails.Algorithms.MonotoneHessianReuse
import LongTails.Proofs.QuarticStageExecution

namespace LongTails.Proofs.MonotoneHessianCounts

open OracleTemplate LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.EnergyHessianExecution LongTails.Proofs.QuarticStageExecution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma stage_finish_hessian (p : Parameters E) (O : Fin 2 × E → Reply E) (status : Status E) :
    counts O (LongTails.Algorithms.MonotoneCurvatureStage.finish p status) 1 = 0 := by
  classical
  cases status <;> simp only [LongTails.Algorithms.MonotoneCurvatureStage.finish]
  all_goals (try split) <;> simp [counts]

lemma stage_hessian (p : Parameters E) (O : Fin 2 × E → Reply E) (n : ℕ) :
    counts O (LongTails.Algorithms.MonotoneCurvatureStage.plan p n) 1 = 0 := by
  simp [LongTails.Algorithms.MonotoneCurvatureStage.plan, counts_cast, counts_bind,
    loop_counts, certificate_counts, stage_finish_hessian]

lemma search_hessian (D : E →L[ℝ] E) (x : Point E) (H a : ℝ) (u : E)
    (O : Fin 2 × E → Reply E) (n : ℕ) :
    counts O (LongTails.Algorithms.RelativeCurvatureSearch.search D x H a u n) 1 = 0 := by
  have hp (τ : ℝ) (v : E) : counts O (LongTails.Algorithms.RelativeCurvatureSearch.product D x H τ v) 1 = 0 := by
    simp [LongTails.Algorithms.RelativeCurvatureSearch.product, counts]
  have ht (τ : ℝ) (v : E) : counts O (LongTails.Algorithms.RelativeCurvatureSearch.transformedProduct D x H a τ v) 1 = 0 := by
    simp [LongTails.Algorithms.RelativeCurvatureSearch.transformedProduct, counts_map, hp]
  have hf (τ : ℝ) (v : E) (k : ℕ) : counts O (LongTails.Algorithms.RelativeCurvatureSearch.filter D x H a τ v k) 1 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [LongTails.Algorithms.RelativeCurvatureSearch.filter, counts_cast, counts_bind, counts_map, ht, ih]
  simp [LongTails.Algorithms.RelativeCurvatureSearch.search, counts_cast, counts_bind, counts_map, hp, hf]

open LongTails.Setups.HessianLipschitzSecondOrder LongTails.Algorithms.MonotoneHessianReuse

lemma padding_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (x : p.E) (n : ℕ) {U : Type} (u : U) :
    counts O (padding p x n u) 1 = 0 := by
  simp only [padding, counts_cast, counts_map]
  rw [traverse_counts O _ 1 (d := 0) (by intro j; simp [counts])]
  simp

lemma detect_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (S : p.E ≃L[ℝ] p.E)
    (x : Point p.E) (signs : Block p) : counts O (detect p S x signs) 1 = 0 := by
  simp only [detect, searchCalls, counts_map]
  rw [traverse_counts O _ 1 (d := 0) (by intro j; exact search_hessian _ _ _ _ _ _ _)]
  simp

lemma postStage_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (st : State p)
    (snap : Snapshot p) (x : Point p.E) (signs : Block p) : counts O (postStage p st snap x signs) 1 = 0 := by
  classical
  simp only [postStage]
  split
  · exact padding_hessian _ _ _ _ _
  · simp only [counts_cast, counts_bind, detect_hessian, zero_add]
    split
    · exact padding_hessian _ _ _ _ _
    · simp [escape, counts_map, counts]

lemma body_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (st : State p)
    (v : Option p.E) (signs : Block p) : counts O (body p st v signs) 1 = 0 := by
  classical
  simp only [body]
  split
  · exact padding_hessian _ _ _ _ _
  · cases v with
    | some v => simp [counts_bind, escape, counts, padding_hessian]
    | none =>
      cases hs : st.snapshot with
      | none => simp [padding_hessian]
      | some snap =>
        erw [counts_cast, counts_bind, stage_hessian, postStage_hessian]

lemma step_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (st : State p)
    (signs : Block p) : counts O (step p st signs) 1 = counts O (prepare p st) 1 := by
  simp [LongTails.Algorithms.MonotoneHessianReuse.step, counts_bind, body_hessian]

lemma prepare_hessian_le (p : Params) (O : Fin 2 × p.E → Reply p.E) (st : State p) :
    counts O (prepare p st) 1 ≤ 1 := by
  have hh := counts_sum O (prepare p st)
  have hl := Finset.single_le_sum (fun i _ => Nat.zero_le (counts O (prepare p st) i))
    (Finset.mem_univ (1 : Fin 2))
  exact hl.trans_eq hh

lemma done_prepare_hessian (p : Params) (O : Fin 2 × p.E → Reply p.E) (st : State p)
    (hd : st.done = true) : counts O (prepare p st) 1 = 0 := by
  simp [prepare, hd, padding_hessian]

end LongTails.Proofs.MonotoneHessianCounts
