import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapFilterTransport

open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (shift_add shift_smul norm_shift)

noncomputable def shiftMap {d : ℕ} : Features d →ₗ[ℝ] Features d where
  toFun := shift
  map_add' := shift_add
  map_smul' := shift_smul

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def filter (S : E →ₗ[ℝ] E) (b : ℝ) (w : E) : E := w+b • S w

def target (S : E →ₗ[ℝ] E) (h : E) : List ℝ → E
  | [] => h
  | a :: nodes => filter S a (target S h nodes)

def readout (S : E →ₗ[ℝ] E) (h : E) (b : ℝ) : List ℝ → E
  | [] => 0
  | a :: nodes => target S h nodes + (a-b) • S (readout S h b nodes)

lemma one_node (S : E →ₗ[ℝ] E) (a b : ℝ) (w v : E) :
    filter S a w - filter S b (w+(a-b) • S v) = (a-b) • S (w-filter S b v) := by
  simp only [filter,map_add,map_sub,map_smul,smul_add,smul_sub,sub_smul,smul_smul]
  module

lemma residual (S : E →ₗ[ℝ] E) (h : E) (b : ℝ) (nodes : List ℝ) :
    target S h nodes - filter S b (readout S h b nodes) =
      (nodes.map (fun a => a-b)).prod • S^[nodes.length] h := by
  induction nodes with
  | nil => simp [target,readout,filter]
  | cons a nodes ih =>
    simp only [target,readout,one_node,ih,map_smul,List.map_cons,List.prod_cons,
      List.length_cons,Function.iterate_succ_apply',smul_smul]

lemma score_error {d : ℕ} (x h : Features d) (b : ℝ) (nodes : List ℝ) :
    |⟪x,target shiftMap h nodes⟫-⟪x,filter shiftMap b (readout shiftMap h b nodes)⟫| ≤
      ‖x‖*|(nodes.map (fun a => a-b)).prod| * ‖h‖ := by
  have hn (k : ℕ) : ‖(shiftMap (d := d))^[k] h‖ = ‖h‖ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact (norm_shift _).trans ih
  rw [← inner_sub_right,residual,real_inner_smul_right,abs_mul]
  have hc := abs_real_inner_le_norm x ((shiftMap (d := d))^[nodes.length] h)
  rw [hn] at hc
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
       _ = _ := by ring

end LongTails.Proofs.TwoTapFilterTransport
