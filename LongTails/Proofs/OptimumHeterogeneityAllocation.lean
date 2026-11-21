import LongTails.Algorithms.OptimumHeterogeneitySgd
import LongTails.Proofs.OptimumHeterogeneityDesign
import LongTails.Proofs.DistributedBatchedSgd

namespace LongTails.Proofs.OptimumHeterogeneityAllocation

open DistributedTemplate LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneityDesign LongTails.Algorithms.OptimumHeterogeneitySgd

variable {p : Params}

lemma period_lower (p : Params) : 8 ≤ period p := le_max_left _ _
lemma phase_pos (p : Params) : 0 < phase p := Nat.mul_pos (by have := period_lower p; omega) (by omega)
lemma batch_pos (p : Params) (i : Fin p.n) : 0 < batch p i := Nat.zero_lt_of_lt (le_max_left 1 _)
lemma round_pos (p : Params) : 0 < rounds p := by unfold rounds; omega

lemma total_pos (p : Params) : 0 < ∑ i, batch p i :=
  (batch_pos p 0).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))

lemma fraction_pos (p : Params) (i : Fin p.n) : 0 < fraction p i :=
  div_pos (by exact_mod_cast batch_pos p i) (by exact_mod_cast total_pos p)

lemma fraction_sum (p : Params) : ∑ i, fraction p i = 1 :=
  DistributedBatchedSgd.batch_weights_sum _ (total_pos p)

lemma weight_nn (hp : spec.valid p) (i) : 0 ≤ weights p i := (OptimumHeterogeneityDesign.weights_optimal hp).1.1 i

lemma cost_nn (p : Params) : 0 ≤ cost p (weights p) := Finset.sum_nonneg fun i _ => by positivity

lemma time_ge (p : Params) (i : Fin p.n) : p.h i ≤ batchTime p :=
  (Finset.le_sup (s := Finset.univ) (f := p.h) (Finset.mem_univ i)).trans (le_max_left _ _)

lemma time_pos (hp : spec.valid p) : 0 < (batchTime p : ℝ) := by
  exact_mod_cast (hp.1.1 0).trans_le (time_ge p 0)

lemma batch_bounds (hp : spec.valid p) (i : Fin p.n) :
    (batchTime p : ℝ) / (p.h i : ℝ) ≤ batch p i ∧
    (batch p i : ℝ) ≤ 2 * ((batchTime p : ℝ) / (p.h i : ℝ)) := by
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1.1 i
  have ha : (1 : ℝ) ≤ (batchTime p : ℝ) / (p.h i : ℝ) :=
    (one_le_div hh).mpr (by exact_mod_cast time_ge p i)
  have hb : 1 ≤ ⌈(batchTime p : ℝ) / (p.h i : ℝ)⌉₊ := by exact_mod_cast ha.trans (Nat.le_ceil _)
  rw [batch, max_eq_right hb]
  exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (zero_le_one.trans ha)]⟩

lemma fraction_inverse (hp : spec.valid p) (i : Fin p.n) :
    1 / fraction p i ≤ 2 * (p.h i : ℝ) * ∑ j, (p.h j : ℝ)⁻¹ := by
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1.1 i
  have hb : 0 < (batch p i : ℝ) := by exact_mod_cast batch_pos p i
  have ht := (div_le_iff₀ hh).mp (batch_bounds hp i).1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (batch_bounds hp j).2)
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at hs
  unfold fraction
  rw [one_div_div, div_le_iff₀ hb, Nat.cast_sum]
  have h' := mul_le_mul_of_nonneg_right ht (Finset.sum_nonneg (s := Finset.univ)
    (fun j _ => inv_nonneg.mpr (p.h j).coe_nonneg))
  linarith

lemma capacity_bound (hp : spec.valid p) (v : Fin p.n → ℝ) (hv : ∀ i, 0 ≤ v i) (i : Fin p.n) :
    weights p i / fraction p i * v i ≤ capacity p v := by
  have h := mul_le_mul_of_nonneg_left (fraction_inverse hp i) (mul_nonneg (weight_nn hp i) (hv i))
  have he := Finset.le_sup' (s := Finset.univ) (fun j => (p.h j : ℝ) * weights p j * v j) (Finset.mem_univ i)
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * ∑ j : Fin p.n, (p.h j : ℝ)⁻¹)
  unfold capacity
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  linarith

lemma capacity_nn (hp : spec.valid p) {v : Fin p.n → ℝ} (hv : ∀ i, 0 ≤ v i) : 0 ≤ capacity p v :=
  (mul_nonneg (div_nonneg (weight_nn hp 0) (fraction_pos p 0).le) (hv 0)).trans (capacity_bound hp v hv 0)

lemma curvature_bound (hp : spec.valid p) : ∑ i, weights p i * p.L i ≤ capacity p p.L := by
  have hl := hp.1.2.1
  calc
    _ = ∑ i, fraction p i * (weights p i / fraction p i * p.L i) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(fraction_pos p i).ne']
    _ ≤ ∑ i, fraction p i * capacity p p.L := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (capacity_bound hp _ hl i) (fraction_pos p i).le
    _ = _ := by rw [← Finset.sum_mul, fraction_sum, one_mul]

lemma step_bounds (hp : spec.valid p) (k : ℕ) :
    0 ≤ stepSize p k ∧ stepSize p k ≤ 4 / period p ∧ stepSize p k * capacity p p.L ≤ 1/4 := by
  have hm : 8 ≤ (period p : ℝ) := by exact_mod_cast period_lower p
  have hm' : 0 < (period p : ℝ) := by linarith
  have hC : 16 * capacity p p.L ≤ (period p : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_max_right 8 ⌈16 * capacity p p.L⌉₊)
  have hη : stepSize p k ≤ 4 / period p := by
    unfold stepSize
    split_ifs
    · exact le_rfl
    · rw [div_le_div_iff₀ (by positivity) hm']
      linarith [Nat.cast_nonneg (α := ℝ) (k-phase p)]
  refine ⟨by unfold stepSize; split <;> positivity, hη, ?_⟩
  apply (mul_le_mul_of_nonneg_right hη (capacity_nn hp hp.1.2.1)).trans
  rw [div_mul_eq_mul_div, div_le_iff₀ hm']
  linarith

lemma variance_cost (hp : spec.valid p) :
    ∑ i, weights p i ^ 2 / batch p i ≤ cost p (weights p) / (batchTime p : ℝ) := by
  rw [le_div_iff₀ (time_pos hp), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1.1 i
  have hb : 0 < (batch p i : ℝ) := by exact_mod_cast batch_pos p i
  have h := (div_le_iff₀ hh).mp (batch_bounds hp i).1
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  linarith [mul_le_mul_of_nonneg_left h (sq_nonneg (weights p i))]

end LongTails.Proofs.OptimumHeterogeneityAllocation
