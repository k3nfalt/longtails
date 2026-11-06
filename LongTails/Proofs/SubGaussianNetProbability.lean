import LongTails.Proofs.SubGaussianMatrixNet
import LongTails.Proofs.EuclideanGridNet
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SubGaussianNetProbability

lemma abs_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c P) (B : ℝ) (hB : 0 ≤ B) :
    P.real {ω | B < |X ω|} ≤ 2 * Real.exp (-B ^ 2 / (2 * c)) := by
  have hp := h.measure_ge_le hB
  have hn := h.neg.measure_ge_le hB
  have hs : {ω | B < |X ω|} ⊆ {ω | B ≤ X ω} ∪ {ω | B ≤ (-X) ω} := by
    intro ω hω
    change B < |X ω| at hω
    rcases le_total 0 (X ω) with hx | hx
    · left
      simpa only [Set.mem_ofPred_eq, abs_of_nonneg hx] using hω.le
    · right
      simpa only [Set.mem_ofPred_eq, abs_of_nonpos hx, Pi.neg_apply] using hω.le
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by linarith))

lemma finite_abs_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {c : ℝ≥0}
    (h : ∀ i, HasSubgaussianMGF (X i) c P) (B : ℝ) (hB : 0 ≤ B) :
    P.real {ω | ∃ i, B < |X i ω|} ≤
      2 * Fintype.card ι * Real.exp (-B ^ 2 / (2 * c)) := by
  have heq : {ω | ∃ i, B < |X i ω|} = ⋃ i, {ω | B < |X i ω|} := by ext ω; simp
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    ∑ i, P.real {ω | B < |X i ω|} ≤ ∑ _i : ι, 2 * Real.exp (-B ^ 2 / (2 * c)) :=
      Finset.sum_le_sum fun i _ => abs_tail (h i) B hB
    _ = _ := by simp; ring

open EuclideanGridNet

lemma vector_net_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (k : ℕ) (X : Ω → Point k)
    (c : ℝ≥0) (B : ℝ) (hB : 0 ≤ B)
    (hmgf : ∀ u ∈ grid k, HasSubgaussianMGF (fun ω => ⟪X ω, u⟫) c P) :
    P.real {ω | 2 * B < ‖X ω‖} ≤
      2 * (grid k).card * Real.exp (-B ^ 2 / (2 * c)) := by
  classical
  let ι := {u : Point k // u ∈ grid k}
  have hs : {ω | 2 * B < ‖X ω‖} ⊆ {ω | ∃ u : ι, B < |⟪X ω, u.val⟫|} := by
    intro ω hω
    by_contra hnot
    have hb : ∀ u ∈ grid k, |⟪X ω, u⟫| ≤ B := by
      intro u hu
      exact le_of_not_gt (fun h => hnot ⟨⟨u, hu⟩, h⟩)
    have hn := SubGaussianMatrixNet.norm_of_inner_net (X ω) (grid k) B hB
      (grid_covers_unit k) hb
    exact not_lt_of_ge hn hω
  have ht := finite_abs_tail (fun u : ι => hmgf u.val u.property) B hB
  exact (measureReal_mono hs).trans (by simpa [ι] using ht)

lemma matrix_net_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (m T : ℕ)
    (L : Ω → Point T →L[ℝ] Point m) (c : ℝ≥0) (B : ℝ) (hB : 0 ≤ B)
    (hmgf : ∀ u ∈ grid T, ∀ v ∈ grid m,
      HasSubgaussianMGF (fun ω => ⟪L ω u, v⟫) c P) :
    P.real {ω | 2 * B < ‖L ω‖} ≤
      2 * (grid T).card * (grid m).card * Real.exp (-B ^ 2 / (2 * c)) := by
  classical
  let ι := {u : Point T // u ∈ grid T} × {v : Point m // v ∈ grid m}
  have hs : {ω | 2 * B < ‖L ω‖} ⊆
      {ω | ∃ i : ι, B < |⟪L ω i.1.val, i.2.val⟫|} := by
    intro ω hω
    by_contra hnot
    have hb : ∀ u ∈ grid T, ∀ v ∈ grid m, |⟪L ω u, v⟫| ≤ B := by
      intro u hu v hv
      exact le_of_not_gt (fun h => hnot ⟨(⟨u, hu⟩, ⟨v, hv⟩), h⟩)
    have hn := SubGaussianMatrixNet.operator_norm_of_bilinear_net (L ω) (grid T) (grid m) B hB
      (grid_covers_unit T) (grid_covers_unit m) (grid_norm T) hb
    exact not_lt_of_ge hn hω
  have ht := finite_abs_tail
    (fun i : ι => hmgf i.1.val i.1.property i.2.val i.2.property) B hB
  exact (measureReal_mono hs).trans (by simpa [ι, mul_assoc] using ht)

noncomputable def columnOperator {m T : ℕ} (e : Fin T → Point m) : Point T →L[ℝ] Point m :=
  ∑ i, (EuclideanSpace.proj i).smulRight (e i)

lemma columnOperator_apply {m T : ℕ} (e : Fin T → Point m) (a : Point T) :
    columnOperator e a = ∑ i, a i • e i := by
  simp [columnOperator, ContinuousLinearMap.smulRight_apply]

lemma columnOperator_square_bound {m T : ℕ} (e : Fin T → Point m) (V : ℝ)
    (hV : ‖columnOperator e‖ ^ 2 ≤ V) (a : Fin T → ℝ) :
    ‖∑ i, a i • e i‖ ^ 2 ≤ V * ∑ i, a i ^ 2 := by
  let x : Point T := WithLp.toLp 2 a
  have h := (columnOperator e).le_opNorm x
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg x))).2 h
  rw [mul_pow] at hs
  have hm := mul_le_mul_of_nonneg_right hV (sq_nonneg ‖x‖)
  have hh := hs.trans hm
  simpa only [columnOperator_apply, EuclideanSpace.real_norm_sq_eq, x] using hh

lemma squared_tail_conversion {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → ℝ) (c S C : ℝ)
    (hc : 0 < c) (hS : 0 ≤ S)
    (htail : ∀ B, 0 ≤ B → P.real {ω | 2*B < X ω} ≤ C*Real.exp (-B^2/(2*c))) :
    P.real {ω | 8*c*S < (X ω)^2 ∧ 0 ≤ X ω} ≤ C*Real.exp (-S) := by
  let B := Real.sqrt (2*c*S)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B^2 = 2*c*S := Real.sq_sqrt (by positivity)
  have he : -B^2/(2*c) = -S := by rw [hBs]; field_simp
  have hs : {ω | 8*c*S < (X ω)^2 ∧ 0 ≤ X ω} ⊆ {ω | 2*B < X ω} := by
    intro ω hω
    change 8*c*S < (X ω)^2 ∧ 0 ≤ X ω at hω
    change 2*B < X ω
    nlinarith
  have hh := htail B hB
  rw [he] at hh
  exact (measureReal_mono hs).trans hh

lemma vector_square_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (k : ℕ) (X : Ω → Point k)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) (S : ℝ) (hS : 0 ≤ S)
    (hmgf : ∀ u ∈ grid k, HasSubgaussianMGF (fun ω => ⟪X ω, u⟫) c P) :
    P.real {ω | 8*c*S < ‖X ω‖^2} ≤ 2*(grid k).card*Real.exp (-S) := by
  have hh := squared_tail_conversion (fun ω => ‖X ω‖) c S (2*(grid k).card) hc hS
    (fun B hB => vector_net_tail k X c B hB hmgf)
  simpa only [norm_nonneg, and_true] using hh

lemma matrix_square_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (m T : ℕ)
    (L : Ω → Point T →L[ℝ] Point m) (c : ℝ≥0) (hc : 0 < (c : ℝ)) (S : ℝ) (hS : 0 ≤ S)
    (hmgf : ∀ u ∈ grid T, ∀ v ∈ grid m,
      HasSubgaussianMGF (fun ω => ⟪L ω u, v⟫) c P) :
    P.real {ω | 8*c*S < ‖L ω‖^2} ≤ 2*(grid T).card*(grid m).card*Real.exp (-S) := by
  have hh := squared_tail_conversion (fun ω => ‖L ω‖) c S
    (2*(grid T).card*(grid m).card) hc hS
    (fun B hB => matrix_net_tail m T L c B hB hmgf)
  simpa only [norm_nonneg, and_true] using hh

lemma grid_card_le_exp (k : ℕ) :
    ((grid k).card : ℝ) ≤ Real.exp ((k : ℝ)*Real.log (16*(k : ℝ)+1)) := by
  rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  exact_mod_cast grid_card k

lemma entropy_tail_prefactor (C H ρ : ℝ) (hρ : 0 < ρ) (hC : C ≤ Real.exp H) :
    2*C*Real.exp (-(H+Real.log (4/ρ))) ≤ ρ/2 := by
  have he : Real.exp H * Real.exp (-(H+Real.log (4/ρ))) = ρ/4 := by
    rw [← Real.exp_add]
    have hx : H + -(H+Real.log (4/ρ)) = -Real.log (4/ρ) := by ring
    rw [hx, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hm := mul_le_mul_of_nonneg_right hC (Real.exp_pos (-(H+Real.log (4/ρ)))).le
  rw [he] at hm
  nlinarith

lemma grid_product_failure_bound (m T : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    2*(grid T).card*(grid m).card * Real.exp (-((m : ℝ)*Real.log (16*(m : ℝ)+1) +
      (T : ℝ)*Real.log (16*(T : ℝ)+1) + Real.log (4/ρ))) ≤ ρ/2 := by
  have hc : ((grid T).card : ℝ)*(grid m).card ≤
      Real.exp ((m : ℝ)*Real.log (16*(m : ℝ)+1)+(T : ℝ)*Real.log (16*(T : ℝ)+1)) := by
    rw [Real.exp_add]
    have hh := mul_le_mul (grid_card_le_exp T) (grid_card_le_exp m)
      (Nat.cast_nonneg _) (Real.exp_pos _).le
    simpa only [mul_comm] using hh
  have hh := entropy_tail_prefactor (((grid T).card : ℝ)*(grid m).card)
    ((m : ℝ)*Real.log (16*(m : ℝ)+1)+(T : ℝ)*Real.log (16*(T : ℝ)+1)) ρ hρ hc
  simpa only [mul_assoc] using hh

lemma grid_vector_failure_bound (m T : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    2*(grid T).card * Real.exp (-((m : ℝ)*Real.log (16*(m : ℝ)+1) +
      (T : ℝ)*Real.log (16*(T : ℝ)+1) + Real.log (4/ρ))) ≤ ρ/2 := by
  have hm : 0 ≤ (m : ℝ)*Real.log (16*(m : ℝ)+1) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hc := (grid_card_le_exp T).trans (Real.exp_le_exp.mpr
    (show (T : ℝ)*Real.log (16*(T : ℝ)+1) ≤
      (m : ℝ)*Real.log (16*(m : ℝ)+1)+(T : ℝ)*Real.log (16*(T : ℝ)+1) by linarith))
  exact entropy_tail_prefactor _ _ ρ hρ hc

lemma grid_entropy_nonneg (m T : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ (m : ℝ)*Real.log (16*(m : ℝ)+1) +
      (T : ℝ)*Real.log (16*(T : ℝ)+1) + Real.log (4/ρ) := by
  have hn (k : ℕ) : 0 ≤ (k : ℝ)*Real.log (16*(k : ℝ)+1) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hr : 0 ≤ Real.log (4/ρ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hρ).mpr
    linarith
  exact add_nonneg (add_nonneg (hn m) (hn T)) hr

lemma joint_net_square_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (m T : ℕ)
    (L : Ω → Point T →L[ℝ] Point m) (Z : Ω → Point T)
    (ν R ρ : ℝ) (hν : 0 < ν) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : ∀ u ∈ grid T, ∀ v ∈ grid m,
      HasSubgaussianMGF (fun ω => ⟪L ω u, v⟫) ⟨16*ν, by positivity⟩ P)
    (hv : ∀ u ∈ grid T,
      HasSubgaussianMGF (fun ω => ⟪Z ω, u⟫) ⟨16*ν*R^2, by positivity⟩ P) :
    let S := (m : ℝ)*Real.log (16*(m : ℝ)+1) +
      (T : ℝ)*Real.log (16*(T : ℝ)+1) + Real.log (4/ρ)
    P.real {ω | 128*ν*S < ‖L ω‖^2 ∨ 128*ν*R^2*S < ‖Z ω‖^2} ≤ ρ := by
  dsimp only
  let S := (m : ℝ)*Real.log (16*(m : ℝ)+1) +
    (T : ℝ)*Real.log (16*(T : ℝ)+1) + Real.log (4/ρ)
  have hS : 0 ≤ S := grid_entropy_nonneg m T ρ hρ hρ1
  have hm' := matrix_square_tail m T L ⟨16*ν, by positivity⟩ (by change 0 < 16*ν; positivity) S hS hm
  have hv' := vector_square_tail T Z ⟨16*ν*R^2, by positivity⟩ (by change 0 < 16*ν*R^2; positivity) S hS hv
  have hme : 8*(16*ν)*S = 128*ν*S := by ring
  have hve : 8*(16*ν*R^2)*S = 128*ν*R^2*S := by ring
  change P.real {ω | 8*(16*ν)*S < ‖L ω‖^2} ≤
    2*(grid T).card*(grid m).card*Real.exp (-S) at hm'
  change P.real {ω | 8*(16*ν*R^2)*S < ‖Z ω‖^2} ≤
    2*(grid T).card*Real.exp (-S) at hv'
  rw [hme] at hm'
  rw [hve] at hv'
  have hmb := hm'.trans (grid_product_failure_bound m T ρ hρ)
  have hvb := hv'.trans (grid_vector_failure_bound m T ρ hρ)
  have hu := measureReal_union_le {ω | 128*ν*S < ‖L ω‖^2} {ω | 128*ν*R^2*S < ‖Z ω‖^2} (μ := P)
  change P.real ({ω | 128*ν*S < ‖L ω‖^2} ∪ {ω | 128*ν*R^2*S < ‖Z ω‖^2}) ≤ ρ
  linarith

end LongTails.Proofs.SubGaussianNetProbability
