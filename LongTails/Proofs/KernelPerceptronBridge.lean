import LongTails.Setups.KernelConvolutionalPerceptron
import LongTails.Algorithms.KernelConvolutionalPerceptron
import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
import LongTails.Proofs.KernelPerceptronAnalysis
import LongTails.Proofs.Execution

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.KernelPerceptronGeometry

open LongTails.Setups.KernelConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift ones)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry (axis_inner axis_norm shift_axis axis_shift_inner)
open KernelPerceptronDynamics

variable {k d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

section Shifts

variable {d : ℕ}

lemma shifted_zero (b : Features d) : shifted 0 b = b := rfl

lemma shifted_succ (j : ℕ) (b : Features d) : shifted (j + 1) b = shift (shifted j b) := by
  simp [shifted, Function.iterate_succ_apply']

lemma shifted_axis (j : ℕ) : shifted j (axis d) = axis d := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, ih, shift_axis]

lemma shifted_add (j : ℕ) (x y : Features d) : shifted j (x + y) = shifted j x + shifted j y := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, shifted_succ, shifted_succ, ih, shift_add]

lemma shifted_smul (j : ℕ) (a : ℝ) (x : Features d) : shifted j (a • x) = a • shifted j x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, shifted_succ, ih, shift_smul]

lemma shifted_sub (j : ℕ) (x y : Features d) : shifted j (x - y) = shifted j x - shifted j y := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, shifted_succ, shifted_succ, ih, shift_sub]

lemma norm_shifted (j : ℕ) (x : Features d) : ‖shifted j x‖ = ‖x‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, norm_shift, ih]

lemma axis_shifted_inner (j : ℕ) (u : Features d) : ⟪axis d, shifted j u⟫ = ⟪axis d, u⟫ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shifted_succ, axis_shift_inner, ih]

lemma shifted_sum {ι : Type*} (s : Finset ι) (j : ℕ) (f : ι → Features d) :
    shifted j (∑ i ∈ s, f i) = ∑ i ∈ s, shifted j (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using shifted_smul j 0 (0 : Features d)
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, shifted_add, ih]

end Shifts

section FilterSpace

variable {k : ℕ}

noncomputable def onesK (k : ℕ) : Filter k := WithLp.toLp 2 fun _ => 1

lemma onesK_apply (j : Fin k) : onesK k j = 1 := rfl

lemma filter_inner_eq_sum (x y : Filter k) : ⟪x, y⟫ = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

lemma filter_norm_sq (x : Filter k) : ‖x‖ ^ 2 = ∑ j, x j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, filter_inner_eq_sum]
  simp [sq]

lemma onesK_inner (x : Filter k) : ⟪onesK k, x⟫ = ∑ j, x j := by
  rw [filter_inner_eq_sum]; simp [onesK_apply]

lemma sum_abs_le_sqrt (x : Filter k) : ∑ j, |x j| ≤ Real.sqrt k * ‖x‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |x j|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sq_abs] at h
  rw [← filter_norm_sq] at h
  have hs : 0 ≤ ∑ j, |x j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hk : (0 : ℝ) ≤ k := by positivity
  have hr : Real.sqrt k * ‖x‖ = Real.sqrt (k * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul hk, Real.sqrt_sq (norm_nonneg _)]
  rw [hr]
  exact Real.le_sqrt_of_sq_le (by linarith)

lemma centered_norm_le (x : Filter k) (m : ℝ) (hm : (k : ℝ) * m = ∑ j, x j) :
    ∑ j, |x j - m| ≤ Real.sqrt k * ‖x‖ := by
  have h1 := sum_abs_le_sqrt (x - (WithLp.toLp 2 fun _ => m))
  have h2 : ∀ j, (x - (WithLp.toLp 2 fun _ => m) : Filter k) j = x j - m := fun j => rfl
  simp only [h2] at h1
  have h3 : ‖x - (WithLp.toLp 2 fun _ => m)‖ ≤ ‖x‖ := by
    have hsq : ‖x - (WithLp.toLp 2 fun _ => m)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [filter_norm_sq, filter_norm_sq]
      simp only [h2]
      have : ∑ j, (x j - m) ^ 2 = ∑ j, x j ^ 2 - 2 * m * ∑ j, x j + k * m ^ 2 := by
        have e : ∀ j, (x j - m) ^ 2 = x j ^ 2 - 2 * m * x j + m ^ 2 := fun j => by ring
        simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      rw [this, ← hm]
      nlinarith [sq_nonneg m, (by positivity : (0:ℝ) ≤ k)]
    exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2
  have hk : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  calc ∑ j, |x j - m| ≤ Real.sqrt k * ‖x - (WithLp.toLp 2 fun _ => m)‖ := h1
    _ ≤ Real.sqrt k * ‖x‖ := mul_le_mul_of_nonneg_left h3 hk

end FilterSpace

section Features

variable (G : Geometry k D g R μ κ)

noncomputable def plusFeature (i : Fin (n + 1)) : Features d :=
  (Real.sqrt k)⁻¹ • ∑ j : Fin k, shifted j (G.defect i)

noncomputable def centeredShift (i : Fin (n + 1)) (j : Fin k) : Features d :=
  shifted j (G.defect i) - (k : ℝ)⁻¹ • ∑ l : Fin k, shifted l (G.defect i)

noncomputable def highOp (i : Fin (n + 1)) : Filter k →L[ℝ] Features d :=
  ∑ j : Fin k, (EuclideanSpace.proj j).smulRight (centeredShift G i j)

lemma highOp_apply (i : Fin (n + 1)) (t : Filter k) :
    highOp G i t = ∑ j : Fin k, t j • centeredShift G i j := by
  simp [highOp, ContinuousLinearMap.smulRight_apply]

lemma highOp_apply' (i : Fin (n + 1)) (t : Filter k) :
    highOp G i t = ∑ j : Fin k, (t j - (k : ℝ)⁻¹ * ∑ l, t l) • shifted j (G.defect i) := by
  rw [highOp_apply]
  simp only [centeredShift, smul_sub, Finset.sum_sub_distrib, sub_smul]
  congr 1
  rw [← Finset.sum_smul, ← Finset.smul_sum, smul_smul, mul_comm]

lemma highOp_sum_zero_apply (i : Fin (n + 1)) (t : Filter k) (ht : ∑ j, t j = 0) :
    highOp G i t = ∑ j : Fin k, t j • shifted j (G.defect i) := by
  rw [highOp_apply', ht]
  simp

lemma plusFeature_centered (i : Fin (n + 1)) : ⟪axis d, plusFeature G i⟫ = 0 := by
  simp only [plusFeature, real_inner_smul_right, inner_sum, axis_shifted_inner, G.centered,
    Finset.sum_const_zero, mul_zero]

lemma centeredShift_centered (i : Fin (n + 1)) (j : Fin k) :
    ⟪axis d, centeredShift G i j⟫ = 0 := by
  simp only [centeredShift, inner_sub_right, real_inner_smul_right, inner_sum,
    axis_shifted_inner, G.centered, Finset.sum_const_zero, mul_zero, sub_zero]

lemma highOp_centered (i : Fin (n + 1)) (t : Filter k) : ⟪axis d, highOp G i t⟫ = 0 := by
  rw [highOp_apply]
  simp only [inner_sum, real_inner_smul_right, centeredShift_centered, mul_zero,
    Finset.sum_const_zero]

lemma centeredShift_sum (hk : 0 < k) (i : Fin (n + 1)) :
    ∑ j : Fin k, centeredShift G i j = 0 := by
  unfold centeredShift
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (k : ℝ) * (k : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [this, one_smul, sub_self]

lemma plusFeature_norm (hk : 0 < k) (i : Fin (n + 1)) : ‖plusFeature G i‖ ≤ 1 := by
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have h1 : ‖∑ j : Fin k, shifted j (G.defect i)‖ ≤ ∑ j : Fin k, ‖G.defect i‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [norm_shifted]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 := G.defect_norm i
  unfold plusFeature
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hk2 : (Real.sqrt k)⁻¹ * ((k : ℝ) * (Real.sqrt k)⁻¹) = 1 := by
    have : Real.sqrt (k : ℝ) * Real.sqrt k = k := Real.mul_self_sqrt (by positivity)
    field_simp
    linarith
  calc (Real.sqrt k)⁻¹ * ‖∑ j : Fin k, shifted j (G.defect i)‖
      ≤ (Real.sqrt k)⁻¹ * ((k : ℝ) * (Real.sqrt k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hs).le
        calc ‖∑ j : Fin k, shifted j (G.defect i)‖ ≤ (k : ℝ) * ‖G.defect i‖ := h1
          _ ≤ (k : ℝ) * (Real.sqrt k)⁻¹ := by gcongr
    _ = 1 := hk2

lemma highOp_norm (hk : 0 < k) (i : Fin (n + 1)) : ‖highOp G i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro t
  rw [highOp_apply', one_mul]
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have h1 : ‖∑ j : Fin k, (t j - (k : ℝ)⁻¹ * ∑ l, t l) • shifted j (G.defect i)‖ ≤
      ∑ j : Fin k, |t j - (k : ℝ)⁻¹ * ∑ l, t l| * ‖G.defect i‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, Real.norm_eq_abs, norm_shifted]
  rw [← Finset.sum_mul] at h1
  have h2 := centered_norm_le t ((k : ℝ)⁻¹ * ∑ l, t l) (by field_simp)
  have h3 := G.defect_norm i
  have hk2 : Real.sqrt (k : ℝ) * (Real.sqrt k)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  calc _ ≤ (∑ j : Fin k, |t j - (k : ℝ)⁻¹ * ∑ l, t l|) * ‖G.defect i‖ := h1
    _ ≤ (Real.sqrt k * ‖t‖) * (Real.sqrt k)⁻¹ := by
        apply mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    _ = ‖t‖ := by rw [mul_comm (Real.sqrt (k:ℝ)) ‖t‖, mul_assoc, hk2, mul_one]

end Features

section Decode

variable (G : Geometry k D g R μ κ)

noncomputable def decode (ε : ℝ) (x : State (Filter k) (Features d)) : Space k d :=
  ((x.a / Real.sqrt k) • onesK k + x.t, x.q • axis d + ε • x.z)

noncomputable def startFilter (k : ℕ) : Filter k :=
  WithLp.toLp 2 fun j => (if j.val = 0 then (1 : ℝ) else 0) - (k : ℝ)⁻¹

lemma startFilter_apply (j : Fin k) :
    startFilter k j = (if j.val = 0 then (1 : ℝ) else 0) - (k : ℝ)⁻¹ := rfl

lemma sum_indicator_zero (hk : 0 < k) :
    ∑ j : Fin k, (if j.val = 0 then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp
  · intro j _ hj
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma startFilter_sum (hk : 0 < k) : ∑ j : Fin k, startFilter k j = 0 := by
  simp only [startFilter_apply, Finset.sum_sub_distrib, sum_indicator_zero hk, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (by positivity : (k : ℝ) ≠ 0)]
  ring

lemma startFilter_norm_sq (hk : 0 < k) : ‖startFilter k‖ ^ 2 = 1 - (k : ℝ)⁻¹ := by
  rw [filter_norm_sq]
  simp only [startFilter_apply, sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ j : Fin k, (if j.val = 0 then (1 : ℝ) else 0) ^ 2 = 1 := by
    have e : ∀ j : Fin k, (if j.val = 0 then (1 : ℝ) else 0) ^ 2 = if j.val = 0 then 1 else 0 :=
      fun j => by split_ifs <;> norm_num
    simp only [e]
    exact sum_indicator_zero hk
  have h2 : ∑ j : Fin k, 2 * (if j.val = 0 then (1 : ℝ) else 0) * (k : ℝ)⁻¹ = 2 * (k : ℝ)⁻¹ := by
    have : ∀ j : Fin k, 2 * (if j.val = 0 then (1 : ℝ) else 0) * (k : ℝ)⁻¹ =
        (2 * (k : ℝ)⁻¹) * (if j.val = 0 then (1 : ℝ) else 0) := fun j => by ring
    simp only [this, ← Finset.mul_sum, sum_indicator_zero hk, mul_one]
  rw [h1, h2]
  have hk' : (k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma startFilter_highOp (hk : 0 < k) (i : Fin (n + 1)) :
    highOp G i (startFilter k) = G.defect i - (k : ℝ)⁻¹ • ∑ j : Fin k, shifted j (G.defect i) := by
  rw [highOp_sum_zero_apply G i _ (startFilter_sum hk)]
  simp only [startFilter_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp [shifted_zero]
  · intro j _ hj
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma startFilter_margin (hk : 2 ≤ k) (i : Fin (n + 1)) :
    κ * Real.sqrt (1 - (k : ℝ)⁻¹) ≤ ⟪G.separator, highOp G i (startFilter k)⟫ := by
  have hk0 : 0 < k := by omega
  have hk1 : (k : ℝ)⁻¹ ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2
  have hpos : 0 < Real.sqrt (1 - (k : ℝ)⁻¹) := Real.sqrt_pos.mpr (by linarith)
  have hm := G.derivative_margin i
  unfold highPass at hm
  rw [real_inner_smul_right] at hm
  rw [startFilter_highOp G hk0 i]
  have h1 := mul_le_mul_of_nonneg_right hm hpos.le
  have hne := hpos.ne'
  have e : (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ *
      ⟪G.separator, G.defect i - (k : ℝ)⁻¹ • ∑ j : Fin k, shifted j (G.defect i)⟫ *
      Real.sqrt (1 - (k : ℝ)⁻¹) =
      ⟪G.separator, G.defect i - (k : ℝ)⁻¹ • ∑ j : Fin k, shifted j (G.defect i)⟫ := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  linarith

lemma decode_start (hk : 0 < k) (ε : ℝ) :
    decode (k := k) (d := d) ε (start (Real.sqrt k)⁻¹ (startFilter k)) = identityFilter k d := by
  unfold decode start identityFilter
  have hs : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  have hk' : (Real.sqrt k)⁻¹ / Real.sqrt k = (k : ℝ)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  simp only [smul_zero, zero_smul, add_zero]
  refine Prod.ext ?_ rfl
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, onesK_apply, startFilter_apply, smul_eq_mul, mul_one,
    hk']
  ring

lemma response_decode (hk : 0 < k) (ε : ℝ) (x : State (Filter k) (Features d))
    (ht : ∑ j, x.t j = 0) (i : Fin (n + 1)) :
    response (decode ε x).1 (D i) =
      (Real.sqrt k * G.background i / Real.sqrt 2 * x.a) • axis d +
        μ • (x.a • plusFeature G i + highOp G i x.t) := by
  have hc : ∀ j : Fin k, (decode ε x).1 j = x.a / Real.sqrt k + x.t j := fun j => by
    simp [decode, onesK_apply]
  have hs : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  have hsk : Real.sqrt (k : ℝ) * Real.sqrt k = k := Real.mul_self_sqrt (by positivity)
  have hsum : ∑ j : Fin k, (decode ε x).1 j = Real.sqrt k * x.a := by
    simp only [hc, Finset.sum_add_distrib, ht, add_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_assoc', div_eq_iff hs]
    linear_combination (-x.a) * hsk
  have e : ∀ j : Fin k, (decode ε x).1 j • shifted j (D i) =
      ((decode ε x).1 j * (G.background i / Real.sqrt 2)) • axis d +
        (μ * (x.a / Real.sqrt k)) • shifted j (G.defect i) +
        (μ * x.t j) • shifted j (G.defect i) := by
    intro j
    rw [G.sample_eq i, shifted_add, shifted_smul, shifted_smul, shifted_axis, hc j]
    module
  have e2 : ∑ j : Fin k, (μ * x.t j) • shifted j (G.defect i) =
      μ • ∑ j : Fin k, x.t j • shifted j (G.defect i) := by
    rw [Finset.smul_sum]
    simp only [smul_smul]
  unfold response
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.sum_mul, hsum, ← Finset.smul_sum, e2,
    highOp_sum_zero_apply G i x.t ht]
  unfold plusFeature
  module

noncomputable def bcoef (η : ℝ) (i : Fin (n + 1)) : ℝ :=
  η * (Real.sqrt k * G.background i / Real.sqrt 2)

lemma decode_fst_apply (ε : ℝ) (x : State (Filter k) (Features d)) (j : Fin k) :
    (decode ε x).1 j = x.a / Real.sqrt k + x.t j := by
  simp [decode, onesK_apply]

lemma decode_axis_inner (hd : 0 < d) (ε : ℝ) (x : State (Filter k) (Features d))
    (hz : ⟪axis d, x.z⟫ = 0) : ⟪axis d, (decode ε x).2⟫ = x.q := by
  simp only [decode, inner_add_right, real_inner_smul_right, axis_inner hd, hz, mul_one, mul_zero,
    add_zero]

lemma sample_margin (hd : 0 < d) (hk : 0 < k) (η : ℝ) (x : State (Filter k) (Features d))
    (ht : ∑ j, x.t j = 0) (hz : ⟪axis d, x.z⟫ = 0) (i : Fin (n + 1)) :
    η * margin (D i) (decode (η * μ) x) =
      bcoef G η i * x.a * x.q + (η * μ) ^ 2 * res (plusFeature G i) (highOp G i) x := by
  unfold margin
  rw [response_decode G hk (η * μ) x ht i]
  have hpa : ⟪axis d, plusFeature G i⟫ = 0 := plusFeature_centered G i
  have hRa : ⟪axis d, highOp G i x.t⟫ = 0 := highOp_centered G i x.t
  simp only [decode, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    axis_inner hd, hz, real_inner_comm (axis d) (plusFeature G i), hpa,
    real_inner_comm (axis d) (highOp G i x.t), hRa]
  unfold bcoef res
  ring

lemma highOp_single (i : Fin (n + 1)) (j : Fin k) :
    highOp G i (EuclideanSpace.single j (1 : ℝ)) = centeredShift G i j := by
  rw [highOp_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma highOp_adjoint_apply (i : Fin (n + 1)) (z : Features d) (j : Fin k) :
    (ContinuousLinearMap.adjoint (highOp G i)) z j = ⟪centeredShift G i j, z⟫ := by
  have h1 : (ContinuousLinearMap.adjoint (highOp G i)) z j =
      ⟪(ContinuousLinearMap.adjoint (highOp G i)) z, EuclideanSpace.single j (1 : ℝ)⟫ := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [h1, ContinuousLinearMap.adjoint_inner_left, highOp_single, real_inner_comm]

lemma next_sum_zero (hk : 0 < k) (δ : ℝ) (x : State (Filter k) (Features d)) (ht : ∑ j, x.t j = 0)
    (i : Fin (n + 1)) :
    ∑ j, (x.t + δ • (ContinuousLinearMap.adjoint (highOp G i)) x.z) j = 0 := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ht, zero_add,
    ← Finset.mul_sum, highOp_adjoint_apply, ← sum_inner, centeredShift_sum G hk, inner_zero_left,
    mul_zero]

lemma next_centered (x : State (Filter k) (Features d)) (hz : ⟪axis d, x.z⟫ = 0)
    (i : Fin (n + 1)) :
    ⟪axis d, x.z + x.a • plusFeature G i + highOp G i x.t⟫ = 0 := by
  simp only [inner_add_right, real_inner_smul_right, hz, highOp_centered,
    plusFeature_centered G i, mul_zero, add_zero]

lemma shifted_sample_inner (hd : 0 < d) (ε : ℝ) (x : State (Filter k) (Features d))
    (hz : ⟪axis d, x.z⟫ = 0) (i : Fin (n + 1)) (j : ℕ) :
    ⟪shifted j (D i), (decode ε x).2⟫ =
      G.background i / Real.sqrt 2 * x.q + μ * ε * ⟪shifted j (G.defect i), x.z⟫ := by
  rw [G.sample_eq i, shifted_add, shifted_smul, shifted_smul, shifted_axis]
  have h1 : ⟪shifted j (G.defect i), axis d⟫ = 0 := by
    rw [real_inner_comm, axis_shifted_inner, G.centered]
  simp only [decode, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    axis_inner hd, hz, h1, mul_zero, add_zero, mul_one]
  ring

lemma decode_step (hd : 0 < d) (hk : 0 < k) (η : ℝ) (x : State (Filter k) (Features d))
    (ht : ∑ j, x.t j = 0) (hz : ⟪axis d, x.z⟫ = 0) (i : Fin (n + 1)) :
    decode (η * μ) (step (bcoef G η i) ((η * μ) ^ 2) (plusFeature G i) (highOp G i) x) =
      decode (η * μ) x + η • direction (D i) (decode (η * μ) x) := by
  have hs : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  have hkk : (Real.sqrt k)⁻¹ * (Real.sqrt k)⁻¹ = (k : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · ext j
    have hsh := shifted_sample_inner G hd (η * μ) x hz i j
    simp only [decode] at hsh
    simp only [decode, step, direction, Prod.smul_mk, Prod.mk_add_mk, PiLp.add_apply,
      PiLp.smul_apply, onesK_apply, smul_eq_mul, mul_one]
    rw [highOp_adjoint_apply, hsh]
    unfold bcoef centeredShift plusFeature
    simp only [inner_sub_left, real_inner_smul_left]
    rw [← hkk]
    field_simp
    ring
  · have hr := response_decode G hk (η * μ) x ht i
    simp only [decode] at hr
    simp only [decode, step, direction, Prod.smul_mk, Prod.mk_add_mk]
    rw [hr]
    unfold bcoef
    module

end Decode

end LongTails.Proofs.KernelPerceptronGeometry


namespace LongTails.Proofs.KernelPerceptronExecution

open LongTails.Setups.KernelConvolutionalPerceptron
open LongTails.Algorithms.KernelConvolutionalPerceptron
open KernelPerceptronDynamics
open KernelPerceptronGeometry

variable {k d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

structure Trace (G : Geometry k D g R μ κ) (η : ℝ) where
  length : ℕ
  states : ℕ → State (Filter k) (Features d)
  events : ℕ → Fin (n + 1)
  valid : Trajectory (fun i => bcoef G η i) ((η * μ) ^ 2) (plusFeature G) (highOp G)
    (Real.sqrt k)⁻¹ (startFilter k) states events length

namespace Trace

variable {G : Geometry k D g R μ κ} {η : ℝ}

def endpoint (t : Trace G η) : State (Filter k) (Features d) := t.states t.length

noncomputable def empty (G : Geometry k D g R μ κ) (η : ℝ) : Trace G η where
  length := 0
  states _ := start (Real.sqrt k)⁻¹ (startFilter k)
  events _ := 0
  valid := ⟨rfl, by omega, by omega⟩

noncomputable def append (t : Trace G η) (j : Fin (n + 1))
    (hj : misclassified (bcoef G η j) ((η * μ) ^ 2) (plusFeature G j) (highOp G j) t.endpoint) :
    Trace G η where
  length := t.length + 1
  states := Function.update t.states (t.length + 1)
    (step (bcoef G η j) ((η * μ) ^ 2) (plusFeature G j) (highOp G j) t.endpoint)
  events := Function.update t.events t.length j
  valid := {
    initial := by
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
      exact t.valid.initial
    update := by
      intro m hm
      by_cases hm0 : m < t.length
      · rw [Function.update_of_ne (by omega : m + 1 ≠ t.length + 1),
          Function.update_of_ne (by omega : m ≠ t.length),
          Function.update_of_ne (by omega : m ≠ t.length + 1)]
        exact t.valid.update m hm0
      · have he : m = t.length := by omega
        subst he
        simp [endpoint]
    mistake := by
      intro m hm
      by_cases hm0 : m < t.length
      · rw [Function.update_of_ne (by omega : m ≠ t.length),
          Function.update_of_ne (by omega : m ≠ t.length + 1)]
        exact t.valid.mistake m hm0
      · have he : m = t.length := by omega
        subst he
        simpa [Function.update_of_ne (by omega : t.length ≠ t.length + 1), endpoint] using hj }

lemma append_endpoint (t : Trace G η) (j : Fin (n + 1))
    (hj : misclassified (bcoef G η j) ((η * μ) ^ 2) (plusFeature G j) (highOp G j) t.endpoint) :
    (t.append j hj).endpoint =
      step (bcoef G η j) ((η * μ) ^ 2) (plusFeature G j) (highOp G j) t.endpoint := by
  simp [endpoint, append]

end Trace

section Scan

variable (G : Geometry k D g R μ κ) {η : ℝ}

noncomputable def scanStep (D : Data d n) (η : ℝ) (s : ScanState k d n) : ScanState k d n :=
  scanUpdate η s (answer D (s.cursor, s.point))

noncomputable def initialScan : ScanState k d n := ⟨identityFilter k d, 0⟩

structure Ready (Q : ℕ) (s : ScanState k d n) where
  trace : Trace G η
  point_eq : s.point = decode (η * μ) trace.endpoint
  centered : ⟪axis d, trace.endpoint.z⟫ = 0
  sumzero : ∑ j, trace.endpoint.t j = 0
  dirty : Bool
  earlier : dirty = false → ∀ i : Fin (n + 1), i.val < s.cursor.val →
    0 < (answer D (i, s.point)).margin
  accounted : Q + (if dirty then n + 1 else 0) ≤ (n + 1) * trace.length + s.cursor.val

noncomputable def initialReady (hk : 0 < k) : Ready G (η := η) 0 (initialScan (k := k) (d := d) (n := n)) where
  trace := Trace.empty G η
  point_eq := by
    simp only [initialScan, Trace.endpoint, Trace.empty]
    exact (decode_start hk (η * μ)).symm
  centered := by simp [Trace.endpoint, Trace.empty, start]
  sumzero := by
    simp only [Trace.endpoint, Trace.empty, start]
    exact startFilter_sum hk
  dirty := false
  earlier _ i hi := by simp [initialScan] at hi
  accounted := by simp [Trace.empty, initialScan]

lemma rotate_last {i : Fin (n + 1)} (hi : i.val = n) : finRotate (n + 1) i = 0 := by
  have : i = Fin.last n := Fin.ext hi
  rw [this, finRotate_last]

lemma rotate_not_last {i : Fin (n + 1)} (hi : i.val ≠ n) :
    (finRotate (n + 1) i).val = i.val + 1 := by
  have h : i ≠ Fin.last n := fun h => hi (by rw [h]; rfl)
  exact coe_finRotate_of_ne_last h

lemma scanStep_cursor (D : Data d n) (η : ℝ) (s : ScanState k d n) :
    (scanStep D η s).cursor = finRotate (n + 1) s.cursor := rfl

lemma scanStep_wrong_point {s : ScanState k d n}
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (scanStep D η s).point = s.point + η • (answer D (s.cursor, s.point)).direction := by
  simp [scanStep, scanUpdate, hm]

lemma scanStep_correct_point {s : ScanState k d n}
    (hm : 0 < (answer D (s.cursor, s.point)).margin) :
    (scanStep D η s).point = s.point := by
  simp [scanStep, scanUpdate, not_le.mpr hm]

lemma scanStep_good {s : ScanState k d n} (hs : Separates D s.point) :
    Separates D (scanStep D η s).point := by
  rw [scanStep_correct_point (hs s.cursor)]
  exact hs

lemma wrong_permitted (hd : 0 < d) (hk : 0 < k) (hη : 0 < η) {Q : ℕ} {s : ScanState k d n}
    (hs : Ready G (η := η) Q s) (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    misclassified (bcoef G η s.cursor) ((η * μ) ^ 2) (plusFeature G s.cursor)
      (highOp G s.cursor) hs.trace.endpoint := by
  have hmul := mul_nonpos_of_nonneg_of_nonpos hη.le hm
  change η * margin (D s.cursor) s.point ≤ 0 at hmul
  rw [hs.point_eq, sample_margin G hd hk η _ hs.sumzero hs.centered s.cursor] at hmul
  exact hmul

lemma wrong_point (hd : 0 < d) (hk : 0 < k) {Q : ℕ} {s : ScanState k d n}
    (hs : Ready G (η := η) Q s) (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (scanStep D η s).point = decode (η * μ)
      (step (bcoef G η s.cursor) ((η * μ) ^ 2) (plusFeature G s.cursor) (highOp G s.cursor)
        hs.trace.endpoint) := by
  rw [scanStep_wrong_point hm, hs.point_eq, decode_step G hd hk η _ hs.sumzero hs.centered]
  rfl

noncomputable def Ready.wrong (hd : 0 < d) (hk : 0 < k) (hη : 0 < η) {Q : ℕ} {s : ScanState k d n}
    (hs : Ready G (η := η) Q s) (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    Ready G (η := η) (Q + 1) (scanStep D η s) where
  trace := hs.trace.append s.cursor (wrong_permitted G hd hk hη hs hm)
  point_eq := by
    rw [Trace.append_endpoint]
    exact wrong_point G hd hk hs hm
  centered := by
    rw [Trace.append_endpoint]
    exact next_centered G _ hs.centered s.cursor
  sumzero := by
    rw [Trace.append_endpoint]
    exact next_sum_zero G hk _ _ hs.sumzero s.cursor
  dirty := if s.cursor.val = n then false else true
  earlier := by
    intro hclean i hi
    by_cases hl : s.cursor.val = n
    · rw [scanStep_cursor, rotate_last hl] at hi
      simp at hi
    · simp [hl] at hclean
  accounted := by
    have ha := hs.accounted
    have hc := s.cursor.isLt
    change Q + 1 + (if (if s.cursor.val = n then false else true) then n + 1 else 0) ≤
      (n + 1) * (hs.trace.length + 1) + (scanStep D η s).cursor.val
    rw [scanStep_cursor, Nat.mul_add, Nat.mul_one]
    by_cases hl : s.cursor.val = n
    · rw [rotate_last hl]
      simp only [hl, ite_true, Bool.false_eq_true, ite_false, Fin.val_zero, Nat.add_zero]
      split_ifs at ha <;> omega
    · rw [rotate_not_last hl]
      simp only [hl, ite_false, ite_true]
      split_ifs at ha <;> omega

noncomputable def Ready.correctNext {Q : ℕ} {s : ScanState k d n} (hs : Ready G (η := η) Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val ≠ n) :
    Ready G (η := η) (Q + 1) (scanStep D η s) where
  trace := hs.trace
  point_eq := by rw [scanStep_correct_point hm]; exact hs.point_eq
  centered := hs.centered
  sumzero := hs.sumzero
  dirty := hs.dirty
  earlier := by
    intro hclean i hi
    rw [scanStep_cursor, rotate_not_last hl] at hi
    rw [scanStep_correct_point hm]
    by_cases he : i.val < s.cursor.val
    · exact hs.earlier hclean i he
    · have hie : i = s.cursor := Fin.ext (by omega)
      subst i
      exact hm
  accounted := by
    rw [scanStep_cursor, rotate_not_last hl]
    have ha := hs.accounted
    omega

noncomputable def Ready.correctLast {Q : ℕ} {s : ScanState k d n} (hs : Ready G (η := η) Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val = n)
    (hdirty : hs.dirty = true) : Ready G (η := η) (Q + 1) (scanStep D η s) where
  trace := hs.trace
  point_eq := by rw [scanStep_correct_point hm]; exact hs.point_eq
  centered := hs.centered
  sumzero := hs.sumzero
  dirty := false
  earlier := by
    intro _ i hi
    rw [scanStep_cursor, rotate_last hl] at hi
    simp at hi
  accounted := by
    rw [scanStep_cursor, rotate_last hl]
    have ha := hs.accounted
    simp only [hdirty, ite_true, hl] at ha
    simp only [Bool.false_eq_true, ite_false, Fin.val_zero, Nat.add_zero]
    omega

lemma Ready.certified {Q : ℕ} {s : ScanState k d n} (hs : Ready G (η := η) Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val = n)
    (hclean : hs.dirty = false) : Separates D (scanStep D η s).point := by
  rw [scanStep_correct_point hm]
  intro i
  by_cases hi : i.val < s.cursor.val
  · exact hs.earlier hclean i hi
  · have hie : i = s.cursor := Fin.ext (by have := i.isLt; omega)
    subst i
    exact hm

lemma iterate_ready_or_good (hd : 0 < d) (hk : 0 < k) (hη : 0 < η) (Q : ℕ) :
    Separates D ((scanStep D η)^[Q] (initialScan (k := k) (d := d) (n := n))).point ∨
      Nonempty (Ready G (η := η) Q ((scanStep D η)^[Q] initialScan)) := by
  induction Q with
  | zero => exact Or.inr ⟨initialReady G hk⟩
  | succ Q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hg | hs
    · exact Or.inl (scanStep_good hg)
    · let hs := Classical.choice hs
      by_cases hm : (answer D (((scanStep D η)^[Q] (initialScan : ScanState k d n)).cursor,
          ((scanStep D η)^[Q] (initialScan : ScanState k d n)).point)).margin ≤ 0
      · exact Or.inr ⟨hs.wrong G hd hk hη hm⟩
      · have hp := lt_of_not_ge hm
        by_cases hl : ((scanStep D η)^[Q] (initialScan : ScanState k d n)).cursor.val = n
        · cases he : hs.dirty with
          | false => exact Or.inl (hs.certified G hp hl he)
          | true => exact Or.inr ⟨hs.correctLast G hp hl he⟩
        · exact Or.inr ⟨hs.correctNext G hp hl⟩

lemma iterate_separates (hd : 0 < d) (hk : 0 < k) (hη : 0 < η) {L : ℕ}
    (hL : ∀ t : Trace G η, t.length ≤ L) :
    Separates D ((scanStep D η)^[(n + 1) * (L + 2)] (initialScan (k := k) (d := d) (n := n))).point := by
  rcases iterate_ready_or_good G hd hk hη ((n + 1) * (L + 2)) with hg | hs
  · exact hg
  · let hs := Classical.choice hs
    have hlen := hL hs.trace
    have hm := Nat.mul_le_mul_left (n + 1) hlen
    have ha := hs.accounted
    have hc := ((scanStep D η)^[(n + 1) * (L + 2)] (initialScan (k := k) (d := d) (n := n))).cursor.isLt
    simp only [Nat.mul_succ] at ha hm
    split_ifs at ha <;> omega

end Scan

section Execute

open OracleTemplate

variable (p : Params) (D : Data p.dimension p.samples)
  (O : Oracle (Query p.kernel p.dimension p.samples) (Reply p.kernel p.dimension))

lemma output_eq_iterate (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    output p O K seed ξ = ((scanStep D (stepSize p))^[K] initialScan).point := by
  unfold output
  rw [OracleTemplate.execute_eq_of_answer_eq O (answer D) (fun h q s => hlaw h (0, q) s),
    OracleTemplate.execute_iterate]
  rfl

end Execute

end LongTails.Proofs.KernelPerceptronExecution
