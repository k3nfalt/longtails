import LongTails.Algorithms.AffineSoftmaxProx
import LongTails.Proofs.AffineSoftmaxBallSolver

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxMultilevel

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open OracleTemplate.ComponentEnvelope

lemma truncated_geometric_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : ℕ → E) (J : ℕ) :
    (∫ k : ℕ, (if k < J then (2 : ℝ) ^ (k + 1) • d k else 0)
      ∂(countLaw : Measure ℕ)) = ∑ k ∈ Finset.range J, d k := by
  change (∫ k : ℕ, (if k < J then (2 : ℝ) ^ (k + 1) • d k else 0)
    ∂ProbabilityTheory.geometricMeasure halfSuccess) = _
  rw [ProbabilityTheory.integral_geometricMeasure AffineSoftmaxSampling.halfSuccess_ne_zero]
  have he (k : ℕ) :
      ((1 - (halfSuccess : ℝ)) ^ k * (halfSuccess : ℝ)) •
        (if k < J then (2 : ℝ) ^ (k + 1) • d k else 0) =
      if k < J then d k else 0 := by
    split_ifs with hk
    · rw [smul_smul]
      have hw : ((1 - (halfSuccess : ℝ)) ^ k * (halfSuccess : ℝ)) * (2 : ℝ) ^ (k + 1) = 1 := by
        change ((1 - 1 / 2 : ℝ) ^ k * (1 / 2)) * 2 ^ (k + 1) = 1
        rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
        have hp : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
        rw [pow_succ]
        calc
          _ = ((1 / 2 : ℝ) ^ k * 2 ^ k) * ((1 / 2) * 2) := by ring
          _ = 1 := by rw [hp]; norm_num
      rw [hw, one_smul]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range J) (fun k hk =>
    ite_eq_right (by simpa only [Finset.mem_range] using hk))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [ite_eq_left (Finset.mem_range.mp hk)]



lemma truncated_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : ProbabilityMeasure Ω)
    (d : ℕ → Ω → E) (hd : ∀ k, Integrable (d k) (Q : Measure Ω)) (J : ℕ) :
    Integrable (fun z : ℕ × Ω => if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0)
      ((countLaw : Measure ℕ).prod (Q : Measure Ω)) := by
  induction J with
  | zero => simpa only [Nat.not_lt_zero, ite_false] using
      (integrable_const (0 : E) : Integrable (fun _ : ℕ × Ω => (0 : E)) _)
  | succ J ih =>
    have hs : MeasurableSet {z : ℕ × Ω | z.1 = J} :=
      measurable_fst (measurableSet_singleton J)
    have hp := Integrable.piecewise hs
      ((((hd J).comp_snd (countLaw : Measure ℕ)).smul ((2 : ℝ) ^ (J + 1))).integrableOn)
      ih.integrableOn
    convert hp using 1
    funext z
    by_cases h : z.1 = J
    · simp [h]
    · by_cases hk : z.1 < J
      · simp [h, hk, show z.1 < J + 1 by omega]
      · simp [h, hk, show ¬z.1 < J + 1 by omega]

lemma truncated_random_mean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : ProbabilityMeasure Ω) (d : ℕ → Ω → E)
    (hd : ∀ k, Integrable (d k) (Q : Measure Ω)) (J : ℕ) :
    (∫ z : ℕ × Ω, (if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0)
      ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) =
      ∑ k ∈ Finset.range J, ∫ ω, d k ω ∂(Q : Measure Ω) := by
  rw [integral_prod _ (truncated_integrable Q d hd J)]
  have he (k : ℕ) :
      (∫ ω, (if k < J then (2 : ℝ) ^ (k + 1) • d k ω else 0) ∂(Q : Measure Ω)) =
      if k < J then (2 : ℝ) ^ (k + 1) • (∫ ω, d k ω ∂(Q : Measure Ω)) else 0 := by
    by_cases hk : k < J <;> simp only [hk, ite_true, ite_false, integral_smul, integral_zero]
  simp_rw [he]
  exact truncated_geometric_mean _ J


lemma multilevel_mean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : ProbabilityMeasure Ω) (B : Ω → E) (F C : ℕ → Ω → E)
    (hB : Integrable B (Q : Measure Ω))
    (hF : ∀ j, Integrable (F j) (Q : Measure Ω))
    (hC : ∀ j, Integrable (C j) (Q : Measure Ω))
    (m : ℕ → E) (hmB : (∫ ω, B ω ∂(Q : Measure Ω)) = m 0)
    (hmF : ∀ j, (∫ ω, F j ω ∂(Q : Measure Ω)) = m j)
    (hmC : ∀ j, (∫ ω, C j ω ∂(Q : Measure Ω)) = m j) (J : ℕ) :
    (∫ z : ℕ × Ω, B z.2 +
      (if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • (F (z.1 + 1) z.2 - C z.1 z.2) else 0)
      ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) = m J := by
  have hd (k : ℕ) : Integrable (fun ω => F (k + 1) ω - C k ω) (Q : Measure Ω) :=
    (hF (k + 1)).sub (hC k)
  rw [integral_add (hB.comp_snd _) (truncated_integrable Q _ hd J), integral_fun_snd,
    probReal_univ, one_smul, hmB, truncated_random_mean Q _ hd J]
  simp_rw [integral_sub (hF _) (hC _), hmF, hmC]
  have ht : ∀ n : ℕ, m 0 + (∑ k ∈ Finset.range n, (m (k + 1) - m k)) = m n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      abel
  exact ht J


lemma norm_add_square_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hh := norm_add_le a b
  have hs : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hh
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

lemma difference_second_moment_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (Q : ProbabilityMeasure Ω) (F C : Ω → E) (u : E)
    (hF : Integrable (fun ω => ‖F ω - u‖ ^ 2) (Q : Measure Ω))
    (hC : Integrable (fun ω => ‖C ω - u‖ ^ 2) (Q : Measure Ω))
    (hd : Integrable (fun ω => ‖F ω - C ω‖ ^ 2) (Q : Measure Ω)) :
    (∫ ω, ‖F ω - C ω‖ ^ 2 ∂(Q : Measure Ω)) ≤
      2 * (∫ ω, ‖F ω - u‖ ^ 2 ∂(Q : Measure Ω)) +
        2 * (∫ ω, ‖C ω - u‖ ^ 2 ∂(Q : Measure Ω)) := by
  have hh := integral_mono hd ((hF.const_mul 2).add (hC.const_mul 2)) (fun ω => by
    have hb := norm_add_square_le (F ω - u) (u - C ω)
    simpa only [sub_add_sub_cancel, norm_sub_rev u (C ω), Pi.add_apply] using hb)
  simpa only [Pi.add_apply, integral_add (hF.const_mul 2) (hC.const_mul 2), integral_const_mul] using hh

lemma truncated_correction_square {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ProbabilityMeasure Ω) (d : ℕ → Ω → E)
    (hd : ∀ k, Integrable (fun ω => ‖d k ω‖ ^ 2) (Q : Measure Ω)) (J : ℕ) :
    Integrable (fun z : ℕ × Ω =>
      ‖if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0‖ ^ 2)
      ((countLaw : Measure ℕ).prod (Q : Measure Ω)) ∧
    (∫ z : ℕ × Ω, ‖if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0‖ ^ 2
      ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) =
      ∑ k ∈ Finset.range J, (2 : ℝ) ^ (k + 1) * (∫ ω, ‖d k ω‖ ^ 2 ∂(Q : Measure Ω)) := by
  have he (z : ℕ × Ω) :
      ‖if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0‖ ^ 2 =
      if z.1 < J then (2 : ℝ) ^ (z.1 + 1) •
        ((2 : ℝ) ^ (z.1 + 1) * ‖d z.1 z.2‖ ^ 2) else 0 := by
    split_ifs
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [smul_eq_mul]
      ring
    · simp
  constructor
  · simp_rw [he]
    exact truncated_integrable Q (fun k ω => (2 : ℝ) ^ (k + 1) * ‖d k ω‖ ^ 2)
      (fun k => (hd k).const_mul _) J
  · simp_rw [he]
    rw [truncated_random_mean Q (fun k ω => (2 : ℝ) ^ (k + 1) * ‖d k ω‖ ^ 2)
      (fun k => (hd k).const_mul _) J]
    simp only [integral_const_mul]


lemma multilevel_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ProbabilityMeasure Ω) (B : Ω → E) (d : ℕ → Ω → E) (u : E)
    (hB : Integrable B (Q : Measure Ω))
    (hB2 : Integrable (fun ω => ‖B ω - u‖ ^ 2) (Q : Measure Ω))
    (hd : ∀ k, Integrable (d k) (Q : Measure Ω))
    (hd2 : ∀ k, Integrable (fun ω => ‖d k ω‖ ^ 2) (Q : Measure Ω))
    {v : ℝ} (hb : (∫ ω, ‖B ω - u‖ ^ 2 ∂(Q : Measure Ω)) ≤ v)
    (hdb : ∀ k, (∫ ω, ‖d k ω‖ ^ 2 ∂(Q : Measure Ω)) ≤ 6 * v / 2 ^ (k + 1)) (J : ℕ) :
    let Y := fun z : ℕ × Ω => B z.2 +
      (if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0)
    Integrable (fun z => ‖Y z - u‖ ^ 2) ((countLaw : Measure ℕ).prod (Q : Measure Ω)) ∧
      (∫ z, ‖Y z - u‖ ^ 2 ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) ≤
        (2 + 12 * (J : ℝ)) * v := by
  let P := (countLaw : Measure ℕ).prod (Q : Measure Ω)
  let U := fun z : ℕ × Ω => B z.2 - u
  let D := fun z : ℕ × Ω => if z.1 < J then (2 : ℝ) ^ (z.1 + 1) • d z.1 z.2 else 0
  have hUi : Integrable U P := (hB.sub (integrable_const u)).comp_snd _
  have hU2 : Integrable (fun z => ‖U z‖ ^ 2) P := hB2.comp_snd _
  have hDi : Integrable D P := truncated_integrable Q d hd J
  have hDsq := truncated_correction_square Q d hd2 J
  have hD2 : Integrable (fun z => ‖D z‖ ^ 2) P := hDsq.1
  have hsum : Integrable (fun z => ‖U z + D z‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm (hUi.add hDi).aestronglyMeasurable).1
      (((memLp_two_iff_integrable_sq_norm hUi.aestronglyMeasurable).2 hU2).add
        ((memLp_two_iff_integrable_sq_norm hDi.aestronglyMeasurable).2 hD2))
  have htotal := integral_mono hsum ((hU2.const_mul 2).add (hD2.const_mul 2))
    (fun z => norm_add_square_le (U z) (D z))
  simp only [Pi.add_apply, integral_add (hU2.const_mul 2) (hD2.const_mul 2), integral_const_mul] at htotal
  have hbase : (∫ z, ‖U z‖ ^ 2 ∂P) ≤ v := by
    change (∫ z : ℕ × Ω, (fun ω => ‖B ω - u‖ ^ 2) z.2
      ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) ≤ v
    rw [integral_fun_snd (fun ω => ‖B ω - u‖ ^ 2), probReal_univ, one_smul]
    exact hb
  have hcor : (∫ z, ‖D z‖ ^ 2 ∂P) ≤ (J : ℝ) * (6 * v) := by
    rw [show (∫ z, ‖D z‖ ^ 2 ∂P) = _ from hDsq.2]
    calc
      _ ≤ ∑ k ∈ Finset.range J, (2 : ℝ) ^ (k + 1) * (6 * v / 2 ^ (k + 1)) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hdb k) (by positivity))
      _ = (J : ℝ) * (6 * v) := by
        simp only [mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ (_ + 1) ≠ 0),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have he (z : ℕ × Ω) : B z.2 + D z - u = U z + D z := by dsimp [U]; abel
  dsimp only
  change Integrable (fun z => ‖B z.2 + D z - u‖ ^ 2) P ∧
    (∫ z, ‖B z.2 + D z - u‖ ^ 2 ∂P) ≤ (2 + 12 * (J : ℝ)) * v
  simp_rw [he]
  exact ⟨hsum, by nlinarith [htotal, hbase, hcor]⟩


lemma triple_integrals {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : ProbabilityMeasure Ω) (f : Ω → E) :
    (∫ z : Ω × Ω × Ω, f z.1 ∂((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))) =
        ∫ ω, f ω ∂(Q : Measure Ω) ∧
    (∫ z : Ω × Ω × Ω, f z.2.1 ∂((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))) =
        ∫ ω, f ω ∂(Q : Measure Ω) ∧
    (∫ z : Ω × Ω × Ω, f z.2.2 ∂((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))) =
        ∫ ω, f ω ∂(Q : Measure Ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_fun_fst, probReal_univ, one_smul]
  · rw [integral_fun_snd (fun z : Ω × Ω => f z.1), probReal_univ, one_smul,
      integral_fun_fst, probReal_univ, one_smul]
  · rw [integral_fun_snd (fun z : Ω × Ω => f z.2), probReal_univ, one_smul,
      integral_fun_snd, probReal_univ, one_smul]

lemma independent_level_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ProbabilityMeasure Ω) (level : ℕ → Ω → E)
    (hi : ∀ j, Integrable (level j) (Q : Measure Ω)) (J : ℕ) :
    Integrable (fun z : ℕ × (Ω × Ω × Ω) => level 0 z.2.1 +
      (if z.1 + 1 ≤ J then (2 : ℝ) ^ (z.1 + 1) •
        (level (z.1 + 1) z.2.2.1 - level z.1 z.2.2.2) else 0))
      ((countLaw : Measure ℕ).prod
        ((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))) := by
  let T : ProbabilityMeasure (Ω × Ω × Ω) :=
    ⟨(Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)), inferInstance⟩
  have hB : Integrable (fun z : Ω × Ω × Ω => level 0 z.1) (T : Measure _) :=
    (hi 0).comp_fst _
  have hF j : Integrable (fun z : Ω × Ω × Ω => level j z.2.1) (T : Measure _) :=
    ((hi j).comp_fst (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hC j : Integrable (fun z : Ω × Ω × Ω => level j z.2.2) (T : Measure _) :=
    ((hi j).comp_snd (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hd := truncated_integrable T (fun j z => level (j + 1) z.2.1 - level j z.2.2)
    (fun j => (hF (j + 1)).sub (hC j)) J
  have hs := (hB.comp_snd (countLaw : Measure ℕ)).add hd
  change Integrable (fun z : ℕ × (Ω × Ω × Ω) => level 0 z.2.1 +
    (if z.1 < J then (2 : ℝ) ^ (z.1 + 1) •
      (level (z.1 + 1) z.2.2.1 - level z.1 z.2.2.2) else 0))
    ((countLaw : Measure ℕ).prod (T : Measure _)) at hs
  simpa only [T, ProbabilityMeasure.coe_mk, Nat.lt_iff_add_one_le] using hs

lemma independent_level_mean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : ProbabilityMeasure Ω) (level : ℕ → Ω → E)
    (hi : ∀ j, Integrable (level j) (Q : Measure Ω)) (J : ℕ) :
    (∫ z : ℕ × (Ω × Ω × Ω), level 0 z.2.1 +
      (if z.1 + 1 ≤ J then (2 : ℝ) ^ (z.1 + 1) •
        (level (z.1 + 1) z.2.2.1 - level z.1 z.2.2.2) else 0)
      ∂((countLaw : Measure ℕ).prod
        ((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω))))) =
      ∫ ω, level J ω ∂(Q : Measure Ω) := by
  let T : ProbabilityMeasure (Ω × Ω × Ω) :=
    ⟨(Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)), inferInstance⟩
  have hB : Integrable (fun z : Ω × Ω × Ω => level 0 z.1) (T : Measure _) :=
    (hi 0).comp_fst _
  have hF j : Integrable (fun z : Ω × Ω × Ω => level j z.2.1) (T : Measure _) :=
    ((hi j).comp_fst (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hC j : Integrable (fun z : Ω × Ω × Ω => level j z.2.2) (T : Measure _) :=
    ((hi j).comp_snd (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hh := multilevel_mean T _ _ _ hB hF hC (fun j => ∫ ω, level j ω ∂(Q : Measure Ω))
    (triple_integrals Q (level 0)).1 (fun j => (triple_integrals Q (level j)).2.1)
    (fun j => (triple_integrals Q (level j)).2.2) J
  simpa only [T, ProbabilityMeasure.coe_mk, Nat.lt_iff_add_one_le] using hh


lemma difference_square_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (Q : ProbabilityMeasure Ω) (F C : Ω → E) (u : E)
    (hF : Integrable F (Q : Measure Ω)) (hC : Integrable C (Q : Measure Ω))
    (hF2 : Integrable (fun ω => ‖F ω - u‖ ^ 2) (Q : Measure Ω))
    (hC2 : Integrable (fun ω => ‖C ω - u‖ ^ 2) (Q : Measure Ω)) :
    Integrable (fun ω => ‖F ω - C ω‖ ^ 2) (Q : Measure Ω) := by
  have hf := (memLp_two_iff_integrable_sq_norm (hF.sub (integrable_const u)).aestronglyMeasurable).2 hF2
  have hc := (memLp_two_iff_integrable_sq_norm (hC.sub (integrable_const u)).aestronglyMeasurable).2 hC2
  have hh := hf.sub hc
  have he : (fun ω => (F ω - u) - (C ω - u)) = (fun ω => F ω - C ω) := by funext ω; abel
  change MemLp (fun ω => (F ω - u) - (C ω - u)) 2 (Q : Measure Ω) at hh
  rw [he] at hh
  exact (memLp_two_iff_integrable_sq_norm (hF.sub hC).aestronglyMeasurable).1 hh

lemma independent_level_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ProbabilityMeasure Ω) (level : ℕ → Ω → E) (u : E)
    (hi : ∀ j, Integrable (level j) (Q : Measure Ω))
    (hi2 : ∀ j, Integrable (fun ω => ‖level j ω - u‖ ^ 2) (Q : Measure Ω))
    {v : ℝ} (hb : ∀ j, (∫ ω, ‖level j ω - u‖ ^ 2 ∂(Q : Measure Ω)) ≤ v / 2 ^ j) (J : ℕ) :
    let Y := fun z : ℕ × (Ω × Ω × Ω) => level 0 z.2.1 +
      (if z.1 + 1 ≤ J then (2 : ℝ) ^ (z.1 + 1) •
        (level (z.1 + 1) z.2.2.1 - level z.1 z.2.2.2) else 0)
    let P := (countLaw : Measure ℕ).prod
      ((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))
    Integrable (fun z => ‖Y z - u‖ ^ 2) P ∧
      (∫ z, ‖Y z - u‖ ^ 2 ∂P) ≤ (2 + 12 * (J : ℝ)) * v := by
  let T : ProbabilityMeasure (Ω × Ω × Ω) :=
    ⟨(Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)), inferInstance⟩
  let B := fun z : Ω × Ω × Ω => level 0 z.1
  let F := fun j (z : Ω × Ω × Ω) => level j z.2.1
  let C := fun j (z : Ω × Ω × Ω) => level j z.2.2
  have hB : Integrable B (T : Measure _) := (hi 0).comp_fst _
  have hB2 : Integrable (fun z => ‖B z - u‖ ^ 2) (T : Measure _) := (hi2 0).comp_fst _
  have hF j : Integrable (F j) (T : Measure _) :=
    ((hi j).comp_fst (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hC j : Integrable (C j) (T : Measure _) :=
    ((hi j).comp_snd (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hF2 j : Integrable (fun z => ‖F j z - u‖ ^ 2) (T : Measure _) :=
    ((hi2 j).comp_fst (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hC2 j : Integrable (fun z => ‖C j z - u‖ ^ 2) (T : Measure _) :=
    ((hi2 j).comp_snd (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hd j : Integrable (fun z => F (j + 1) z - C j z) (T : Measure _) := (hF _).sub (hC _)
  have hd2 j := difference_square_integrable T (F (j + 1)) (C j) u (hF _) (hC _) (hF2 _) (hC2 _)
  have hbase : (∫ z, ‖B z - u‖ ^ 2 ∂(T : Measure _)) ≤ v := by
    rw [show (∫ z, ‖B z - u‖ ^ 2 ∂(T : Measure _)) =
      (∫ ω, ‖level 0 ω - u‖ ^ 2 ∂(Q : Measure Ω)) from (triple_integrals Q (fun ω => ‖level 0 ω - u‖ ^ 2)).1]
    simpa only [pow_zero, div_one] using hb 0
  have hdiff j : (∫ z, ‖F (j + 1) z - C j z‖ ^ 2 ∂(T : Measure _)) ≤ 6 * v / 2 ^ (j + 1) := by
    have hh := difference_second_moment_le T (F (j + 1)) (C j) u (hF2 _) (hC2 _) (hd2 j)
    have heF : (∫ z, ‖F (j + 1) z - u‖ ^ 2 ∂(T : Measure _)) =
        (∫ ω, ‖level (j + 1) ω - u‖ ^ 2 ∂(Q : Measure Ω)) :=
      (triple_integrals Q (fun ω => ‖level (j + 1) ω - u‖ ^ 2)).2.1
    have heC : (∫ z, ‖C j z - u‖ ^ 2 ∂(T : Measure _)) =
        (∫ ω, ‖level j ω - u‖ ^ 2 ∂(Q : Measure Ω)) :=
      (triple_integrals Q (fun ω => ‖level j ω - u‖ ^ 2)).2.2
    rw [heF, heC] at hh
    have he : 2 * (v / 2 ^ (j + 1)) + 2 * (v / 2 ^ j) = 6 * v / 2 ^ (j + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [← he]
    linarith [hb (j + 1), hb j]
  have hh := multilevel_second_moment T B (fun j z => F (j + 1) z - C j z) u hB hB2 hd hd2
    hbase hdiff J
  simpa only [T, B, F, C, ProbabilityMeasure.coe_mk, Nat.lt_iff_add_one_le] using hh


lemma mean_square_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : ProbabilityMeasure Ω) (X : Ω → E)
    (hX : Integrable X (Q : Measure Ω))
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) (Q : Measure Ω)) :
    ‖∫ ω, X ω ∂(Q : Measure Ω)‖ ^ 2 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂(Q : Measure Ω) := by
  let a := ∫ ω, X ω ∂(Q : Measure Ω)
  have hn : 0 ≤ (∫ ω, ‖X ω - a‖ ^ 2 ∂(Q : Measure Ω)) :=
    integral_nonneg (fun ω => sq_nonneg _)
  simp_rw [norm_sub_sq_real] at hn
  have hi : Integrable (fun ω => 2 * ⟪X ω, a⟫) (Q : Measure Ω) :=
    (hX.inner_const a).const_mul 2
  have hd : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪X ω, a⟫) (Q : Measure Ω) := hX2.sub hi
  rw [integral_add hd (integrable_const _), integral_sub hX2 hi, integral_const_mul] at hn
  have hint : (∫ ω, ⟪X ω, a⟫ ∂(Q : Measure Ω)) = ⟪a, a⟫ := by
    calc
      _ = ∫ ω, ⟪a, X ω⟫ ∂(Q : Measure Ω) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = _ := integral_inner (𝕜 := ℝ) hX a
  rw [hint, real_inner_self_eq_norm_sq] at hn
  simp only [integral_const, probReal_univ, one_smul] at hn
  change ‖a‖ ^ 2 ≤ _
  linarith


lemma multilevel_tuning {μ σ β : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (hβ : 0 < β) :
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let C := 2 + 12 * (J : ℝ)
    let δ := σ ^ 2 / (2 * μ * C)
    0 < δ ∧ μ ^ 2 * C * (2 * δ / μ) = σ ^ 2 ∧
      μ ^ 2 * ((2 * δ / μ) / 2 ^ J) ≤ β ^ 2 := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let C := 2 + 12 * (J : ℝ)
  let δ := σ ^ 2 / (2 * μ * C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    linarith [Nat.cast_nonneg (α := ℝ) J]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨hδ, ?_, ?_⟩
  · change μ ^ 2 * C * (2 * δ / μ) = σ ^ 2
    dsimp [δ]
    field_simp
  · change μ ^ 2 * ((2 * δ / μ) / 2 ^ J) ≤ β ^ 2
    have he : μ ^ 2 * ((2 * δ / μ) / 2 ^ J) = (σ ^ 2 / 2 ^ J) / C := by
      dsimp [δ]
      field_simp
    rw [he]
    exact (div_le_self (by positivity : 0 ≤ σ ^ 2 / (2 : ℝ) ^ J) hC1).trans
      (AffineSoftmaxRestarts.restartRounds_accuracy (d := σ ^ 2) (by positivity))


lemma prox_gradient_moments {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : ProbabilityMeasure Ω) (Y Z : Ω → E) (y u : E) {μ σ β : ℝ}
    (hμ : 0 ≤ μ) (hβ : 0 ≤ β)
    (hY : Integrable Y (Q : Measure Ω)) (hZ : Integrable Z (Q : Measure Ω))
    (hY2 : Integrable (fun ω => ‖Y ω - u‖ ^ 2) (Q : Measure Ω))
    (hZ2 : Integrable (fun ω => ‖Z ω - u‖ ^ 2) (Q : Measure Ω))
    (hm : (∫ ω, Y ω ∂(Q : Measure Ω)) = ∫ ω, Z ω ∂(Q : Measure Ω))
    (hbY : μ ^ 2 * (∫ ω, ‖Y ω - u‖ ^ 2 ∂(Q : Measure Ω)) ≤ σ ^ 2)
    (hbZ : μ ^ 2 * (∫ ω, ‖Z ω - u‖ ^ 2 ∂(Q : Measure Ω)) ≤ β ^ 2) :
    let g := fun ω => μ • (y - Y ω)
    let target := μ • (y - u)
    Integrable g (Q : Measure Ω) ∧
      ‖(∫ ω, g ω ∂(Q : Measure Ω)) - target‖ ≤ β ∧
      Integrable (fun ω => ‖g ω - target‖ ^ 2) (Q : Measure Ω) ∧
      (∫ ω, ‖g ω - target‖ ^ 2 ∂(Q : Measure Ω)) ≤ σ ^ 2 := by
  let g := fun ω => μ • (y - Y ω)
  let target := μ • (y - u)
  have hgi : Integrable g (Q : Measure Ω) := ((integrable_const y).sub hY).smul μ
  have he (ω : Ω) : ‖g ω - target‖ ^ 2 = μ ^ 2 * ‖Y ω - u‖ ^ 2 := by
    have hv : g ω - target = μ • (u - Y ω) := by dsimp [g, target]; module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ, norm_sub_rev u (Y ω), mul_pow]
  have hgi2 : Integrable (fun ω => ‖g ω - target‖ ^ 2) (Q : Measure Ω) :=
    (hY2.const_mul (μ ^ 2)).congr (Filter.Eventually.of_forall (fun ω => (he ω).symm))
  have hmean : (∫ ω, g ω ∂(Q : Measure Ω)) = μ • (y - ∫ ω, Y ω ∂(Q : Measure Ω)) := by
    dsimp [g]
    rw [integral_smul, integral_sub (integrable_const y) hY, integral_const, probReal_univ, one_smul]
  have hz := mean_square_le Q (fun ω => Z ω - u) (hZ.sub (integrable_const u)) hZ2
  rw [integral_sub hZ (integrable_const u), integral_const, probReal_univ, one_smul] at hz
  have hbias : ‖(∫ ω, g ω ∂(Q : Measure Ω)) - target‖ ^ 2 ≤ β ^ 2 := by
    have hv : (∫ ω, g ω ∂(Q : Measure Ω)) - target =
        μ • (u - ∫ ω, Z ω ∂(Q : Measure Ω)) := by rw [hmean, hm]; dsimp [target]; module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ,
      norm_sub_rev u (∫ ω, Z ω ∂(Q : Measure Ω)), mul_pow]
    exact (mul_le_mul_of_nonneg_left hz (sq_nonneg μ)).trans hbZ
  refine ⟨hgi, (sq_le_sq₀ (norm_nonneg _) hβ).1 hbias, hgi2, ?_⟩
  change (∫ ω, ‖g ω - target‖ ^ 2 ∂(Q : Measure Ω)) ≤ σ ^ 2
  simp_rw [he]
  rw [integral_const_mul]
  exact hbY


lemma multilevel_first_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ProxSeed → E) :
    (∫ seed : MultilevelSeed, f seed.2.1 ∂(multilevelLaw : Measure MultilevelSeed)) =
      ∫ seeds, f seeds ∂(proxLaw : Measure ProxSeed) := by
  change (∫ z : ℕ × (ProxSeed × ProxSeed × ProxSeed), f z.2.1
    ∂((countLaw : Measure ℕ).prod ((proxLaw : Measure ProxSeed).prod
      ((proxLaw : Measure ProxSeed).prod (proxLaw : Measure ProxSeed))))) = _
  rw [integral_fun_snd (fun z : ProxSeed × ProxSeed × ProxSeed => f z.1), probReal_univ, one_smul]
  exact (triple_integrals proxLaw f).1


section Execution

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma multilevelPlan_eval (s : Snapshot ι E) (τ L G r μ δ : ℝ)
    (project : E → E) (J : ℕ) (seed : MultilevelSeed) (reply : ι × E → ℝ × E) :
    Program.eval reply (multilevelPlan s τ L G r μ δ project J seed) =
      Program.eval reply (levelPlan s τ L G r μ δ project 0 seed.2.1) +
      if seed.1 + 1 ≤ J then (2 : ℝ) ^ (seed.1 + 1) •
        (Program.eval reply (levelPlan s τ L G r μ δ project (seed.1 + 1) seed.2.2.1) -
          Program.eval reply (levelPlan s τ L G r μ δ project seed.1 seed.2.2.2)) else 0 := by
  by_cases h : seed.1 + 1 ≤ J
  · simp only [multilevelPlan, Program.eval_bind, ite_eq_left h, Program.eval_map]
  · simp only [multilevelPlan, Program.eval_bind, ite_eq_right h, Program.eval, add_zero]

lemma multilevelPlan_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (s : Snapshot ι E) (τ L G r μ δ : ℝ) (project : E → E) (J : ℕ)
    (reply : ι × E → ℝ × E)
    (hm : ∀ j, Measurable (fun seeds =>
      Program.eval reply (levelPlan s τ L G r μ δ project j seeds))) :
    Measurable (fun seed => Program.eval reply
      (multilevelPlan s τ L G r μ δ project J seed)) := by
  simp_rw [multilevelPlan_eval]
  apply measurable_from_prod_countable_right
  intro k
  by_cases hk : k + 1 ≤ J
  · simp only [hk, ite_true]
    exact ((hm 0).comp measurable_fst).add
      ((((hm (k + 1)).comp measurable_snd.fst).sub
        ((hm k).comp measurable_snd.snd)).const_smul ((2 : ℝ) ^ (k + 1)))
  · simpa only [hk, ite_false, add_zero, Function.comp_def] using (hm 0).comp measurable_fst

lemma multilevelPlan_param_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Z : Type*} [MeasurableSpace Z]
    (s : Z → Snapshot ι E) (τ L G r : ℝ) (μ δ : Z → ℝ)
    (project : Z → E → E) (J : Z → ℕ) (hJ : Measurable J)
    (reply : ι × E → ℝ × E) (seed : Z → MultilevelSeed) (hseed : Measurable seed)
    (hm : ∀ j, Measurable (fun w : Z × ProxSeed => Program.eval reply
      (levelPlan (s w.1) τ L G r (μ w.1) (δ w.1) (project w.1) j w.2))) :
    Measurable (fun z => Program.eval reply
      (multilevelPlan (s z) τ L G r (μ z) (δ z) (project z) (J z) (seed z))) := by
  simp_rw [multilevelPlan_eval]
  have hb := (hm 0).comp (measurable_id.prodMk hseed.snd.fst)
  have hf := AffineSoftmaxMeasurability.measurable_select
    (fun z k => Program.eval reply
      (levelPlan (s z) τ L G r (μ z) (δ z) (project z) (k + 1) (seed z).2.2.1))
    (fun k => (hm (k + 1)).comp (measurable_id.prodMk hseed.snd.snd.fst))
    (fun z => (seed z).1) hseed.fst
  have hc := AffineSoftmaxMeasurability.measurable_select
    (fun z k => Program.eval reply
      (levelPlan (s z) τ L G r (μ z) (δ z) (project z) k (seed z).2.2.2))
    (fun k => (hm k).comp (measurable_id.prodMk hseed.snd.snd.snd))
    (fun z => (seed z).1) hseed.fst
  have hw : Measurable (fun z => (2 : ℝ) ^ ((seed z).1 + 1)) :=
    (measurable_of_countable (fun k : ℕ => (2 : ℝ) ^ (k + 1))).comp hseed.fst
  exact hb.add ((hw.smul (hf.sub hc)).ite
    (measurableSet_le (hseed.fst.add_const 1) hJ) measurable_const)

lemma cachedProxGradientPlan_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (s : Snapshot ι E) (τ L G r μ σ β : ℝ) (project : E → E)
    (reply : ι × E → ℝ × E)
    (hm : ∀ j, Measurable (fun seeds => Program.eval reply
      (levelPlan s τ L G r μ
        (σ ^ 2 / (2 * μ * (2 + 12 *
          (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2) : ℝ))))
        project j seeds))) :
    Measurable (fun seed => Program.eval reply
      (cachedProxGradientPlan s τ L G r μ σ β project seed)) := by
  simp only [cachedProxGradientPlan, Program.eval_map]
  exact (measurable_const.sub (multilevelPlan_measurable s τ L G r μ _ project _ reply hm)).const_smul μ

lemma cachedProxGradientPlan_param_measurable
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Z : Type*} [MeasurableSpace Z] (s : Z → Snapshot ι E) (τ L G r : ℝ)
    (μ σ β : Z → ℝ) (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i))
    (hμ : Measurable μ) (hσ : Measurable σ) (hβ : Measurable β)
    (project : Z → E → E) (hp : Measurable (Function.uncurry project))
    (reply : ι × E → ℝ × E) (hr : Measurable reply)
    (seed : Z → MultilevelSeed) (hseed : Measurable seed) :
    Measurable (fun z => Program.eval reply
      (cachedProxGradientPlan (s z) τ L G r (μ z) (σ z) (β z) (project z) (seed z))) := by
  let J := fun z => LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ z ^ 2) (β z ^ 2)
  have hJ : Measurable J := AffineSoftmaxRestarts.restartRounds_measurable _ _ (hσ.pow_const 2) (hβ.pow_const 2)
  have hJr : Measurable (fun z => (J z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hJ
  let δ := fun z => σ z ^ 2 / (2 * μ z * (2 + 12 * (J z : ℝ)))
  have hδ : Measurable δ := (hσ.pow_const 2).div
    ((hμ.const_mul 2).mul (measurable_const.add (hJr.const_mul 12)))
  have hm := multilevelPlan_param_measurable s τ L G r μ δ project J hJ reply seed hseed
    (fun j => AffineSoftmaxBallSolver.cachedProxPlan_param_measurable
      (fun w : Z × ProxSeed => s w.1) τ L G r (fun w => μ w.1)
      (fun w => δ w.1 / 2 ^ j) (ha.comp measurable_fst)
      (fun i => (hv i).comp measurable_fst) (fun i => (hg i).comp measurable_fst)
      (hμ.comp measurable_fst) ((hδ.comp measurable_fst).div_const (2 ^ j))
      (fun w => project w.1) (hp.comp (measurable_fst.fst.prodMk measurable_snd))
      reply hr (fun w => w.2)
      (fun j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_snd)))
  have hh : Measurable (fun z => μ z • ((s z).anchor - Program.eval reply
      (multilevelPlan (s z) τ L G r (μ z) (δ z) (project z) (J z) (seed z)))) :=
    hμ.smul (ha.sub hm)
  simpa only [cachedProxGradientPlan, Program.eval_map, J, δ] using hh

lemma multilevelPlan_cost (s : Snapshot ι E) (τ L G r μ δ : ℝ)
    (project : E → E) (J : ℕ) (seed : MultilevelSeed) (reply : ι × E → ℝ × E) :
    Program.cost reply (multilevelPlan s τ L G r μ δ project J seed) =
      Program.cost reply (levelPlan s τ L G r μ δ project 0 seed.2.1) +
      if seed.1 + 1 ≤ J then
        Program.cost reply (levelPlan s τ L G r μ δ project (seed.1 + 1) seed.2.2.1) +
          Program.cost reply (levelPlan s τ L G r μ δ project seed.1 seed.2.2.2) else 0 := by
  by_cases h : seed.1 + 1 ≤ J
  · simp only [multilevelPlan, Program.cost_bind, ite_eq_left h, Program.cost_map]
  · simp only [multilevelPlan, Program.cost_bind, ite_eq_right h, Program.cost]

lemma multilevelPlan_integrable (s : Snapshot ι E) (τ L G r μ δ : ℝ)
    (project : E → E) (J : ℕ) (reply : ι × E → ℝ × E)
    (hi : ∀ j, Integrable (fun seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds))
      (proxLaw : Measure ProxSeed)) :
    Integrable (fun seed => Program.eval reply (multilevelPlan s τ L G r μ δ project J seed))
      (multilevelLaw : Measure MultilevelSeed) := by
  have hh := independent_level_integrable proxLaw
    (fun j seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds)) hi J
  simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk] using hh

lemma multilevelPlan_moments [FiniteDimensional ℝ E]
    (s : Snapshot ι E) (τ L G r μ δ : ℝ) (project : E → E) (J : ℕ)
    (reply : ι × E → ℝ × E) (u : E) {v : ℝ}
    (hi : ∀ j, Integrable (fun seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds))
      (proxLaw : Measure ProxSeed))
    (hi2 : ∀ j, Integrable (fun seeds => ‖Program.eval reply (levelPlan s τ L G r μ δ project j seeds) - u‖ ^ 2)
      (proxLaw : Measure ProxSeed))
    (hb : ∀ j, (∫ seeds, ‖Program.eval reply (levelPlan s τ L G r μ δ project j seeds) - u‖ ^ 2
      ∂(proxLaw : Measure ProxSeed)) ≤ v / 2 ^ j) :
    (∫ seed, Program.eval reply (multilevelPlan s τ L G r μ δ project J seed)
      ∂(multilevelLaw : Measure MultilevelSeed)) =
      (∫ seeds, Program.eval reply (levelPlan s τ L G r μ δ project J seeds) ∂(proxLaw : Measure ProxSeed)) ∧
    Integrable (fun seed => ‖Program.eval reply (multilevelPlan s τ L G r μ δ project J seed) - u‖ ^ 2)
      (multilevelLaw : Measure MultilevelSeed) ∧
    (∫ seed, ‖Program.eval reply (multilevelPlan s τ L G r μ δ project J seed) - u‖ ^ 2
      ∂(multilevelLaw : Measure MultilevelSeed)) ≤ (2 + 12 * (J : ℝ)) * v := by
  let level := fun j seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds)
  have hm := independent_level_mean proxLaw level hi J
  have hsq := independent_level_second_moment proxLaw level u hi hi2 hb J
  constructor
  · simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk, level] using hm
  · simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk, level] using hsq

lemma cachedProxGradientPlan_moments [FiniteDimensional ℝ E]
    (s : Snapshot ι E) (τ L G r : ℝ) {μ σ β : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ) (hβ : 0 < β) (project : E → E)
    (reply : ι × E → ℝ × E) (u : E) :
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
    (∀ j, Integrable (fun seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds))
      (proxLaw : Measure ProxSeed)) →
    (∀ j, Integrable (fun seeds => ‖Program.eval reply (levelPlan s τ L G r μ δ project j seeds) - u‖ ^ 2)
      (proxLaw : Measure ProxSeed)) →
    (∀ j, (∫ seeds, ‖Program.eval reply (levelPlan s τ L G r μ δ project j seeds) - u‖ ^ 2
      ∂(proxLaw : Measure ProxSeed)) ≤ (2 * δ / μ) / 2 ^ j) →
    let g := fun seed => Program.eval reply (cachedProxGradientPlan s τ L G r μ σ β project seed)
    Integrable g (multilevelLaw : Measure MultilevelSeed) ∧
      ‖(∫ seed, g seed ∂(multilevelLaw : Measure MultilevelSeed)) - μ • (s.anchor - u)‖ ≤ β ∧
      Integrable (fun seed => ‖g seed - μ • (s.anchor - u)‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) ∧
      (∫ seed, ‖g seed - μ • (s.anchor - u)‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  dsimp only
  intro hi hi2 hb
  let level := fun j seeds => Program.eval reply (levelPlan s τ L G r μ δ project j seeds)
  let Y := fun seed => Program.eval reply (multilevelPlan s τ L G r μ δ project J seed)
  let Z := fun seed : MultilevelSeed => level J seed.2.1
  have hYi : Integrable Y (multilevelLaw : Measure MultilevelSeed) :=
    multilevelPlan_integrable s τ L G r μ δ project J reply hi
  have hZi : Integrable Z (multilevelLaw : Measure MultilevelSeed) :=
    ((hi J).comp_fst ((proxLaw : Measure ProxSeed).prod (proxLaw : Measure ProxSeed))).comp_snd
      (countLaw : Measure ℕ)
  have hZ2 : Integrable (fun seed => ‖Z seed - u‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) :=
    ((hi2 J).comp_fst ((proxLaw : Measure ProxSeed).prod (proxLaw : Measure ProxSeed))).comp_snd
      (countLaw : Measure ℕ)
  have hYmom := multilevelPlan_moments s τ L G r μ δ project J reply u hi hi2 hb
  have hmean : (∫ seed, Y seed ∂(multilevelLaw : Measure MultilevelSeed)) =
      ∫ seed, Z seed ∂(multilevelLaw : Measure MultilevelSeed) :=
    hYmom.1.trans (multilevel_first_integral (level J)).symm
  have ht := multilevel_tuning hμ hσ hβ
  have hYbound : μ ^ 2 * (∫ seed, ‖Y seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hYmom.2.2 (sq_nonneg μ)
    have he : μ ^ 2 * ((2 + 12 * (J : ℝ)) * (2 * δ / μ)) = σ ^ 2 := by
      rw [← mul_assoc]
      exact ht.2.1
    exact hh.trans_eq he
  have hZbound : μ ^ 2 * (∫ seed, ‖Z seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ β ^ 2 := by
    rw [show (∫ seed, ‖Z seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) =
      (∫ seeds, ‖level J seeds - u‖ ^ 2 ∂(proxLaw : Measure ProxSeed)) from
      multilevel_first_integral (fun seeds => ‖level J seeds - u‖ ^ 2)]
    exact (mul_le_mul_of_nonneg_left (hb J) (sq_nonneg μ)).trans ht.2.2
  have hh := prox_gradient_moments multilevelLaw Y Z s.anchor u hμ.le hβ.le hYi hZi hYmom.2.1 hZ2
    hmean hYbound hZbound
  simpa only [cachedProxGradientPlan, Program.eval_map, J, δ, Y] using hh

end Execution

end LongTails.Proofs.AffineSoftmaxMultilevel
