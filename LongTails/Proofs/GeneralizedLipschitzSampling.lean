import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.GeneralizedLipschitzPilot
import LongTails.Proofs.RobustValue
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.StochasticGeneralizedLipschitzConvex
import LongTails.Proofs.GeneralizedLipschitzConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.GeneralizedLipschitzSampling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma bounded_nonnegative_variance {X : Ω → ℝ} (hX : MemLp X 2 P) {L : ℝ}
    (hb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ L) :
    variance X P ≤ L * (∫ ω, X ω ∂P) := by
  have hi := integral_mono_ae hX.integrable_sq
    ((hX.integrable (by norm_num)).const_mul L) (by
      filter_upwards [hb] with ω hω
      nlinarith [mul_nonneg hω.1 (sub_nonneg.mpr hω.2)])
  rw [integral_const_mul] at hi
  rw [variance_eq_sub hX]
  change (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 ≤ _
  nlinarith [sq_nonneg (∫ ω, X ω ∂P)]

lemma bounded_mean_deviation {X : Ω → ℝ} (hX : MemLp X 2 P)
    {B m : ℝ} (hB : 0 < B) (hm : 0 < m)
    (hb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ B ^ 2)
    (hq : 0 < ∫ ω, X ω ∂P) {n : ℕ} (hn : 0 < n) (hnm : B ≤ (n : ℝ) * m) :
    (Measure.pi fun _ : Fin n => P)
      {ξ | 4 * Real.sqrt (B * m * (∫ ω, X ω ∂P)) ≤
        |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P|} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
  let q := ∫ ω, X ω ∂P
  have hq' : 0 < q := hq
  have ht : 0 < B * m * q := by positivity
  have ha : 0 < 4 * Real.sqrt (B * m * q) := by positivity
  have hs : (4 * Real.sqrt (B * m * q)) ^ 2 = 16 * (B * m * q) := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    norm_num
  have hv := bounded_nonnegative_variance hX hb
  have h := OracleTemplate.FiniteVariance.average_deviation hX hn ha
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hs]
  apply (div_le_iff₀ (show 0 < (n : ℝ) * (16 * (B * m * q)) by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right hnm (show 0 ≤ B * q by positivity)
  change variance X P ≤ B ^ 2 * q at hv
  nlinarith

lemma bounded_mean_deviation_strict {X : Ω → ℝ} (hX : MemLp X 2 P)
    {B m : ℝ} (hB : 0 < B) (hm : 0 < m)
    (hb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ B ^ 2)
    {n : ℕ} (hn : 0 < n) (hnm : B ≤ (n : ℝ) * m) :
    (Measure.pi fun _ : Fin n => P)
      {ξ | 4 * Real.sqrt (B * m * (∫ ω, X ω ∂P)) <
        |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P|} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
  have hq : 0 ≤ ∫ ω, X ω ∂P := integral_nonneg_of_ae (hb.mono fun _ h => h.1)
  rcases eq_or_lt_of_le hq with hz | hpos
  · have hzero : X =ᵐ[P] (fun _ => 0) :=
      (integral_eq_zero_iff_of_nonneg_ae (hb.mono fun _ h => h.1)
        (hX.integrable (by norm_num))).mp hz.symm
    have hcoord (i : Fin n) : (fun ξ : Fin n → Ω => X (ξ i)) =ᵐ[Measure.pi fun _ => P]
        (fun _ => 0) :=
      (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.ae_eq_comp hzero
    have hall : ∀ᵐ ξ ∂(Measure.pi fun _ : Fin n => P), ∀ i, X (ξ i) = 0 :=
      ae_all_iff.mpr hcoord
    have hempty : (Measure.pi fun _ : Fin n => P)
        {ξ | 4 * Real.sqrt (B * m * (∫ ω, X ω ∂P)) <
          |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P|} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hall] with ξ hξ
      simp [hz.symm, hξ]
    rw [hempty]
    exact bot_le
  · refine (measure_mono ?_).trans (bounded_mean_deviation hX hB hm hb hpos hn hnm)
    intro ξ hξ
    exact le_of_lt (show 4 * Real.sqrt (B * m * (∫ ω, X ω ∂P)) <
      |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P| from hξ)

lemma fixed_moment_deviation {X : Ω → ℝ} (hX : MemLp X 2 P)
    {κ m : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ (256 * κ * m) ^ 2)
    {n : ℕ} (hn : 0 < n) (hnκ : 67108864 * κ ≤ (n : ℝ)) :
    (Measure.pi fun _ : Fin n => P)
      {ξ | (∫ ω, X ω ∂P) / 4 + κ * m ^ 2 / 64 ≤
        |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P|} ≤
      ENNReal.ofReal (1 / 16 : ℝ) := by
  let q := ∫ ω, X ω ∂P
  let a := q / 4 + κ * m ^ 2 / 64
  have hq : 0 ≤ q := integral_nonneg_of_ae (hb.mono fun _ h => h.1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : κ * m ^ 2 * q / 64 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg (q / 4 - κ * m ^ 2 / 64)]
  have hv := bounded_nonnegative_variance hX hb
  have h := OracleTemplate.FiniteVariance.average_deviation hX hn ha
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  apply (div_le_iff₀ (show 0 < (n : ℝ) * a ^ 2 by positivity)).mpr
  have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ (n : ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hnκ
    (show 0 ≤ κ * m ^ 2 * q / 64 by positivity)
  change variance X P ≤ (256 * κ * m) ^ 2 * q at hv
  nlinarith

lemma fixed_moment_tree_deviation {X : Ω → ℝ} (hXm : Measurable X) (hX : MemLp X 2 P)
    {κ m : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ (256 * κ * m) ^ 2)
    {n : ℕ} (hn : 0 < n) (hnκ : 67108864 * κ ≤ (n : ℝ)) (depth : ℕ) :
    OracleTemplate.FiniteVariance.treeLaw (Measure.pi fun _ : Fin n => P) depth
      {ξ | (∫ ω, X ω ∂P) / 4 + κ * m ^ 2 / 64 <
        |OracleTemplate.FiniteVariance.treeValue
          (fun z : Fin n → Ω => (∑ i, X (z i)) / n) depth ξ - ∫ ω, X ω ∂P|} ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ depth)) := by
  have hmean : Measurable (fun z : Fin n → Ω => (∑ i, X (z i)) / n) :=
    (Finset.measurable_sum _ (fun i _ => hXm.comp (measurable_pi_apply i))).div_const _
  apply OracleTemplate.FiniteVariance.treeValue_deviation hmean
  have h := fixed_moment_deviation hX hκ hm hb hn hnκ
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal (by norm_num)))
  intro ξ hξ
  exact le_of_lt (show (∫ ω, X ω ∂P) / 4 + κ * m ^ 2 / 64 <
    |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂P| from hξ)

lemma raw_miss_probability {A : Set Ω} (hA : MeasurableSet A) {p : ℝ}
    (hp : p ≤ P.real A) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real {ξ | ∀ i, ξ i ∉ A} ≤ Real.exp (-(n : ℝ) * p) := by
  have he : {ξ : Fin n → Ω | ∀ i, ξ i ∉ A} = Set.univ.pi (fun _ => Aᶜ) := by
    ext ξ
    simp
  rw [measureReal_def, he, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  change (P.real Aᶜ) ^ n ≤ _
  have hc : P.real Aᶜ ≤ Real.exp (-p) := by
    rw [measureReal_compl hA, probReal_univ]
    exact (sub_le_sub_left hp 1).trans (Real.one_sub_le_exp_neg p)
  calc
    (P.real Aᶜ) ^ n ≤ (Real.exp (-p)) ^ n := pow_le_pow_left₀ (measureReal_nonneg) hc n
    _ = Real.exp (-(n : ℝ) * p) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma raw_hit_union {A : Set Ω} (hA : MeasurableSet A) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real {ξ | ∃ i, ξ i ∈ A} ≤ (n : ℝ) * P.real A := by
  have he : {ξ : Fin n → Ω | ∃ i, ξ i ∈ A} = ⋃ i : Fin n, {ξ | ξ i ∈ A} := by
    ext ξ
    simp
  rw [he]
  refine (measureReal_iUnion_fintype_le _).trans_eq ?_
  have hcoord (i : Fin n) : (Measure.pi fun _ : Fin n => P).real {ξ | ξ i ∈ A} = P.real A := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      ((measurePreserving_eval (fun _ : Fin n => P) i).measure_preimage hA.nullMeasurableSet)
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma raw_failure_tuning {κ δ σ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) (hnκ : 16 * κ * Real.log (3 / δ) ≤ (n : ℝ)) :
    2 * Real.exp (-(n : ℝ) * (1 / (16 * κ))) +
      (n : ℝ) * (σ ^ 2 / (Real.sqrt (3 * (n : ℝ) / δ) * σ) ^ 2) ≤ δ := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (3 / δ) ≤ (n : ℝ) / (16 * κ) := by
    apply (le_div_iff₀ (show 0 < 16 * κ by positivity)).mpr
    nlinarith
  have he : Real.exp (-(n : ℝ) * (1 / (16 * κ))) ≤ δ / 3 := by
    calc
      _ ≤ Real.exp (-Real.log (3 / δ)) := by
        apply Real.exp_le_exp.mpr
        simpa only [div_eq_mul_inv, one_mul, neg_mul] using neg_le_neg hlog
      _ = δ / 3 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hs : (n : ℝ) * (σ ^ 2 / (Real.sqrt (3 * (n : ℝ) / δ) * σ) ^ 2) = δ / 3 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hs]
  linarith

open LongTails.Algorithms.GeneralizedLipschitzPilot

lemma tuning_tail_bounds (κ δ : ℝ) (hδ : 0 < δ) :
    (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ (tuning κ δ).depth) ≤ δ / (3 * (tuning κ δ).scales) ∧
    (1 / 2 : ℝ) ^ (tuning κ δ).repetitions ≤ δ / (3 * (tuning κ δ).scales) := by
  let J := (tuning κ δ).scales
  have hJ : 0 < (J : ℝ) := by exact_mod_cast (LongTails.Proofs.GeneralizedLipschitzPilot.tuning_counts_pos κ δ).2.1
  have hd : 0 < δ / (3 * J) := by positivity
  have he : 1 / (δ / (3 * (J : ℝ))) = 3 * J / δ := by field_simp
  constructor
  · have h := OracleTemplate.FiniteVariance.tree_depth_tail hd
    dsimp only at h
    rw [he] at h
    exact h
  · have hceil := LongTails.Proofs.GeneralizedLipschitzPilot.le_two_pow_ceil_log (show 0 < 3 * (J : ℝ) / δ by positivity)
    have hp : 3 * (J : ℝ) / δ ≤ (2 : ℝ) ^ (tuning κ δ).repetitions :=
      hceil.trans (pow_le_pow_right₀ (by norm_num)
        (le_max_right 1 ⌈Real.log (3 * (J : ℝ) / δ) / Real.log 2⌉₊))
    have hmul := (div_le_iff₀ hδ).mp hp
    rw [one_div, inv_pow]
    rw [← one_div]
    apply (div_le_iff₀ (show 0 < (2 : ℝ) ^ (tuning κ δ).repetitions by positivity)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < 3 * (J : ℝ) by positivity)).mpr
    nlinarith

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped RealInnerProductSpace

lemma centered_secondMoment {X : Ω → E} (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P ∧
      (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) ≤ ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  let u := ∫ z, X z ∂P
  have he : (fun ω => ‖X ω - u‖ ^ 2) =
      (fun ω => ‖X ω‖ ^ 2 + ‖u‖ ^ 2 - 2 * ⟪u, X ω⟫) := by
    funext ω
    rw [norm_sub_sq_real, real_inner_comm]
    ring
  have hsum : Integrable (fun ω => ‖X ω‖ ^ 2 + ‖u‖ ^ 2) P := hX2.add (integrable_const _)
  have hinter : Integrable (fun ω => 2 * ⟪u, X ω⟫) P := (hXi.const_inner u).const_mul 2
  have hi := hsum.sub hinter
  constructor
  · rw [he]
    exact hi
  · change (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ _
    rw [he, integral_sub hsum hinter, integral_add hX2 (integrable_const (‖u‖ ^ 2)),
      integral_const_mul, integral_inner hXi u]
    simp only [integral_const, probReal_univ, one_smul]
    change (∫ ω, ‖X ω‖ ^ 2 ∂P) + ‖u‖ ^ 2 - 2 * ⟪u, u⟫ ≤ _
    rw [real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖u‖]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma fresh_mean_moments {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (n : ℕ) (hn : 0 < n) :
    let avg := fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i)
    let Q := Measure.pi (fun _ : Fin n => P)
    Integrable avg Q ∧ (∫ ξ, avg ξ ∂Q) = ∫ ω, X ω ∂P ∧
    Integrable (fun ξ => ‖avg ξ‖ ^ 2) Q ∧
    (∫ ξ, ‖avg ξ‖ ^ 2 ∂Q) ≤ 2 * ‖∫ ω, X ω ∂P‖ ^ 2 + 2 * (∫ ω, ‖X ω‖ ^ 2 ∂P) / n := by
  dsimp only
  let Q := Measure.pi (fun _ : Fin n => P)
  let avg := fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i)
  let u := ∫ ω, X ω ∂P
  have hc := centered_secondMoment hXi hX2
  have hv := OracleTemplate.RobustGradient.finite_mean_variance hX hXi u hc.1 rfl n hn
  have hcoord (i : Fin n) : Integrable (fun ξ : Fin n → Ω => X (ξ i)) Q :=
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp hXi.aestronglyMeasurable |>.mpr hXi
  have ha : Integrable avg Q := (integrable_finsetSum _ (fun i _ => hcoord i)).smul _
  have hmean : (∫ ξ, avg ξ ∂Q) = u := by
    dsimp [avg]
    rw [integral_smul, integral_finsetSum _ (fun i _ => hcoord i)]
    have hl (i : Fin n) : ProbabilityTheory.HasLaw (fun ξ : Fin n → Ω => ξ i) P Q :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    have hm (i : Fin n) : (∫ ξ : Fin n → Ω, X (ξ i) ∂Q) = u :=
      (hl i).integral_comp hXi.aestronglyMeasurable
    simp_rw [hm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn)]
  have hdom (ξ : Fin n → Ω) : ‖avg ξ‖ ^ 2 ≤ 2 * ‖avg ξ - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have h := norm_add_le (avg ξ - u) u
    rw [sub_add_cancel] at h
    nlinarith [sq_nonneg (‖avg ξ - u‖ - ‖u‖), pow_le_pow_left₀ (norm_nonneg _) h 2]
  have ha2 : Integrable (fun ξ => ‖avg ξ‖ ^ 2) Q := by
    apply Integrable.mono' ((hv.1.const_mul 2).add (integrable_const (2 * ‖u‖ ^ 2)))
    · apply Measurable.aestronglyMeasurable
      dsimp [avg]
      fun_prop
    · filter_upwards [] with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom ξ
  refine ⟨ha, hmean, ha2, ?_⟩
  have h := integral_mono ha2 ((hv.1.const_mul 2).add (integrable_const (2 * ‖u‖ ^ 2))) hdom
  simp only [Pi.add_apply] at h
  rw [integral_add (hv.1.const_mul 2) (integrable_const _), integral_const_mul, hv.2] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have hb := div_le_div_of_nonneg_right hc.2 (by positivity : 0 ≤ (n : ℝ))
  change (∫ ξ, ‖avg ξ‖ ^ 2 ∂Q) ≤ _
  dsimp [u] at h
  rw [mul_div_assoc]
  linarith
lemma fresh_mean_secondMoment_bound {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) {κ m : ℝ}
    (hg : ‖∫ ω, X ω ∂P‖ ≤ m) (hS : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 16 * κ * m ^ 2)
    (n : ℕ) (hn : 0 < n) (hnκ : 16 * κ ≤ (n : ℝ)) :
    (∫ ξ : Fin n → Ω, ‖(1 / (n : ℝ)) • ∑ i, X (ξ i)‖ ^ 2 ∂Measure.pi (fun _ : Fin n => P)) ≤ 4 * m ^ 2 := by
  have h := (fresh_mean_moments hX hXi hX2 n hn).2.2.2
  have hg2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hvar : (∫ ω, ‖X ω‖ ^ 2 ∂P) / n ≤ m ^ 2 := by
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
    have hmul := mul_le_mul_of_nonneg_right hnκ (sq_nonneg m)
    nlinarith
  rw [mul_div_assoc] at h
  linarith

lemma fixed_vector_mean_deviation {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) {κ m : ℝ} (hm : 0 < m)
    (hq : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ κ * m ^ 2 / 16)
    {n : ℕ} (hn : 0 < n) (hnκ : 9216 * κ ≤ (n : ℝ)) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | m / 96 < ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - ∫ ω, X ω ∂P‖} ≤ 1 / 16 := by
  have hc := centered_secondMoment hXi hX2
  have hv := OracleTemplate.RobustGradient.finite_mean_variance hX hXi
    (∫ ω, X ω ∂P) hc.1 rfl n hn
  have ht := OracleTemplate.RobustGradient.norm_tail_le_second_moment hv.1
    (show 0 < m / 96 by positivity) hv.2.le
  refine ht.trans ?_
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < m / 96 by positivity))).mpr
  apply (div_le_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn)).mpr
  have hmul := mul_le_mul_of_nonneg_right hnκ (sq_nonneg m)
  nlinarith [hc.2]

lemma fixed_vector_center_deviation {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) {κ m : ℝ} (hm : 0 < m)
    (hq : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ κ * m ^ 2 / 16)
    {n : ℕ} (hn : 0 < n) (hnκ : 9216 * κ ≤ (n : ℝ)) (r : ℕ) :
    (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => P)
      {ξ | m / 32 < ‖OracleTemplate.RobustGradient.pilotCenter (m / 16)
        (fun j => (1 / (n : ℝ)) • ∑ i, X (ξ j i)) - ∫ ω, X ω ∂P‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ r) := by
  have hV : Measurable (fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i)) := by
    fun_prop
  have h := OracleTemplate.RobustGradient.pilotCenter_failure_probability (P := Measure.pi fun _ : Fin n => P) hV
    (∫ ω, X ω ∂P) (m / 16) (by
      simpa only [div_div, show (16 : ℝ) * 6 = 96 by norm_num] using
        fixed_vector_mean_deviation hX hXi hX2 hm hq hn hnκ) r
  simpa only [div_div, show (16 : ℝ) * 2 = 32 by norm_num] using h

lemma clipped_meanReply_confidence {X : Ω → E} (hX : Measurable X)
    {B κ m : ℝ} (hB : 0 ≤ B) (hm : 0 < m)
    (hq : (∫ ω, ‖OracleTemplate.clip B (X ω)‖ ^ 2 ∂P) ≤ κ * m ^ 2 / 16)
    {n : ℕ} (hn : 0 < n) (hnκ : 9216 * κ ≤ (n : ℝ)) (r : ℕ) :
    (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => P)
      {ξ | m / 32 < ‖LongTails.Algorithms.GeneralizedLipschitzPilot.meanReply B m n r
        (fun j i => X (ξ j i)) - ∫ ω, OracleTemplate.clip B (X ω) ∂P‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ r) := by
  have hc := (OracleTemplate.measurable_clip B).comp hX
  have hi : Integrable (fun ω => OracleTemplate.clip B (X ω)) P :=
    Integrable.of_bound hc.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun ω => OracleTemplate.norm_clip_le hB (X ω)))
  have h2 : Integrable (fun ω => ‖OracleTemplate.clip B (X ω)‖ ^ 2) P := by
    apply Integrable.mono' (integrable_const (B ^ 2)) (hc.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le hB _) 2
  exact fixed_vector_center_deviation hc hi h2 hm hq hn hnκ r

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma rawScale_lower_failure {X : Ω → E} (hX : Measurable X) (G0 t p : ℝ)
    (hp : p ≤ P.real {ω | t < ‖X ω‖}) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | LongTails.Algorithms.GeneralizedLipschitzPilot.rawScale G0 (fun i => X (ξ i)) < 2 * t} ≤
      Real.exp (-(n : ℝ) * p) := by
  refine (measureReal_mono ?_).trans
    (raw_miss_probability (measurableSet_lt measurable_const hX.norm) hp n)
  intro ξ hξ i hi
  have hs := LongTails.Proofs.GeneralizedLipschitzPilot.rawScale_ge_sample G0
    (fun i => X (ξ i)) i
  change t < ‖X (ξ i)‖ at hi
  change LongTails.Algorithms.GeneralizedLipschitzPilot.rawScale G0 (fun i => X (ξ i)) < 2 * t at hξ
  linarith

omit [CompleteSpace E] in
lemma raw_mean_scale_confidence {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u) (hui : Integrable u P)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ : ℝ}
    (hgdef : ‖∫ ω, X ω ∂P‖ = g) (hσ : 0 ≤ σ) (hκ : 1 ≤ κ)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | LongTails.Algorithms.GeneralizedLipschitzPilot.rawScale σ (fun i => X (ξ i)) < g} ≤
      Real.exp (-(n : ℝ) * (1 / (16 * κ))) := by
  by_cases hg : g ≤ 2 * σ
  · have he : {ξ : Fin n → Ω |
        LongTails.Algorithms.GeneralizedLipschitzPilot.rawScale σ (fun i => X (ξ i)) < g} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      have hf := LongTails.Proofs.GeneralizedLipschitzPilot.rawScale_ge_floor σ (fun i => X (ξ i))
      change LongTails.Algorithms.GeneralizedLipschitzPilot.rawScale σ (fun i => X (ξ i)) < g at hξ
      linarith
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hgpos : 0 < g := by linarith
    have hd := LongTails.Proofs.GeneralizedLipschitzPilot.raw_mean_detection
      hX hXi hu hui hu2 hsplit hgpos hgdef hσ (by linarith) hκ hmoment hv
    simpa only [show 2 * (g / 2) = g by ring] using
      rawScale_lower_failure hX σ (g / 2) (1 / (16 * κ)) hd n

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma raw_noise_maximum {u : Ω → E} (hu : Measurable u)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P) {σ t : ℝ} (ht : 0 < t)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real {ξ | ∃ i, t < ‖u (ξ i)‖} ≤
      (n : ℝ) * (σ ^ 2 / t ^ 2) := by
  have h := OracleTemplate.RobustGradient.norm_tail_le_second_moment hu2 ht hmoment
  exact (raw_hit_union (measurableSet_lt measurable_const hu.norm) n).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n))

open LongTails.Algorithms.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzPilot

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma raw_rms_scale_confidence {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ t : ℝ}
    (hσ : 0 ≤ σ) (hκ : 1 ≤ κ) (ht : 0 ≤ t)
    (hS : (∫ ω, ‖X ω‖ ^ 2 ∂P) = 16 * κ * t ^ 2)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | g ≤ rawScale σ (fun i => X (ξ i)) ∧
        16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 < ∫ ω, ‖X ω‖ ^ 2 ∂P} ≤
      Real.exp (-(n : ℝ) * (1 / (16 * κ))) := by
  have hκpos : 0 < κ := by linarith
  by_cases htH : t ≤ max g σ
  · have hempty : {ξ : Fin n → Ω | g ≤ rawScale σ (fun i => X (ξ i)) ∧
        16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 < ∫ ω, ‖X ω‖ ^ 2 ∂P} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      obtain ⟨hg, hs⟩ := hξ
      have hf := rawScale_ge_floor σ (fun i => X (ξ i))
      have htm : t ≤ rawScale σ (fun i => X (ξ i)) := htH.trans (max_le hg (by linarith))
      have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htm 2)
        (show 0 ≤ 16 * κ by positivity)
      rw [hS] at hs
      linarith
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have htpos : 0 < t := by
      have h := lt_of_not_ge htH
      have hmax := le_max_right g σ
      linarith
    have hgt : g ≤ t := (le_max_left _ _).trans (le_of_not_ge htH)
    have hσt : σ ≤ t := (le_max_right _ _).trans (le_of_not_ge htH)
    have hu : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ t ^ 2 :=
      hmoment.trans (pow_le_pow_left₀ hσ hσt 2)
    have hv' : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * t := hv.mono fun ω hω =>
      hω.trans (mul_le_mul_of_nonneg_left hgt (by positivity))
    have hd := raw_rms_detection hX hu2 hsplit hκ htpos hS.ge hu hv'
    refine (measureReal_mono ?_).trans (rawScale_lower_failure hX σ t _ hd n)
    intro ξ hξ
    obtain ⟨_, hs⟩ := hξ
    rw [hS] at hs
    have hsq : (rawScale σ (fun i => X (ξ i))) ^ 2 < t ^ 2 := by
      by_contra hn
      have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
        (show 0 ≤ 16 * κ by positivity)
      linarith
    have hm0 : 0 ≤ rawScale σ (fun i => X (ξ i)) :=
      (by positivity : 0 ≤ 2 * σ).trans (rawScale_ge_floor σ _)
    have hmt := (sq_lt_sq₀ hm0 ht).mp hsq
    change rawScale σ (fun i => X (ξ i)) < 2 * t
    linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma raw_upper_scale_confidence {X u v : Ω → E} (hu : Measurable u)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ A : ℝ}
    (hσ : 0 < σ) (hκ : 1 ≤ κ) (hA : 0 < A)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | 2 * (A + 2 * κ) * max g σ < rawScale σ (fun i => X (ξ i))} ≤
      (n : ℝ) * (σ ^ 2 / (A * σ) ^ 2) := by
  let Q := Measure.pi fun _ : Fin n => P
  have hcoord (i : Fin n) : ∀ᵐ ξ ∂Q,
      X (ξ i) = u (ξ i) + v (ξ i) ∧ ‖v (ξ i)‖ ≤ 2 * κ * g :=
    (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.ae (hsplit.and hv)
  have hall := ae_all_iff.mpr hcoord
  have hsub : ∀ᵐ ξ ∂Q,
      ξ ∈ {ξ | 2 * (A + 2 * κ) * max g σ < rawScale σ (fun i => X (ξ i))} →
      ξ ∈ {ξ | ∃ i, A * σ < ‖u (ξ i)‖} := by
    filter_upwards [hall] with ξ hξ
    intro hbad
    by_contra hn
    have hsmall (i : Fin n) : ‖u (ξ i)‖ ≤ A * σ := by
      exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
    have hbound (i : Fin n) : ‖X (ξ i)‖ ≤ (A + 2 * κ) * max g σ := by
      rw [(hξ i).1]
      have hu := hsmall i
      have hv := (hξ i).2
      have h₁ := mul_le_mul_of_nonneg_left (le_max_right g σ) hA.le
      have h₂ := mul_le_mul_of_nonneg_left (le_max_left g σ) (show 0 ≤ 2 * κ by linarith)
      have hs := norm_add_le (u (ξ i)) (v (ξ i))
      nlinarith
    have hm := rawScale_upper (fun i => X (ξ i)) hσ.le (by linarith : 1 ≤ A + 2 * κ) hbound
    exact (not_lt_of_ge hm) hbad
  have hmeasure := measure_mono_ae hsub
  have hreal := ENNReal.toReal_mono (measure_ne_top Q _) hmeasure
  exact hreal.trans (raw_noise_maximum hu hu2 (show 0 < A * σ by positivity) hmoment n)

omit [CompleteSpace E] in
lemma raw_initialization_confidence {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u) (hui : Integrable u P)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ A : ℝ}
    (hgdef : ‖∫ ω, X ω ∂P‖ = g) (hσ : 0 < σ) (hκ : 1 ≤ κ) (hA : 0 < A)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).real {ξ | ¬(
      g ≤ rawScale σ (fun i => X (ξ i)) ∧
      (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 ∧
      rawScale σ (fun i => X (ξ i)) ≤ 2 * (A + 2 * κ) * max g σ)} ≤
      2 * Real.exp (-(n : ℝ) * (1 / (16 * κ))) + (n : ℝ) * (σ ^ 2 / (A * σ) ^ 2) := by
  let Q := Measure.pi fun _ : Fin n => P
  let M := {ξ : Fin n → Ω | rawScale σ (fun i => X (ξ i)) < g}
  let R := {ξ : Fin n → Ω | g ≤ rawScale σ (fun i => X (ξ i)) ∧
    16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 < ∫ ω, ‖X ω‖ ^ 2 ∂P}
  let U := {ξ : Fin n → Ω | 2 * (A + 2 * κ) * max g σ < rawScale σ (fun i => X (ξ i))}
  let t := Real.sqrt ((∫ ω, ‖X ω‖ ^ 2 ∂P) / (16 * κ))
  have hκpos : 0 < κ := by linarith
  have hS : (∫ ω, ‖X ω‖ ^ 2 ∂P) = 16 * κ * t ^ 2 := by
    dsimp [t]
    rw [Real.sq_sqrt (div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))]
    field_simp
  have hM := raw_mean_scale_confidence hX hXi hu hui hu2 hsplit hgdef hσ.le hκ hmoment hv n
  have hR := raw_rms_scale_confidence hX hu2 hsplit hσ.le hκ (Real.sqrt_nonneg _) hS hmoment hv n
  have hU := raw_upper_scale_confidence hu hu2 hsplit hσ hκ hA hmoment hv n
  have hsub : {ξ : Fin n → Ω | ¬(g ≤ rawScale σ (fun i => X (ξ i)) ∧
      (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 ∧
      rawScale σ (fun i => X (ξ i)) ≤ 2 * (A + 2 * κ) * max g σ)} ⊆ (M ∪ R) ∪ U := by
    intro ξ hξ
    by_cases hm : g ≤ rawScale σ (fun i => X (ξ i))
    · by_cases hr : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2
      · exact Or.inr (lt_of_not_ge (fun hu => hξ ⟨hm, hr, hu⟩))
      · exact Or.inl (Or.inr ⟨hm, lt_of_not_ge hr⟩)
    · exact Or.inl (Or.inl (lt_of_not_ge hm))
  have hb : Q.real ((M ∪ R) ∪ U) ≤ Q.real M + Q.real R + Q.real U := by
    have h₁ : Q.real (M ∪ R) ≤ Q.real M + Q.real R := measureReal_union_le M R
    have h₂ : Q.real ((M ∪ R) ∪ U) ≤ Q.real (M ∪ R) + Q.real U :=
      measureReal_union_le (M ∪ R) U
    linarith
  have hh := (measureReal_mono hsub).trans hb
  change Q.real M ≤ _ at hM
  change Q.real R ≤ _ at hR
  change Q.real U ≤ _ at hU
  exact hh.trans (by linarith)

omit [CompleteSpace E] in
lemma configured_raw_confidence {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u) (hui : Integrable u P)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ δ : ℝ}
    (hgdef : ‖∫ ω, X ω ∂P‖ = g) (hσ : 0 < σ) (hκ : 1 ≤ κ) (hδ : 0 < δ)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) :
    let n := (tuning κ δ).rawCount
    let K := 2 * κ + Real.sqrt (9 * (n : ℝ) / δ)
    (Measure.pi fun _ : Fin n => P).real {ξ | ¬(
      g ≤ rawScale σ (fun i => X (ξ i)) ∧
      (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 16 * κ * (rawScale σ (fun i => X (ξ i))) ^ 2 ∧
      rawScale σ (fun i => X (ξ i)) ≤ 2 * K * max g σ)} ≤ δ / 3 := by
  dsimp only
  let n := (tuning κ δ).rawCount
  have hn : 0 < n := (tuning_counts_pos κ δ).1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hA : 0 < Real.sqrt (9 * (n : ℝ) / δ) := by positivity
  have h := raw_initialization_confidence hX hXi hu hui hu2 hsplit hgdef hσ hκ hA hmoment hv n
  have hnκ : 16 * κ * Real.log (3 / (δ / 3)) ≤ (n : ℝ) := by
    rw [show (3 : ℝ) / (δ / 3) = 9 / δ by field_simp; norm_num]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈16 * κ * Real.log (9 / δ)⌉₊)
  have ht := raw_failure_tuning (by linarith : 0 < κ) (show 0 < δ / 3 by positivity) hσ hn hnκ
  have he : 3 * (n : ℝ) / (δ / 3) = 9 * (n : ℝ) / δ := by field_simp; norm_num
  rw [he] at ht
  simpa only [add_comm (Real.sqrt (9 * (n : ℝ) / δ)) (2 * κ)] using h.trans ht

end Vector

section Indexed

open OracleTemplate.FiniteVariance
open LongTails.Algorithms.GeneralizedLipschitzPilot

lemma indexed_moment_deviation {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω)
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hXm : Measurable X) (hX : MemLp X 2 p)
    {κ m : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hb : ∀ᵐ ω ∂p, 0 ≤ X ω ∧ X ω ≤ (256 * κ * m) ^ 2)
    {n : ℕ} (hn : 0 < n) (hnκ : 67108864 * κ ≤ (n : ℝ)) (depth offset : ℕ) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | (∫ ω, X ω ∂p) / 4 + κ * m ^ 2 / 64 <
        |blockValue (fun (_ : Unit) leaf => (∑ i : Fin n, X (ξ (offset + leaf * n + i))) / n)
          depth () 0 - ∫ ω, X ω ∂p|} ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ depth)) := by
  let Q := Measure.infinitePi (fun _ : ℕ => p)
  have hshift : MeasurePreserving (fun ξ : ℕ → Ω => fun i => ξ (offset + i)) Q Q :=
    measurePreserving_snd.comp ((OracleTemplate.StochasticGeneralized.infinitePi_iid p).prefix_tail_law offset)
  have htree := (averaged_indexed_tree_law p Q
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).independent
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).marginal hn depth 0).comp hshift
  have hstat : Measurable (fun ξ : TreeSample (Fin n → Ω) depth =>
      treeValue (fun z : Fin n → Ω => (∑ i, X (z i)) / n) depth ξ) :=
    measurable_treeValue ((Finset.measurable_sum _ (fun i _ => hXm.comp (measurable_pi_apply i))).div_const _) depth
  have hevent : MeasurableSet {ξ : TreeSample (Fin n → Ω) depth |
      (∫ ω, X ω ∂p) / 4 + κ * m ^ 2 / 64 <
        |treeValue (fun z : Fin n → Ω => (∑ i, X (z i)) / n) depth ξ - ∫ ω, X ω ∂p|} := by
    simp only [← Real.norm_eq_abs]
    exact measurableSet_lt measurable_const ((hstat.sub measurable_const).norm)
  have hprob := htree.measure_preimage hevent.nullMeasurableSet
  have hbound := fixed_moment_tree_deviation hXm hX hκ hm hb hn hnκ depth
  rw [← hprob] at hbound
  convert hbound using 1
  congr 1
  ext ξ
  have he := blockValue_eq_tree (fun (_ : Unit) (z : Fin n → Ω) => (∑ i, X (z i)) / n)
    (fun i => ξ (offset + i)) depth () 0
  simpa only [Function.comp_def, Set.mem_preimage, Set.mem_ofPred_eq, Nat.zero_mul, Nat.zero_add,
    Nat.add_assoc] using (congrArg (fun v => (∫ ω, X ω ∂p) / 4 + κ * m ^ 2 / 64 < |v - ∫ ω, X ω ∂p|) he).to_iff
lemma blockMoment_confidence {Ω E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (p : Measure Ω) [IsProbabilityMeasure p] {X : Ω → E} (hX : Measurable X)
    (c : LongTails.Algorithms.GeneralizedLipschitzPilot.Config) (κ G0 initial : ℝ) (j : ℕ)
    (hκ : 0 < κ) (hm : 0 < LongTails.Algorithms.GeneralizedLipschitzPilot.scale G0 initial j)
    (hn : 0 < c.momentCount) (hnκ : 67108864 * κ ≤ (c.momentCount : ℝ)) :
    let m := LongTails.Algorithms.GeneralizedLipschitzPilot.scale G0 initial j
    let q := ∫ ω, ‖OracleTemplate.clip (256 * κ * m) (X ω)‖ ^ 2 ∂p
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | q / 4 + κ * m ^ 2 / 64 <
        |LongTails.Algorithms.GeneralizedLipschitzPilot.blockMoment c κ G0 initial (fun i => X (ξ i)) j - q|} ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ c.depth)) := by
  let m := LongTails.Algorithms.GeneralizedLipschitzPilot.scale G0 initial j
  let B := 256 * κ * m
  have hB : 0 ≤ B := by dsimp [B, m]; positivity
  let Z := fun ω => ‖OracleTemplate.clip B (X ω)‖ ^ 2
  have hZ : Measurable Z := (((OracleTemplate.measurable_clip B).comp hX).norm).pow_const 2
  have hb (ω : Ω) : 0 ≤ Z ω ∧ Z ω ≤ B ^ 2 :=
    ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le hB _) 2⟩
  have hz : MemLp Z 2 p := MemLp.of_bound hZ.aestronglyMeasurable (B ^ 2) (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]
    exact (hb ω).2)
  exact indexed_moment_deviation p hZ hz hκ hm (Filter.Eventually.of_forall hb) hn hnκ c.depth (c.rawCount + j * c.scaleCalls)

lemma indexed_meanReply_confidence {Ω E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p : Measure Ω) [IsProbabilityMeasure p] {X : Ω → E} (hX : Measurable X)
    {B κ m : ℝ} (hB : 0 ≤ B) (hm : 0 < m)
    (hq : (∫ ω, ‖OracleTemplate.clip B (X ω)‖ ^ 2 ∂p) ≤ κ * m ^ 2 / 16)
    {n : ℕ} (hn : 0 < n) (hnκ : 9216 * κ ≤ (n : ℝ)) (r offset : ℕ) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | m / 32 < ‖meanReply B m n r
        (fun j i => X (ξ (offset + j * n + i))) - ∫ ω, OracleTemplate.clip B (X ω) ∂p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ r) := by
  let Q := Measure.infinitePi (fun _ : ℕ => p)
  have hshift : MeasurePreserving (fun ξ : ℕ → Ω => fun i => ξ (offset + i)) Q Q :=
    measurePreserving_snd.comp ((OracleTemplate.StochasticGeneralized.infinitePi_iid p).prefix_tail_law offset)
  have hblocks := OracleTemplate.FiniteVariance.infinite_block_law p Q
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).independent
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p).marginal n
  have hfinite := (OracleTemplate.StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin n => p) r).comp (hblocks.comp hshift)
  have hstat : Measurable (fun ξ : Fin r → Fin n → Ω => meanReply B m n r (fun j i => X (ξ j i))) := by
    have hv : Measurable (fun ξ : Fin r → Fin n → Ω => fun j : Fin r =>
        (1 / (n : ℝ)) • ∑ i : Fin n, OracleTemplate.clip B (X (ξ j i))) := by
      apply Measurable.of_eval
      intro j
      apply Measurable.const_smul
      apply Finset.measurable_sum
      intro i _
      exact (OracleTemplate.measurable_clip B).comp (hX.comp ((measurable_pi_apply i).comp (measurable_pi_apply j)))
    exact (OracleTemplate.RobustGradient.measurable_pilotCenter r).comp
      ((measurable_const (a := m / 16)).prodMk hv)
  have hevent : MeasurableSet {ξ : Fin r → Fin n → Ω |
      m / 32 < ‖meanReply B m n r (fun j i => X (ξ j i)) - ∫ ω, OracleTemplate.clip B (X ω) ∂p‖} :=
    measurableSet_lt measurable_const ((hstat.sub measurable_const).norm)
  have hprob := hfinite.measure_preimage hevent.nullMeasurableSet
  have hbound := clipped_meanReply_confidence hX hB hm hq hn hnκ r
  rw [← hprob] at hbound
  simpa only [Function.comp_def, Set.preimage_ofPred_eq, Nat.add_assoc] using hbound
lemma blockMean_confidence {Ω E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p : Measure Ω) [IsProbabilityMeasure p] {X : Ω → E} (hX : Measurable X)
    (c : Config) (κ G0 initial : ℝ) (j : ℕ) (hκ : 0 < κ) (hm : 0 < scale G0 initial j)
    (hq : (∫ ω, ‖OracleTemplate.clip (256 * κ * scale G0 initial j) (X ω)‖ ^ 2 ∂p) ≤
      κ * (scale G0 initial j) ^ 2 / 16)
    (hn : 0 < c.meanCount) (hnκ : 9216 * κ ≤ (c.meanCount : ℝ)) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | scale G0 initial j / 32 < ‖blockMean c κ G0 initial (fun i => X (ξ i)) j -
        ∫ ω, OracleTemplate.clip (256 * κ * scale G0 initial j) (X ω) ∂p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ c.repetitions) := by
  exact indexed_meanReply_confidence p hX (by positivity) hm hq hn hnκ c.repetitions
    (c.rawCount + j * c.scaleCalls + 3 ^ c.depth * c.momentCount)

end Indexed

section OracleBounds

open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Proofs.GeneralizedLipschitzPilot
variable {Ξ F : Type} [MeasurableSpace Ξ] {p : Measure Ξ} [IsProbabilityMeasure p]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
omit [CompleteSpace F] [SecondCountableTopology F] in
lemma oracle_moment_bounds {f : F → ℝ} {xstar : F} {oracle : F → Ξ → F} {G0 G1 : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0) (x : F) :
    ‖∫ ω, oracle x ω ∂p‖ ≤ G0 + G1 * (f x - f xstar) ∧
    Integrable (fun ω => ‖oracle x ω‖ ^ 2) p ∧
    (∫ ω, ‖oracle x ω‖ ^ 2 ∂p) ≤ 2 * G0 ^ 2 + 2 * (G1 * (f x - f xstar)) ^ 2 := by
  obtain ⟨u, v, hu, _, he, hui, hub, hv⟩ := ho.decomposition x
  have hx : Measurable (oracle x) := ho.measurable.comp (measurable_const.prodMk measurable_id)
  have h := split_moment_bounds hx (ho.integrable x) hu hui he hG0 hub hv
  exact ⟨h.1, split_secondMoment_integrable hx hui he hv, h.2⟩

omit [CompleteSpace F] [SecondCountableTopology F] in
lemma oracle_gap_bound {f : F → ℝ} {xstar : F} {oracle : F → Ξ → F} {G0 G1 G : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0) (hG : 0 < G)
    (hG1 : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x) (x : F) (N : ℕ)
    (hN : 0 < N) (hd : 2 * G * ‖x - xstar‖ ≤ N) :
    f x - f xstar ≤ ((2 : ℝ) ^ N - 1) * (G0 / G) := by
  apply GeneralizedLipschitzConvex.gap_bound_of_local f xstar x G0 G N hG0 hG hN hd
  intro y z hsmall
  have hg := (oracle_moment_bounds ho hG0 y).1
  have hmul := mul_le_mul_of_nonneg_right hG1 (sub_nonneg.mpr (hmin y))
  exact GeneralizedLipschitzConvex.local_gap_le f (∫ ω, oracle y ω ∂p) z y xstar G0 G
    (hmin y) (ho.subgradient y z) (by linarith) hsmall
omit [CompleteSpace F] [SecondCountableTopology F] in
lemma oracle_ball_secondMoment {f : F → ℝ} {xstar : F} {oracle : F → Ξ → F}
    {G0 G1 G D : ℝ} (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0)
    (hG1pos : 0 ≤ G1) (hG : 0 < G) (hG1 : G1 ≤ G)
    (hmin : ∀ x, f xstar ≤ f x) (N : ℕ) (hN : 0 < N) (hD : 2 * G * D ≤ N)
    (x : F) (hx : ‖x - xstar‖ ≤ D) :
    (∫ ω, ‖oracle x ω‖ ^ 2 ∂p) ≤
      2 * G0 ^ 2 + 2 * (G1 * (((2 : ℝ) ^ N - 1) * (G0 / G))) ^ 2 := by
  have hd : 2 * G * ‖x - xstar‖ ≤ N :=
    (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * G)).trans hD
  have hb := oracle_gap_bound ho hG0 hG hG1 hmin x N hN hd
  have hp := pow_le_pow_left₀ (mul_nonneg hG1pos (sub_nonneg.mpr (hmin x)))
    (mul_le_mul_of_nonneg_left hb hG1pos) 2
  exact (oracle_moment_bounds ho hG0 x).2.2.trans (by linarith)

end OracleBounds

end LongTails.Proofs.GeneralizedLipschitzSampling
