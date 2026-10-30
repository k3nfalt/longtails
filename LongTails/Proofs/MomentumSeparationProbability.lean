import LongTails.Proofs.MomentumSeparationLower

namespace LongTails.Proofs.MomentumSeparationProbability

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.MomentumSeparationInstance LongTails.Proofs.MomentumSeparationModel
open LongTails.Proofs.MomentumSeparationBridge

variable {m n : ℕ}

lemma colLaw_fst (i : Col m n) :
    (colLaw m n : Measure (Col m n × Bool)) {ω | ω.1 = i} = ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ := by
  have hset : {ω : Col m n × Bool | ω.1 = i} = ↑({(i, true), (i, false)} : Finset (Col m n × Bool)) := by
    ext ω
    rcases ω with ⟨j, b⟩
    cases b <;> simp
  rw [hset, colLaw, ProbabilityMeasure.coe_mk, PMF.toMeasure_apply_finset]
  rw [Finset.sum_pair (by simp)]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [← two_mul, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]
  rw [show ((2 : ℕ) : ENNReal) = 2 by norm_num, mul_comm (2 : ENNReal), mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

lemma pair_prob {a b : ℕ} (hab : a ≠ b) :
    (colStream m n : Measure (ℕ → Col m n × Bool)) {ξ | (ξ a).1 = (ξ b).1} ≤
      ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ := by
  set μ := (colStream m n : Measure (ℕ → Col m n × Bool))
  set k : ENNReal := ((n - min m n + 1 : ℕ) : ENNReal)
  have hiid := colStream_iid (m := m) (n := n)
  have hind : IndepFun (fun ξ : ℕ → Col m n × Bool => ξ a) (fun ξ => ξ b) μ :=
    hiid.independent.indepFun hab
  have hS : ∀ i : Col m n, MeasurableSet {ω : Col m n × Bool | ω.1 = i} :=
    fun i => (Set.toFinite _).measurableSet
  have hmarg : ∀ c : ℕ, ∀ i : Col m n, μ ((fun ξ : ℕ → Col m n × Bool => ξ c) ⁻¹'
      {ω | ω.1 = i}) = k⁻¹ := by
    intro c i
    rw [← Measure.map_apply (hiid.measurable c) (hS i), hiid.marginal c, colLaw_fst]
  have hset : {ξ : ℕ → Col m n × Bool | (ξ a).1 = (ξ b).1} = ⋃ i : Col m n,
      ((fun ξ : ℕ → Col m n × Bool => ξ a) ⁻¹' {ω | ω.1 = i} ∩
        (fun ξ : ℕ → Col m n × Bool => ξ b) ⁻¹' {ω | ω.1 = i}) := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h; exact ⟨(ξ a).1, rfl, h.symm⟩
    · rintro ⟨i, h1, h2⟩; rw [h1, h2]
  rw [hset]
  calc μ (⋃ i : Col m n, ((fun ξ : ℕ → Col m n × Bool => ξ a) ⁻¹' {ω | ω.1 = i} ∩
        (fun ξ : ℕ → Col m n × Bool => ξ b) ⁻¹' {ω | ω.1 = i})) ≤
        ∑ i : Col m n, μ ((fun ξ : ℕ → Col m n × Bool => ξ a) ⁻¹' {ω | ω.1 = i} ∩
          (fun ξ : ℕ → Col m n × Bool => ξ b) ⁻¹' {ω | ω.1 = i}) := measure_iUnion_fintype_le _ _
    _ = ∑ _i : Col m n, k⁻¹ * k⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hind.measure_inter_preimage_eq_mul _ _ (hS i) (hS i), hmarg a i, hmarg b i]
    _ = k * (k⁻¹ * k⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = k⁻¹ := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp [k]) (by simp [k]), one_mul]

lemma bad_prob (B T : ℕ) :
    (colStream m n : Measure (ℕ → Col m n × Bool)) {ξ | ¬ Distinct B T ξ} ≤
      ((B * T : ℕ) : ENNReal) ^ 2 * ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ := by
  set μ := (colStream m n : Measure (ℕ → Col m n × Bool))
  have hset : {ξ : ℕ → Col m n × Bool | ¬ Distinct B T ξ} ⊆
      ⋃ a ∈ Finset.range (B * T), ⋃ b ∈ (Finset.range (B * T)).erase a,
        {ξ | (ξ a).1 = (ξ b).1} := by
    intro ξ hξ
    simp only [Set.mem_ofPred_eq, Distinct] at hξ
    push Not at hξ
    obtain ⟨a, b, ha, hb, hab, he⟩ := hξ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, Finset.mem_erase]
    exact ⟨a, ha, b, ⟨Ne.symm hab, hb⟩, he⟩
  calc μ {ξ | ¬ Distinct B T ξ} ≤ μ (⋃ a ∈ Finset.range (B * T),
        ⋃ b ∈ (Finset.range (B * T)).erase a, {ξ | (ξ a).1 = (ξ b).1}) := measure_mono hset
    _ ≤ ∑ a ∈ Finset.range (B * T), μ (⋃ b ∈ (Finset.range (B * T)).erase a,
        {ξ : ℕ → Col m n × Bool | (ξ a).1 = (ξ b).1}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ Finset.range (B * T), ∑ b ∈ (Finset.range (B * T)).erase a,
        μ {ξ : ℕ → Col m n × Bool | (ξ a).1 = (ξ b).1} :=
        Finset.sum_le_sum fun a _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ Finset.range (B * T), ∑ _b ∈ Finset.range (B * T),
        ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ := by
        apply Finset.sum_le_sum
        intro a _
        calc ∑ b ∈ (Finset.range (B * T)).erase a, μ {ξ : ℕ → Col m n × Bool | (ξ a).1 = (ξ b).1}
              ≤ ∑ _b ∈ (Finset.range (B * T)).erase a, ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ :=
              Finset.sum_le_sum fun b hb => pair_prob (Finset.ne_of_mem_erase hb).symm
          _ ≤ ∑ _b ∈ Finset.range (B * T), ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ :=
              Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    _ = ((B * T : ℕ) : ENNReal) ^ 2 * ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

lemma distinct_measurable (B T : ℕ) :
    MeasurableSet {ξ : ℕ → Col m n × Bool | Distinct B T ξ} := by
  have h : {ξ : ℕ → Col m n × Bool | Distinct B T ξ} = ⋂ a ∈ Finset.range (B * T),
      ⋂ b ∈ (Finset.range (B * T)).erase a, {ξ | (ξ a).1 ≠ (ξ b).1} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Distinct, Set.mem_iInter, Finset.mem_range, Finset.mem_erase]
    constructor
    · intro h a ha b hb; exact h a b ha hb.2 (Ne.symm hb.1)
    · intro h a b ha hb hab; exact h a ha b ⟨Ne.symm hab, hb⟩
  rw [h]
  refine Finset.measurableSet_biInter _ fun a _ => Finset.measurableSet_biInter _ fun b _ => ?_
  exact (measurableSet_eq_fun ((measurable_pi_apply a).fst) ((measurable_pi_apply b).fst)).compl

lemma norm_stiffVec_le (x0 X : Space m n) : ‖stiffVec x0 X‖ ≤ ‖X‖ + ‖x0‖ := by
  have h : ‖stiffVec x0 X‖ ≤ ‖X - x0‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro p _
    simp only [stiffVec, PiLp.toLp_apply, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    split_ifs <;> nlinarith [sq_nonneg (X p - x0 p)]
  exact h.trans (norm_sub_le _ _)

lemma norm_gradient_le {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (φ : SeparationInstance.FlatShape)
    (x0 X : Space m n) :
    ‖gradient (MomentumSeparationInstance.objective ℓ c φ x0) X‖ ≤
      ℓ * (‖X‖ + ‖x0‖) + (min m n) * c := by
  rw [MomentumSeparationInstance.gradient_objective]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg hℓ]
    exact mul_le_mul_of_nonneg_left (norm_stiffVec_le x0 X) hℓ
  · have hb : ∀ i, |SeparationInstance.coefficients 0 c φ (SeparationInstance.offset x0 X) i| ≤ c := by
      intro i
      simp only [SeparationInstance.coefficients]
      split_ifs
      · simp [hc]
      · rw [abs_mul, abs_of_nonneg hc]
        exact mul_le_of_le_one_right hc (φ.bounded _)
    apply le_of_sq_le_sq _ (by positivity)
    rw [LongTails.Proofs.SeparationTrajectory.norm_sq_diagMat]
    calc ∑ i, SeparationInstance.coefficients 0 c φ (SeparationInstance.offset x0 X) i ^ 2 ≤
          ∑ _i : Fin (min m n), c ^ 2 := Finset.sum_le_sum fun i _ => by
            have := hb i
            nlinarith [abs_nonneg (SeparationInstance.coefficients 0 c φ
              (SeparationInstance.offset x0 X) i), sq_abs (SeparationInstance.coefficients 0 c φ
                (SeparationInstance.offset x0 X) i)]
      _ = (min m n) * c ^ 2 := by simp
      _ ≤ ((min m n) * c) ^ 2 := by
          have h1 : (1 : ℝ) * (min m n) ≤ (min m n) * (min m n) := by
            rcases Nat.eq_zero_or_pos (min m n) with h0 | h0
            · simp [h0]
            · have : (1 : ℝ) ≤ (min m n) := by exact_mod_cast h0
              nlinarith
          nlinarith [sq_nonneg c]

lemma norm_noise_le (hr : 0 < min m n) {s : ℝ} (hs : 0 ≤ s) (ω : Col m n × Bool) :
    ‖noise hr s ω‖ ≤ s := by
  rw [noise, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hs, AdamSeparationModel.sign_abs, mul_one]

lemma norm_batchNoise_le (hr : 0 < min m n) {s : ℝ} (hs : 0 ≤ s) {B : ℕ} (hB : 0 < B)
    (ξ : ℕ → Col m n × Bool) (t : ℕ) : ‖batchNoise hr s B ξ t‖ ≤ s := by
  unfold batchNoise
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ j ∈ Finset.range B, noise hr s (ξ (B * t + j))‖ ≤ B * s := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j ∈ Finset.range B, s := Finset.sum_le_sum fun j _ => norm_noise_le hr hs _
      _ = B * s := by simp
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  calc 1 / (B : ℝ) * ‖∑ j ∈ Finset.range B, noise hr s (ξ (B * t + j))‖ ≤ 1 / B * (B * s) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = s := by field_simp

lemma iter_bounded {hr : 0 < min m n} {ℓ c s β η : ℝ} {φ : SeparationInstance.FlatShape} {B : ℕ}
    {x0 : Space m n} {direction : Space m n → Space m n} (hdirb : ∀ M, ‖direction M‖ ≤ 1 + ‖M‖)
    (hB : 0 < B) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c)
    (hη : 0 ≤ η) (t : ℕ) :
    ∃ K : ℝ, ∀ ξ, ‖(iter hr ℓ c s β η φ B x0 direction ξ t).1‖ ≤ K ∧
      ‖(iter hr ℓ c s β η φ B x0 direction ξ t).2‖ ≤ K := by
  induction t with
  | zero => exact ⟨‖x0‖, fun ξ => by
      simp [iter, LongTails.Proofs.MomentumDirectionExecution.sampledMomentum]⟩
  | succ t ih =>
      obtain ⟨K, hK⟩ := ih
      set K' := K + (ℓ * (K + ‖x0‖) + (min m n) * c + s)
      refine ⟨K + η * (1 + K') + K', fun ξ => ?_⟩
      have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK ξ).1
      have hM : ‖(iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2‖ ≤ K' := by
        change ‖β • (iter hr ℓ c s β η φ B x0 direction ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
          ∑ j ∈ Finset.range B, MomentumSeparationModel.sample hr
            (MomentumSeparationInstance.objective ℓ c φ x0) s
              (iter hr ℓ c s β η φ B x0 direction ξ t).1 (ξ (B * t + j)))‖ ≤ K'
        rw [batch_mean_split hr _ s hB ξ t]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hβ0, Real.norm_of_nonneg (by linarith)]
        have hg := norm_gradient_le hℓ hc φ x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1
        have hn := norm_batchNoise_le hr hs hB ξ t
        have hsum := (norm_add_le (gradient (MomentumSeparationInstance.objective ℓ c φ x0)
          (iter hr ℓ c s β η φ B x0 direction ξ t).1) (batchNoise hr s B ξ t)).trans
            (add_le_add hg hn)
        have h1 := (hK ξ).1
        have h2 := (hK ξ).2
        have h3 : ℓ * (‖(iter hr ℓ c s β η φ B x0 direction ξ t).1‖ + ‖x0‖) ≤ ℓ * (K + ‖x0‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hℓ
        have hb1 : β ≤ 1 := hβ1.le
        have hpos : 0 ≤ ℓ * (K + ‖x0‖) + (min m n) * c + s := by positivity
        nlinarith
      constructor
      · change ‖(iter hr ℓ c s β η φ B x0 direction ξ t).1 -
          η • direction (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2‖ ≤ _
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg hη]
        have hd := hdirb (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2
        have hK'0 : 0 ≤ K' := le_trans (norm_nonneg _) hM
        nlinarith [(hK ξ).1, mul_le_mul_of_nonneg_left (hd.trans (by linarith : 1 +
          ‖(iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2‖ ≤ 1 + K')) hη]
      · have hK'0 : 0 ≤ K' := le_trans (norm_nonneg _) hM
        nlinarith [mul_nonneg hη (by linarith : (0 : ℝ) ≤ 1 + K')]

lemma nuclearNorm_le_mul_norm (Y : Space m n) : nuclearNorm Y ≤ m * ‖Y‖ := by
  refine (LongTails.Proofs.MatrixCovariance.nuclearNorm_le_rows
    (EuclideanSpace.basisFun (Fin m) ℝ) Y).trans ?_
  have hrow : ∀ i : Fin m, ‖(operatorEquiv m n Y).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i)‖ ≤
      ‖Y‖ := by
    intro i
    rw [row_norm_eq, ← Real.sqrt_sq (norm_nonneg Y), EuclideanSpace.norm_sq_eq]
    apply Real.sqrt_le_sqrt
    rw [Fintype.sum_prod_type]
    simp only [Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun i => ∑ j, Y (i, j) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc _ ≤ ∑ _i : Fin m, ‖Y‖ := Finset.sum_le_sum fun i _ => hrow i
    _ = m * ‖Y‖ := by simp

end LongTails.Proofs.MomentumSeparationProbability
