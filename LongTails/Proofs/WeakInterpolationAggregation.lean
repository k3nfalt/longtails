import LongTails.Proofs.DistributedBatchedSgd

namespace LongTails.Proofs.WeakInterpolationAggregation

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedSmoothNonconvex

variable {p : Params} {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

lemma weighted_norm (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1)
    (v : ι → Point p) {R : ℝ} (hv : ∀ i, ‖v i‖ ≤ R) : ‖∑ i, q i • v i‖ ≤ R := by
  calc
    _ ≤ ∑ i, ‖q i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, q i * R := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq i)]
      exact mul_le_mul_of_nonneg_left (hv i) (hq i)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

lemma broadcast_displacement (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (Q : Point p → Point p)
    (hQ : ∀ z, ‖Q z - OracleTemplate.clip R z‖ ≤ δ)
    (v : ι → Point p) :
    let a := ∑ i, q i • Q (v i)
    ‖Q a - a‖ ≤ 2 * δ := by
  intro a
  have hlocal (i : ι) : ‖Q (v i)‖ ≤ R + δ := by
    have ht := norm_le_norm_sub_add (Q (v i)) (OracleTemplate.clip R (v i))
    linarith [hQ (v i), OracleTemplate.norm_clip_le hR (v i)]
  have hlen : ‖a‖ ≤ R + δ := weighted_norm q hq hs _ hlocal
  have hres : ‖OracleTemplate.clip R a - a‖ ≤ δ := by
    rw [norm_sub_rev, OracleTemplate.clip_residual_norm hR]
    exact max_le hδ (by linarith)
  linarith [hQ a, norm_sub_le_norm_sub_add_norm_sub (Q a) (OracleTemplate.clip R a) a]

lemma weighted_moments (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1)
    (X : ι → Ω → Point p) (u : ι → Point p) (V : ι → ℝ) (b : ℝ)
    (hi : iIndepFun X P) (hX : ∀ i, Integrable (X i) P)
    (hX2 : ∀ i, Integrable (fun s => ‖X i s - u i‖ ^ 2) P)
    (hV : ∀ i, ∫ s, ‖X i s - u i‖ ^ 2 ∂P ≤ V i)
    (hb : ∀ i, ‖(∫ s, X i s ∂P) - u i‖ ≤ b) :
    let Y := fun s => ∑ i, q i • (X i s - u i)
    Integrable Y P ∧ Integrable (fun s => ‖Y s‖ ^ 2) P ∧
      (∫ s, ‖Y s‖ ^ 2 ∂P) ≤ (∑ i, q i ^ 2 * V i) + b ^ 2 ∧
      ‖∫ s, Y s ∂P‖ ≤ b := by
  let Z i := fun s => q i • (X i s - u i)
  change Integrable (fun s => ∑ i, Z i s) P ∧ _
  have hZi (i : ι) : Integrable (Z i) P := ((hX i).sub (integrable_const _)).fun_smul _
  have hmean (i : ι) : ∫ s, Z i s ∂P = q i • ((∫ s, X i s ∂P) - u i) := by
    simp [Z, integral_smul, integral_sub (hX i) (integrable_const _)]
  have hsq (i : ι) (s : Ω) : ‖Z i s‖^2 = q i^2 * ‖X i s - u i‖^2 := by
    simp [Z, norm_smul, mul_pow]
  have hZi2 (i : ι) : Integrable (fun s => ‖Z i s‖^2) P := by
    simp_rw [hsq]; exact (hX2 i).const_mul _
  have hvar (i : ι) : ∫ s, ‖Z i s‖^2 ∂P ≤ q i^2 * V i := by
    simp_rw [hsq, integral_const_mul]; exact mul_le_mul_of_nonneg_left (hV i) (sq_nonneg _)
  have hbias (i : ι) : ‖∫ s, Z i s ∂P‖ ≤ q i * b := by
    rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq i)]
    exact mul_le_mul_of_nonneg_left (hb i) (hq i)
  have hZI : iIndepFun Z P := hi.comp (fun i v => q i • (v - u i))
    (fun i => (measurable_id.sub_const _).fun_const_smul _)
  obtain ⟨hI,hE⟩ := DistributedBatchedSgd.independent_biased_sum (p := p) P Z _ _ hZI hZi hZi2 hvar hbias
  rw [← Finset.sum_mul, hs, one_mul] at hE
  refine ⟨integrable_finsetSum _ (fun i _ => hZi i), hI, hE, ?_⟩
  change ‖∫ s, ∑ i, Z i s ∂P‖ ≤ b
  rw [integral_finsetSum _ (fun i _ => hZi i)]
  simp_rw [hmean]
  exact weighted_norm q hq hs _ hb

open scoped RealInnerProductSpace

lemma noisy_displacement (P : Measure Ω) [IsProbabilityMeasure P]
    (v : Point p) (Y U : Ω → Point p) (hY : Integrable Y P) (hU : Integrable U P)
    (hY2 : Integrable (fun s => ‖Y s‖^2) P) (hU2 : Integrable (fun s => ‖U s‖^2) P)
    {V b δ : ℝ} (hb : ‖∫ s, Y s ∂P‖ ≤ b) (hV : ∫ s, ‖Y s‖^2 ∂P ≤ V)
    (hedge : ∀ s, ‖U s - Y s‖ ≤ δ) :
    ∫ s, ‖v - U s‖^2 ∂P ≤ ‖v‖^2 + 2 * ‖v‖ * (b + δ) + 2*V + 2*δ^2 := by
  have hmean : ‖∫ s, U s ∂P‖ ≤ b + δ := by
    have hd : ‖(∫ s, U s ∂P) - ∫ s, Y s ∂P‖ ≤ δ := by
      rw [← integral_sub hU hY]
      have hh := integral_mono (hU.sub hY).norm (integrable_const δ) hedge
      exact (norm_integral_le_integral_norm _).trans (by simpa using hh)
    linarith [norm_le_norm_sub_add (∫ s, U s ∂P) (∫ s, Y s ∂P)]
  have hdom : Integrable (fun s => 2 * ‖Y s‖^2 + 2*δ^2) P :=
    (hY2.const_mul 2).add (integrable_const _)
  have hsq := integral_mono hU2 hdom (fun s => show ‖U s‖^2 ≤ _ by
    have h := norm_le_norm_sub_add (U s) (Y s)
    have hle : ‖U s‖ ≤ δ + ‖Y s‖ := by linarith [hedge s]
    nlinarith [sq_le_sq' (by linarith [norm_nonneg (U s), norm_nonneg (Y s)] : -(δ + ‖Y s‖) ≤ ‖U s‖) hle,
      sq_nonneg (δ - ‖Y s‖)])
  rw [integral_add (hY2.const_mul 2) (integrable_const _), integral_const_mul] at hsq
  simp only [integral_const, probReal_univ, one_smul] at hsq
  simp_rw [norm_sub_sq_real]
  have hint := (hU.const_inner (𝕜 := ℝ) v).const_mul (2 : ℝ)
  have hfirst : Integrable (fun s => ‖v‖^2 - 2*inner ℝ v (U s)) P := (integrable_const _).sub hint
  rw [integral_add hfirst hU2, integral_sub (integrable_const (‖v‖^2)) hint,
    integral_const_mul, integral_inner hU v]
  simp only [integral_const, probReal_univ, one_smul]
  have hl := (abs_le.mp (abs_real_inner_le_norm v (∫ s, U s ∂P))).1
  linarith [mul_le_mul_of_nonneg_left hmean (norm_nonneg v)]

end LongTails.Proofs.WeakInterpolationAggregation
