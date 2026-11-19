import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.AuxiliaryInner
import LongTails.Proofs.LocalNonlinearExtragradientGeometry

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalNonlinearExtragradientAveraging

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace E] [BorelSpace E] in
lemma centered_square {X : Ω → E} (hX : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - ∫ t, X t ∂P‖ ^ 2) P ∧
      (∫ ω, ‖X ω - ∫ t, X t ∂P‖ ^ 2 ∂P) =
        (∫ ω, ‖X ω‖ ^ 2 ∂P) - ‖∫ t, X t ∂P‖ ^ 2 := by
  let u := ∫ t, X t ∂P
  have he (ω : Ω) : ‖X ω - u‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪u, X ω⟫ + ‖u‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm (X ω) u]
  change Integrable (fun ω => ‖X ω - u‖ ^ 2) P ∧
    (∫ ω, ‖X ω - u‖ ^ 2 ∂P) = (∫ ω, ‖X ω‖ ^ 2 ∂P) - ‖u‖ ^ 2
  simp_rw [he]
  have hi := (hX.const_inner u).const_mul (2 : ℝ)
  have hs : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪u, X ω⟫) P := hX2.sub hi
  refine ⟨hs.add (integrable_const _), ?_⟩
  rw [integral_add hs (integrable_const _), integral_sub hX2 hi,
    integral_const_mul, integral_inner hX u]
  simp only [integral_const, probReal_univ, one_smul]
  rw [real_inner_self_eq_norm_sq]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma shifted_square {X : Ω → E} (v : E) (hX : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hzero : ∫ ω, X ω ∂P = 0) :
    Integrable (fun ω => ‖v + X ω‖ ^ 2) P ∧
      (∫ ω, ‖v + X ω‖ ^ 2 ∂P) = ‖v‖ ^ 2 + ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  simp_rw [norm_add_sq_real]
  have hi := (hX.const_inner v).const_mul (2 : ℝ)
  have hs : Integrable (fun ω => ‖v‖ ^ 2 + 2 * ⟪v, X ω⟫) P :=
    (integrable_const _).add hi
  refine ⟨hs.add hX2, ?_⟩
  rw [integral_add hs hX2, integral_add (integrable_const _) hi,
    integral_const_mul, integral_inner hX v, hzero]
  simp

lemma independent_average_bound {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → E)
    (hind : iIndepFun X P) (hXi : ∀ i, Integrable (X i) P)
    (hX2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    {a V : ℝ} (ha : 0 ≤ a)
    (hmean : ∀ i, ‖∫ ω, X i ω ∂P‖ ≤ a)
    (hmoment : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun ω => ‖(1 / (n : ℝ)) • ∑ i, X i ω‖ ^ 2) P ∧
      (∫ ω, ‖(1 / (n : ℝ)) • ∑ i, X i ω‖ ^ 2 ∂P) ≤ a ^ 2 + V / n := by
  classical
  let u : Fin n → E := fun i => ∫ ω, X i ω ∂P
  let Z : Fin n → Ω → E := fun i ω => X i ω - u i
  let c : ℝ := 1 / n
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hZi (i : Fin n) : Integrable (Z i) P := (hXi i).sub (integrable_const _)
  have hZ2 (i : Fin n) : Integrable (fun ω => ‖Z i ω‖ ^ 2) P :=
    (centered_square (hXi i) (hX2i i)).1
  have hZ0 (i : Fin n) : (∫ ω, Z i ω ∂P) = 0 := by
    dsimp [Z, u]
    rw [integral_sub (hXi i) (integrable_const _)]
    simp
  have hindZ : iIndepFun Z P :=
    hind.comp (fun i y => y - u i) (fun i => measurable_id.sub_const (u i))
  have hs := OracleTemplate.RobustGradient.independent_sum_second_moment Z hindZ hZi hZ2 hZ0
  have hsum : Integrable (fun ω => ∑ i, Z i ω) P :=
    integrable_finsetSum _ (fun i _ => hZi i)
  have hscaled : Integrable (fun ω => ‖c • ∑ i, Z i ω‖ ^ 2) P := by
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hs.1.const_mul (c ^ 2)
  have hscaled0 : (∫ ω, c • ∑ i, Z i ω ∂P) = 0 := by
    rw [integral_smul, integral_finsetSum _ (fun i _ => hZi i)]
    simp [hZ0]
  have he (ω : Ω) : c • ∑ i, X i ω = c • ∑ i, u i + c • ∑ i, Z i ω := by
    simp only [Z, Finset.sum_sub_distrib, smul_sub]
    abel
  have hshift := shifted_square (X := fun ω => c • ∑ i, Z i ω)
    (c • ∑ i, u i) (hsum.smul c) hscaled hscaled0
  have hnorm : ‖c • ∑ i, u i‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c * ∑ i, ‖u i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc
      _ ≤ c * ∑ _ : Fin n, a := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hmean i) hc
      _ = a := by simp [c, ne_of_gt hn0]
  have hv : (∫ ω, ‖c • ∑ i, Z i ω‖ ^ 2 ∂P) ≤ V / n := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_const_mul, hs.2]
    calc
      _ ≤ c ^ 2 * ∑ _ : Fin n, V := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
        apply Finset.sum_le_sum
        intro i _
        exact ((centered_square (hXi i) (hX2i i)).2 ▸
          sub_le_self _ (sq_nonneg (‖u i‖))).trans (hmoment i)
      _ = V / n := by simp [c]; field_simp
  change Integrable (fun ω => ‖c • ∑ i, X i ω‖ ^ 2) P ∧
    (∫ ω, ‖c • ∑ i, X i ω‖ ^ 2 ∂P) ≤ a ^ 2 + V / n
  simp_rw [he]
  refine ⟨hshift.1, ?_⟩
  rw [hshift.2]
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) ha).mpr hnorm) hv

omit [CompleteSpace E] in
lemma clipped_endpoint_bounds [SecondCountableTopology E] {X : Ω → E}
    (c : E) {H : ℝ} (hH : 0 < H) (hc : ‖c‖ ≤ H)
    (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    let C : Ω → E := fun ω => c + OracleTemplate.clip H (X ω - c)
    Integrable C P ∧ Integrable (fun ω => ‖C ω‖ ^ 2) P ∧
      (∫ ω, ‖C ω‖ ^ 2 ∂P) ≤ (∫ ω, ‖X ω‖ ^ 2 ∂P) ∧
      ‖(∫ ω, C ω ∂P) - ∫ ω, X ω ∂P‖ ≤
        (2 * (∫ ω, ‖X ω‖ ^ 2 ∂P) + 2 * ‖c‖ ^ 2) / H := by
  let C : Ω → E := fun ω => c + OracleTemplate.clip H (X ω - c)
  have hCm : Measurable C := measurable_const.add
    ((OracleTemplate.measurable_clip H).comp (hX.sub_const c))
  have hCn (ω : Ω) : ‖C ω‖ ≤ ‖X ω‖ := by
    have hh := OracleTemplate.norm_clip_sub_le hH.le
      (u := -c) (by simpa using hc) (X ω - c)
    simpa [C, sub_neg_eq_add, add_comm] using hh
  have hCi : Integrable C P :=
    hXi.norm.mono' hCm.aestronglyMeasurable (Filter.Eventually.of_forall hCn)
  have hC2n (ω : Ω) : ‖C ω‖ ^ 2 ≤ ‖X ω‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hCn ω)
  have hC2 : Integrable (fun ω => ‖C ω‖ ^ 2) P :=
    hX2.mono' (hCm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hC2n ω)
  refine ⟨hCi, hC2, integral_mono hC2 hX2 hC2n, ?_⟩
  have hres (ω : Ω) : ‖C ω - X ω‖ ≤ (2 * ‖X ω‖ ^ 2 + 2 * ‖c‖ ^ 2) / H := by
    have he : C ω - X ω = -(X ω - c - OracleTemplate.clip H (X ω - c)) := by
      dsimp [C]
      abel
    rw [he, norm_neg]
    exact (LocalNonlinearExtragradientGeometry.clipping_bias_bound (X ω - c) hH).trans
      (div_le_div_of_nonneg_right (AuxiliaryInner.norm_sub_sq_le (X ω) c) hH.le)
  have hi : Integrable (fun ω => (2 * ‖X ω‖ ^ 2 + 2 * ‖c‖ ^ 2) / H) P :=
    ((hX2.const_mul 2).add (integrable_const _)).div_const H
  rw [← integral_sub hCi hXi]
  calc
    _ ≤ ∫ ω, ‖C ω - X ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (2 * ‖X ω‖ ^ 2 + 2 * ‖c‖ ^ 2) / H ∂P :=
      integral_mono (hCi.sub hXi).norm hi hres
    _ = _ := by
      rw [integral_div, integral_add (hX2.const_mul 2) (integrable_const _), integral_const_mul]
      simp

lemma clipped_independent_average_bound [SecondCountableTopology E]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → E) (c : E) {H : ℝ}
    (hH : 0 < H) (hc : ‖c‖ ≤ H)
    (hind : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) P)
    (hX2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    {a V : ℝ} (ha : 0 ≤ a)
    (hmean : ∀ i, ‖∫ ω, X i ω ∂P‖ ≤ a)
    (hmoment : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ V) :
    let C : Fin n → Ω → E := fun i ω => c + OracleTemplate.clip H (X i ω - c)
    Integrable (fun ω => ‖(1 / (n : ℝ)) • ∑ i, C i ω‖ ^ 2) P ∧
      (∫ ω, ‖(1 / (n : ℝ)) • ∑ i, C i ω‖ ^ 2 ∂P) ≤
        (a + (2 * V + 2 * ‖c‖ ^ 2) / H) ^ 2 + V / n := by
  let C : Fin n → Ω → E := fun i ω => c + OracleTemplate.clip H (X i ω - c)
  have hb (i : Fin n) := clipped_endpoint_bounds c hH hc (hXm i) (hXi i) (hX2i i)
  have hindC : iIndepFun C P := hind.comp
    (fun _ y => c + OracleTemplate.clip H (y - c))
    (fun _ => measurable_const.add ((OracleTemplate.measurable_clip H).comp (measurable_id.sub_const c)))
  have hV : 0 ≤ V := (integral_nonneg fun _ => sq_nonneg _).trans (hmoment ⟨0, hn⟩)
  apply independent_average_bound hn C hindC (fun i => (hb i).1) (fun i => (hb i).2.1)
    (show 0 ≤ a + (2 * V + 2 * ‖c‖ ^ 2) / H by positivity)
  · intro i
    have he : (∫ ω, C i ω ∂P) = (∫ ω, X i ω ∂P) +
        ((∫ ω, C i ω ∂P) - ∫ ω, X i ω ∂P) := by abel
    calc
      _ = ‖(∫ ω, X i ω ∂P) + ((∫ ω, C i ω ∂P) - ∫ ω, X i ω ∂P)‖ := congrArg norm he
      _ ≤ ‖∫ ω, X i ω ∂P‖ + ‖(∫ ω, C i ω ∂P) - ∫ ω, X i ω ∂P‖ := norm_add_le _ _
      _ ≤ a + (2 * (∫ ω, ‖X i ω‖ ^ 2 ∂P) + 2 * ‖c‖ ^ 2) / H :=
        add_le_add (hmean i) (hb i).2.2.2
      _ ≤ _ := by gcongr; exact hmoment i
  · intro i
    exact (hb i).2.2.1.trans (hmoment i)

end LongTails.Proofs.LocalNonlinearExtragradientAveraging
