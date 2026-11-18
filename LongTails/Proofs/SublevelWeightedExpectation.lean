import LongTails.Proofs.SublevelWeightedGeometry
import LongTails.Proofs.SublevelWeightedSchedule
import LongTails.Proofs.SublevelWeightedExecution
import LongTails.Proofs.SublevelPLConvergence

namespace OracleTemplate.SublevelWeighted

open MeasureTheory LongTails.Setups.SublevelPLBoundedVariance

lemma expected_output (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) μ P)
    {f : p.E → ℝ} {m : ℝ} (H : SublevelRobustGradient.Hyp f m p.L p.τ p.α p.x0)
    (hε : 0 < p.ε) {g : p.E → Ω → p.E} (ho : SublevelRobustGradient.Oracle μ f g p.σ) :
    let X := fun ξ => point p.L p.x0 (batch (steps p) (scale p)) g ξ (steps p)
    Integrable (fun ξ => f (X ξ) - m) P ∧ (∫ ξ, f (X ξ) - m ∂P) ≤ p.ε := by
  let K := steps p
  let v := scale p
  let b := batch K v
  let A := (p.τ / p.ε) ^ (2 / p.α)
  let X := fun j (ξ : ℕ → Ω) => point p.L p.x0 b g ξ j
  let E₂ := fun j ξ => ‖mean g (X j ξ) (b j) (calls b j) ξ - gradient f (X j ξ)‖ ^ 2
  let D := p.L * p.ε
  let C := 16 * D * A
  let w := fun j : ℕ => (3 + C / (j + 1)) / D
  have hL := H.hL
  have hτ := H.hτ
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hv : v = 1 + 128 * p.σ ^ 2 * (K / D + A) := rfl
  have hvp : 0 < v := by rw [hv]; positivity
  have hK : 0 < K := by simp [K, steps]
  have hw (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  have hX j : Measurable (X j) := measurable_point _ _ _ ho.hg _
  have hgrad := SublevelRobustGradient.gradient_measurable H.hL H.hlip
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr fun x => (H.hg x).continuousAt).measurable
  have he j : Integrable (E₂ j) P ∧ (∫ ξ, E₂ j ξ ∂P) ≤ p.σ ^ 2 / b j :=
    LongTails.Proofs.SymmetricThirdOrderSampling.adaptive_mean_variance_stream hind
      (calls b j) (b j) (batch_pos _ _ _) (X j) (hX j) (fun _ _ => point_congr _ _ _ _ j)
      g ho.hg (gradient f) hgrad ho.hgi ho.hmean ho.h2i ho.hvar
  let F := fun ξ => f (X K ξ) - m
  let S := fun ξ => 1 + ∑ j ∈ Finset.range K, w j * E₂ j ξ
  have hSi : Integrable S P := (integrable_const _).add
    (integrable_finsetSum _ fun j _ => (he j).1.const_mul (w j))
  have hbound ξ : 2 * F ξ / p.ε ≤ S ξ := by
    have h := normalized_descent p H hε (fun j => X j ξ)
      (fun j => mean g (X j ξ) (b j) (calls b j) ξ) rfl (fun _ => rfl)
    dsimp only at h
    rw [show 16 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) = C by dsimp [C, D, A]; ring] at h
    change 2 * F ξ / p.ε ≤ 1 + 3 * (∑ j ∈ Finset.range K, E₂ j ξ / D) +
      C * ∑ j ∈ Finset.range K, E₂ j ξ / D / (j + 1) at h
    apply h.trans
    apply le_of_eq
    dsimp [S, w]
    rw [Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hFi : Integrable F P := by
    apply Integrable.mono' (hSi.const_mul (p.ε / 2)) ((hfm.comp (hX K)).sub_const m).aestronglyMeasurable
    filter_upwards with ξ
    change ‖f (X K ξ) - m‖ ≤ _
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (H.hm _))]
    have hb := (div_le_iff₀ hε).mp (hbound ξ)
    change F ξ ≤ p.ε / 2 * S ξ
    linarith
  have hsum : ∑ j ∈ Finset.range K, w j * (p.σ ^ 2 / b j) ≤ 1 := by
    have hsqrt : 0 < Real.sqrt (K : ℝ) := by positivity
    let a := 3 * p.σ ^ 2 / (D * v)
    let t := C * p.σ ^ 2 / (D * v * Real.sqrt K)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    calc
      _ ≤ ∑ j ∈ Finset.range K, (a + t * (1 / Real.sqrt (j + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨h₁, h₂⟩ := batch_variance hK hvp (Finset.mem_range.mp hj)
        change 1 / (b j : ℝ) ≤ 1 / v at h₁
        change 1 / (b j : ℝ) / (j + 1) ≤ _ at h₂
        have h₃ := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 3 * p.σ ^ 2 / D)
        have h₄ := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ C * p.σ ^ 2 / D)
        dsimp only [w, a, t]
        convert add_le_add h₃ h₄ using 1 <;> ring
      _ ≤ K * a + t * (2 * Real.sqrt K) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (inv_sqrt_sum K) ht) _
      _ ≤ 1 := by
        dsimp [a, t, C]
        field_simp [hD.ne', hvp.ne', hsqrt.ne']
        have hv' : v * D = D + 128 * p.σ ^ 2 * (K + A * D) := by rw [hv]; field_simp
        nlinarith [sq_nonneg p.σ, mul_nonneg (sq_nonneg p.σ) (show 0 ≤ (K : ℝ) by positivity),
          mul_nonneg (sq_nonneg p.σ) (mul_nonneg hA.le hD.le)]
  have hSint : (∫ ξ, S ξ ∂P) ≤ 2 := by
    dsimp only [S]
    rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (he j).1.const_mul _),
      integral_finsetSum _ (fun j _ => (he j).1.const_mul _)]
    simp_rw [integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    linarith [Finset.sum_le_sum (s := Finset.range K)
      (fun j _ => mul_le_mul_of_nonneg_left (he j).2 (hw j))]
  refine ⟨hFi, ?_⟩
  have hb := integral_mono hFi (hSi.const_mul (p.ε / 2))
    (show ∀ ξ, F ξ ≤ p.ε / 2 * S ξ from fun ξ => by
      have := (div_le_iff₀ hε).mp (hbound ξ); linarith)
  rw [integral_const_mul] at hb
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hSint hε.le])

end OracleTemplate.SublevelWeighted
