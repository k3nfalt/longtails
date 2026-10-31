import LongTails.Proofs.AffineAdamHistory
import LongTails.Proofs.AffineAdamGeometry

open MeasureTheory

namespace LongTails.Proofs.AffineAdamDescent

open AffineAdamHistory

lemma total_history_error (E R N D : ℕ → ℝ)
    (hE : ∀ t, 0 ≤ E t) (hR : ∀ t, 0 ≤ R t)
    (hE0 : E 0 = 0) (hR0 : R 0 = 0)
    (hEm : ∀ t, E (t + 1) ≤ (9 / 10 : ℝ) * E t + (9 / 10 : ℝ) * D t + N t)
    (hRv : ∀ t, R (t + 1) ≤ (1999 / 2000 : ℝ) * R t +
      (1999 / 2000 : ℝ) * D t + N t) (T : ℕ) :
    82 * (∑ t ∈ Finset.range T, E (t + 1)) + (∑ t ∈ Finset.range T, R (t + 1)) ≤
      2820 * (∑ t ∈ Finset.range T, N t) + 2737 * (∑ t ∈ Finset.range T, D t) := by
  have he := contraction_sum E N D (by norm_num : (0 : ℝ) ≤ 9 / 10)
    (by norm_num) hE hE0 hEm T
  have hr := contraction_sum R N D (by norm_num : (0 : ℝ) ≤ 1999 / 2000)
    (by norm_num) hR hR0 hRv T
  norm_num at he hr
  linarith

lemma pathwise_bound (F G H E R N D : ℕ → ℝ) {η Δ δ : ℝ} (d T : ℕ)
    (hη : 0 < η) (hgap : F 0 - F T ≤ Δ)
    (hE : ∀ t, 0 ≤ E t) (hR : ∀ t, 0 ≤ R t)
    (hN : ∀ t, 0 ≤ N t) (hH : ∀ t, 0 ≤ H t)
    (hE0 : E 0 = 0) (hR0 : R 0 = 0)
    (hEm : ∀ t, E (t + 1) ≤ (9 / 10 : ℝ) * E t + (9 / 10 : ℝ) * D t + N t)
    (hRv : ∀ t, R (t + 1) ≤ (1999 / 2000 : ℝ) * R t +
      (1999 / 2000 : ℝ) * D t + N t)
    (hD : (∑ t ∈ Finset.range T, D t) ≤ 80 * η * ∑ t ∈ Finset.range T, H t)
    (hdesc : ∀ t < T, F (t + 1) ≤ F t - η * G t +
      η * (82 * E (t + 1) + R (t + 1) + d * δ) + 3200 * η ^ 2 * H t) :
    (∑ t ∈ Finset.range T, G t) ≤ Δ / η +
      4096 * (∑ t ∈ Finset.range T, N t) +
      2 ^ 26 * η * (∑ t ∈ Finset.range T, H t) + T * d * δ := by
  have he := total_history_error E R N D hE hR hE0 hR0 hEm hRv T
  have hs := Finset.sum_le_sum (fun t (ht : t ∈ Finset.range T) => hdesc t (Finset.mem_range.mp ht))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have ht := Finset.sum_range_succ' F T
  rw [Finset.sum_range_succ] at ht
  have hNN : 0 ≤ ∑ t ∈ Finset.range T, N t := Finset.sum_nonneg (fun t _ => hN t)
  have hHH : 0 ≤ η * ∑ t ∈ Finset.range T, H t :=
    mul_nonneg hη.le (Finset.sum_nonneg (fun t _ => hH t))
  have hx : η * (∑ t ∈ Finset.range T, G t) ≤ Δ + η *
      (4096 * (∑ t ∈ Finset.range T, N t) +
        2 ^ 26 * η * (∑ t ∈ Finset.range T, H t) + T * d * δ) := by
    nlinarith
  apply (mul_le_mul_iff_of_pos_left hη).mp
  simp only [mul_add, mul_div_cancel₀ _ hη.ne']
  nlinarith

lemma integrated_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G N : ℕ → Ω → ℝ) (T d : ℕ) {η Δ δ L0 L1 a b : ℝ}
    (hGi : ∀ t, Integrable (G t) P) (hNi : ∀ t, Integrable (N t) P)
    (hnoise : ∀ t, (∫ ω, N t ω ∂P) ≤ a + b * ∫ ω, G t ω ∂P)
    (hpath : ∀ ω, (∑ t ∈ Finset.range T, G t ω) ≤ Δ / η +
      4096 * (∑ t ∈ Finset.range T, N t ω) +
      2 ^ 26 * η * (T * L0 + L1 * ∑ t ∈ Finset.range T, G t ω) + T * d * δ) :
    (1 - 4096 * b - 2 ^ 26 * η * L1) * (∑ t ∈ Finset.range T, ∫ ω, G t ω ∂P) ≤
      Δ / η + T * (4096 * a + 2 ^ 26 * η * L0 + d * δ) := by
  have hiG := integrable_finsetSum (Finset.range T) (fun t _ => hGi t)
  have hiN := integrable_finsetSum (Finset.range T) (fun t _ => hNi t)
  have hiA : Integrable (fun ω => Δ / η + 4096 * ∑ t ∈ Finset.range T, N t ω) P :=
    (integrable_const _).add (hiN.const_mul _)
  have hiH : Integrable (fun ω => (T : ℝ) * L0 + L1 * ∑ t ∈ Finset.range T, G t ω) P :=
    (integrable_const _).add (hiG.const_mul _)
  have hiC : Integrable (fun ω => (2 : ℝ) ^ 26 * η *
      ((T : ℝ) * L0 + L1 * ∑ t ∈ Finset.range T, G t ω)) P := hiH.const_mul _
  have hiAC : Integrable (fun ω => Δ / η + 4096 * (∑ t ∈ Finset.range T, N t ω) +
      2 ^ 26 * η * ((T : ℝ) * L0 + L1 * ∑ t ∈ Finset.range T, G t ω)) P := hiA.add hiC
  have hiR : Integrable (fun ω => Δ / η + 4096 * (∑ t ∈ Finset.range T, N t ω) +
      2 ^ 26 * η * ((T : ℝ) * L0 + L1 * ∑ t ∈ Finset.range T, G t ω) + T * d * δ) P :=
    hiAC.add (integrable_const _)
  have hs := integral_mono hiG hiR hpath
  rw [integral_add hiAC (integrable_const _), integral_add hiA hiC,
    integral_add (integrable_const _) (hiN.const_mul _), integral_const_mul,
    integral_const_mul, integral_add (integrable_const _) (hiG.const_mul _),
    integral_const_mul] at hs
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_finsetSum _ (fun t _ => hGi t), integral_finsetSum _ (fun t _ => hNi t)] at hs
  have hn := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hnoise t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hn
  nlinarith

end LongTails.Proofs.AffineAdamDescent
