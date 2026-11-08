import LongTails.Proofs.BirchWindow

namespace LongTails.Proofs.BirchWindow

open Finset MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.NormBallLMO
open LongTails.Algorithms.BirchWindow
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open LongTails.Setups.BirchNonEuclidean (Params Objective StochasticGradient DualRegularityWitness)

lemma iterate_measurable {Ω : Type} [MeasurableSpace Ω] (p : Params) (B : ℕ) (η : ℝ)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (g : Point p.d → Ω → Point p.d) (hg : Measurable (Function.uncurry g))
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => iterate p B η lmo (fun j x => g x (ξ j)) k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [iterate] using
        (measurable_const : Measurable (fun _ : ℕ → Ω => p.x0))
    | succ k =>
      let m := fun ξ : ℕ → Ω => (1 / (B : ℝ)) • ∑ i : Fin B,
        g (iterate p B η lmo (fun j x => g x (ξ j)) (source B (k + i))) (ξ (k + i))
      have hs : Measurable (fun ξ : ℕ → Ω => ∑ i : Fin B,
          g (iterate p B η lmo (fun j x => g x (ξ j)) (source B (k + i))) (ξ (k + i))) := by
        apply Finset.measurable_sum
        intro i _
        have hi : source B (k + i) < k + 1 := by have := i.isLt; unfold source; omega
        exact hg.comp ((ih _ hi).prodMk (measurable_pi_apply (k + i)))
      have hm : Measurable m := hs.const_smul (1 / (B : ℝ))
      simp only [iterate]
      exact (ih k (Nat.lt_succ_self k)).add
        ((((continuous_dualNorm hR hR0).measurable.comp hm).smul (hlmo.comp hm)).const_smul η)

lemma iterate_past {Ω : Type} (p : Params) (B : ℕ) (η : ℝ)
    (lmo : Point p.d → Point p.d) (g : Point p.d → Ω → Point p.d) (k : ℕ)
    (ξ ξ' : ℕ → Ω) (hξ : ∀ j < calls B k, ξ j = ξ' j) :
    iterate p B η lmo (fun j x => g x (ξ j)) k =
      iterate p B η lmo (fun j x => g x (ξ' j)) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp only [iterate]
    | succ k =>
      rw [iterate, iterate]
      have hk := ih k (Nat.lt_succ_self k)
        (fun j hj => hξ j (by unfold calls at *; omega))
      have hs : (∑ i : Fin B,
            g (iterate p B η lmo (fun j x => g x (ξ j)) (source B (k + i))) (ξ (k + i))) =
          ∑ i : Fin B,
            g (iterate p B η lmo (fun j x => g x (ξ' j)) (source B (k + i))) (ξ' (k + i)) := by
        apply sum_congr rfl
        intro i _
        have hi := i.isLt
        rw [hξ (k + i) (by unfold calls; omega),
          ih _ (by unfold source; omega) (fun j hj => hξ j (by unfold calls source at *; omega))]
      rw [hk, hs]

lemma window_noise {Ω : Type} [MeasurableSpace Ω] (p : Params) (B K : ℕ) (hB : 0 < B)
    (η : ℝ) (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    (w : DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (k : ℕ) (hk : k < K) :
    let Z := fun j ξ => iterate p B η lmo (fun i x => g x (ξ i)) (source B j)
    let V := fun ξ => dualNorm p.N (∑ j ∈ range (calls B K),
      row B k j • (g (Z j ξ) (ξ j) - gradient f (Z j ξ))) ^ 2
    Integrable V (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, V ξ ∂(P : Measure (ℕ → Ω))) ≤ p.κ * p.σ ^ 2 / B := by
  let Z := fun j (ξ : ℕ → Ω) => iterate p B η lmo (fun i x => g x (ξ i)) (source B j)
  have hpast (j : ℕ) (ξ ξ' : ℕ → Ω) (h : ∀ i < j, ξ i = ξ' i) : Z j ξ = Z j ξ' := by
    by_cases hz : source B j = 0
    · simp only [Z, hz, iterate]
    · exact iterate_past p B η lmo g _ ξ ξ'
        (fun i hi => h i (by unfold calls source at *; omega))
  have hh := LongTails.Proofs.BirchNonEuclideanMoments.iid_indexed_noise_bound p μ P hiid
    f g ho w hR hR0 id Z (fun j => iterate_measurable p B η lmo hlmo g ho.measurable hR hR0 _)
    hpast (row B k) (fun _ _ h _ _ => h) (calls B K)
  simpa only [id_eq, row_square B K k hB hk, mul_one_div] using hh

lemma expected_window {Ω : Type} [MeasurableSpace Ω] (p : Params) (B K : ℕ)
    (hB : 0 < B) (η : ℝ) (hη : 0 < η) (hL : 0 < p.L)
    (hstep : η * p.L ≤ 1 / 2) (hsmall : η * p.L * B ≤ 1 / 4)
    (lmo : Point p.d → Point p.d) (hlmo : IsBallLMO p.N 1 lmo)
    (I : Instance p.d) (hf : Objective p I)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (ho : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (hdef : ∀ v, p.N v = 0 → v = 0) :
    let X := fun k (ξ : ℕ → Ω) => iterate p B η lmo (fun j x => g x (ξ j)) k
    let G := fun ξ => ∑ k ∈ range K, dualNorm p.N (gradient I.f (X k ξ)) ^ 2
    Integrable G (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, G ξ ∂(P : Measure (ℕ → Ω))) ≤ 6 * p.Δ / η + 16 * K * (p.κ * p.σ ^ 2 / B) := by
  let X := fun k (ξ : ℕ → Ω) => iterate p B η lmo (fun j x => g x (ξ j)) k
  let G := fun ξ => ∑ k ∈ range K, dualNorm p.N (gradient I.f (X k ξ)) ^ 2
  let V := fun k ξ => dualNorm p.N (∑ j ∈ range (calls B K), row B k j •
    (g (X (source B j) ξ) (ξ j) - gradient I.f (X (source B j) ξ))) ^ 2
  have hnoise (k : ℕ) (hk : k < K) : Integrable (V k) (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, V k ξ ∂(P : Measure (ℕ → Ω))) ≤ p.κ * p.σ ^ 2 / B :=
    window_noise p B K hB η lmo hlmo.measurable μ P hiid I.f g ho w hR hR0 k hk
  have hVI := integrable_finsetSum (μ := (P : Measure (ℕ → Ω))) (range K)
    (fun k hk => (hnoise k (mem_range.mp hk)).1)
  have hpoint (ξ : ℕ → Ω) : G ξ ≤ 6 * p.Δ / η + 16 * ∑ k ∈ range K, V k ξ := by
    exact trajectory hB hR hdef hlmo hL.le hη hstep hsmall hf.differentiable hf.smooth
      (fun k => X k ξ) (fun j => g (X (source B j) ξ) (ξ j))
      (by
        dsimp only [X]
        rw [iterate]
        exact (sub_le_sub_left (hf.lower _) _).trans hf.gap)
      (fun k _ => by
        dsimp only [X]
        rw [iterate])
  have hGM : Measurable G := by
    apply Finset.measurable_sum
    intro k _
    exact ((continuous_dualNorm hR hR0).measurable.comp ((measurable_gradient_space I.f).comp
      (iterate_measurable p B η lmo hlmo.measurable g ho.measurable hR hR0 k))).pow_const 2
  have hbound : Integrable (fun ξ => 6 * p.Δ / η + 16 * ∑ k ∈ range K, V k ξ)
      (P : Measure (ℕ → Ω)) := (integrable_const _).add (hVI.const_mul _)
  have hGI : Integrable G (P : Measure (ℕ → Ω)) := by
    apply hbound.mono' hGM.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hpoint ξ
  refine ⟨hGI, ?_⟩
  have h := integral_mono hGI hbound hpoint
  rw [integral_add (integrable_const _) (hVI.const_mul _), integral_const_mul, integral_const,
    probReal_univ, one_smul, integral_finsetSum _ (fun k hk => (hnoise k (mem_range.mp hk)).1)] at h
  have hV := sum_le_sum (fun k (hk : k ∈ range K) => (hnoise k (mem_range.mp hk)).2)
  simp only [sum_const, card_range, nsmul_eq_mul] at hV
  linarith only [h, hV]

end LongTails.Proofs.BirchWindow
