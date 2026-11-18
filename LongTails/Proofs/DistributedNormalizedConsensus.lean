import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.AdamHeavyTailedProcess

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedConsensus

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma finite_linearization_bound (g : E → E) (A : E →L[ℝ] E)
    (x : E) (u : ι → E) {a L Q : ℝ} (ha : 0 ≤ a)
    (hA : ∀ v, ‖A v‖ ≤ L * ‖v‖)
    (hrem : ∀ i, ‖g (x + u i) - g x - A (u i)‖ ≤ Q * ‖u i‖ ^ 2) :
    ‖a • ∑ i, (g (x + u i) - g x)‖ ≤
      L * ‖a • ∑ i, u i‖ + a * Q * ∑ i, ‖u i‖ ^ 2 := by
  have heq : a • ∑ i, (g (x + u i) - g x) =
      A (a • ∑ i, u i) + a • ∑ i, (g (x + u i) - g x - A (u i)) := by
    simp only [map_smul, map_sum, Finset.sum_sub_distrib, smul_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖A (a • ∑ i, u i)‖ + ‖a • ∑ i, (g (x + u i) - g x - A (u i))‖ :=
      norm_add_le _ _
    _ ≤ L * ‖a • ∑ i, u i‖ + a * ‖∑ i, (g (x + u i) - g x - A (u i))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact add_le_add (hA _) le_rfl
    _ ≤ L * ‖a • ∑ i, u i‖ + a * ∑ i, (Q * ‖u i‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ ha
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hrem i)
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma finite_gradient_linearization_bound
    (g : E → E) (x : E) (u : ι → E) {a L Q : ℝ} (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hg : Differentiable ℝ g)
    (hH : ∀ y z, ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ Q * ‖y - z‖)
    (hA : ∀ v, ‖fderiv ℝ g x v‖ ≤ L * ‖v‖) :
    ‖a • ∑ i, (g (x + u i) - g x)‖ ≤
      L * ‖a • ∑ i, u i‖ + a * Q * ∑ i, ‖u i‖ ^ 2 := by
  apply finite_linearization_bound g (fderiv ℝ g x) x u ha hA
  intro i
  simpa only [add_sub_cancel_left] using OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound
    hQ hg hH x (x + u i)

omit [InnerProductSpace ℝ E] in
lemma expected_linearization_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (R B : Ω → E) (V : Ω → ℝ)
    {L Q : ℝ} (hL : 0 ≤ L)
    (hRm : AEStronglyMeasurable R P) (hBm : AEStronglyMeasurable B P)
    (hBi : Integrable (fun ω => ‖B ω‖) P)
    (hB2 : Integrable (fun ω => ‖B ω‖ ^ 2) P) (hVi : Integrable V P)
    (hbound : ∀ ω, ‖R ω‖ ≤ L * ‖B ω‖ + Q * V ω) :
    Integrable (fun ω => ‖R ω‖) P ∧
      (∫ ω, ‖R ω‖ ∂P) ≤
        L * Real.sqrt (∫ ω, ‖B ω‖ ^ 2 ∂P) + Q * ∫ ω, V ω ∂P := by
  have hi : Integrable (fun ω => L * ‖B ω‖ + Q * V ω) P :=
    (hBi.const_mul L).add (hVi.const_mul Q)
  have hRi : Integrable (fun ω => ‖R ω‖) P := by
    apply hi.mono' hRm.norm
    filter_upwards [] with ω
    simpa only [norm_norm] using hbound ω
  refine ⟨hRi, ?_⟩
  have hb := integral_mono hRi hi hbound
  rw [integral_add (hBi.const_mul L) (hVi.const_mul Q),
    integral_const_mul, integral_const_mul] at hb
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left
      (OracleTemplate.NormalizedStorm.integral_norm_le_sqrt hBm hB2) hL) le_rfl)

lemma adaptive_error_energy [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {S Ω : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S)
    (e : S → E) (W : S → Ω → E) (s : S) (v : ℝ)
    (hn : Measurable (Function.uncurry next)) (he : Measurable e)
    (hW : Measurable (Function.uncurry W))
    (hWi : ∀ z, Integrable (W z) P)
    (hW2 : ∀ z, Integrable (fun ω => ‖W z ω‖ ^ 2) P)
    (hW0 : ∀ z, ∫ ω, W z ω ∂P = 0)
    (hvar : ∀ z, (∫ ω, ‖W z ω‖ ^ 2 ∂P) ≤ v)
    (hstep : ∀ z ω, e (next z ω) = e z + W z ω) (k : ℕ) :
    Integrable (fun ξ => ‖e (AdamHeavyTailedProcess.stateAt next s ξ k)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖e (AdamHeavyTailedProcess.stateAt next s ξ k)‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ‖e s‖ ^ 2 + k * v := by
  induction k with
  | zero => simp only [AdamHeavyTailedProcess.stateAt_zero, Nat.cast_zero, zero_mul,
      add_zero, integral_const, probReal_univ, one_smul]
            exact ⟨integrable_const _, le_rfl⟩
  | succ k ih =>
    have hfresh := OracleTemplate.NormalizedStorm.fresh_step_sq P k
      (fun ξ => AdamHeavyTailedProcess.stateAt next s ξ k)
      (AdamHeavyTailedProcess.measurable_stateAt hn s k)
      (fun ξ ζ h => AdamHeavyTailedProcess.stateAt_congr next s k h)
      e he W hW hWi hW0 hW2 (fun _ => v) hvar (integrable_const v) ih.1 1
    simp only [one_smul, one_pow, one_mul, integral_const, probReal_univ, one_smul] at hfresh
    have hrec (ξ : ℕ → Ω) :
        e (AdamHeavyTailedProcess.stateAt next s ξ (k + 1)) =
          e (AdamHeavyTailedProcess.stateAt next s ξ k) +
            W (AdamHeavyTailedProcess.stateAt next s ξ k) (ξ k) := by
      rw [AdamHeavyTailedProcess.stateAt_succ, hstep]
    simp_rw [hrec]
    refine ⟨hfresh.1, hfresh.2.trans ?_⟩
    have h := add_le_add ih.2 (le_rfl : v ≤ v)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h

lemma periodic_energy_bound (r : ℕ+) (V : ℕ → ℝ) (v₀ v : ℝ) (K : ℕ)
    (hv₀ : 0 ≤ v₀) (hinit : V 0 ≤ 0)
    (hreset : ∀ k, k < K → (k + 1) % (r : ℕ) = 0 → V (k + 1) ≤ v₀)
    (hstep : ∀ k, k < K → (k + 1) % (r : ℕ) ≠ 0 → V (k + 1) ≤ V k + v)
    (k : ℕ) (hk : k ≤ K) : V k ≤ v₀ + (k % r : ℕ) * v := by
  revert hk
  induction k with
  | zero => intro _; simpa only [Nat.zero_mod, Nat.cast_zero, zero_mul, add_zero] using hinit.trans hv₀
  | succ k ih =>
    intro hk
    have hprev := ih (Nat.le_of_succ_le hk)
    by_cases h : (k + 1) % (r : ℕ) = 0
    · simpa only [h, Nat.cast_zero, zero_mul, add_zero] using hreset k (by omega) h
    · have hm : (k + 1) % (r : ℕ) = k % r + 1 := by
        have hr := r.pos
        have hk := Nat.mod_lt k hr
        have he : (k + 1) % (r : ℕ) = (k % r + 1) % r := by
          simp only [Nat.add_mod, Nat.mod_mod]
        by_cases hb : k % (r : ℕ) + 1 < r
        · rw [he, Nat.mod_eq_of_lt hb]
        · have hb' : k % (r : ℕ) + 1 = r := by omega
          rw [he, hb', Nat.mod_self] at h
          exact (h rfl).elim
      calc
        V (k + 1) ≤ V k + v := hstep k (by omega) h
        _ ≤ (v₀ + (k % r : ℕ) * v) + v := add_le_add hprev le_rfl
        _ = v₀ + ((k + 1) % r : ℕ) * v := by rw [hm]; push_cast; ring

lemma periodic_energy_uniform (r : ℕ+) (V : ℕ → ℝ) (v₀ v : ℝ) (K : ℕ)
    (hv₀ : 0 ≤ v₀) (hv : 0 ≤ v) (hinit : V 0 ≤ 0)
    (hreset : ∀ k, k < K → (k + 1) % (r : ℕ) = 0 → V (k + 1) ≤ v₀)
    (hstep : ∀ k, k < K → (k + 1) % (r : ℕ) ≠ 0 → V (k + 1) ≤ V k + v)
    (k : ℕ) (hk : k ≤ K) : V k ≤ v₀ + ((r : ℝ) - 1) * v := by
  apply (periodic_energy_bound r V v₀ v K hv₀ hinit hreset hstep k hk).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hv
  have h : k % (r : ℕ) + 1 ≤ r := Nat.mod_lt k r.pos
  have hc : ((k % (r : ℕ) : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast h
  linarith

lemma periodic_fresh_energy [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {S Ω : Type} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (r : ℕ+) (K : ℕ)
    (X : ℕ → (ℕ → Ω) → S) (R : S → E) (W : ℕ → S → Ω → E)
    (v₀ v : ℝ) (hv₀ : 0 ≤ v₀)
    (hXm : ∀ k, Measurable (X k))
    (hprefix : ∀ k ξ ζ, (∀ j, j < k → ξ j = ζ j) → X k ξ = X k ζ)
    (hR : Measurable R) (hWm : ∀ k < K, Measurable (Function.uncurry (W k)))
    (hWi : ∀ k < K, ∀ s, Integrable (W k s) P)
    (hW2 : ∀ k < K, ∀ s, Integrable (fun ω => ‖W k s ω‖ ^ 2) P)
    (hW0 : ∀ k < K, ∀ s, (∫ ω, W k s ω ∂P) = 0)
    (hvar : ∀ k < K, ∀ s, (∫ ω, ‖W k s ω‖ ^ 2 ∂P) ≤
      if (k + 1) % (r : ℕ) = 0 then v₀ else v)
    (hinit : ∀ ξ, R (X 0 ξ) = 0)
    (hstep : ∀ k < K, ∀ ξ, R (X (k + 1) ξ) =
      (if (k + 1) % (r : ℕ) = 0 then (0 : ℝ) else 1) • R (X k ξ) + W k (X k ξ) (ξ k)) :
    ∀ k, k ≤ K →
      Integrable (fun ξ => ‖R (X k ξ)‖ ^ 2) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖R (X k ξ)‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ v₀ + (k % r : ℕ) * v := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [hinit, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
      Nat.zero_mod, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨integrable_const _, hv₀⟩
  | succ k ih =>
    intro hk
    have hk' : k < K := by omega
    have hp := ih (Nat.le_of_succ_le hk)
    have hf := OracleTemplate.NormalizedStorm.fresh_step_sq P k (X k) (hXm k)
      (hprefix k) R hR (W k) (hWm k hk') (hWi k hk') (hW0 k hk') (hW2 k hk')
      (fun _ => if (k + 1) % (r : ℕ) = 0 then v₀ else v) (hvar k hk')
      (integrable_const _) hp.1 (if (k + 1) % (r : ℕ) = 0 then (0 : ℝ) else 1)
    have he : (fun ξ => ‖R (X (k + 1) ξ)‖ ^ 2) =
        (fun ξ => ‖(if (k + 1) % (r : ℕ) = 0 then (0 : ℝ) else 1) • R (X k ξ) +
          W k (X k ξ) (ξ k)‖ ^ 2) := by
      funext ξ
      rw [hstep k hk']
    refine ⟨he ▸ hf.1, ?_⟩
    rw [he]
    apply hf.2.trans
    simp only [integral_const, probReal_univ, one_smul]
    by_cases hz : (k + 1) % (r : ℕ) = 0
    · simp only [hz, ↓reduceIte, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add,
        Nat.cast_zero, add_zero]
      exact le_rfl
    · have hm : (k + 1) % (r : ℕ) = k % r + 1 := by
        have hlt := Nat.mod_lt k r.pos
        have heq : (k + 1) % (r : ℕ) = (k % r + 1) % r := by
          simp only [Nat.add_mod, Nat.mod_mod]
        by_cases hb : k % (r : ℕ) + 1 < r
        · rw [heq, Nat.mod_eq_of_lt hb]
        · have heq' : k % (r : ℕ) + 1 = r := by omega
          rw [heq, heq', Nat.mod_self] at hz
          exact (hz rfl).elim
      simp only [ite_eq_right hz, one_pow, one_mul]
      rw [hm]
      push_cast
      nlinarith [hp.2]

end LongTails.Proofs.DistributedNormalizedConsensus
