import LongTails.Proofs.VarianceReducedWeakMintySampling

open scoped BigOperators

namespace OracleTemplate.GeneralizedFiniteSum

noncomputable def stoppedRun {S Ω : Type*} (step : S → Ω → S) (energy : S → ℝ)
    (threshold : ℝ) : (k : ℕ) → S → (Fin k → Ω) → S
  | 0, s, _ => s
  | k + 1, s, ξ => if threshold < energy s then s
      else stoppedRun step energy threshold k (step s (ξ 0)) (fun j => ξ j.succ)

lemma stoppedRun_invariant {S Ω : Type*} (step : S → Ω → S) (energy : S → ℝ)
    (threshold : ℝ) (P : S → Prop)
    (hstep : ∀ s, P s → energy s ≤ threshold → ∀ ω, P (step s ω))
    (k : ℕ) (s : S) (hs : P s) (ξ : Fin k → Ω) :
    P (stoppedRun step energy threshold k s ξ) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih =>
    simp only [stoppedRun]
    split_ifs with h
    · exact hs
    · exact ih _ (hstep s hs (le_of_not_gt h) _) _

lemma stoppedRun_mean {S Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (step : S → Ω → S) (energy : S → ℝ) (threshold : ℝ) (P : S → Prop)
    (hstep : ∀ s, P s → energy s ≤ threshold → ∀ ω, P (step s ω))
    (hmean : ∀ s, P s → energy s ≤ threshold → (𝔼 ω, energy (step s ω)) ≤ energy s)
    (k : ℕ) (s : S) (hs : P s) :
    (𝔼 ξ : Fin k → Ω, energy (stoppedRun step energy threshold k s ξ)) ≤ energy s := by
  induction k generalizing s with
  | zero => simp [stoppedRun]
  | succ k ih =>
    rw [VarianceReducedWeakMinty.expect_fin_succ]
    by_cases h : threshold < energy s
    · simp [stoppedRun, h]
    · simp only [stoppedRun, ite_eq_right h, Fin.cons_zero, Fin.cons_succ]
      exact (Finset.expect_le_expect (s := Finset.univ) (fun ω _ =>
        ih _ (hstep s hs (le_of_not_gt h) ω))).trans (hmean s hs (le_of_not_gt h))

lemma stoppedRun_failure {S Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (step : S → Ω → S) (energy : S → ℝ) (threshold : ℝ) (P : S → Prop)
    (hthreshold : 0 < threshold) (hnonneg : ∀ s, P s → 0 ≤ energy s)
    (hstep : ∀ s, P s → energy s ≤ threshold → ∀ ω, P (step s ω))
    (hmean : ∀ s, P s → energy s ≤ threshold → (𝔼 ω, energy (step s ω)) ≤ energy s)
    (k : ℕ) (s : S) (hs : P s) :
    (𝔼 ξ : Fin k → Ω, if threshold < energy (stoppedRun step energy threshold k s ξ)
      then (1 : ℝ) else 0) ≤ energy s / threshold := by
  classical
  apply (le_div_iff₀ hthreshold).mpr
  rw [Finset.expect_mul]
  refine (Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => ?_)).trans
    (stoppedRun_mean step energy threshold P hstep hmean k s hs)
  split_ifs with h
  · simpa using h.le
  · simpa using hnonneg _ (stoppedRun_invariant step energy threshold P hstep k s hs ξ)

def plainRun {S Ω : Type*} (step : S → Ω → S) : (k : ℕ) → S → (Fin k → Ω) → S
  | 0, s, _ => s
  | k + 1, s, ξ => plainRun step k (step s (ξ 0)) (fun j => ξ j.succ)

lemma stoppedRun_eq_plainRun {S Ω : Type*} (step : S → Ω → S) (energy : S → ℝ)
    (threshold : ℝ) (k : ℕ) (s : S) (ξ : Fin k → Ω)
    (h : energy (stoppedRun step energy threshold k s ξ) ≤ threshold) :
    stoppedRun step energy threshold k s ξ = plainRun step k s ξ := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    by_cases hc : threshold < energy s
    · simp only [stoppedRun, ite_eq_left hc] at h
      exact (not_lt_of_ge h hc).elim
    · simp only [stoppedRun, ite_eq_right hc] at h ⊢
      exact ih _ _ h

lemma uniform_product_mean {Ω : Type*} [Fintype Ω] (F : Ω → ℝ) (k : ℕ) :
    (𝔼 ξ : Fin k → Ω, ∏ i, F (ξ i)) = (𝔼 ω, F ω) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [VarianceReducedWeakMinty.expect_fin_succ]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_expect, ih,
      ← Finset.expect_mul]
    rw [pow_succ]
    ring

lemma finite_minimum_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (F : Ω → ℝ)
    (k : ℕ) (B : (Fin k → Ω) → ℝ) {η Δ ρ : ℝ} (hη : 0 ≤ η) (hΔ : 0 ≤ Δ)
    (hbound : ∀ ξ, B ξ ≤ Δ) (hmin : ∀ ξ j, B ξ ≤ F (ξ j))
    (hprob : (𝔼 ω, if η < F ω then (1 : ℝ) else 0) ≤ ρ) :
    (𝔼 ξ, B ξ) ≤ η + Δ * ρ ^ k := by
  classical
  let bad := fun ω => if η < F ω then (1 : ℝ) else 0
  have hb (ω : Ω) : 0 ≤ bad ω := by dsimp [bad]; split_ifs <;> norm_num
  have hpoint (ξ : Fin k → Ω) : B ξ ≤ η + Δ * ∏ j, bad (ξ j) := by
    by_cases hall : ∀ j, η < F (ξ j)
    · have hp : ∏ j, bad (ξ j) = 1 := by simp [bad, hall]
      rw [hp, mul_one]
      linarith [hbound ξ]
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      have hp : ∏ j, bad (ξ j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [bad, hj])
      rw [hp, mul_zero, add_zero]
      exact (hmin ξ j).trans (le_of_not_gt hj)
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => hpoint ξ)
  rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
    uniform_product_mean] at hh
  have hp := pow_le_pow_left₀ (Finset.expect_nonneg fun ω _ => hb ω) hprob k
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hΔ])

end OracleTemplate.GeneralizedFiniteSum
