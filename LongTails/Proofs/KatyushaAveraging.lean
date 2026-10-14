import LongTails.Algorithms.Katyusha
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

open Set
open scoped BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

lemma weightSum_zero (θ : ℝ) : weightSum θ 0 = 0 := by simp [weightSum]

lemma weightSum_succ (θ : ℝ) (k : ℕ) : weightSum θ (k + 1) = 1 + θ * weightSum θ k := by
  simp only [weightSum, Finset.sum_range_succ', pow_zero, pow_succ', ← Finset.mul_sum]
  ring

lemma weightSum_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) : 0 ≤ weightSum θ k := by
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg hθ _)

lemma weightSum_pos {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} (hk : 0 < k) : 0 < weightSum θ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [weightSum_succ]
  have := weightSum_nonneg hθ k
  positivity

lemma weightSum_ge {θ : ℝ} (hθ : 1 ≤ θ) (k : ℕ) : (k : ℝ) ≤ weightSum θ k := by
  have h := Finset.sum_le_sum (s := Finset.range k) (fun j _ => one_le_pow₀ hθ (n := j))
  simpa [weightSum] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def innerValues {n : ℕ} (F : E → ℝ) (τ α L θ : ℝ)
    (g : Fin n × E → E) (prox : ℝ → E → E → E) (snapshot full : E) :
    (k : ℕ) → (E × E) → (Fin k → Fin n) → ℝ
  | 0, _, _ => 0
  | k + 1, s, samples =>
    let x := mix τ snapshot s
    let next := advance τ α L prox snapshot s (g (samples 0, x) - g (samples 0, snapshot) + full)
    F next.1 + θ * innerValues F τ α L θ g prox snapshot full k next (fun i => samples i.succ)

lemma inner_average {n : ℕ} {F : E → ℝ} (hc : ConvexOn ℝ univ F)
    (τ α L θ : ℝ) (hθ : 0 < θ) (g : Fin n × E → E)
    (prox : ℝ → E → E → E) (snapshot full : E)
    (k : ℕ) (s : E × E) (samples : Fin k → Fin n) :
    weightSum θ k * F ((weightSum θ k)⁻¹ •
      (innerRun τ α L θ g prox snapshot full k s samples).2) ≤
        innerValues F τ α L θ g prox snapshot full k s samples := by
  induction k generalizing s with
  | zero => simp [weightSum_zero, innerValues]
  | succ k ih =>
      let next := advance τ α L prox snapshot s
        (g (samples 0, mix τ snapshot s) - g (samples 0, snapshot) + full)
      let tail := fun i : Fin k => samples i.succ
      let rest := innerRun τ α L θ g prox snapshot full k next tail
      change weightSum θ (k + 1) * F ((weightSum θ (k + 1))⁻¹ • (next.1 + θ • rest.2)) ≤
        F next.1 + θ * innerValues F τ α L θ g prox snapshot full k next tail
      by_cases hk : k = 0
      · subst k
        simp [rest, innerRun, weightSum_succ, weightSum_zero, innerValues]
      · have hW := weightSum_pos hθ.le (Nat.pos_of_ne_zero hk)
        have hW' := weightSum_pos hθ.le (Nat.succ_pos k)
        have hw : (weightSum θ (k + 1))⁻¹ +
            θ * weightSum θ k / weightSum θ (k + 1) = 1 := by
          rw [weightSum_succ]
          field_simp
        have hc' := hc.2 (mem_univ next.1) (mem_univ ((weightSum θ k)⁻¹ • rest.2))
          (inv_nonneg.mpr hW'.le) (div_nonneg (mul_nonneg hθ.le hW.le) hW'.le) hw
        have hv : (weightSum θ (k + 1))⁻¹ • next.1 +
            (θ * weightSum θ k / weightSum θ (k + 1)) • ((weightSum θ k)⁻¹ • rest.2) =
            (weightSum θ (k + 1))⁻¹ • (next.1 + θ • rest.2) := by
          rw [smul_smul, smul_add, smul_smul]
          congr 1
          congr 1
          field_simp
        rw [hv] at hc'
        simp only [smul_eq_mul] at hc'
        have hb := mul_le_mul_of_nonneg_left hc' hW'.le
        have h₁ := mul_le_mul_of_nonneg_left (ih next tail) hθ.le
        change θ * (weightSum θ k * F ((weightSum θ k)⁻¹ • rest.2)) ≤ _ at h₁
        have he : weightSum θ (k + 1) *
            ((weightSum θ (k + 1))⁻¹ * F next.1 +
              θ * weightSum θ k / weightSum θ (k + 1) * F ((weightSum θ k)⁻¹ • rest.2)) =
            F next.1 + θ * (weightSum θ k * F ((weightSum θ k)⁻¹ • rest.2)) := by
          field_simp
        rw [he] at hb
        linarith

end OracleTemplate.Katyusha
