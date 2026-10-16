import LongTails.Algorithms.OnlineMetricAccelerated
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

noncomputable def learnerPotential (D : ℝ) (u : Fin d → ℝ) (Λ : BandLearner d) : ℝ :=
  (D ^ 2 - ∑ i, (Λ.φ i - u i) ^ 2) * Real.sqrt Λ.G / (2 * D) + D * Real.sqrt Λ.G

lemma clampBand_mem {lo hi : ℝ} (h : lo ≤ hi) (v : Fin d → ℝ) (i : Fin d) :
    lo ≤ clampBand lo hi v i ∧ clampBand lo hi v i ≤ hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

lemma clampBand_dist {lo hi : ℝ} {u : Fin d → ℝ} (hu : ∀ i, lo ≤ u i ∧ u i ≤ hi)
    (v : Fin d → ℝ) (i : Fin d) : (clampBand lo hi v i - u i) ^ 2 ≤ (v i - u i) ^ 2 := by
  have h1 := hu i
  simp only [clampBand]
  rcases le_total (v i) hi with h | h
  · rw [min_eq_right h]
    rcases le_total lo (v i) with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h']; nlinarith
  · rw [min_eq_left h, max_eq_right (by linarith)]; nlinarith

lemma band_dist_le {lo hi : ℝ} {u φ : Fin d → ℝ} (hu : ∀ i, lo ≤ u i ∧ u i ≤ hi)
    (hφ : ∀ i, lo ≤ φ i ∧ φ i ≤ hi) :
    ∑ i, (φ i - u i) ^ 2 ≤ d * (hi - lo) ^ 2 := by
  have : ∀ i ∈ Finset.univ, (φ i - u i) ^ 2 ≤ (hi - lo) ^ 2 := by
    intro i _
    have := hu i; have := hφ i
    nlinarith
  calc ∑ i, (φ i - u i) ^ 2 ≤ ∑ _i : Fin d, (hi - lo) ^ 2 := Finset.sum_le_sum this
    _ = d * (hi - lo) ^ 2 := by simp

lemma learner_step_bound {lo hi D : ℝ} (hD : 0 < D) {u : Fin d → ℝ}
    (hu : ∀ i, lo ≤ u i ∧ u i ≤ hi) (Λ : BandLearner d) (hG : 0 ≤ Λ.G)
    (hdist : ∑ i, (Λ.φ i - u i) ^ 2 ≤ D ^ 2) (γ : Fin d → ℝ) :
    ∑ i, γ i * (Λ.φ i - u i) ≤
      learnerPotential D u (learnerStep lo hi D Λ γ) - learnerPotential D u Λ := by
  set Q := ∑ i, γ i ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  set G' := Λ.G + Q
  set s := Real.sqrt Λ.G
  set s' := Real.sqrt G'
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = Λ.G := Real.sq_sqrt hG
  have hss' : s' ^ 2 = G' := Real.sq_sqrt (by positivity)
  have hle : s ≤ s' := Real.sqrt_le_sqrt (by linarith)
  set n0 := ∑ i, (Λ.φ i - u i) ^ 2
  set n1 := ∑ i, ((learnerStep lo hi D Λ γ).φ i - u i) ^ 2
  have hpot : learnerPotential D u (learnerStep lo hi D Λ γ) - learnerPotential D u Λ =
      (D ^ 2 - n1) * s' / (2 * D) + D * s' - ((D ^ 2 - n0) * s / (2 * D) + D * s) := rfl
  rw [hpot]
  rcases eq_or_lt_of_le hQ with hQ0 | hQpos
  · have hγ : ∀ i, γ i = 0 := by
      intro i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (γ i))).mp hQ0.symm i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hG' : G' = Λ.G := by simp [G', ← hQ0]
    have hsame : s' = s := by simp only [s', s, hG']
    have hlhs : ∑ i, γ i * (Λ.φ i - u i) = 0 := by simp [hγ]
    rw [hlhs, hsame]
    have hn : n1 ≤ n0 := by
      apply Finset.sum_le_sum
      intro i _
      have := clampBand_dist hu (fun i => Λ.φ i - D / s' * γ i) i
      simp only [hγ, mul_zero, sub_zero] at this
      simp only [learnerStep, hγ, mul_zero, sub_zero]
      exact this
    have : 0 ≤ (n0 - n1) * s / (2 * D) := div_nonneg (mul_nonneg (by linarith) hs) (by linarith)
    have e : (D ^ 2 - n1) * s / (2 * D) + D * s - ((D ^ 2 - n0) * s / (2 * D) + D * s) =
        (n0 - n1) * s / (2 * D) := by ring
    linarith
  · have hG'pos : 0 < G' := by positivity
    have hs'pos : 0 < s' := Real.sqrt_pos.mpr hG'pos
    set η := D / s'
    have hη : 0 < η := div_pos hD hs'pos
    have hn1 : n1 ≤ ∑ i, (Λ.φ i - η * γ i - u i) ^ 2 :=
      Finset.sum_le_sum fun i _ => clampBand_dist hu (fun i => Λ.φ i - η * γ i) i
    have hexpand : ∑ i, (Λ.φ i - η * γ i - u i) ^ 2 =
        n0 - 2 * η * ∑ i, γ i * (Λ.φ i - u i) + η ^ 2 * Q := by
      simp only [n0, Q, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    set R := ∑ i, γ i * (Λ.φ i - u i)
    have key : 2 * η * R ≤ n0 - n1 + η ^ 2 * Q := by linarith
    have hR : R ≤ (n0 - n1) * s' / (2 * D) + D * Q / (2 * s') := by
      have h2 : R ≤ (n0 - n1 + η ^ 2 * Q) / (2 * η) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have e : (n0 - n1 + η ^ 2 * Q) / (2 * η) = (n0 - n1) * s' / (2 * D) + D * Q / (2 * s') := by
        simp only [η]; field_simp
      linarith
    have hQeq : Q = s' ^ 2 - s ^ 2 := by rw [hss, hss']; simp only [G']; ring
    have hfin : D * s + D * Q / (2 * s') ≤ D * s' := by
      rw [hQeq]
      have : s + (s' ^ 2 - s ^ 2) / (2 * s') ≤ s' := by
        rw [← sub_nonneg]
        have e : s' - (s + (s' ^ 2 - s ^ 2) / (2 * s')) = (s' - s) ^ 2 / (2 * s') := by
          field_simp; ring
        rw [e]; positivity
      have := mul_le_mul_of_nonneg_left this hD.le
      have e2 : D * (s + (s' ^ 2 - s ^ 2) / (2 * s')) = D * s + D * (s' ^ 2 - s ^ 2) / (2 * s') := by
        ring
      linarith
    have hfirst : (D ^ 2 - n0) * s / (2 * D) ≤ (D ^ 2 - n0) * s' / (2 * D) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    have e : (D ^ 2 - n1) * s' / (2 * D) =
        (D ^ 2 - n0) * s' / (2 * D) + (n0 - n1) * s' / (2 * D) := by ring
    linarith

lemma learnerPotential_le {D : ℝ} (hD : 0 < D) (u : Fin d → ℝ) (Λ : BandLearner d)
    (hdist : 0 ≤ ∑ i, (Λ.φ i - u i) ^ 2) :
    learnerPotential D u Λ ≤ 3 / 2 * D * Real.sqrt Λ.G := by
  unfold learnerPotential
  have hs := Real.sqrt_nonneg Λ.G
  have : (D ^ 2 - ∑ i, (Λ.φ i - u i) ^ 2) * Real.sqrt Λ.G / (2 * D) ≤ D * Real.sqrt Λ.G / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma self_bounding {X X' G F D : ℝ} (hX : 0 ≤ X) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hreg : X ≤ X' + 3 / 2 * D * Real.sqrt G) (hG : G ≤ F * X) :
    X ≤ 2 * X' + 9 / 4 * D ^ 2 * F := by
  have h1 : Real.sqrt G ≤ Real.sqrt (F * X) := Real.sqrt_le_sqrt hG
  have h2 : 3 / 2 * D * Real.sqrt (F * X) ≤ X / 2 + 9 / 8 * D ^ 2 * F := by
    have hsq := Real.sq_sqrt (mul_nonneg hF hX)
    have ht := Real.sqrt_nonneg (F * X)
    have hb : 0 ≤ X / 2 + 9 / 8 * D ^ 2 * F := by positivity
    have hsq2 : (3 / 2 * D * Real.sqrt (F * X)) ^ 2 ≤ (X / 2 + 9 / 8 * D ^ 2 * F) ^ 2 := by
      have e : (3 / 2 * D * Real.sqrt (F * X)) ^ 2 = 9 / 4 * D ^ 2 * (F * X) := by
        rw [mul_pow, hsq]; ring
      rw [e]; nlinarith [sq_nonneg (X / 2 - 9 / 8 * D ^ 2 * F)]
    by_contra hc
    push Not at hc
    nlinarith [mul_self_lt_mul_self hb hc]
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 / 2 * D)
  linarith

end OracleTemplate.OnlineMetricAccelerated
