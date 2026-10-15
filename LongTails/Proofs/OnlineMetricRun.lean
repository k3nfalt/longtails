import LongTails.Proofs.OnlineMetricFacts

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

lemma Inv.phi_band {s : Core d} {n : ℕ} (I : Inv f w μ fstar x0 b0 s n) :
    ∀ i, bandLo d ≤ s.φ i ∧ s.φ i ≤ bandHi := by
  rw [I.phi]; exact (learnerFor_band I.band0 I.band1 s.ep).1

lemma Inv.scale_lower {s : Core d} {n : ℕ} (hd : 1 ≤ (d : ℝ)) (I : Inv f w μ fstar x0 b0 s n) :
    1 / (2 * d) ≤ stepScale s := by
  have h1 := bestCut_band hd I.cuts I.phi_band
  have h2 := I.certified
  have hθ := stepScale_pos s
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hθ] at h2
  nlinarith

lemma Inv.cuts_len {s : Core d} {n : ℕ} (hd : 1 ≤ (d : ℝ)) (I : Inv f w μ fstar x0 b0 s n) :
    (s.cuts.length : ℝ) ≤ logTwo d :=
  cuts_length_le (w := w) hd I.cuts I.phi_band I.certified

lemma Inv.running {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n) (hk : 1 ≤ s.k) :
    0 < s.fs - fstar ∧ s.A ≤ 8 * d / μ := by
  have hnh := I.not_halved hk
  have hpot := I.pot xstar
  have hdist := metric_dist_le hd H.w_pos I.box_ge I.phi_band (fun i => s.xs i - xstar i)
  have hgr := H.dist_le s.xs
  have hz : 0 ≤ ∑ i, (s.z i - xstar i) ^ 2 / metric s i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (metric_pos H.w_pos I.box_ge i).le
  rw [H.fmin] at hpot
  rw [← I.fs] at hgr
  have hθ := I.scale_lower hd
  have hA := I.A_lower
  have hkpos : (0 : ℝ) < s.k * (s.k + 1) := by
    have : (1 : ℝ) ≤ s.k := by exact_mod_cast hk
    positivity
  have hθpos := stepScale_pos s
  have hApos : 0 < s.A := lt_of_lt_of_le (by positivity) hA
  have hΔ0 : 0 ≤ s.fs - fstar := by rw [I.fs]; linarith [H.ge_fstar s.xs]
  have hμ := H.μ_pos
  have key : s.A * (f s.x - fstar) ≤ 4 * d / μ * (s.fs - fstar) := by
    have e : (∑ i, (s.xs i - xstar i) ^ 2 / metric s i) / 2 ≤ 4 * d / μ * (s.fs - fstar) := by
      have : 4 * d * ∑ i, w i * (s.xs i - xstar i) ^ 2 ≤ 4 * d * (2 / μ * (s.fs - fstar)) :=
        mul_le_mul_of_nonneg_left hgr (by positivity)
      have e2 : 4 * d * (2 / μ * (s.fs - fstar)) = 2 * (4 * d / μ * (s.fs - fstar)) := by ring
      linarith
    linarith
  have hstrict : s.A * ((s.fs - fstar) / 2) < s.A * (f s.x - fstar) :=
    mul_lt_mul_of_pos_left hnh hApos
  constructor
  · by_contra hc
    have h0 : s.fs - fstar = 0 := le_antisymm (not_lt.mp hc) hΔ0
    rw [h0] at hstrict key
    simp at hstrict
    nlinarith
  · have hΔpos : 0 < s.fs - fstar := by
      by_contra hc
      have h0 : s.fs - fstar = 0 := le_antisymm (not_lt.mp hc) hΔ0
      rw [h0] at hstrict key; simp at hstrict; nlinarith
    have : s.A * ((s.fs - fstar) / 2) < 4 * d / μ * (s.fs - fstar) := by linarith
    have e : 4 * d / μ * (s.fs - fstar) = (8 * d / μ) * ((s.fs - fstar) / 2) := by ring
    rw [e] at this
    exact (lt_of_mul_lt_mul_right this (by linarith)).le

lemma Inv.k_le {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n) : (s.k : ℝ) ≤ runCap d μ := by
  rcases Nat.eq_zero_or_pos s.k with hk | hk
  · rw [hk]; simp only [Nat.cast_zero]; exact runCap_nonneg H.μ_pos
  have hA := (I.running H hd hk).2
  have hθ := I.scale_lower hd
  have hlow := I.A_lower
  have hμ := H.μ_pos
  have hk0 : (0 : ℝ) ≤ s.k := Nat.cast_nonneg _
  have h1 : (s.k : ℝ) * (s.k + 1) ≤ 64 * d ^ 2 / μ := by
    have h2 : 1 / (2 * d) * (s.k * (s.k + 1)) / 4 ≤ 8 * d / μ := by
      have := mul_le_mul_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ s.k * (s.k + 1))
      have h3 : stepScale s * (s.k * (s.k + 1)) / 4 ≤ 8 * d / μ := le_trans hlow hA
      have h4 : 1 / (2 * d) * (s.k * (s.k + 1)) / 4 ≤ stepScale s * (s.k * (s.k + 1)) / 4 := by
        linarith
      linarith
    have e : 1 / (2 * (d : ℝ)) * ((s.k : ℝ) * ((s.k : ℝ) + 1)) / 4 =
        (s.k : ℝ) * ((s.k : ℝ) + 1) / (8 * d) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at h2
    have e2 : 8 * d / μ * (8 * d) = 64 * d ^ 2 / μ := by ring
    linarith
  have hsq : (s.k : ℝ) ^ 2 ≤ runCap d μ ^ 2 := by
    unfold runCap
    rw [mul_pow, kappaRoot_sq hμ]
    have : (8 * (d : ℝ)) ^ 2 * (1 / μ) = 64 * d ^ 2 / μ := by ring
    nlinarith
  by_contra hc
  push Not at hc
  nlinarith [mul_self_lt_mul_self (runCap_nonneg hμ) hc]

lemma Inv.record_bound {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n) (u : EuclideanSpace ℝ (Fin d))
    (hu : f u - fstar ≤ (s.fs - fstar) / 4) :
    (s.k : ℝ) ≤ lossL (fun i => (s.xs i - u i) ^ 2 / ((s.fs - fstar) * s.b i)) s.cuts s.φ := by
  rcases Nat.eq_zero_or_pos s.k with hk | hk
  · rw [hk]; simp only [Nat.cast_zero]; exact lossL_nonneg _ _ _
  obtain ⟨hΔ, -⟩ := I.running H hd hk
  have hnh := I.not_halved hk
  have hpot := I.pot u
  set Δ := s.fs - fstar
  set c : Fin d → ℝ := fun i => (s.xs i - u i) ^ 2 / (Δ * s.b i)
  have hbpos : ∀ i, 0 < s.b i := fun i =>
    lt_of_lt_of_le (by have := H.w_pos i; positivity) (I.box_ge i)
  have hc : ∀ i, 0 ≤ c i := fun i => div_nonneg (sq_nonneg _) (by have := hbpos i; positivity)
  have hid : ∑ i, (s.xs i - u i) ^ 2 / metric s i = Δ * lossEll c s.φ := by
    rw [lossEll, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c, metric]
    rw [Real.exp_neg]
    have := hbpos i
    field_simp
  have hz : 0 ≤ ∑ i, (s.z i - u i) ^ 2 / metric s i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (metric_pos H.w_pos I.box_ge i).le
  have hθ := stepScale_pos s
  have hlow := I.A_lower
  have hkpos : (0 : ℝ) < s.k * (s.k + 1) := by
    have : (1 : ℝ) ≤ s.k := by exact_mod_cast hk
    positivity
  have hApos : 0 < s.A := lt_of_lt_of_le (by positivity) hlow
  have hgap : Δ / 4 < f s.x - f u := by linarith
  have hA : s.A < 2 * lossEll c s.φ := by
    have h1 : s.A * (Δ / 4) < s.A * (f s.x - f u) := mul_lt_mul_of_pos_left hgap hApos
    have h2 : s.A * (f s.x - f u) ≤ Δ * lossEll c s.φ / 2 := by rw [← hid]; linarith
    have h3 : s.A * (Δ / 4) < (2 * lossEll c s.φ) * (Δ / 4) := by nlinarith
    exact lt_of_mul_lt_mul_right h3 (by linarith)
  set V := (bestCut s.cuts s.φ).1
  have hV := I.certified
  have hk0 : (0 : ℝ) ≤ s.k := Nat.cast_nonneg _
  have hksq : (s.k : ℝ) ^ 2 < 8 * lossEll c s.φ * V := by
    have h1 : stepScale s * (s.k : ℝ) ^ 2 < 8 * lossEll c s.φ := by nlinarith
    have h2 : 1 ≤ stepScale s * V := by
      rw [div_le_iff₀ hθ] at hV; linarith
    have hℓ := lossEll_nonneg hc s.φ
    nlinarith
  have hL : lossL c s.cuts s.φ = Real.sqrt (8 * lossEll c s.φ * V) := rfl
  rw [hL]
  apply Real.le_sqrt_of_sq_le hksq.le

end OracleTemplate.OnlineMetricAccelerated
