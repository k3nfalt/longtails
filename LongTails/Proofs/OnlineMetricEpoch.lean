import LongTails.Proofs.OnlineMetricBox

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

lemma sqrt_cap {μ : ℝ} (_hμ : 0 < μ) :
    8 * d * Real.sqrt (9 / 2 / μ) ≤ lossCap d μ := by
  unfold lossCap kappaRoot
  have h : Real.sqrt (9 / 2 / μ) = Real.sqrt (9 / 2) * Real.sqrt (1 / μ) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  rw [h]
  have h2 : Real.sqrt (9 / 2) ≤ 17 / 8 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h3 := Real.sqrt_nonneg (1 / μ)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hd h3)]

lemma record_loss_sum {fstar : ℝ} {R : Record d} {u : EuclideanSpace ℝ (Fin d)}
    (hw : ∀ i, 0 < w i) (hb : ∀ i, 1 / w i ≤ R.b i) (hΔ : 0 ≤ R.fs - fstar)
    {B : ℝ} (hB : 0 ≤ B) (hdist : ∑ i, w i * (R.xs i - u i) ^ 2 ≤ B * (R.fs - fstar)) :
    ∑ i, recordLoss fstar R u i ≤ B ∧
      ∑ i, recordLoss fstar R u i / (1 / w i / (2 * R.b i)) ≤ 2 * B := by
  have hbpos : ∀ i, 0 < R.b i := fun i => lt_of_lt_of_le (by have := hw i; positivity) (hb i)
  rcases eq_or_lt_of_le hΔ with h0 | hpos
  · have hz : ∀ i, recordLoss fstar R u i = 0 := by
      intro i; simp [recordLoss, ← h0]
    simp only [hz, zero_div, Finset.sum_const_zero]
    exact ⟨hB, by linarith⟩
  constructor
  · have h1 : ∀ i, recordLoss fstar R u i ≤ w i * (R.xs i - u i) ^ 2 / (R.fs - fstar) := by
      intro i
      unfold recordLoss
      rw [div_le_div_iff₀ (mul_pos hpos (hbpos i)) hpos]
      have : 1 ≤ w i * R.b i := by
        have := hb i; rw [div_le_iff₀ (hw i)] at this; linarith
      have hs := sq_nonneg (R.xs i - u i)
      have hm := mul_le_mul_of_nonneg_left this (mul_nonneg hs hpos.le)
      nlinarith [hm]
    calc ∑ i, recordLoss fstar R u i ≤ ∑ i, w i * (R.xs i - u i) ^ 2 / (R.fs - fstar) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, w i * (R.xs i - u i) ^ 2) / (R.fs - fstar) := by rw [Finset.sum_div]
      _ ≤ B := by rw [div_le_iff₀ hpos]; exact hdist
  · have h1 : ∀ i, recordLoss fstar R u i / (1 / w i / (2 * R.b i)) =
        2 * (w i * (R.xs i - u i) ^ 2) / (R.fs - fstar) := by
      intro i
      unfold recordLoss
      have := hbpos i; have := hw i
      field_simp
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_div, div_le_iff₀ hpos,
      ← Finset.mul_sum]
    nlinarith

noncomputable def epochNext (t s : Core d) (xn : EuclideanSpace ℝ (Fin d)) (fn : ℝ) : Core d :=
  { t with
    ep := s.ep + 1
    xs := xn
    fs := fn
    φ := (learnerFor t (s.ep + 1)).φ
    x := xn
    z := xn
    A := 0
    k := 0
    cuts := []
    prev := some ⟨s.xs, s.fs, s.b, s.φ, s.cuts, s.seg, s.k + 1 + s.cuts.length⟩ }

lemma endEpoch_eq (fstar : ℝ) (s : Core d) (xn : EuclideanSpace ℝ (Fin d)) (fn : ℝ) :
    endEpoch fstar s xn fn = epochNext (resolvePrev fstar s xn) s xn fn := rfl

lemma inv_epochNext {s t : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar)
    (hd : 1 ≤ (d : ℝ)) (I : Inv f w μ fstar x0 b0 s n)
    (ht_b : t.b = s.b) (ht_seg : t.seg = s.seg) (ht_stage : t.stage = s.stage)
    (ht0 : BandOK t.learner0) (ht1 : BandOK t.learner1)
    (ht_keep : learnerFor t s.ep = learnerFor s s.ep)
    (hhalf : f (trialPoint s (extrapolate s) (gradient f (extrapolate s))) - fstar ≤
      (s.fs - fstar) / 2)
    (hledger : Ledger w μ (epochNext t s (trialPoint s (extrapolate s)
      (gradient f (extrapolate s))) (f (trialPoint s (extrapolate s)
      (gradient f (extrapolate s))))) (n + 1)) :
    Inv f w μ fstar x0 b0 (epochNext t s (trialPoint s (extrapolate s)
      (gradient f (extrapolate s))) (f (trialPoint s (extrapolate s)
      (gradient f (extrapolate s))))) (n + 1) := by
  set xp := trialPoint s (extrapolate s) (gradient f (extrapolate s))
  have hk := I.k_le H hd
  have hcl := I.cuts_len hd
  refine ⟨?_, ?_, ?_, ht0, ht1, rfl, rfl, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, hledger⟩
  · show t.stage = d; rw [ht_stage]; exact I.stage
  · show ∀ i, 1 / w i ≤ t.b i; rw [ht_b]; exact I.box_ge
  · show ∃ m : Fin d → ℕ, (∀ i, t.b i = b0 i / 2 ^ m i) ∧ t.seg = ∑ i, m i
    rw [ht_b, ht_seg]; exact I.box_pow
  · show f xp - fstar ≤ (f x0 - fstar) / 2 ^ (s.ep + 1)
    have := I.halving
    rw [pow_succ]
    have h2 : (s.fs - fstar) / 2 ≤ (f x0 - fstar) / 2 ^ s.ep / 2 := by linarith
    rw [div_div] at h2
    linarith
  · intro u
    simp [epochNext]
  · show stepScale (epochNext t s xp (f xp)) * (((0 : ℕ) : ℝ) * ((0 : ℕ) + 1)) / 4 ≤ 0
    simp
  · intro h; simp [epochNext] at h
  · intro a ha; simp [epochNext] at ha
  · show 1 / stepScale (epochNext t s xp (f xp)) ≤ (bestCut [] _).1
    simp [stepScale, bestCut, epochNext]
  · show PrevOK f w μ fstar (epochNext t s xp (f xp))
    unfold PrevOK
    simp only [epochNext]
    refine ⟨by omega, I.fs, hhalf, I.phi_band, I.cuts, I.box_ge, by rw [ht_seg], ?_, ?_, ?_⟩
    · intro _
      refine ⟨ht_b.symm, ?_⟩
      show (learnerFor t (s.ep + 1 + 1)).φ = s.φ
      rw [show s.ep + 1 + 1 = s.ep + 2 by ring, learnerFor_add_two, ht_keep, I.phi]
    · intro u hu
      have hb := I.record_bound H hd u hu
      have e : recordLoss fstar ⟨s.xs, s.fs, s.b, s.φ, s.cuts, s.seg,
          s.k + 1 + s.cuts.length⟩ u = fun i => (s.xs i - u i) ^ 2 / ((s.fs - fstar) * s.b i) :=
        rfl
      rw [e]; push_cast; linarith
    · push_cast; linarith

end OracleTemplate.OnlineMetricAccelerated
