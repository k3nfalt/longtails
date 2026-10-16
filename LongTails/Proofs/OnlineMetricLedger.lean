import LongTails.Proofs.OnlineMetricEpoch

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

lemma ledger_first {s : Core d} {n : ℕ} (I : Inv f w μ fstar x0 b0 s n) (hR : s.prev = none)
    (xn : EuclideanSpace ℝ (Fin d)) (fn : ℝ) :
    Ledger w μ (epochNext s s xn fn) (n + 1) := by
  obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ := I.ledger
  have hps : prevSteps s = 0 := by simp [prevSteps, hR]
  have hpg : prevSeg s = s.seg := by simp [prevSeg, hR]
  rw [hR] at hep
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, add_zero] at hep
  refine ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, ?_, ?_, ?_, hXc, hL0, hL1, ?_⟩
  · show s.ep + 1 = _ + (if (some _ : Option (Record d)).isSome then 1 else 0)
    simp only [Option.isSome_some, ite_true]; omega
  · show ndrop ≤ s.seg; rw [← hpg]; exact hd1
  · show s.seg ≤ s.seg; exact le_rfl
  · show ((n + 1 : ℕ) : ℝ) ≤ _ + ((s.k + 1 + s.cuts.length : ℕ) : ℝ) + _ +
      (((0 : ℕ) : ℝ) + (([] : List (Fin d → ℝ)).length : ℝ))
    rw [hps] at hn
    have hsg : ((epochNext s s xn fn).seg : ℝ) = s.seg := rfl
    rw [hsg]
    push_cast at hn ⊢
    simp only [List.length_nil, Nat.cast_zero, add_zero]
    linarith

lemma ledger_drop {s : Core d} {n : ℕ} (I : Inv f w μ fstar x0 b0 s n) {R0 : Record d}
    (hR : s.prev = some R0) (hne : R0.seg ≠ s.seg) (xn : EuclideanSpace ℝ (Fin d)) (fn : ℝ) :
    Ledger w μ (epochNext s s xn fn) (n + 1) := by
  obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ := I.ledger
  have hp := I.prev
  unfold PrevOK at hp
  rw [hR] at hp
  obtain ⟨-, -, -, -, -, -, hseg, -, -, hcap⟩ := hp
  have hps : prevSteps s = R0.steps := by simp [prevSteps, hR]
  have hpg : prevSeg s = R0.seg := by simp [prevSeg, hR]
  rw [hR] at hep
  simp only [Option.isSome_some, ite_true] at hep
  rw [hpg] at hd1
  refine ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop + 1, ?_, ?_, ?_, hXc, hL0, hL1, ?_⟩
  · show s.ep + 1 = _ + (if (some _ : Option (Record d)).isSome then 1 else 0)
    simp only [Option.isSome_some, ite_true]; omega
  · show ndrop + 1 ≤ s.seg; omega
  · show s.seg ≤ s.seg; exact le_rfl
  · show ((n + 1 : ℕ) : ℝ) ≤ _ + ((ndrop + 1 : ℕ) : ℝ) * (runCap d μ + 1 + logTwo d) +
      ((s.k + 1 + s.cuts.length : ℕ) : ℝ) + _ +
      (((0 : ℕ) : ℝ) + (([] : List (Fin d → ℝ)).length : ℝ))
    rw [hps] at hn
    have hsg : ((epochNext s s xn fn).seg : ℝ) = s.seg := rfl
    rw [hsg]
    push_cast at hn ⊢
    simp only [List.length_nil, Nat.cast_zero, add_zero]
    linarith

lemma feed_facts {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n) {R0 : Record d} (hR : s.prev = some R0)
    (heq : R0.seg = s.seg) {xn : EuclideanSpace ℝ (Fin d)}
    (hhalf : f xn - fstar ≤ (s.fs - fstar) / 2) :
    let c0 := recordLoss fstar R0 xn
    let L := lossL c0 R0.cuts R0.φ
    let Lu := lossL c0 R0.cuts (comparator w s.b)
    let γ := lossGrad c0 R0.cuts R0.φ
    let Λ := learnerFor s (s.ep + 1)
    (R0.steps : ℝ) ≤ 1 + L + logTwo d ∧ 0 ≤ L ∧ L ≤ lossCap d μ ∧ Lu ≤ 12 * kappaRoot μ ∧
      L - Lu ≤ learnerPotential (bandWidth d) (comparator w s.b)
        (learnerStep (bandLo d) bandHi (bandWidth d) Λ γ) -
        learnerPotential (bandWidth d) (comparator w s.b) Λ ∧
      ∑ i, γ i ^ 2 ≤ L * lossCap d μ := by
  intro c0 L Lu γ Λ
  have hp := I.prev
  unfold PrevOK at hp
  rw [hR] at hp
  obtain ⟨-, hRfs, hRh, hRφ, hRcuts, hRb, -, hsame, hRF1, -⟩ := hp
  obtain ⟨hbeq, hφeq⟩ := hsame heq
  have hΔR : 0 ≤ R0.fs - fstar := by rw [hRfs]; linarith [H.ge_fstar R0.xs]
  have hu4 : f xn - fstar ≤ (R0.fs - fstar) / 4 := by linarith
  have hsteps := hRF1 xn hu4
  have hdist := H.pair_dist R0.xs xn (le_of_eq (by rw [hRfs])) hu4
  have hμ := H.μ_pos
  obtain ⟨hsum1, hsum2⟩ := record_loss_sum (u := xn) H.w_pos hRb hΔR
    (by positivity : (0 : ℝ) ≤ 9 / 2 / μ) hdist
  have hc0 : ∀ i, 0 ≤ c0 i := fun i => recordLoss_nonneg (by linarith) (fun i =>
    lt_of_lt_of_le (by have := H.w_pos i; positivity) (hRb i)) xn i
  have hcutsnn : ∀ a ∈ R0.cuts, ∀ i, 0 ≤ a i := fun a ha => (hRcuts a ha).1
  have hband := lossL_band hc0 (cuts := R0.cuts) (fun a ha => ⟨(hRcuts a ha).1, (hRcuts a ha).2.1⟩)
    hd (φ := R0.φ)
    (fun i => by
      have := (band_exp hd hRφ i).1
      rw [Real.exp_neg, inv_eq_one_div]
      rw [div_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ (by positivity)] at this; linarith)
    (fun i => (band_exp hd hRφ i).2)
  have hL : L ≤ lossCap d μ := by
    refine le_trans hband ?_
    refine le_trans ?_ (sqrt_cap hμ)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum1) (by positivity)
  have hbox := I.box_ge
  have hLu : Lu ≤ 12 * kappaRoot μ := by
    have hr : ∀ i, 0 < 1 / w i / (2 * s.b i) := fun i => by
      have := H.w_pos i
      have : 0 < s.b i := lt_of_lt_of_le (by positivity) (hbox i)
      positivity
    have hcomp := lossL_comparator hc0 (cuts := R0.cuts) hr
      (fun a ha => by rw [← hbeq]; exact hRcuts a ha) hd
      (fun i => (comparator_exp hd H.w_pos hbox i).1) (fun i => (comparator_exp hd H.w_pos hbox i).2)
    refine le_trans hcomp ?_
    have e : ∀ i, c0 i / (1 / w i / (2 * s.b i)) = recordLoss fstar R0 xn i / (1 / w i / (2 * R0.b i)) := by
      intro i; rw [hbeq]
    rw [Finset.sum_congr rfl fun i _ => e i]
    have h16 : 16 * ∑ i, recordLoss fstar R0 xn i / (1 / w i / (2 * R0.b i)) ≤ (12 * kappaRoot μ) ^ 2 := by
      rw [mul_pow, kappaRoot_sq hμ]
      have : 16 * (2 * (9 / 2 / μ)) = 12 ^ 2 * (1 / μ) := by ring
      nlinarith
    calc Real.sqrt (16 * ∑ i, recordLoss fstar R0 xn i / (1 / w i / (2 * R0.b i)))
        ≤ Real.sqrt ((12 * kappaRoot μ) ^ 2) := Real.sqrt_le_sqrt h16
      _ = 12 * kappaRoot μ := Real.sqrt_sq (by unfold kappaRoot; positivity)
  have hlin := lossL_linear hc0 hcutsnn R0.φ (comparator w s.b)
  have hΛband := learnerFor_band I.band0 I.band1 (s.ep + 1)
  have hcomp_band := comparator_band hd H.w_pos hbox
  have hreg := learner_step_bound (bandWidth_pos hd) hcomp_band Λ hΛband.2
    (by
      have := band_dist_le hcomp_band hΛband.1
      rw [bandWidth_sq hd]; exact this) γ
  have hgsq := lossGrad_sq hc0 hcutsnn R0.φ
  have hL0 : 0 ≤ L := lossL_nonneg _ _ _
  refine ⟨hsteps, hL0, hL, hLu, ?_, ?_⟩
  · have e : ∑ i, γ i * (Λ.φ i - comparator w s.b i) =
        -∑ i, lossGrad c0 R0.cuts R0.φ i * (comparator w s.b i - R0.φ i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Λ.φ = R0.φ from hφeq]; ring
    linarith
  · calc ∑ i, γ i ^ 2 ≤ L ^ 2 := hgsq
      _ = L * L := sq L
      _ ≤ L * lossCap d μ := mul_le_mul_of_nonneg_left hL hL0

lemma ledger_feed {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar)
    (hd : 1 ≤ (d : ℝ)) (I : Inv f w μ fstar x0 b0 s n) {R0 : Record d}
    (hR : s.prev = some R0) (heq : R0.seg = s.seg) {xn : EuclideanSpace ℝ (Fin d)} (fn : ℝ)
    (hhalf : f xn - fstar ≤ (s.fs - fstar) / 2) :
    Ledger w μ (epochNext (feedLearner s (s.ep + 1)
      (lossGrad (recordLoss fstar R0 xn) R0.cuts R0.φ)) s xn fn) (n + 1) := by
  have hff := feed_facts H hd I hR heq hhalf
  simp only at hff
  obtain ⟨hsteps, hL0, hL, hLu, hreg, hG⟩ := hff
  set c0 := recordLoss fstar R0 xn
  set L := lossL c0 R0.cuts R0.φ
  set Lu := lossL c0 R0.cuts (comparator w s.b)
  set γ := lossGrad c0 R0.cuts R0.φ
  obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0', hL1', hn⟩ :=
    I.ledger
  have hps : prevSteps s = R0.steps := by simp [prevSteps, hR]
  have hpg : prevSeg s = R0.seg := by simp [prevSeg, hR]
  rw [hR] at hep
  simp only [Option.isSome_some, ite_true] at hep
  rw [hpg] at hd1
  have hF := lossCap_nonneg (d := d) H.μ_pos
  rcases Nat.mod_two_eq_zero_or_one (s.ep + 1) with hpar | hpar
  · have hΛ : learnerFor s (s.ep + 1) = s.learner0 := by simp [learnerFor, hpar]
    rw [hΛ] at hreg
    obtain ⟨hX0, hr0, hG0, hX0'⟩ := hL0'
    refine ⟨Xc, X0 + L, X0' + Lu, X1, X1', nc, n0 + 1, n1, ndrop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s.ep + 1 = _ + (if (some _ : Option (Record d)).isSome then 1 else 0)
      simp only [Option.isSome_some, ite_true]; omega
    · show ndrop ≤ s.seg
      omega
    · show s.seg ≤ (feedLearner s (s.ep + 1) γ).seg
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]
    · show Xc ≤ _ + ((feedLearner s (s.ep + 1) γ).seg : ℝ) * _
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]; exact hXc
    · show LearnerLedger (bandWidth d) (lossCap d μ)
        (comparator w (feedLearner s (s.ep + 1) γ).b) (kappaRoot μ)
        (feedLearner s (s.ep + 1) γ).learner0 (X0 + L) (X0' + Lu) (n0 + 1)
      rw [(feedLearner_fields s (s.ep + 1) γ).1]
      have hl : (feedLearner s (s.ep + 1) γ).learner0 =
          learnerStep (bandLo d) bandHi (bandWidth d) s.learner0 γ := by
        simp [feedLearner, hpar]
      rw [hl]
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · show s.learner0.G + ∑ i, γ i ^ 2 ≤ lossCap d μ * (X0 + L)
        nlinarith
      · push_cast; linarith
    · show LearnerLedger (bandWidth d) (lossCap d μ)
        (comparator w (feedLearner s (s.ep + 1) γ).b) (kappaRoot μ)
        (feedLearner s (s.ep + 1) γ).learner1 X1 X1' n1
      rw [(feedLearner_fields s (s.ep + 1) γ).1]
      have hl : (feedLearner s (s.ep + 1) γ).learner1 = s.learner1 := by
        simp [feedLearner, hpar]
      rw [hl]; exact hL1'
    · show ((n + 1 : ℕ) : ℝ) ≤ ((nc : ℝ) + ((n0 + 1 : ℕ) : ℝ) + n1) * (1 + logTwo d) + Xc +
        (X0 + L) + X1 + ndrop * (runCap d μ + 1 + logTwo d) +
        ((s.k + 1 + s.cuts.length : ℕ) : ℝ) +
        ((feedLearner s (s.ep + 1) γ).seg : ℝ) * (runCap d μ + 2 + logTwo d) +
        (((0 : ℕ) : ℝ) + (([] : List (Fin d → ℝ)).length : ℝ))
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]
      rw [hps] at hn
      push_cast at hn ⊢
      simp only [List.length_nil, Nat.cast_zero, add_zero]
      linarith
  · have hΛ : learnerFor s (s.ep + 1) = s.learner1 := by simp [learnerFor, hpar]
    rw [hΛ] at hreg
    obtain ⟨hX1, hr1, hG1, hX1'⟩ := hL1'
    refine ⟨Xc, X0, X0', X1 + L, X1' + Lu, nc, n0, n1 + 1, ndrop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s.ep + 1 = _ + (if (some _ : Option (Record d)).isSome then 1 else 0)
      simp only [Option.isSome_some, ite_true]; omega
    · show ndrop ≤ s.seg
      omega
    · show s.seg ≤ (feedLearner s (s.ep + 1) γ).seg
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]
    · show Xc ≤ _ + ((feedLearner s (s.ep + 1) γ).seg : ℝ) * _
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]; exact hXc
    · show LearnerLedger (bandWidth d) (lossCap d μ)
        (comparator w (feedLearner s (s.ep + 1) γ).b) (kappaRoot μ)
        (feedLearner s (s.ep + 1) γ).learner0 X0 X0' n0
      rw [(feedLearner_fields s (s.ep + 1) γ).1]
      have hl : (feedLearner s (s.ep + 1) γ).learner0 = s.learner0 := by
        simp [feedLearner, hpar]
      rw [hl]; exact hL0'
    · show LearnerLedger (bandWidth d) (lossCap d μ)
        (comparator w (feedLearner s (s.ep + 1) γ).b) (kappaRoot μ)
        (feedLearner s (s.ep + 1) γ).learner1 (X1 + L) (X1' + Lu) (n1 + 1)
      rw [(feedLearner_fields s (s.ep + 1) γ).1]
      have hl : (feedLearner s (s.ep + 1) γ).learner1 =
          learnerStep (bandLo d) bandHi (bandWidth d) s.learner1 γ := by
        simp [feedLearner, hpar]
      rw [hl]
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · show s.learner1.G + ∑ i, γ i ^ 2 ≤ lossCap d μ * (X1 + L)
        nlinarith
      · push_cast; linarith
    · show ((n + 1 : ℕ) : ℝ) ≤ ((nc : ℝ) + n0 + ((n1 + 1 : ℕ) : ℝ)) * (1 + logTwo d) + Xc +
        X0 + (X1 + L) + ndrop * (runCap d μ + 1 + logTwo d) +
        ((s.k + 1 + s.cuts.length : ℕ) : ℝ) +
        ((feedLearner s (s.ep + 1) γ).seg : ℝ) * (runCap d μ + 2 + logTwo d) +
        (((0 : ℕ) : ℝ) + (([] : List (Fin d → ℝ)).length : ℝ))
      rw [(feedLearner_fields s (s.ep + 1) γ).2.1]
      rw [hps] at hn
      push_cast at hn ⊢
      simp only [List.length_nil, Nat.cast_zero, add_zero]
      linarith

end OracleTemplate.OnlineMetricAccelerated
