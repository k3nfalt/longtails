import LongTails.Proofs.OnlineMetricInvariant

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

lemma learnerFor_add_two (s : Core d) (r : ℕ) : learnerFor s (r + 2) = learnerFor s r := by
  unfold learnerFor; simp

lemma feedLearner_other (s : Core d) (r : ℕ) (γ : Fin d → ℝ) :
    learnerFor (feedLearner s (r + 1) γ) r = learnerFor s r := by
  unfold feedLearner learnerFor
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · have h1 : (r + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (r + 1) % 2 = 0 := by omega
    simp [h, h1]

lemma feedLearner_same (s : Core d) (r : ℕ) (γ : Fin d → ℝ) :
    learnerFor (feedLearner s r γ) r =
      learnerStep (bandLo d) bandHi (bandWidth d) (learnerFor s r) γ := by
  unfold feedLearner learnerFor
  rcases Nat.mod_two_eq_zero_or_one r with h | h <;> simp [h]

lemma feedLearner_fields (s : Core d) (r : ℕ) (γ : Fin d → ℝ) :
    (feedLearner s r γ).b = s.b ∧ (feedLearner s r γ).seg = s.seg ∧
    (feedLearner s r γ).ep = s.ep ∧ (feedLearner s r γ).prev = s.prev ∧
    (feedLearner s r γ).stage = s.stage := by
  unfold feedLearner; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

lemma learnerStep_band {lo hi D : ℝ} (h : lo ≤ hi) (Λ : BandLearner d) (hG : 0 ≤ Λ.G)
    (γ : Fin d → ℝ) :
    (∀ i, lo ≤ (learnerStep lo hi D Λ γ).φ i ∧ (learnerStep lo hi D Λ γ).φ i ≤ hi) ∧
      0 ≤ (learnerStep lo hi D Λ γ).G := by
  refine ⟨fun i => clampBand_mem h (fun i => Λ.φ i - D / Real.sqrt (Λ.G + ∑ i, γ i ^ 2) * γ i) i, ?_⟩
  show 0 ≤ Λ.G + ∑ i, γ i ^ 2
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (γ i)
  linarith

lemma learnerPotential_fresh (D : ℝ) (u : Fin d → ℝ) :
    learnerPotential D u (freshLearner d) = 0 := by
  simp [learnerPotential, freshLearner]

lemma fresh_ledger (D F : ℝ) (u : Fin d → ℝ) (κr : ℝ) :
    LearnerLedger D F u κr (freshLearner d) 0 0 0 := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · rw [learnerPotential_fresh]; norm_num
  · simp [freshLearner]
  · simp

lemma ledger_close {D F κr X X' : ℝ} {u : Fin d → ℝ} {Λ : BandLearner d} {n : ℕ}
    (hD : 0 < D) (hF : 0 ≤ F) (h : LearnerLedger D F u κr Λ X X' n) :
    X ≤ 24 * κr * n + 9 / 4 * D ^ 2 * F := by
  obtain ⟨hX, hreg, hG, hX'⟩ := h
  have h1 : X ≤ X' + 3 / 2 * D * Real.sqrt Λ.G := by
    have := learnerPotential_le hD u Λ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  have := self_bounding hX hF hD.le h1 hG
  linarith

lemma kappaRoot_ge_one {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) : 1 ≤ kappaRoot μ := by
  unfold kappaRoot
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ hμ]
  linarith

lemma kappaRoot_sq {μ : ℝ} (hμ : 0 < μ) : kappaRoot μ ^ 2 = 1 / μ := by
  unfold kappaRoot; rw [Real.sq_sqrt (by positivity)]

lemma logTwo_nonneg (hd : 1 ≤ (d : ℝ)) : 0 ≤ logTwo d := by
  unfold logTwo
  apply Real.logb_nonneg (by norm_num); linarith

lemma runCap_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ runCap d μ := by
  unfold runCap kappaRoot; positivity

lemma lossCap_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ lossCap d μ := by
  unfold lossCap kappaRoot; positivity

lemma lossL_nonneg (c : Fin d → ℝ) (cuts : List (Fin d → ℝ)) (φ : Fin d → ℝ) :
    0 ≤ lossL c cuts φ := Real.sqrt_nonneg _

lemma lossEll_nonneg {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) (φ : Fin d → ℝ) :
    0 ≤ lossEll c φ := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le

lemma recordLoss_nonneg {fstar : ℝ} {R : Record d} (hR : fstar ≤ R.fs) (hb : ∀ i, 0 < R.b i)
    (u : EuclideanSpace ℝ (Fin d)) (i : Fin d) : 0 ≤ recordLoss fstar R u i := by
  unfold recordLoss
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (hb i).le)

end OracleTemplate.OnlineMetricAccelerated
