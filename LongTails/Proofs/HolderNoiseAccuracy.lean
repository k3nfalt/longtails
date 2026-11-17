import LongTails.Algorithms.HolderNoiseVarianceReduction
import LongTails.Proofs.CenteredDyadicDescent
import LongTails.Proofs.HolderNoiseScales

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseAccuracy

open OracleTemplate.DyadicHolder OracleTemplate.CenteredDyadic HolderNoiseScales

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E}
  {L M ν σ Δ ε : ℝ}

lemma low_exponent_variance (hL : 0 < L) (hM : 0 ≤ M) (hν : ν ≤ 1 / 2)
    (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (j : ℕ) :
    M * (2 ^ j * tEta L ε) ^ (2 * ν) /
      (tb L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε j : ℝ) ≤
      ε ^ 2 / (32 * ((tJ L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε : ℝ) + 1)) := by
  have hη : 0 < tEta L ε := by unfold tEta; positivity
  have hMt : 0 ≤ M * tEta L ε ^ (2 * ν - 1) := by positivity
  have ht : TuneHyp L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε :=
    ⟨hL, hMt, le_rfl, by norm_num, hσ, hΔ, hε⟩
  apply le_trans (div_le_div_of_nonneg_right (level_variance_domination hM hη hν j)
    (Nat.cast_nonneg _))
  simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] using ht.beta j

lemma low_exponent_accuracy (H : OracleTemplate.CenteredDyadic.Hyp p F g L M ν σ) (hν : ν ≤ 1 / 2)
    (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (x0 : E)
    (hgap : ∀ x, F x0 - F x ≤ Δ) :
    let cfg := tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  have hη : 0 < tEta L ε := div_pos hε (mul_pos (by norm_num) H.L_pos)
  have hMt : 0 ≤ M * tEta L ε ^ (2 * ν - 1) :=
    mul_nonneg H.M_nn (Real.rpow_nonneg hη.le _)
  have ht : TuneHyp L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε :=
    ⟨H.L_pos, hMt, le_rfl, by norm_num, hσ, hΔ, hε⟩
  exact H.master_lintegral _ x0 ht.eta_pos (tbA_pos σ ε)
    (tb_pos L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε)
    (fun j _ => low_exponent_variance H.L_pos H.M_nn hν hσ hΔ hε j)
    ht.variance hgap ht.accuracy

lemma high_exponent_accuracy (H : OracleTemplate.CenteredDyadic.Hyp p F g L M ν σ)
    (hν : 1 / 2 ≤ ν) (hν1 : ν ≤ 1) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x0 : E) (hgap : ∀ x, F x0 - F x ≤ Δ) :
    let cfg := tcfg L M ν σ Δ ε
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  have ht : TuneHyp L M ν σ Δ ε := ⟨H.L_pos, H.M_nn, hν, hν1, hσ, hΔ, hε⟩
  exact H.master_lintegral _ x0 ht.eta_pos (tbA_pos σ ε) (tb_pos L M ν σ Δ ε)
    (fun j _ => ht.beta j) ht.variance hgap ht.accuracy

lemma anchor_accuracy (H : OracleTemplate.CenteredDyadic.Hyp p F g L M ν σ)
    (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (x0 : E)
    (hgap : ∀ x, F x0 - F x ≤ Δ) :
    let cfg := OracleTemplate.HolderNoise.anchorConfig L σ Δ ε
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  have ht : TuneHyp L 0 (1 / 2) σ Δ ε :=
    ⟨H.L_pos, le_rfl, le_rfl, by norm_num, hσ, hΔ, hε⟩
  apply H.master_lintegral _ x0 ht.eta_pos (tbA_pos σ ε) (fun _ => le_rfl)
    (β := 0) (V := ε ^ 2 / 16) (Δ := Δ)
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)
  · have hv := ht.variance
    have hnonneg : 0 ≤ ε ^ 2 / (32 * ((tJ L 0 (1 / 2) σ Δ ε : ℝ) + 1)) *
        (tJ L 0 (1 / 2) σ Δ ε : ℝ) := by positivity
    change σ ^ 2 / (tbA σ ε : ℝ) + 0 * (0 : ℕ) ≤ ε ^ 2 / 16
    simpa using (le_trans (le_add_of_nonneg_right hnonneg) hv)
  · exact hgap
  · exact ht.accuracy

lemma selected_accuracy (H : OracleTemplate.CenteredDyadic.Hyp p F g L M ν σ)
    (hν1 : ν ≤ 1) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x0 : E) (hgap : ∀ x, F x0 - F x ≤ Δ) :
    let a := if ν ≤ 1 / 2 then tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
      else tcfg L M ν σ Δ ε
    let cfg := OracleTemplate.HolderNoise.selectConfig a
      (OracleTemplate.HolderNoise.anchorConfig L σ Δ ε)
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  let acc : DyadicConfig → Prop := fun cfg =>
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε
  change acc (OracleTemplate.HolderNoise.selectConfig
    (if ν ≤ 1 / 2 then tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
      else tcfg L M ν σ Δ ε) (OracleTemplate.HolderNoise.anchorConfig L σ Δ ε))
  by_cases hν : ν ≤ 1 / 2
  · rw [ite_eq_left hν]
    unfold OracleTemplate.HolderNoise.selectConfig
    split_ifs
    · exact low_exponent_accuracy H hν hσ hΔ hε x0 hgap
    · exact anchor_accuracy H hσ hΔ hε x0 hgap
  · rw [ite_eq_right hν]
    unfold OracleTemplate.HolderNoise.selectConfig
    split_ifs
    · exact high_exponent_accuracy H (lt_of_not_ge hν).le hν1 hσ hΔ hε x0 hgap
    · exact anchor_accuracy H hσ hΔ hε x0 hgap

lemma selected_batches (L M ν σ Δ ε : ℝ) :
    let a := if ν ≤ 1 / 2 then tcfg L (M * tEta L ε ^ (2 * ν - 1)) (1 / 2) σ Δ ε
      else tcfg L M ν σ Δ ε
    let cfg := OracleTemplate.HolderNoise.selectConfig a
      (OracleTemplate.HolderNoise.anchorConfig L σ Δ ε)
    ∀ k, 1 ≤ cfg.batch k := by
  dsimp only
  unfold OracleTemplate.HolderNoise.selectConfig
  split_ifs <;> intro k <;> unfold DyadicConfig.batch <;> split_ifs
  all_goals first | exact tbA_pos σ ε | exact tb_pos _ _ _ _ _ _ _ | exact le_rfl

end LongTails.Proofs.HolderNoiseAccuracy
