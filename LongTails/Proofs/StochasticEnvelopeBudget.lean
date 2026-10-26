import LongTails.Proofs.StochasticEnvelopeAccuracy
import LongTails.Proofs.StochasticEnvelopeRecursion
open MeasureTheory ProbabilityTheory
namespace LongTails.Proofs.StochasticEnvelopeBudget
open LongTails.Proofs.StochasticEnvelopeWork
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
lemma parameters_level_work {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hσ0 : 0 ≤ σ0) (hp : 1 < p) (hp2 : p ≤ 2)
    (hT : 1 ≤ L * R ^ 2 / ε) :
    let q := p / (p - 1)
    let M := 4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ q + 1 / δ
    let W := 2 + q + Real.log M
    let H := W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3)
    let d := depth L R ε δ σ0 p
    let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
    ∀ i, i ≤ d →
      Integrable (fun n => (levelCalls c i n : ℝ)) (geometricMeasure c.levelProbability) ∧
      (∫ n, (levelCalls c i n : ℝ) ∂geometricMeasure c.levelProbability) ≤ c.baseWork * H := by
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let M := 4 + T + (σ0 * R / ε) ^ q + 1 / δ
  let W := 2 + q + Real.log M
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let d := depth L R ε δ σ0 p
  let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  let a := fun j : ℕ => (κ ^ (-2 : ℝ) / H) * ρ ^ j
  let pp := fun j : ℕ => Q j / (Q j - 1)
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hV : 0 ≤ (σ0 * R / ε) ^ q := Real.rpow_nonneg (by positivity) _
  have hM : 4 ≤ M := by dsimp [M, T]; linarith [one_div_pos.mpr hδ]
  have hTM : T ≤ M := by dsimp [M]; linarith [one_div_pos.mpr hδ]
  have hW : 2 + q ≤ W := by dsimp [W]; linarith [Real.log_nonneg (by linarith : 1 ≤ M)]
  have hdc := depth_choice hM hq
  have hdEq : d = ⌈Real.sqrt (Real.log M)⌉₊ := max_eq_right hdc.1
  have hd : 1 ≤ d := Nat.le_max_left _ _
  have hdW : (d : ℝ) ≤ W := by rw [hdEq]; exact hdc.2.1
  have hk : 1 < k := (geometric_depth_tuning hT d hd).1
  have hκ : 2 ≤ κ := by dsimp [κ]; linarith
  have hklog : Real.log κ ≤ W := (condition_log_bound hT hTM d hd).trans (by dsimp [W]; linarith)
  have hratio (j : ℕ) : (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1) = κ :=
    level_smoothness_ratio hL (by linarith : 0 < k) j
  dsimp only
  intro i hi
  obtain ⟨ht, ht1, hw⟩ := geometric_level_work hq hW hκ hklog d hd hdW i hi
  let cost := fun ell => (approximationTuning κ (pp i) (a i) (m * (2 : ℝ) ^ ell)).calls
  have hlevel (n : ℕ) : levelCalls c i n = cost 0 + cost (n + 1) + cost n := by
    dsimp only [levelCalls]
    rw [hratio]
    rfl
  have hv : c.levelProbability = levelProbability t ht.le ht1 := rfl
  change Integrable (fun n => (levelCalls c i n : ℝ)) (geometricMeasure c.levelProbability) ∧
    (∫ n, (levelCalls c i n : ℝ) ∂geometricMeasure c.levelProbability) ≤ c.baseWork * H
  simp only [hlevel, hv]
  exact hw
open StochasticEnvelopeRecursion
lemma accuracy_level_work_integrable {c : Parameters} {p s a t : ℝ} {d : ℕ}
    (h : AccuracyTuning c p s a t d) (j : ℕ) :
    Integrable (fun n => (levelCalls c j n : ℝ)) (geometricMeasure c.levelProbability) := by
  let κ := (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1)
  have ha1 : c.relative j ≤ 1 := (h.relative_small j).trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [h.condition j]) (by norm_num))
  have hw := tuned_envelope_work (h.condition j) (h.relative_pos j) ha1 h.base_work
    (h.base_work_condition j) (h.moments j).1 (h.moments j).2 h.drift_pos h.drift_le
  rw [h.probability]
  exact hw.1

lemma parameters_recovery_work {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ σ0) (ha : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 1 ≤ L * R ^ 2 / ε) :
    let q := p / (p - 1)
    let M := 4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ q + 1 / δ
    let W := 2 + q + Real.log M
    let H := W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3)
    let d := depth L R ε δ σ0 p
    let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
    let κ := (2 * (L * R ^ 2 / ε)) ^ (1 / (d : ℝ)) + 1
    ∀ i, i < d → ((recoveryLevelTuning c i).calls : ℝ) ≤
      H * (Real.sqrt κ + (recoveryLevelTuning c i).accuracyScale + 1) := by
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let V := (σ0 * R / ε) ^ q
  let M := 4 + T + V + 1 / δ
  let W := 2 + q + Real.log M
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let d := depth L R ε δ σ0 p
  let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hV : 0 ≤ V := Real.rpow_nonneg (by positivity) _
  have hM : 4 ≤ M := by dsimp [M, T]; linarith [one_div_pos.mpr hδ]
  have hTM : T ≤ M := by dsimp [M]; linarith [one_div_pos.mpr hδ]
  have hW : 2 + q ≤ W := by dsimp [W]; linarith [Real.log_nonneg (by linarith : 1 ≤ M)]
  have hW4 : 4 ≤ W := by linarith
  have hd : 1 ≤ d := Nat.le_max_left _ _
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdW : (d : ℝ) ≤ W := chosen_depth_bound hR hε hs hδ hp hp2 hT
  have htune := parameters_accuracy_tuning hL hR hε hδ hs ha hp hp2 hT d hd hdW
  have hk : 1 < k := (geometric_depth_tuning hT d hd).1
  have hk0 : 0 < k := by linarith
  have hκ : 2 ≤ κ := by dsimp [κ]; linarith
  have hklog : Real.log κ ≤ W := (condition_log_bound hT hTM d hd).trans (by dsimp [W]; linarith)
  have hratio (j : ℕ) : (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1) = κ :=
    level_smoothness_ratio hL hk0 j
  have hA : 1024 ≤ A := by
    have hh : 1 ≤ (1 + q) ^ 3 := one_le_pow₀ (by linarith)
    dsimp [A]; norm_num; nlinarith
  have hH : 1 ≤ H := Real.one_le_rpow (by linarith) (by linarith)
  have hQd := depth_conjugates hq d hd d le_rfl
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  obtain ⟨hm, hms, hmu, hρ, hρ1⟩ := base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2
  change 1 ≤ m at hm
  change m ≤ 2 * Real.sqrt κ * H ^ (4 * q) at hmu
  change 0 < ρ at hρ
  change ρ ≤ 1 at hρ1
  have hHlog : Real.log H ≤ A * W := overhead_log_bound (by linarith) (by linarith)
  have hmlog := base_work_log_bound (by linarith : 0 < κ) (by linarith : 0 < H)
    hm hq (by linarith : 1 ≤ A) (by linarith : 1 ≤ W) hklog hHlog hmu
  have hδM : 1 / δ ≤ M := by dsimp [M, T]; linarith
  have hδlog : Real.log (1 / δ) ≤ W :=
    (Real.log_le_log (by positivity) hδM).trans (by dsimp [W]; linarith)
  have hη : 0 < c.recoveryFailure := by change 0 < δ / (4 * (d : ℝ)); positivity
  have hη1 : c.recoveryFailure ≤ 1 := by
    change δ / (4 * (d : ℝ)) ≤ 1
    apply (div_le_one (by positivity : 0 < 4 * (d : ℝ))).2
    linarith
  have hηlog : Real.log (1 / c.recoveryFailure) ≤ 3 * W :=
    recovery_confidence_log hδ hd' hW4 hdW hδlog
  have hσM : σ0 * R / ε ≤ M := by
    have hz := rpow_le_one_add_rpow (by positivity : 0 ≤ σ0 * R / ε) (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ q by linarith)
    rw [Real.rpow_one] at hz
    change σ0 * R / ε ≤ 1 + V at hz
    dsimp [M]
    linarith [one_div_pos.mpr hδ]
  dsimp only
  intro i hi
  let n := (recoveryLevelTuning c i).accuracyScale
  have hQi := depth_conjugates hq d hd i hi.le
  change 2 ≤ Q i ∧ Q i ≤ 2 * q at hQi
  have hconj : c.moment i / (c.moment i - 1) = Q i := (conjugate_moment_range hQi.1).2.2
  have hai : 0 < c.relative i := htune.relative_pos i
  have hai1 : c.relative i ≤ 1 := by
    have hh := htune.relative_small i
    rw [hratio] at hh
    exact hh.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
  have hsi : 0 ≤ c.additive i := htune.additive_nonneg i
  have hμ : 0 < c.smoothness (i + 1) := htune.smoothness_pos (i + 1)
  have hμlower : ε / (2 * R ^ 2) ≤ c.smoothness (i + 1) := by
    rw [← depth_smoothness_endpoint hL hR hε hT d hd]
    change L / k ^ d ≤ L / k ^ (i + 1)
    exact div_le_div_of_nonneg_left hL.le (pow_pos hk0 _) (pow_le_pow_right₀ hk.le (by omega))
  have hsiupper : c.additive i ≤ 4 * σ0 := by
    have hB : 1 ≤ (c.batchSize : ℝ) := by exact_mod_cast htune.batch_pos
    exact attenuated_additive_le hB hs (by linarith : 0 < q) hρ.le hρ1 i
  have harg := recovery_argument_bound hε hμ (by linarith : 0 < (d : ℝ)) (by linarith : 0 < κ)
    hR hμlower hsi hsiupper hai1 (by linarith : 1 ≤ M) hσM
  change (c.additive i / c.smoothness (i + 1) + c.relative i * c.recoveryRadius i) /
    c.recoveryDistance i ≤ 10 * M * Real.sqrt ((d : ℝ) * κ) at harg
  have hD : 0 < c.recoveryDistance i := Real.sqrt_pos.2 (by change 0 < ε / (2 * (d : ℝ) * c.smoothness (i + 1) * κ); positivity)
  have harg0 : 0 ≤ (c.additive i / c.smoothness (i + 1) + c.relative i * c.recoveryRadius i) /
      c.recoveryDistance i := by
    have hU : 0 ≤ c.recoveryRadius i := Real.sqrt_nonneg _
    positivity
  have hnid : n = 1 + ((c.additive i / c.smoothness (i + 1) + c.relative i * c.recoveryRadius i) /
      c.recoveryDistance i) ^ Q i := by
    dsimp [n, recoveryLevelTuning, recoveryTuning]
    rw [hconj]
  have hn : 1 ≤ n := by rw [hnid]; exact le_add_of_nonneg_right (Real.rpow_nonneg harg0 _)
  have hnupper : n ≤ 1 + (10 * M * Real.sqrt ((d : ℝ) * κ)) ^ Q i := by
    rw [hnid]
    exact add_le_add_right (Real.rpow_le_rpow harg0 harg (by linarith)) 1
  have hnlog := recovery_sample_log hn (by linarith : 1 ≤ M) hd' hκ hq
    (by linarith : 0 ≤ Q i) hQi.2 hW4 (by dsimp [W]; linarith) hklog hdW hnupper
  have hiW : (i : ℝ) ≤ W := (by exact_mod_cast hi.le : (i : ℝ) ≤ d).trans hdW
  have htlog := tuning_log_bound hκ hH hm (by linarith : 1 ≤ Q d) hq hA hW4 hklog hHlog hmlog i hiW
  have halog : Real.log (1 / c.relative i) ≤ 32 * q * A * W ^ 2 := by
    have h1 := Real.log_nonneg (show 1 ≤ 1025 * κ by linarith)
    have h2 := Real.log_nonneg hm
    change 1 + Real.log (1025 * κ) + Real.log (1 / c.relative i) + Real.log m ≤ _ at htlog
    linarith
  let X := 1 + Real.log n + Real.log (1 / c.relative i) + Real.log (1 / c.recoveryFailure)
  have hX : 0 ≤ X := by
    have h1 := Real.log_nonneg hn
    have h2 := Real.log_nonneg ((le_div_iff₀ hai).2 (by simpa using hai1) : 1 ≤ 1 / c.relative i)
    have h3 := Real.log_nonneg ((le_div_iff₀ hη).2 (by simpa using hη1) : 1 ≤ 1 / c.recoveryFailure)
    dsimp [X]; linarith
  have hXW : X ≤ 64 * q * A * W ^ 2 := recovery_total_log hq (by linarith) hW4 hnlog halog hηlog
  have hw := recovery_work_bound (κ := κ) hn hai hai1 hη hη1 (show 0 ≤ Q i by linarith)
  have hcost : ((recoveryLevelTuning c i).calls : ℝ) ≤
      128 * (268435456 : ℝ) ^ Q i * (Real.sqrt κ + n + 1) * X ^ 2 := by
    change ((recoveryTuning (c.smoothness i) (c.smoothness (i + 1)) (c.moment i)
      (c.additive i) (c.relative i) (c.recoveryRadius i) (c.recoveryDistance i) c.recoveryFailure).calls : ℝ) ≤ _
    unfold RecoveryTuning.calls recoveryTuning
    rw [hratio, hconj, ← hnid]
    exact hw
  refine hcost.trans ?_
  change _ ≤ H * (Real.sqrt κ + n + 1)
  rw [mul_comm H]
  exact recovery_work_domination hq (show 0 ≤ Q i by linarith)
    hQi.2 hW (show 0 ≤ Real.sqrt κ + n + 1 by positivity) hX hXW


lemma parameters_total_work {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ σ0) (ha : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 1 ≤ L * R ^ 2 / ε) :
    let q := p / (p - 1)
    let M := 4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ q + 1 / δ
    let W := 2 + q + Real.log M
    let H := W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3)
    let d := depth L R ε δ σ0 p
    let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
    let κ := (2 * (L * R ^ 2 / ε)) ^ (1 / (d : ℝ)) + 1
    let Q := q * (1 + 1 / (d : ℝ) ^ 2) ^ d
    let F := (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q
    Integrable (fun seed => (recoveryCalls c d seed : ℝ))
      (recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)) ∧
    (∫ seed, (recoveryCalls c d seed : ℝ)
      ∂(recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))) ≤
      2 * (d : ℝ) * H * F * ((c.batchSize : ℝ) * (c.baseWork * H) ^ d +
        (4 * σ0 * (R / ε)) ^ Q * H ^ ((1 + Q) * (d : ℝ))) := by
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let V := (σ0 * R / ε) ^ q
  let M := 4 + T + V + 1 / δ
  let W := 2 + q + Real.log M
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let d := depth L R ε δ σ0 p
  let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hV : 0 ≤ V := Real.rpow_nonneg (by positivity) _
  have hM : 4 ≤ M := by dsimp [M, T]; linarith [one_div_pos.mpr hδ]
  have hTM : T ≤ M := by dsimp [M]; linarith [one_div_pos.mpr hδ]
  have hW : 2 + q ≤ W := by dsimp [W]; linarith [Real.log_nonneg (by linarith : 1 ≤ M)]
  have hW4 : 4 ≤ W := by linarith
  have hd : 1 ≤ d := Nat.le_max_left _ _
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdW : (d : ℝ) ≤ W := chosen_depth_bound hR hε hs hδ hp hp2 hT
  have htune := parameters_accuracy_tuning hL hR hε hδ hs ha hp hp2 hT d hd hdW
  have hk : 1 < k := (geometric_depth_tuning hT d hd).1
  have hk0 : 0 < k := by linarith
  have hκ : 2 ≤ κ := by dsimp [κ]; linarith
  have hklog : Real.log κ ≤ W := (condition_log_bound hT hTM d hd).trans (by dsimp [W]; linarith)
  have hratio (j : ℕ) : (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1) = κ :=
    level_smoothness_ratio hL hk0 j
  have hA : 1024 ≤ A := by
    have hh : 1 ≤ (1 + q) ^ 3 := one_le_pow₀ (by linarith)
    dsimp [A]; norm_num; nlinarith
  have hH : 1 ≤ H := Real.one_le_rpow (by linarith) (by linarith)
  have hQd := depth_conjugates hq d hd d le_rfl
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  obtain ⟨hm, hms, hmu, hρ, hρ1⟩ := base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2
  change 1 ≤ m at hm
  change m ≤ 2 * Real.sqrt κ * H ^ (4 * q) at hmu
  change 0 < ρ at hρ
  change ρ ≤ 1 at hρ1
  let B := (c.batchSize : ℝ)
  let a := κ ^ (-2 : ℝ) / H
  let b := 2 * Real.sqrt ((d : ℝ) * κ)
  let F := (2 * b) ^ Q d
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ (c.batchSize : ℝ)
    exact_mod_cast (show 1 ≤ c.batchSize from htune.batch_pos)
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    have hh : κ ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    exact (div_le_one (by linarith : 0 < H)).2 (hh.trans hH)
  have hqQ : q ≤ Q d := by
    have hh : 1 ≤ (1 + t) ^ d := one_le_pow₀ (by dsimp [t]; linarith [sq_nonneg (d : ℝ), one_div_nonneg.mpr (sq_nonneg (d : ℝ))])
    dsimp [Q]; nlinarith
  have hn := accuracy_level_work_integrable htune
  have hlevels := parameters_level_work (σ := σ) hL hR hε hδ hs hp hp2 hT
  have hcounts := parameters_recovery_work hL hR hε hδ hδ1 hs ha hp hp2 hT
  have hmean : ∀ j < d, (∫ n, (levelCalls c j n : ℝ) ∂geometricMeasure c.levelProbability) ≤ m * H :=
    fun j hj => (hlevels j hj.le).2
  have harg (i : ℕ) (hi : i < d) : (recoveryLevelTuning c i).accuracyScale ≤
      1 + (b * (c.additive i * (R / ε) + c.relative i)) ^ Q i := by
    have hμ := htune.smoothness_pos (i + 1)
    have hμlower : ε / (2 * R ^ 2) ≤ c.smoothness (i + 1) := by
      rw [← depth_smoothness_endpoint hL hR hε hT d hd]
      change L / k ^ d ≤ L / k ^ (i + 1)
      exact div_le_div_of_nonneg_left hL.le (pow_pos hk0 _) (pow_le_pow_right₀ hk.le (by omega))
    have hh := recovery_normalized_argument (a := c.relative i) hε hμ (by linarith : 0 < (d : ℝ))
      (by linarith : 0 < κ) hR (htune.additive_nonneg i) hμlower
    have hQi := depth_conjugates hq d hd i hi.le
    have hconj : c.moment i / (c.moment i - 1) = Q i := (conjugate_moment_range hQi.1).2.2
    have harg0 : 0 ≤ (c.additive i / c.smoothness (i + 1) + c.relative i * c.recoveryRadius i) / c.recoveryDistance i := by
      have hsi : 0 ≤ c.additive i := htune.additive_nonneg i
      have hai : 0 ≤ c.relative i := (htune.relative_pos i).le
      have hmu0 : 0 ≤ c.smoothness (i + 1) := (htune.smoothness_pos (i + 1)).le
      have hU : 0 ≤ c.recoveryRadius i := Real.sqrt_nonneg _
      have hD : 0 ≤ c.recoveryDistance i := Real.sqrt_nonneg _
      positivity
    dsimp only [recoveryLevelTuning, recoveryTuning]
    rw [hconj]
    apply add_le_add_right
    exact Real.rpow_le_rpow harg0 hh (by dsimp [Q]; positivity)
  have hsum := recovery_sum_work (b := b) (κ := κ) hB hs (by positivity : 0 ≤ R / ε) hH hm
    (by linarith : 0 < q) hqQ (by linarith : 1 ≤ Q d) (by dsimp [b]; positivity)
    ha0 ha1 hρ1 Q d (fun i hi => ⟨by dsimp [Q]; positivity,
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by dsimp [t]; linarith [sq_nonneg (d : ℝ), one_div_nonneg.mpr (sq_nonneg (d : ℝ))]) hi.le) (by linarith)⟩)
  have hfd : Real.sqrt κ + 3 ≤ F := by
    dsimp [F, b]
    rw [show 2 * (2 * Real.sqrt ((d : ℝ) * κ)) = 4 * Real.sqrt ((d : ℝ) * κ) by ring]
    exact recovery_factor_domination hd' hκ hQd.1
  have hwork := recoveryCalls_integral_le c (m * H) hn d hmean
  have hbound : (∫ seed, (recoveryCalls c d seed : ℝ)
      ∂(recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))) ≤
      H * ((d : ℝ) * ((Real.sqrt κ + 3 + F) * (B * (m * H) ^ d) +
        F * ((4 * σ0 * (R / ε)) ^ Q d * (H ^ (1 + Q d)) ^ d))) := by
    refine hwork.trans ?_
    calc
      _ ≤ H * (∑ i ∈ Finset.range d, (B * (m * H) ^ i) *
          (Real.sqrt κ + (1 + (b * (c.additive i * (R / ε) + c.relative i)) ^ Q i) + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hic := hcounts i (Finset.mem_range.mp hi)
        have hia := harg i (Finset.mem_range.mp hi)
        calc
          _ ≤ (H * (Real.sqrt κ + (recoveryLevelTuning c i).accuracyScale + 1)) * B * (m * H) ^ i := by gcongr
          _ ≤ (H * (Real.sqrt κ + (1 + (b * (c.additive i * (R / ε) + c.relative i)) ^ Q i) + 1)) * B * (m * H) ^ i := by gcongr
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by linarith)
  dsimp only
  refine ⟨(recoveryCalls_integral c hn d).1, ?_⟩
  change _ ≤ 2 * (d : ℝ) * H * (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d *
    (B * (m * H) ^ d + (4 * σ0 * (R / ε)) ^ Q d * H ^ ((1 + Q d) * (d : ℝ)))
  have hFp : F = (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d := by dsimp [F, b]; congr 1; ring
  have hHp : (H ^ (1 + Q d)) ^ d = H ^ ((1 + Q d) * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ H)]
  rw [hHp, hFp] at hbound
  rw [hFp] at hfd
  have hX : 0 ≤ B * (m * H) ^ d := by positivity
  have hF0 : 0 ≤ (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d := by positivity
  have hY : 0 ≤ (4 * σ0 * (R / ε)) ^ Q d * H ^ ((1 + Q d) * (d : ℝ)) := by positivity
  refine hbound.trans ?_
  calc
    _ ≤ H * ((d : ℝ) * ((2 * (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d) * (B * (m * H) ^ d) +
      (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d * ((4 * σ0 * (R / ε)) ^ Q d * H ^ ((1 + Q d) * (d : ℝ))))) := by
      gcongr
      linarith
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ H) (by linarith : 0 ≤ (d : ℝ))) (mul_nonneg hF0 hY)]

lemma parameters_public_work {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ σ0) (ha : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 1 ≤ L * R ^ 2 / ε) :
    let q := p / (p - 1)
    let T := L * R ^ 2 / ε
    let V := (σ0 * R / ε) ^ q
    let M := 4 + T + V + 1 / δ
    let W := 2 + q + Real.log M
    let d := depth L R ε δ σ0 p
    let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
    Integrable (fun seed => (recoveryCalls c d seed : ℝ))
      (recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)) ∧
    4 * (∫ seed, (recoveryCalls c d seed : ℝ)
      ∂(recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))) ≤
      Real.exp ((2 : ℝ) ^ (32 : ℕ) * q ^ 4 * (1 + Real.sqrt (Real.log M)) * Real.log W) *
        ((1 + σ) ^ q * Real.sqrt T + 1 + V) := by
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let V := (σ0 * R / ε) ^ q
  let M := 4 + T + V + 1 / δ
  let W := 2 + q + Real.log M
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let d := depth L R ε δ σ0 p
  let c := parameters L R ε δ σ0 σ p d (Nat.le_max_left _ _)
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hV : 0 ≤ V := Real.rpow_nonneg (by positivity) _
  have hM : 4 ≤ M := by dsimp [M, T]; linarith [one_div_pos.mpr hδ]
  have hTM : T ≤ M := by dsimp [M]; linarith [one_div_pos.mpr hδ]
  have hW : 2 + q ≤ W := by dsimp [W]; linarith [Real.log_nonneg (by linarith : 1 ≤ M)]
  have hW4 : 4 ≤ W := by linarith
  have hd : 1 ≤ d := Nat.le_max_left _ _
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdW : (d : ℝ) ≤ W := chosen_depth_bound hR hε hs hδ hp hp2 hT
  have htune := parameters_accuracy_tuning hL hR hε hδ hs ha hp hp2 hT d hd hdW
  have hk : 1 < k := (geometric_depth_tuning hT d hd).1
  have hk0 : 0 < k := by linarith
  have hκ : 2 ≤ κ := by dsimp [κ]; linarith
  have hklog : Real.log κ ≤ W := (condition_log_bound hT hTM d hd).trans (by dsimp [W]; linarith)
  have hratio (j : ℕ) : (c.smoothness j + c.smoothness (j + 1)) / c.smoothness (j + 1) = κ :=
    level_smoothness_ratio hL hk0 j
  have hA : 1024 ≤ A := by
    have hh : 1 ≤ (1 + q) ^ 3 := one_le_pow₀ (by linarith)
    dsimp [A]; norm_num; nlinarith
  have hH : 1 ≤ H := Real.one_le_rpow (by linarith) (by linarith)
  have hQd := depth_conjugates hq d hd d le_rfl
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  obtain ⟨hm, hms, hmu, hρ, hρ1⟩ := base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2
  change 1 ≤ m at hm
  change m ≤ 2 * Real.sqrt κ * H ^ (4 * q) at hmu
  change 0 < ρ at hρ
  change ρ ≤ 1 at hρ1
  let S := Real.sqrt (Real.log M)
  let B := (c.batchSize : ℝ)
  let G := 2 * (d : ℝ) * H * (4 * Real.sqrt ((d : ℝ) * κ)) ^ Q d
  let D := (2 : ℝ) ^ (2 * (d : ℝ) + 2) * (4 : ℝ) ^ q * κ ^ (2 * q) * H ^ (q + (4 * q + 1) * (d : ℝ))
  let N := (4 : ℝ) ^ Q d * Real.exp (2 * S) * H ^ ((1 + Q d) * (d : ℝ))
  let E := Real.exp (32 * A * q * (1 + S) * Real.log W)
  have hdc := depth_choice hM hq
  have hdEq : d = ⌈Real.sqrt (Real.log M)⌉₊ := max_eq_right hdc.1
  have hdS : (d : ℝ) ≤ 1 + S := by rw [hdEq]; exact hdc.2.2.2
  have hlog : Real.log M / (d : ℝ) ≤ S := by rw [hdEq]; exact hdc.2.2.1
  have hkS : Real.log κ ≤ 2 + S := condition_depth_log hT hTM d hd hlog
  have hproducts := scalar_overhead_products hq (by linarith : 16 ≤ A) hW4
    (log_four_lower hW4) (Real.sqrt_nonneg _) hd' hdS hκ hkS hQd.1 hQd.2
  change 4 * G * D ≤ E ∧ 4 * G * N ≤ E at hproducts
  have hBu : B ≤ 2 * (4 * (1 + σ) * κ ^ 2 * H) ^ q :=
    (initial_batch_relative ha hκ hH (by linarith : 0 < q)).2.2
  have hκd : κ ^ d ≤ (2 : ℝ) ^ d * (2 * T) := (geometric_depth_tuning hT d hd).2.2
  have hdet := deterministic_work_bound (by linarith : 0 ≤ m) (by linarith : 0 < H)
    (by linarith : 0 ≤ κ) (by linarith : 0 ≤ T) ha d hκd hBu hmu
  have hpow : (2 : ℝ) ^ (2 * d + 2) = (2 : ℝ) ^ (2 * (d : ℝ) + 2) := by
    rw [← Real.rpow_natCast]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hpow] at hdet
  change B * (m * H) ^ d ≤ ((1 + σ) ^ q * Real.sqrt T) * D at hdet
  have he : Q d / q ≤ 1 + 2 / (d : ℝ) := by
    have hh : Q d / q = (1 + 1 / (d : ℝ) ^ 2) ^ d := by dsimp [Q, t]; field_simp
    rw [hh]; exact (depth_exponent_drift d hd).2
  have hVM : V ≤ M := by dsimp [M]; linarith [one_div_pos.mpr hδ]
  have hnoise := noise_exponent_overhead hV hVM (by positivity : 0 ≤ Q d / q) he
    (by linarith : 0 < (d : ℝ)) (Real.sqrt_nonneg _) hlog
  have hqp : q ≠ 0 := by linarith
  have hVpow : V ^ (Q d / q) = (σ0 * R / ε) ^ Q d := by
    dsimp [V]; rw [← Real.rpow_mul (by positivity : 0 ≤ σ0 * R / ε)]
    congr 1; field_simp
  rw [hVpow] at hnoise
  have hnoisework : (4 * σ0 * (R / ε)) ^ Q d * H ^ ((1 + Q d) * (d : ℝ)) ≤ (1 + V) * N := by
    rw [show 4 * σ0 * (R / ε) = 4 * (σ0 * R / ε) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
    calc
      _ ≤ (4 : ℝ) ^ Q d * ((1 + V) * Real.exp (2 * S)) * H ^ ((1 + Q d) * (d : ℝ)) := by gcongr
      _ = _ := by dsimp [N]; ring
  have hactual := parameters_total_work hL hR hε hδ hδ1 hs ha hp hp2 hT
  dsimp only
  refine ⟨hactual.1, ?_⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hx : 0 ≤ (1 + σ) ^ q * Real.sqrt T := by positivity
  have hy : 0 ≤ 1 + V := by positivity
  have hEbound : 4 * (∫ seed, (recoveryCalls c d seed : ℝ)
      ∂(recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))) ≤
      E * ((1 + σ) ^ q * Real.sqrt T + 1 + V) := by
    have hact := hactual.2
    change _ ≤ G * (B * (m * H) ^ d + (4 * σ0 * (R / ε)) ^ Q d * H ^ ((1 + Q d) * (d : ℝ))) at hact
    have hh1 := mul_le_mul_of_nonneg_left (add_le_add hdet hnoisework) hG
    have hh2 := mul_le_mul_of_nonneg_right hproducts.1 hx
    have hh3 := mul_le_mul_of_nonneg_right hproducts.2 hy
    nlinarith only [hact, hh1, hh2, hh3]
  refine hEbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (public_overhead_coefficient hq) (by positivity : 0 ≤ 1 + S))
    (Real.log_nonneg (by linarith : 1 ≤ W))

end LongTails.Proofs.StochasticEnvelopeBudget
