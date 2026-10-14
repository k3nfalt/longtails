import LongTails.Algorithms.NonlinearTemporalAccelerated
import LongTails.Proofs.NonlinearTemporalParameters

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

lemma condition_root_bounds (p : Params) (hp : spec.valid p) :
    1 ≤ Real.sqrt (p.L / p.μ) ∧ (Real.sqrt (p.L / p.μ)) ^ 2 * p.μ = p.L := by
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  have hL : 0 < p.L := hμ.trans_le hμL
  have hs := Real.sq_sqrt (div_nonneg hL.le hμ.le)
  have hr : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  refine ⟨?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (p.L / p.μ)]
  · rw [hs, div_mul_cancel₀ _ hμ.ne']

lemma momentum_valid (p : Params) (hp : spec.valid p) :
    (0 < warmupMomentum p ∧ warmupMomentum p ≤ 1 ∧
      warmupMomentum p ^ 2 * p.L ≤ p.μ) ∧
    (0 < finalMomentum p ∧ finalMomentum p ≤ 1 ∧ finalMomentum p ^ 2 * p.L ≤ p.μ) := by
  obtain ⟨hκ, hκ2⟩ := condition_root_bounds p hp
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  have hκpos : 0 < Real.sqrt (p.L / p.μ) := by linarith
  have hL : 0 < p.L := hμ.trans_le hμL
  obtain ⟨ht, ht1, htκ, hta, htb⟩ := reciprocal_momentum_bounds hκ
    (show 0 ≤ p.M * p.D / p.μ ^ 2 by positivity)
    (show 0 ≤ p.D / Real.sqrt (p.μ * p.ε) by positivity)
  have hw : 0 < warmupMomentum p := by unfold warmupMomentum; positivity
  have hw1 : warmupMomentum p ≤ 1 := by
    unfold warmupMomentum
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hwκ : warmupMomentum p * Real.sqrt (p.L / p.μ) = 1 / 2 := by
    unfold warmupMomentum
    field_simp
  have hs (θ : ℝ) (hθ : 0 ≤ θ) (hh : θ * Real.sqrt (p.L / p.μ) ≤ 1) :
      θ ^ 2 * p.L ≤ p.μ := by
    have hpow := pow_le_pow_left₀ (mul_nonneg hθ hκpos.le) hh 2
    have hmul := mul_le_mul_of_nonneg_right hpow hμ.le
    rw [← hκ2]
    nlinarith
  exact ⟨⟨hw, hw1, hs _ hw.le (by rw [hwκ]; norm_num)⟩,
    ⟨ht, ht1, hs _ ht.le htκ⟩⟩

lemma warmup_batch_positive (p : Params) (hp : spec.valid p) : 0 < warmupBatch p := by
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  apply Nat.ceil_pos.mpr
  positivity

lemma final_noise_tuning (p : Params) (hp : spec.valid p) (hgap : p.ε < p.Δ) :
    p.M * (33 * finalMomentum p * (2 * p.D) / p.μ) ≤ p.μ / 32 ∧
      Real.sqrt p.μ * (33 * finalMomentum p * (2 * p.D) / p.μ) ≤ Real.sqrt p.ε / 8 ∧
      0 < finalLength p ∧
      2 * (finalMomentum p * Real.sqrt (2 / p.μ)) * (2 * p.D) /
        ((1 - Real.sqrt (1 - finalMomentum p)) * finalLength p) ≤ Real.sqrt p.ε / 8 := by
  obtain ⟨hκ, hκ2⟩ := condition_root_bounds p hp
  obtain ⟨_, ht, ht1, hstep⟩ := momentum_valid p hp
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  obtain ⟨_, _, _, hta, htb⟩ := reciprocal_momentum_bounds hκ
    (show 0 ≤ p.M * p.D / p.μ ^ 2 by positivity)
    (show 0 ≤ p.D / Real.sqrt (p.μ * p.ε) by positivity)
  change finalMomentum p * (p.M * p.D / p.μ ^ 2) ≤ 1 / 4096 at hta
  change finalMomentum p * (p.D / Real.sqrt (p.μ * p.ε)) ≤ 1 / 4096 at htb
  have hχ : 0 < Real.sqrt p.μ := Real.sqrt_pos.mpr hμ
  have hψ : 0 < Real.sqrt p.ε := Real.sqrt_pos.mpr hε
  have hχ2 := Real.sq_sqrt hμ.le
  have hid : p.M * (33 * finalMomentum p * (2 * p.D) / p.μ) =
      66 * p.μ * (finalMomentum p * (p.M * p.D / p.μ ^ 2)) := by field_simp; ring
  have hid' : Real.sqrt p.μ * (33 * finalMomentum p * (2 * p.D) / p.μ) =
      66 * Real.sqrt p.ε * (finalMomentum p * (p.D / Real.sqrt (p.μ * p.ε))) := by
    rw [Real.sqrt_mul hμ.le]
    field_simp
    nlinarith
  have hbM : p.M * (33 * finalMomentum p * (2 * p.D) / p.μ) ≤ p.μ / 32 := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hta (show 0 ≤ 66 * p.μ by positivity)
    linarith
  have hbε : Real.sqrt p.μ * (33 * finalMomentum p * (2 * p.D) / p.μ) ≤ Real.sqrt p.ε / 8 := by
    rw [hid']
    have hh := mul_le_mul_of_nonneg_left htb (show 0 ≤ 66 * Real.sqrt p.ε by positivity)
    linarith
  have hr : 1 ≤ p.Δ / p.ε := (le_div_iff₀ hε).mpr (by linarith)
  obtain ⟨hn, hnθ, hdecay⟩ := tail_length_decay ht ht1 hr
  change 0 < finalLength p at hn
  change 1 / finalMomentum p ≤ (finalLength p : ℝ) at hnθ
  refine ⟨hbM, hbε, hn, ?_⟩
  have hρ0 : 0 ≤ Real.sqrt (1 - finalMomentum p) := Real.sqrt_nonneg _
  have hρ1 : Real.sqrt (1 - finalMomentum p) < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  have hθρ : finalMomentum p = 1 - Real.sqrt (1 - finalMomentum p) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hh := averaged_noise_constant hχ ht hρ0 hρ1 hθρ (show 0 ≤ 2 * p.D by positivity)
    (finalLength p) hn hnθ
  have hβ : finalMomentum p * Real.sqrt 2 / Real.sqrt p.μ =
      finalMomentum p * Real.sqrt (2 / p.μ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [hβ] at hh
  have he : 8 * finalMomentum p * (2 * p.D) / Real.sqrt p.μ =
      16 * Real.sqrt p.ε * (finalMomentum p * (p.D / Real.sqrt (p.μ * p.ε))) := by
    rw [Real.sqrt_mul hμ.le]; field_simp; ring
  have hl := mul_le_mul_of_nonneg_left htb (show 0 ≤ 16 * Real.sqrt p.ε by positivity)
  rw [he] at hh
  linarith

lemma final_transient_tuning (p : Params) (hp : spec.valid p) (hgap : p.ε < p.Δ)
    {P : ℝ} (hP2 : P ^ 2 ≤ 6 * p.Δ) :
    P * ((1 + Real.sqrt (1 - finalMomentum p)) / 2) ^ finalLength p ≤ Real.sqrt p.ε / 8 := by
  obtain ⟨_, ht, ht1, _⟩ := momentum_valid p hp
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  have hr : 1 ≤ p.Δ / p.ε := (le_div_iff₀ hε).mpr (by linarith)
  have hdecay := (tail_length_decay ht ht1 hr).2.2
  apply tail_transient_bound hr hε.le ?_ (by positivity) hdecay
  convert hP2 using 1; field_simp

end OracleTemplate.NonlinearTemporalDiscrepancy
