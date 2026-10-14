import LongTails.Proofs.QuasarSimilarity
import LongTails.Proofs.GdPL

namespace OracleTemplate.SimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma inner_energy_sharp {n : ℕ} [NeZero n] {f : E → ℝ} {g : Fin n × E → E}
    {μ γ θ ν : ℝ} {u : E} (hrt : γ * θ ≤ 1)
    (anchor : E × E)
    (hstep : ∀ s, energy f μ u
      (update γ θ μ s (FiniteSum.estimator g anchor.1 (query θ s) 0)) ≤
        (1 - γ * θ / 2) * energy f μ u s + γ * θ / 2 * ν * energy f μ u anchor)
    (k : ℕ) (s : E × E) :
    energy f μ u (innerRun g γ θ μ anchor.1 k s) ≤
      (1 - γ * θ / 2) ^ k * energy f μ u s +
        (1 - (1 - γ * θ / 2) ^ k) * ν * energy f μ u anchor := by
  have hq : 0 ≤ 1 - γ * θ / 2 := by linarith
  induction k generalizing s with
  | zero => simp [innerRun]
  | succ k ih =>
    rw [innerRun]
    have hb := ih (update γ θ μ s (FiniteSum.estimator g anchor.1 (query θ s) 0))
    have hs := mul_le_mul_of_nonneg_left (hstep s) (pow_nonneg hq k)
    rw [pow_succ]
    nlinarith

omit [CompleteSpace E] in
lemma epoch_energy {n : ℕ} [NeZero n] {f : E → ℝ} {g : Fin n × E → E}
    {μ γ θ ν r : ℝ} {u : E} (hrt : γ * θ ≤ 1) (hν : 0 ≤ ν) (hνr : ν ≤ r)
    {m : ℕ} (hm : (1 - γ * θ / 2) ^ m ≤ r)
    (anchor : E × E) (hC : 0 ≤ energy f μ u anchor)
    (hstep : ∀ s, energy f μ u
      (update γ θ μ s (FiniteSum.estimator g anchor.1 (query θ s) 0)) ≤
        (1 - γ * θ / 2) * energy f μ u s + γ * θ / 2 * ν * energy f μ u anchor) :
    energy f μ u (epoch g γ θ μ m anchor) ≤ 2 * r * energy f μ u anchor := by
  have hb := inner_energy_sharp hrt anchor hstep m anchor
  have hp := mul_le_mul_of_nonneg_right hm hC
  have hn := mul_nonneg (pow_nonneg (show 0 ≤ 1 - γ * θ / 2 by linarith) m)
    (mul_nonneg hν hC)
  have hv := mul_le_mul_of_nonneg_right hνr hC
  change energy f μ u (innerRun g γ θ μ anchor.1 m anchor) ≤ _
  nlinarith

omit [CompleteSpace E] in
lemma run_energy {n : ℕ} [NeZero n] {f : E → ℝ} {g : Fin n × E → E}
    {μ γ θ q : ℝ} {u : E} {m : ℕ} (hq : 0 ≤ q)
    (hepoch : ∀ s, energy f μ u (epoch g γ θ μ m s) ≤ q * energy f μ u s)
    (S : ℕ) (s : E × E) :
    energy f μ u (run g γ θ μ m S s) ≤ q ^ S * energy f μ u s := by
  induction S generalizing s with
  | zero => simp [run]
  | succ S ih =>
    rw [run]
    have hb := ih (epoch g γ θ μ m s)
    have he := mul_le_mul_of_nonneg_left (hepoch s) (pow_nonneg hq S)
    rw [pow_succ]
    nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma initial_energy {f : E → ℝ} {μ γ Δ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x u : E) (hgap : f x - f u ≤ Δ)
    (hqg : γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u) :
    energy f μ u (x, x) ≤ 2 * Δ / γ := by
  have hd : 0 < 2 * (2 - γ) := by linarith
  have h := mul_le_mul_of_nonneg_left hqg hd.le
  have hid : 2 * (2 - γ) * (γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2) =
      γ * μ * ‖x - u‖ ^ 2 := by field_simp [ne_of_gt (show 0 < 2 - γ by linarith)]
  rw [hid] at h
  apply (le_div_iff₀ hγ).mpr
  dsimp [energy]
  nlinarith

lemma logarithmic_budget {q B ε : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    let S := ⌈Real.log (1 + B / ε) / Real.log (1 / q)⌉₊
    q ^ S * B ≤ ε := by
  let S := ⌈Real.log (1 + B / ε) / Real.log (1 / q)⌉₊
  have hlog : 0 < Real.log (1 / q) := Real.log_pos ((one_lt_div hq).mpr hq1)
  have hc : Real.log (1 + B / ε) / Real.log (1 / q) ≤ (S : ℝ) := Nat.le_ceil _
  have hm := (div_le_iff₀ hlog).mp hc
  have hi : Real.log (1 / q) = -Real.log q := by simp
  rw [hi] at hm
  have hp : q ^ S = Real.exp ((S : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq]
  have ht : 0 < 1 + B / ε := by positivity
  have he : Real.exp ((S : ℝ) * Real.log q) ≤ Real.exp (-Real.log (1 + B / ε)) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [Real.exp_neg, Real.exp_log ht] at he
  have hl : (1 + B / ε)⁻¹ * B ≤ ε := by
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ ht).mpr
    have hid : ε * (1 + B / ε) = ε + B := by field_simp
    rw [hid]
    linarith
  change q ^ S * B ≤ ε
  rw [hp]
  exact (mul_le_mul_of_nonneg_right he hB).trans hl

lemma zero_discrepancy_refresh_count {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    let r := ε / (16 * (ε + B))
    ⌈Real.log (1 + B / ε) / Real.log (1 / (2 * r))⌉₊ = 1 := by
  have ht : 1 < 1 + B / ε := by linarith [div_pos hB hε]
  have hid : 1 / (2 * (ε / (16 * (ε + B)))) = 8 * (1 + B / ε) := by
    field_simp
    ring
  dsimp only
  rw [hid]
  have hl : 0 < Real.log (1 + B / ε) := Real.log_pos ht
  have hle : Real.log (1 + B / ε) ≤ Real.log (8 * (1 + B / ε)) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hd : 0 < Real.log (8 * (1 + B / ε)) := hl.trans_le hle
  apply (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
  norm_num only [Nat.sub_self, Nat.cast_zero, Nat.cast_one]
  exact ⟨div_pos hl hd, (div_le_one hd).mpr hle⟩

lemma tuning_bounds {μ γ L δ Δ ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hsmall : 384 * δ ^ 2 ≤ γ ^ 3 * μ ^ 2)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let θ := Real.sqrt (μ / L)
    let B := 2 * Δ / γ
    let ν := 48 * δ ^ 2 / (γ ^ 3 * μ ^ 2)
    let r := ν + ε / (16 * (ε + B))
    let m := ⌈(2 / (γ * θ)) * Real.log (1 + 1 / r)⌉₊
    let S := ⌈Real.log (1 + B / ε) / Real.log (1 / (2 * r))⌉₊
    0 < θ ∧ γ * θ ≤ 1 ∧ θ ^ 2 * L ≤ μ ∧ 0 ≤ ν ∧ ν ≤ r ∧
      0 < r ∧ 2 * r < 1 ∧ (1 - γ * θ / 2) ^ m ≤ r ∧ (2 * r) ^ S * B ≤ ε := by
  let θ := Real.sqrt (μ / L)
  let B := 2 * Δ / γ
  let ν := 48 * δ ^ 2 / (γ ^ 3 * μ ^ 2)
  let r := ν + ε / (16 * (ε + B))
  have hL : 0 < L := hμ.trans_le hμL
  have hθ : 0 < θ := Real.sqrt_pos.mpr (div_pos hμ hL)
  have hθ1 : θ ≤ 1 := (Real.sqrt_le_one).mpr ((div_le_one hL).mpr hμL)
  have hθsq : θ ^ 2 = μ / L := Real.sq_sqrt (by positivity)
  have hrt : γ * θ ≤ 1 := by nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν8 : ν ≤ 1 / 8 := by
    apply (div_le_iff₀ (show 0 < γ ^ 3 * μ ^ 2 by positivity)).mpr
    linarith
  have he0 : 0 < ε / (16 * (ε + B)) := by positivity
  have he1 : ε / (16 * (ε + B)) ≤ 1 / 16 := by
    apply (div_le_iff₀ (show 0 < 16 * (ε + B) by positivity)).mpr
    linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : 2 * r < 1 := by dsimp [r]; linarith
  refine ⟨hθ, hrt, ?_, hν, ?_, hr, hr1, ?_, ?_⟩
  · rw [hθsq, div_mul_cancel₀ _ hL.ne']
  · change ν ≤ r
    dsimp [r]
    linarith
  · have hb := PLGradient.geometric_budget 1 (γ * θ / 2) 1 r
      (by positivity) (by linarith) (by norm_num) hr
    have hid : 1 / (γ * θ / 2) = 2 / (γ * θ) := by ring
    simpa only [div_one, hid, mul_one] using hb
  · exact logarithmic_budget (by positivity) hr1 hB hε

end OracleTemplate.SimilarQuasar
