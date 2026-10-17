import LongTails.Setups.SmoothDriftStronglyConvex
import LongTails.Proofs.VelocityTrackingRun

open MeasureTheory

namespace OracleTemplate.VelocityTracking

open LongTails.Setups.SmoothDriftStronglyConvex

lemma tuned_facts {μ L σ ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε) :
    0 < μ * ε / (99 * σ ^ 2 + 2 * L * μ * ε) ∧
    μ * ε / (99 * σ ^ 2 + 2 * L * μ * ε) * L ≤ 1 / 2 ∧
    (μ * ε / (99 * σ ^ 2 + 2 * L * μ * ε) * μ)⁻¹ = 2 * L / μ + 99 * σ ^ 2 / (μ ^ 2 * ε) ∧
    (2 * L / μ + 99 * σ ^ 2 / (μ ^ 2 * ε)) * (μ * ε / (99 * σ ^ 2 + 2 * L * μ * ε)) ^ 2 * σ ^ 2 ≤
      ε / 99 ∧
    2 ≤ 2 * L / μ + 99 * σ ^ 2 / (μ ^ 2 * ε) := by
  have hL : 0 < L := hμ.trans_le hμL
  have hden : 0 < 99 * σ ^ 2 + 2 * L * μ * ε := by positivity
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_nonneg σ]
  · field_simp
    ring
  · have hQ : 2 * L / μ + 99 * σ ^ 2 / (μ ^ 2 * ε) =
        (99 * σ ^ 2 + 2 * L * μ * ε) / (μ ^ 2 * ε) := by
      field_simp
      ring
    rw [hQ]
    have : (99 * σ ^ 2 + 2 * L * μ * ε) / (μ ^ 2 * ε) * (μ * ε / (99 * σ ^ 2 + 2 * L * μ * ε)) ^ 2 *
        σ ^ 2 = ε * σ ^ 2 / (99 * σ ^ 2 + 2 * L * μ * ε) := by
      field_simp
    rw [this, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [mul_pos (mul_pos hL hμ) (mul_pos hε hε), sq_nonneg σ]
  · have h1 : 2 ≤ 2 * L / μ := by rw [le_div_iff₀ hμ]; linarith
    have h2 : 0 ≤ 99 * σ ^ 2 / (μ ^ 2 * ε) := by positivity
    linarith

lemma tuning_bound {γ μ Q σ Γ R V ε : ℝ} {K : ℕ} (hγ : 0 < γ) (hε : 0 < ε) (hQ : (γ * μ)⁻¹ = Q)
    (hQ2 : 2 ≤ Q)
    (hnoise : Q * γ ^ 2 * σ ^ 2 ≤ ε / 99) (hval : 9792 * Γ ^ 2 * Q ^ 4 ≤ ε)
    (hK : 16 * Q * Real.log (1 + (15 * R ^ 2 + 45 * V ^ 2 * Q ^ 2) / ε) ≤ K) :
    2 * ((1 - γ * μ / 16) ^ K * (5 / 2 * R ^ 2 + 15 / 2 * ((γ * μ)⁻¹ ^ 2 * V ^ 2)) +
      16 * (γ * μ)⁻¹ * (102 * Γ ^ 2 * (γ * μ)⁻¹ ^ 3 + γ ^ 2 * σ ^ 2)) + γ ^ 2 * σ ^ 2 ≤ ε := by
  have hQpos : 0 < Q := by linarith
  have hγμ : γ * μ = Q⁻¹ := by rw [← hQ, inv_inv]
  rw [hQ]
  have hnoise2 : γ ^ 2 * σ ^ 2 ≤ ε / 198 := by
    have := mul_le_mul_of_nonneg_right hQ2 (by positivity : (0 : ℝ) ≤ γ ^ 2 * σ ^ 2)
    nlinarith
  set M := 15 * R ^ 2 + 45 * V ^ 2 * Q ^ 2
  have hM : 0 ≤ M := by positivity
  have hQi : Q⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hQpos (by norm_num)]; linarith
  have hnn : 0 ≤ 1 - γ * μ / 16 := by rw [hγμ]; linarith
  have hρ : (1 - γ * μ / 16) ^ K ≤ ε / (ε + M) := by
    have hbase : 1 - γ * μ / 16 ≤ Real.exp (-(Q⁻¹ / 16)) := by
      rw [hγμ]
      linarith [Real.add_one_le_exp (-(Q⁻¹ / 16))]
    have hpow : (1 - γ * μ / 16) ^ K ≤ Real.exp (-(K * (Q⁻¹ / 16))) := by
      calc
        _ ≤ Real.exp (-(Q⁻¹ / 16)) ^ K := pow_le_pow_left₀ hnn hbase K
        _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
    have hlog : Real.log (1 + M / ε) ≤ K * (Q⁻¹ / 16) := by
      rw [show (K : ℝ) * (Q⁻¹ / 16) = K / (16 * Q) by field_simp, le_div_iff₀ (by positivity)]
      linarith
    have h2 : Real.exp (-Real.log (1 + M / ε)) = ε / (ε + M) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have h1 : Real.exp (-(K * (Q⁻¹ / 16))) ≤ Real.exp (-Real.log (1 + M / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hfrac : ε / (ε + M) * M ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : (1 - γ * μ / 16) ^ K * M ≤ ε / (ε + M) * M := mul_le_mul_of_nonneg_right hρ hM
  have hE : 5 / 2 * R ^ 2 + 15 / 2 * (Q ^ 2 * V ^ 2) = M / 6 := by simp only [M]; ring
  have hsplit : 2 * ((1 - γ * μ / 16) ^ K * (5 / 2 * R ^ 2 + 15 / 2 * (Q ^ 2 * V ^ 2)) +
      16 * Q * (102 * Γ ^ 2 * Q ^ 3 + γ ^ 2 * σ ^ 2)) + γ ^ 2 * σ ^ 2 =
      ((1 - γ * μ / 16) ^ K * M) / 3 + 3264 * Γ ^ 2 * Q ^ 4 + 32 * (Q * γ ^ 2 * σ ^ 2) +
        γ ^ 2 * σ ^ 2 := by
    rw [hE]
    ring
  rw [hsplit]
  linarith

lemma tuned_success (q : Params) (hq : spec.valid q) (N : ℕ)
    (hN : 16 * (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) *
      Real.log (1 + (15 * q.R ^ 2 + 45 * q.V ^ 2 *
        (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) ^ 2) / q.ε) + 1 ≤ N)
    (f : ℕ → q.E → ℝ) (O : Oracle q.E q.E) (h : spec.admissible q f O) :
    let γ := q.μ * q.ε / (99 * q.σ ^ 2 + 2 * q.L * q.μ * q.ε)
    let A := velocityTrackingSgd γ (γ * (γ * q.μ) / 4) q.x0
    spec.successful q f (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  intro γ A
  rcases hq with ⟨hμ, hμL, hσ, hΓ, hR, hV, hε, hval⟩
  rcases h with ⟨g, P, rfl, hor, hgr, hst, hlip, xstar, hmin, hx0, hv1, hdr⟩
  have H : Hyp f g (P : Measure q.Ω) xstar q.μ q.L q.σ q.Γ :=
    ⟨hμ, hμL, hor, hgr, hst, hlip, hmin, hdr⟩
  obtain ⟨hγ, hγL, hQ, hnoise, hQ2⟩ := tuned_facts (σ := q.σ) hμ hμL hε
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := by
    refine ⟨N - 1, ?_⟩
    have : (1 : ℝ) ≤ N := by
      have h0 : 0 ≤ 16 * (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) *
          Real.log (1 + (15 * q.R ^ 2 + 45 * q.V ^ 2 *
            (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) ^ 2) / q.ε) := by
        apply mul_nonneg (by positivity)
        apply Real.log_nonneg
        have : 0 ≤ (15 * q.R ^ 2 + 45 * q.V ^ 2 *
            (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) ^ 2) / q.ε := by positivity
        linarith
      linarith
    have : 1 ≤ N := by exact_mod_cast this
    omega
  have hK : 16 * (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) *
      Real.log (1 + (15 * q.R ^ 2 + 45 * q.V ^ 2 *
        (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) ^ 2) / q.ε) ≤ K := by
    push_cast at hN
    linarith
  have he := expected_error H hγ hγL q.x0 hx0 hv1 K
  have hb := tuning_bound hγ hε hQ hQ2 hnoise hval hK
  let output := fun ξ : ℕ → q.Ω =>
    (run g γ (γ * (γ * q.μ) / 4) 0 (K + 1) (q.x0, 0) (fun i : Fin (K + 1) => ξ i)).1
  have hexec : (fun seed : A.Seed × ((k : ℕ) → q.Ω) =>
      execute { Seed := fun _ => q.Ω
                law := ⟨Measure.infinitePi (fun _ : ℕ => (P : Measure q.Ω)), inferInstance⟩
                answer := fun k (_, x) seed => g k x seed } A (fun _ => K + 1) seed.1 seed.2) =
      fun seed => (output seed.2, K + 1) := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_vt P g γ _ q.x0 (K + 1) ξ
  refine ⟨xstar, hmin, ?_⟩
  rw [hexec]
  simp only [Nat.add_sub_cancel]
  refine ⟨(measurePreserving_snd (μ := Measure.dirac ())
    (ν := Measure.infinitePi (fun _ : ℕ => (P : Measure q.Ω)))).integrable_comp_of_integrable
      he.1, ?_⟩
  change (∫ seed : Unit × (ℕ → q.Ω), ‖output seed.2 - xstar K‖ ^ 2
    ∂(Measure.dirac ()).prod (Measure.infinitePi (fun _ : ℕ => (P : Measure q.Ω)))) ≤ q.ε
  rw [integral_fun_snd (fun ξ : ℕ → q.Ω => ‖output ξ - xstar K‖ ^ 2)]
  simpa using he.2.trans hb

end OracleTemplate.VelocityTracking
