import LongTails.Proofs.ComparisonTrustTuning
import LongTails.Proofs.Execution

namespace LongTails.Proofs.ComparisonTrustExecution

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion LongTails.Setups.ComparisonHessianLipschitz
  LongTails.Proofs.ComparisonTrustPlans LongTails.Proofs.ComparisonTrustTaylor
  LongTails.Proofs.ComparisonTrustGuess LongTails.Proofs.ComparisonTrustEpoch
  LongTails.Proofs.ComparisonTrustOuter LongTails.Proofs.ComparisonTrustBounds
  LongTails.Proofs.ComparisonTrustTuning

noncomputable section

def dirLen (t : Tuning) (n : ℕ) : ℕ := 1 * t.m * n + 1 * n + 1 * n

def guessLen (t : Tuning) (n : ℕ) : ℕ :=
  dirLen t n * (4 * t.N) + dirLen t n + dirLen t n * t.N

def epochLen (t : Tuning) (n : ℕ) : ℕ :=
  1 * (4 * t.J + 1) + guessLen t n * t.J + dirLen t n + 1 * t.mt + dirLen t n

lemma epochLen_le (t : Tuning) (n : ℕ) (hJ : 1 ≤ t.J) (hmt : t.mt = t.m) :
    epochLen t n ≤ (n + 1) * (t.m + 2) * t.J * (5 * t.N + 8) := by
  unfold epochLen guessLen dirLen
  rw [hmt]
  have hD : 1 * t.m * n + 1 * n + 1 * n ≤ (n + 1) * (t.m + 2) := by nlinarith
  generalize 1 * t.m * n + 1 * n + 1 * n = D at hD ⊢
  have hP2 : t.m + 2 ≤ (n + 1) * (t.m + 2) := Nat.le_mul_of_pos_left _ (by omega)
  generalize (n + 1) * (t.m + 2) = P at hD hP2 ⊢
  have h1 : (D * (4 * t.N) + D + D * t.N) * t.J ≤ P * t.J * (5 * t.N + 1) := by
    have e : (D * (4 * t.N) + D + D * t.N) * t.J = D * ((5 * t.N + 1) * t.J) := by ring
    have e' : P * t.J * (5 * t.N + 1) = P * ((5 * t.N + 1) * t.J) := by ring
    rw [e, e']
    exact Nat.mul_le_mul_right _ hD
  have h2 : P * t.J * (5 * t.N + 8) = P * t.J * (5 * t.N + 1) + 7 * (P * t.J) := by ring
  have h3 : P ≤ P * t.J := Nat.le_mul_of_pos_right P hJ
  have h4 : 2 * t.J ≤ P * t.J := Nat.mul_le_mul_right _ (by omega)
  rw [h2]
  linarith

noncomputable def bigX (p : Params) : ℝ :=
  250000 * (Module.finrank ℝ p.E + 1) * Real.sqrt (2 * p.L / Real.sqrt (p.ρ * p.ε) + 4) *
    Real.log (2 + Module.finrank ℝ p.E + p.L / Real.sqrt (p.ρ * p.ε) +
      Real.sqrt (2 * p.L * p.Δ) / p.ε) ^ 3

lemma epochLen_real (p : Params) (hp : spec.valid p) :
    (epochLen (tuning p) (Module.finrank ℝ p.E) : ℝ) ≤ bigX p := by
  have h := absOf_ok p hp
  set A := absOf p
  have hΛ := Abs.Λ_pos h
  have hΛ2 := Abs.Λ_ge h
  have hlog2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hΛ69 : (69 / 100 : ℝ) ≤ A.Λ := le_trans hlog2 hΛ2
  have hJ1 : 1 ≤ (tuning p).J := by show 1 ≤ _ + 1; omega
  have hle := epochLen_le (tuning p) (Module.finrank ℝ p.E) hJ1 rfl
  have hcast : (epochLen (tuning p) (Module.finrank ℝ p.E) : ℝ) ≤
      ((Module.finrank ℝ p.E : ℝ) + 1) * ((A.m : ℝ) + 2) * ((tuning p).J : ℝ) *
        (5 * (A.N : ℝ) + 8) := by exact_mod_cast hle
  refine hcast.trans ?_
  set κs := Real.sqrt (2 * p.L / Real.sqrt (p.ρ * p.ε) + 4)
  have hκs : 2 ≤ κs := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have h0 : 0 ≤ 2 * p.L / Real.sqrt (p.ρ * p.ε) :=
      div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h.hL.le) h.hγ.le
    linarith
  have hm : (A.m : ℝ) + 2 ≤ 130 * A.Λ := by
    unfold Abs.m
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 18 * A.Λ by positivity)
    linarith
  have hJ : ((tuning p).J : ℝ) ≤ 5 * A.Λ := by
    show ((⌈Real.logb 2 (A.G / A.ε)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * A.Λ
    push_cast
    have hlb : Real.logb 2 (A.G / A.ε) ≤ A.Λ / Real.log 2 := by
      rcases (div_nonneg h.hG h.hε.le).eq_or_lt with h0 | hpos
      · rw [← h0, Real.logb_zero]; positivity
      · rw [Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
        exact Real.log_le_log hpos (Abs.g_le h)
    have hc : (⌈Real.logb 2 (A.G / A.ε)⌉₊ : ℝ) ≤ A.Λ / Real.log 2 + 1 := by
      rcases le_or_gt (Real.logb 2 (A.G / A.ε)) 0 with hneg | hpos
      · rw [Nat.ceil_eq_zero.mpr hneg]; push_cast; positivity
      · have := Nat.ceil_lt_add_one hpos.le; linarith
    have h3 : A.Λ / Real.log 2 ≤ A.Λ / (69 / 100) := div_le_div_of_nonneg_left hΛ.le (by norm_num) hlog2
    have e : A.Λ / (69 / 100) = A.Λ * (100 / 69) := by ring
    linarith
  have hN : 5 * (A.N : ℝ) + 8 ≤ 341 * A.Λ * κs := by
    unfold Abs.N
    have harg : 0 ≤ Real.sqrt (2 * A.L / A.γ + 4) * (8 * A.Λ + 40) := by positivity
    have hceil := Nat.ceil_lt_add_one harg
    have hκ : Real.sqrt (2 * A.L / A.γ + 4) = κs := rfl
    rw [hκ] at hceil ⊢
    have h66 : 8 * A.Λ + 40 ≤ 66 * A.Λ := by linarith
    have e1 : κs * (8 * A.Λ + 40) ≤ κs * (66 * A.Λ) := mul_le_mul_of_nonneg_left h66 (by linarith)
    have e2 : 69 / 100 * 2 ≤ A.Λ * κs := mul_le_mul hΛ69 hκs (by norm_num) hΛ.le
    linarith
  have hn0 : (0 : ℝ) ≤ Module.finrank ℝ p.E := Nat.cast_nonneg _
  have hAm : (0 : ℝ) ≤ (A.m : ℝ) + 2 := by positivity
  have hJ0 : (0 : ℝ) ≤ (tuning p).J := Nat.cast_nonneg _
  calc ((Module.finrank ℝ p.E : ℝ) + 1) * ((A.m : ℝ) + 2) * ((tuning p).J : ℝ) * (5 * (A.N : ℝ) + 8)
      ≤ ((Module.finrank ℝ p.E : ℝ) + 1) * (130 * A.Λ) * (5 * A.Λ) * (341 * A.Λ * κs) := by
        gcongr
    _ ≤ bigX p := by
        unfold bigX
        show _ ≤ 250000 * ((Module.finrank ℝ p.E : ℝ) + 1) * κs * A.Λ ^ 3
        have : 0 ≤ ((Module.finrank ℝ p.E : ℝ) + 1) * κs * A.Λ ^ 3 := by positivity
        nlinarith

lemma T_spec (p : Params) (hp : spec.valid p) :
    p.Δ < (tuning p).T * ((absOf p).ε * (absOf p).r / 100) := by
  obtain ⟨hL, hρ, hΔ, hε⟩ := hp
  have hθ : (absOf p).ε * (absOf p).r / 100 = p.ε ^ (3 / 2 : ℝ) / (400 * Real.sqrt p.ρ) := by
    show p.ε * (Real.sqrt (p.ε / p.ρ) / 4) / 100 = _
    rw [Real.sqrt_div hε.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hε,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    field_simp
    ring
  rw [hθ]
  show p.Δ < ((⌊400 * p.Δ * Real.sqrt p.ρ / p.ε ^ (3 / 2 : ℝ)⌋₊ + 1 : ℕ) : ℝ) * _
  have hpos : 0 < p.ε ^ (3 / 2 : ℝ) / (400 * Real.sqrt p.ρ) := by
    have := Real.sqrt_pos.mpr hρ
    have := Real.rpow_pos_of_pos hε (3 / 2 : ℝ)
    positivity
  have hfl := Nat.lt_floor_add_one (400 * p.Δ * Real.sqrt p.ρ / p.ε ^ (3 / 2 : ℝ))
  push_cast
  have hq : 400 * p.Δ * Real.sqrt p.ρ / p.ε ^ (3 / 2 : ℝ) =
      p.Δ / (p.ε ^ (3 / 2 : ℝ) / (400 * Real.sqrt p.ρ)) := by
    field_simp
  rw [hq] at hfl ⊢
  have := (div_lt_iff₀ hpos).mp hfl
  linarith

lemma x0_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (t : Tuning) (k : ℕ) (x0 : E) : x0 ∈ (outerPure f t k x0).2 := by
  have key := loopPure_induction
    (fun _ st => (selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1,
      st.2 ++ selectPure f (epochCands f t st.1) (4 * t.J + 1) st.1 :: epochCands f t st.1))
    (fun _ st => x0 ∈ st.2) (x0, [x0]) (List.mem_singleton_self _)
    (fun _ st h => List.mem_append_left _ h) k
  exact key

end

end LongTails.Proofs.ComparisonTrustExecution
