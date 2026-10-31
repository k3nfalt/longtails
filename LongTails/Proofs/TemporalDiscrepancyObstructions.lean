import LongTails.Proofs.GdPL
import LongTails.Proofs.SgdExecution

noncomputable section

namespace OracleTemplate.TemporalDiscrepancy

def quadratic (μ center x : ℝ) : ℝ := μ / 2 * (x - center) ^ 2

def reservoir (D : ℝ) (N k : ℕ) : ℝ := (min k N : ℕ) * (D / N)

def maskedGradient (μ D sign : ℝ) (N k : ℕ) (x : ℝ) : ℝ :=
  μ * x - sign * (D / N) + sign * (reservoir D N (k + 1) - reservoir D N k)

lemma quadratic_gradient (μ center x : ℝ) :
    HasGradientAt (quadratic μ center) (μ * (x - center)) x := by
  have h := (((hasDerivAt_id x).sub_const center).pow 2).const_mul (μ / 2)
  have hd : HasDerivAt (quadratic μ center) (μ * (x - center)) x := by
    convert h using 1
    · rfl
    · simp
      ring
  simpa using hd.hasGradientAt

lemma quadratic_minimizer {μ : ℝ} (hμ : 0 ≤ μ) (center : ℝ) :
    IsMinOn (quadratic μ center) Set.univ center := by
  intro x _
  simp only [quadratic, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]
  change 0 ≤ μ / 2 * (x - center) ^ 2
  positivity

lemma reservoir_bounds {D : ℝ} (hD : 0 ≤ D) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 ≤ reservoir D N k ∧ reservoir D N k ≤ D := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : ((min k N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right k N
  constructor
  · unfold reservoir
    positivity
  · unfold reservoir
    calc
      (min k N : ℕ) * (D / N) ≤ (N : ℝ) * (D / N) :=
        mul_le_mul_of_nonneg_right hm (div_nonneg hD hn.le)
      _ = D := by field_simp

lemma reservoir_increment {N k : ℕ} (hk : k < N) (D : ℝ) :
    reservoir D N (k + 1) - reservoir D N k = D / N := by
  simp only [reservoir, min_eq_left (Nat.succ_le_of_lt hk),
    min_eq_left hk.le, Nat.cast_succ]
  ring

lemma maskedGradient_before {N k : ℕ} (hk : k < N) (μ D sign x : ℝ) :
    maskedGradient μ D sign N k x = μ * x := by
  unfold maskedGradient
  rw [reservoir_increment hk]
  ring

lemma adaptive_transcript {State : Type*} (update : State → ℝ → State)
    (query : State → ℝ) (μ D sign : ℝ) (N count start : ℕ) (h : start + count ≤ N)
    (s : State) :
    StochasticGradient.advance
      (fun k s => update s (maskedGradient μ D sign N k (query s))) count start s =
    StochasticGradient.advance (fun _ s => update s (μ * query s)) count start s := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [StochasticGradient.advance]
    rw [maskedGradient_before (by omega)]
    exact ih (start + 1) (by omega) _

lemma reservoir_sum (D : ℝ) (N start count : ℕ) :
    (∑ k ∈ Finset.range count,
      (reservoir D N (start + k + 1) - reservoir D N (start + k))) =
      reservoir D N (start + count) - reservoir D N start := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_assoc]
    ring

lemma reservoir_discrepancy {D : ℝ} (hD : 0 ≤ D) {N : ℕ} (hN : 0 < N)
    (start count : ℕ) :
    |∑ k ∈ Finset.range count,
      (reservoir D N (start + k + 1) - reservoir D N (start + k))| ≤ D := by
  rw [reservoir_sum, abs_le]
  obtain ⟨hs0, hsD⟩ := reservoir_bounds hD hN start
  obtain ⟨he0, heD⟩ := reservoir_bounds hD hN (start + count)
  constructor <;> linarith

lemma maskedGradient_discrepancy {μ D sign : ℝ} (hμ : μ ≠ 0)
    (hD : 0 ≤ D) (hsign : |sign| = 1) {N : ℕ} (hN : 0 < N)
    (query : ℕ → ℝ) (start count : ℕ) :
    |∑ k ∈ Finset.range count,
      (maskedGradient μ D sign N (start + k) (query (start + k)) -
        gradient (quadratic μ (sign * D / (μ * N))) (query (start + k)))| ≤ D := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he (k : ℕ) :
      maskedGradient μ D sign N k (query k) -
          gradient (quadratic μ (sign * D / (μ * N))) (query k) =
        sign * (reservoir D N (k + 1) - reservoir D N k) := by
    rw [(quadratic_gradient μ (sign * D / (μ * N)) (query k)).gradient]
    unfold maskedGradient
    field_simp
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, abs_mul, hsign, one_mul]
  exact reservoir_discrepancy hD hN start count

lemma quadratic_pair_lower {μ D : ℝ} (hμ : 0 < μ) (N : ℕ) (x : ℝ) :
    D ^ 2 / (2 * μ * (N : ℝ) ^ 2) ≤
      max (quadratic μ (D / (μ * N)) x) (quadratic μ (-(D / (μ * N))) x) := by
  by_cases hn : N = 0
  · subst N
    simp only [Nat.cast_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, div_zero,
      neg_zero, max_self, quadratic, sub_zero]
    positivity
  have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hn
  have ha := le_max_left (quadratic μ (D / (μ * N)) x)
    (quadratic μ (-(D / (μ * N))) x)
  have hb := le_max_right (quadratic μ (D / (μ * N)) x)
    (quadratic μ (-(D / (μ * N))) x)
  have hid : quadratic μ (D / (μ * N)) x + quadratic μ (-(D / (μ * N))) x =
      μ * x ^ 2 + 2 * (D ^ 2 / (2 * μ * (N : ℝ) ^ 2)) := by
    unfold quadratic
    field_simp
    ring
  have hx : 0 ≤ μ * x ^ 2 := mul_nonneg hμ.le (sq_nonneg x)
  linarith

lemma deterministic_oracle_lower {μ D : ℝ} (hμ : 0 < μ) (N : ℕ)
    (A : Algorithm ℝ ℝ ℝ) (seed : A.Seed) :
    let outPlus := (execute { answer := fun history (_, x) _ => maskedGradient μ D 1 N history.length x }
      A (fun _ => N) seed)
    let outMinus := (execute { answer := fun history (_, x) _ => maskedGradient μ D (-1) N history.length x }
      A (fun _ => N) seed)
    D ^ 2 / (2 * μ * (N : ℝ) ^ 2) ≤
      max (quadratic μ (D / (μ * N)) outPlus)
        (quadratic μ (-(D / (μ * N))) outMinus) := by
  dsimp only
  let Oplus : Oracle ℝ ℝ :=
    { Seed := fun _ => PUnit
      answer := fun history (_, x) _ => maskedGradient μ D 1 N history.length x }
  let Ominus : Oracle ℝ ℝ :=
    { Seed := fun _ => PUnit
      answer := fun history (_, x) _ => maskedGradient μ D (-1) N history.length x }
  change D ^ 2 / (2 * μ * (N : ℝ) ^ 2) ≤
    max
      (quadratic μ (D / (μ * N))
        (execute Oplus A (fun _ => N) seed (fun _ => PUnit.unit)))
      (quadratic μ (-(D / (μ * N)))
        (execute Ominus A (fun _ => N) seed (fun _ => PUnit.unit)))
  rw [StochasticGradient.execute_advance_of_answer Oplus A N seed (fun _ => PUnit.unit)
      (fun k q => maskedGradient μ D 1 N k q.2) (by intro history query; rfl),
    StochasticGradient.execute_advance_of_answer Ominus A N seed (fun _ => PUnit.unit)
      (fun k q => maskedGradient μ D (-1) N k q.2) (by intro history query; rfl)]
  rw [adaptive_transcript A.update (fun s => (A.query s).2) μ D 1 N N 0 (by omega),
    adaptive_transcript A.update (fun s => (A.query s).2) μ D (-1) N N 0 (by omega)]
  exact quadratic_pair_lower hμ N _

lemma randomized_oracle_lower {μ D ε : ℝ} (hμ : 0 < μ) (N : ℕ)
    (A : Algorithm ℝ ℝ ℝ) :
    let output := fun sign seed => (execute
      { answer := fun history (_, x) _ => maskedGradient μ D sign N history.length x } A (fun _ => N) seed)
    (∀ᵐ seed ∂(A.law : MeasureTheory.Measure A.Seed),
      quadratic μ (D / (μ * N)) (output 1 seed) ≤ ε) →
    (∀ᵐ seed ∂(A.law : MeasureTheory.Measure A.Seed),
      quadratic μ (-(D / (μ * N))) (output (-1) seed) ≤ ε) →
    D ^ 2 / (2 * μ * (N : ℝ) ^ 2) ≤ ε := by
  dsimp only
  intro hplus hminus
  obtain ⟨seed, hp, hm⟩ := (hplus.and hminus).exists
  exact (deterministic_oracle_lower hμ N A seed).trans (max_le hp hm)

lemma initialized_amplitude {μ D Δ : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (hΔ : 0 ≤ Δ) {N : ℕ} (hN : 0 < N) :
    let d := min D (Real.sqrt (2 * μ * Δ) * N)
    0 ≤ d ∧ d ≤ D ∧
      d ^ 2 / (2 * μ * (N : ℝ) ^ 2) = min Δ (D ^ 2 / (2 * μ * (N : ℝ) ^ 2)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 2 * μ * (N : ℝ) ^ 2 := by positivity
  have hs : 0 ≤ Real.sqrt (2 * μ * Δ) * N := by positivity
  have hsq : (Real.sqrt (2 * μ * Δ) * N) ^ 2 = (2 * μ * (N : ℝ) ^ 2) * Δ := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  refine ⟨le_min hD hs, min_le_left _ _, ?_⟩
  by_cases h : D ≤ Real.sqrt (2 * μ * Δ) * N
  · rw [min_eq_left h]
    have hb : D ^ 2 / (2 * μ * (N : ℝ) ^ 2) ≤ Δ := by
      apply (div_le_iff₀ hc).mpr
      have hsq' := (sq_le_sq₀ hD hs).mpr h
      nlinarith
    exact (min_eq_right hb).symm
  · have h' := le_of_not_ge h
    rw [min_eq_right h']
    have hb : Δ ≤ D ^ 2 / (2 * μ * (N : ℝ) ^ 2) := by
      apply (le_div_iff₀ hc).mpr
      have hsq' := (sq_le_sq₀ hs hD).mpr h'
      nlinarith
    rw [min_eq_left hb, hsq]
    field_simp

lemma initialized_pair_gap {μ D Δ : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (hΔ : 0 ≤ Δ) {N : ℕ} (hN : 0 < N) (sign : ℝ) (hsign : |sign| = 1) :
    let d := min D (Real.sqrt (2 * μ * Δ) * N)
    quadratic μ (sign * d / (μ * N)) 0 ≤ Δ := by
  obtain ⟨_, _, hd⟩ := initialized_amplitude hμ hD hΔ hN
  have hs : sign ^ 2 = 1 := by nlinarith [sq_abs sign]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi (d : ℝ) : quadratic μ (sign * d / (μ * N)) 0 =
      d ^ 2 / (2 * μ * (N : ℝ) ^ 2) := by
    unfold quadratic
    field_simp
    nlinarith [hs]
  dsimp only
  rw [hi, hd]
  exact min_le_left _ _

lemma initialized_discrepancy {μ D Δ sign : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (hΔ : 0 ≤ Δ) (hsign : |sign| = 1) {N : ℕ} (hN : 0 < N)
    (query : ℕ → ℝ) (start count : ℕ) :
    let d := min D (Real.sqrt (2 * μ * Δ) * N)
    |∑ k ∈ Finset.range count,
      (maskedGradient μ d sign N (start + k) (query (start + k)) -
        gradient (quadratic μ (sign * d / (μ * N))) (query (start + k)))| ≤ D := by
  obtain ⟨hd0, hdD, _⟩ := initialized_amplitude hμ hD hΔ hN
  exact (maskedGradient_discrepancy hμ.ne' hd0 hsign hN query start count).trans hdD

lemma initialized_randomized_lower {μ D Δ ε : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (hΔ : 0 ≤ Δ) {N : ℕ} (hN : 0 < N) (A : Algorithm ℝ ℝ ℝ) :
    let d := min D (Real.sqrt (2 * μ * Δ) * N)
    let output := fun sign seed => (execute
      { answer := fun history (_, x) _ => maskedGradient μ d sign N history.length x } A (fun _ => N) seed)
    (∀ᵐ seed ∂(A.law : MeasureTheory.Measure A.Seed),
      quadratic μ (d / (μ * N)) (output 1 seed) ≤ ε) →
    (∀ᵐ seed ∂(A.law : MeasureTheory.Measure A.Seed),
      quadratic μ (-(d / (μ * N))) (output (-1) seed) ≤ ε) →
    min Δ (D ^ 2 / (2 * μ * (N : ℝ) ^ 2)) ≤ ε := by
  dsimp only
  intro hp hm
  have h := randomized_oracle_lower hμ N A hp hm
  rw [(initialized_amplitude hμ hD hΔ hN).2.2] at h
  exact h

lemma alternating_step {μ η D : ℝ} (hden : 2 - η * μ ≠ 0) (k : ℕ) :
    let a := η * D / (2 - η * μ)
    (-1 : ℝ) ^ k * a - η * (μ * ((-1 : ℝ) ^ k * a) + (-1 : ℝ) ^ k * D) =
      (-1 : ℝ) ^ (k + 1) * a := by
  dsimp
  rw [pow_succ]
  field_simp
  ring

lemma alternating_gap (μ a : ℝ) (k : ℕ) :
    quadratic μ 0 ((-1 : ℝ) ^ k * a) = μ / 2 * a ^ 2 := by
  unfold quadratic
  simp [mul_pow, ← pow_mul, mul_comm k 2]

lemma alternating_sum (D : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * D) = (1 - (-1 : ℝ) ^ N) * D / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma alternating_discrepancy {D : ℝ} (hD : 0 ≤ D) (N : ℕ) :
    |∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * D| ≤ D := by
  rw [alternating_sum]
  have hpow : |(-1 : ℝ) ^ N| = 1 := by simp [abs_pow]
  have hh := (abs_le.mp (le_of_eq hpow))
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hh.1 hD,
    mul_le_mul_of_nonneg_right hh.2 hD]

end OracleTemplate.TemporalDiscrepancy
