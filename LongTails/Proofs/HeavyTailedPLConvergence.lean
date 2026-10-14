import LongTails.Setups.HeavyTailedPL
import LongTails.Proofs.HeavyTailedPLEvents
import LongTails.Proofs.HeavyTailedPLTuning
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.FixedBatchConfidenceProbability
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar OracleTemplate.TerminalClipping

namespace OracleTemplate.HeavyTailedPL

open LongTails.Setups.HeavyTailedPL

lemma burn_in_rho {K c T q : ℝ} (hK : 0 < K) (hc : 0 < c) (hT : 0 < T) (hq : 2 < q)
    (h : (K ^ q * c ^ 2) ^ (1 / (q - 2)) ≤ T) : K * (c * T) ^ (2 / q) ≤ T := by
  have hq2 : 0 < q - 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hx : 0 ≤ K ^ q * c ^ 2 := by positivity
  have h1 : K ^ q * c ^ 2 ≤ T ^ (q - 2) := by
    have := Real.rpow_le_rpow (by positivity) h hq2.le
    rwa [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ hq2.ne', Real.rpow_one] at this
  have h2 : K ^ q * (c * T) ^ (2 : ℝ) ≤ T ^ q := by
    have e1 : T ^ q = T ^ (q - 2) * T ^ (2 : ℝ) := by
      rw [← Real.rpow_add hT]; ring_nf
    have e2 : (c * T) ^ (2 : ℝ) = c ^ 2 * T ^ (2 : ℝ) := by
      rw [Real.mul_rpow hc.le hT.le]; norm_cast
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hT.le (2 : ℝ))
    nlinarith
  have h3 := Real.rpow_le_rpow (by positivity) h2 (show 0 ≤ 1 / q by positivity)
  have hr : (T ^ q) ^ (1 / q) = T := by
    rw [← Real.rpow_mul hT.le, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have hl : (K ^ q * (c * T) ^ (2 : ℝ)) ^ (1 / q) = K * (c * T) ^ (2 / q) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK.le,
      mul_one_div_cancel hq0.ne', Real.rpow_one, ← Real.rpow_mul (by positivity), mul_one_div]
  rw [hr, hl] at h3
  exact h3

lemma truncation_power {ν T δ q : ℝ} (hν : 0 < ν) (hT : 0 < T) (hδ : 0 < δ) (hq : 0 < q) :
    (ν * (3 * T / δ) ^ (1 / q)) ^ q = ν ^ q * (3 * T / δ) := by
  rw [Real.mul_rpow hν.le (by positivity), ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hq.ne', Real.rpow_one]

lemma truncation_sq {ν T δ q : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (ν * (3 * T / δ) ^ (1 / q)) ^ 2 = ν ^ 2 * (3 * T / δ) ^ (2 / q) := by
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma one_le_log_three_div {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 1 ≤ Real.log (3 / δ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have h3 : (3 : ℝ) ≤ 3 / δ := by rw [le_div_iff₀ hδ]; linarith
  linarith

lemma plainStep_time {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (μ : ℝ) (t0 : ℕ) (n : ℕ) (s : ℕ × E) (ξ : Fin n → Ω) :
    (iterateSamples (plainStep g μ t0) n s ξ).1 = s.1 + n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change (iterateSamples (plainStep g μ t0) n (plainStep g μ t0 s (ξ 0)) _).1 = _
    rw [ih]; simp [plainStep]; ring

lemma advance_plain {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (μ : ℝ) (t0 : ℕ) (ξ : ℕ → Ω) (K c : ℕ) (st : ℕ × E) :
    StochasticGradient.advance (fun k (state : ℕ × E) =>
        (state.1 + 1, state.2 - stepSize μ t0 state.1 • g state.2 (ξ k))) K c st =
      iterateSamples (plainStep g μ t0) K st (fun i => ξ (c + i)) := by
  induction K generalizing c st with
  | zero => rfl
  | succ K ih =>
    change StochasticGradient.advance _ K (c + 1) (plainStep g μ t0 st (ξ c)) =
      iterateSamples (plainStep g μ t0) K (plainStep g μ t0 st (ξ (c + ((0 : Fin (K + 1)) : ℕ))))
        (fun i => ξ (c + (i.succ : ℕ)))
    rw [ih]
    have hf : (fun i : Fin K => ξ (c + 1 + (i : ℕ))) = fun i : Fin K => ξ (c + ((i.succ : Fin (K + 1)) : ℕ)) := by
      funext i; congr 1; simp [Fin.val_succ]; ring
    rw [hf]
    rfl

lemma execute_plain {Ω E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (μ : ℝ) (t0 : ℕ) (x0 : E) (T : ℕ) [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    execute ({ Seed := fun _ => Ω
               law := P
               answer := fun _ (_, x) seed => g x seed } : Oracle E E)
      (ScheduledSgd.method (stepSize μ t0) x0) (fun _ => T) () ξ =
      (iterateSamples (plainStep g μ t0) T (0, x0) (fun i => ξ i)).2 := by
  erw [StochasticGradient.execute_advance]
  have h := advance_plain g μ t0 ξ T 0 (0, x0)
  simp only [Nat.zero_add] at h
  exact congrArg Prod.snd h

noncomputable def offset (L μ : ℝ) : ℕ := ⌈8 * L / μ⌉₊ + 2

lemma offset_bounds {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    8 * L / μ ≤ offset L μ ∧ (offset L μ : ℝ) ≤ 11 * (L / μ) ∧ 3 ≤ offset L μ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr hμL
  have h8 : 8 * L / μ = 8 * (L / μ) := by ring
  have h0 : 0 ≤ 8 * L / μ := by positivity
  have hc1 := Nat.le_ceil (8 * L / μ)
  have hc2 := Nat.ceil_lt_add_one h0
  have hoff : (offset L μ : ℝ) = (⌈8 * L / μ⌉₊ : ℝ) + 2 := by simp [offset]
  refine ⟨?_, ?_, ?_⟩
  · rw [hoff]; linarith
  · rw [hoff]; linarith
  · have h8r : (8 : ℝ) ≤ ⌈8 * L / μ⌉₊ := by linarith
    have : 8 ≤ ⌈8 * L / μ⌉₊ := by exact_mod_cast h8r
    simp only [offset]; omega

section Assembly

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma finite_accuracy (f : E → ℝ) (g : E → Ω → E) (P0 : ProbabilityMeasure Ω)
    {L μ σ ν q Δ ε δ : ℝ} (x0 : E) (T : ℕ)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hσ : 0 < σ) (hν : 0 < ν) (hq : 2 < q) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hT : 1 ≤ T)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbdd : BddBelow (Set.range f))
    (hpl : ∀ x, 2 * μ * (f x - ⨅ y, f y) ≤ ‖gradient f x‖ ^ 2)
    (hx0 : f x0 - (⨅ y, f y) ≤ Δ)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) (P0 : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(P0 : Measure Ω) = gradient f x)
    (h2i : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure Ω))
    (hvar : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure Ω) ≤ σ ^ 2)
    (hqi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q) (P0 : Measure Ω))
    (hqm : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q ∂(P0 : Measure Ω) ≤ ν ^ q)
    (hbudget : 44 * (L / μ) * Real.sqrt (Δ / ε) +
      1024 * σ ^ 2 * (L / μ + Real.log (3 / δ)) / (μ * ε) +
      ((64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Real.log (3 / δ)) ^ q * (3 / δ) ^ 2) ^ (1 / (q - 2)) ≤ T) :
    (Measure.pi fun _ : Fin T => (P0 : Measure Ω))
      {ξ | ε < f (iterateSamples (plainStep g μ (offset L μ)) T (0, x0) ξ).2 - ⨅ y, f y} ≤
        ENNReal.ofReal δ := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m = ⨅ y, f y := ⟨_, rfl⟩
  rw [← hm] at hpl hx0 ⊢
  obtain ⟨t0, ht0def⟩ : ∃ t0, t0 = offset L μ := ⟨_, rfl⟩
  rw [← ht0def]
  obtain ⟨ht0L, ht0U, ht03⟩ := offset_bounds hμ hμL
  rw [← ht0def] at ht0L ht0U ht03
  have hL : 0 < L := hμ.trans_le hμL
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr hμL
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have ht0r : (3 : ℝ) ≤ t0 := by exact_mod_cast ht03
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (3 / δ) := ⟨_, rfl⟩
  rw [← hΛ] at hbudget
  have hΛ1 : 1 ≤ Λ := hΛ ▸ one_le_log_three_div hδ hδ1
  obtain ⟨M, hMdef⟩ : ∃ M, M = ν * (3 * T / δ) ^ (1 / q) := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (T : ℝ) + t0 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt (L * Δ) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = σ ^ 2 + t0 * M * R / n := ⟨_, rfl⟩
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = μ / (32 * n * s2) := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β, β = σ ^ 2 * (ν ^ q / M ^ q) := ⟨_, rfl⟩
  obtain ⟨start, hstart⟩ : ∃ start, start = ((t0 : ℝ) - 1) * ((t0 : ℝ) - 2) * Δ := ⟨_, rfl⟩
  have hn0 : 0 < n := by rw [hn]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hs2σ : σ ^ 2 ≤ s2 := by
    rw [hs2]; have : 0 ≤ t0 * M * R / n := by positivity
    linarith
  have hs2pos : 0 < s2 := lt_of_lt_of_le (by positivity) hs2σ
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hMq : M ^ q = ν ^ q * (3 * T / δ) := by
    rw [hMdef]; exact truncation_power hν hT0 hδ (by linarith)
  have hTβ : (T : ℝ) * β = σ ^ 2 * δ / 3 := by
    rw [hβdef, hMq]; field_simp
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hgm : Measurable (gradient f) := by
    have hlw : LipschitzWith (Real.toNNReal L) (gradient f) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.coe_toNNReal _ hL.le, dist_eq_norm, dist_eq_norm]; exact hlip x y
    exact hlw.continuous.measurable
  have hm_le : ∀ x, m ≤ f x := fun x => hm ▸ ciInf_le hbdd x
  have hgrad : ∀ x, ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - m) :=
    gradient_sq_le hL hgr hlip hm_le
  have hnoise_meas : ∀ x, Measurable (fun ω => noise f g x ω) := fun x =>
    (noise_measurable hg hgm).comp (measurable_const.prodMk measurable_id)
  have hnoise_int : ∀ x, Integrable (fun ω => noise f g x ω) (P0 : Measure Ω) := fun x =>
    (hgi x).sub (integrable_const _)
  have hnoise_zero : ∀ x, ∫ ω, noise f g x ω ∂(P0 : Measure Ω) = 0 := fun x => by
    simp only [noise]; rw [integral_sub (hgi x) (integrable_const _), hmean x]; simp
  have hbias : ∀ x, ‖∫ u, clip M (noise f g x u) ∂(P0 : Measure Ω)‖ ^ 2 ≤ β := fun x => by
    rw [hβdef]
    exact (clip_bias (hnoise_meas x) (hnoise_int x) (hnoise_zero x) (h2i x) (hqi x) hM hσ hν
      (by linarith) (hvar x) (hqm x)).2
  have hLη : ∀ t, L * stepSize μ t0 t ≤ 1 / 2 := by
    intro t
    simp only [stepSize]
    have ht : 8 * L ≤ μ * ((t : ℝ) + t0) := by
      have h1 := (div_le_iff₀ hμ).mp ht0L
      have h2 : (0 : ℝ) ≤ μ * t := mul_nonneg hμ.le t.cast_nonneg
      have e : μ * ((t : ℝ) + t0) = μ * t + t0 * μ := by ring
      linarith only [h1, h2, e]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith only [ht]
  have hdr : ∀ t, 0 ≤ drift μ t0 t := fun t => by
    simp only [drift]; have := t.cast_nonneg (α := ℝ); apply div_nonneg _ hμ.le
    linarith only [this, ht0r]
  have hcomp : ∀ t ≤ T, lam * drift μ t0 t * σ ^ 2 ≤ 1 / 8 := by
    intro t ht
    have htr : (t : ℝ) ≤ T := by exact_mod_cast ht
    simp only [drift]
    rw [hlamdef, show μ / (32 * n * s2) * (4 * ((t : ℝ) + t0 - 1) / μ) * σ ^ 2 =
      ((t : ℝ) + t0 - 1) * σ ^ 2 / (8 * n * s2) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (t : ℝ) + t0 - 1 ≤ n := by rw [hn]; linarith
    have h2 : 0 ≤ (t : ℝ) + t0 - 1 := by have := t.cast_nonneg (α := ℝ); linarith
    have h3 := mul_le_mul h1 hs2σ (sq_nonneg σ) hn0.le
    linarith only [h3]
  have hb3 : ((64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Λ) ^ q * (3 / δ) ^ 2) ^ (1 / (q - 2)) ≤ T := by
    have h1 : 0 ≤ 44 * (L / μ) * Real.sqrt (Δ / ε) := by positivity
    have h2 : 0 ≤ 1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε) := by positivity
    linarith
  have hρ : 64 * L ^ 2 * M ^ 2 * Λ ≤ μ ^ 2 * σ ^ 2 * n := by
    have hK : 0 < 64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Λ := by positivity
    have hr := burn_in_rho hK (show 0 < 3 / δ by positivity) hT0 hq hb3
    have hM2 : M ^ 2 = ν ^ 2 * (3 * T / δ) ^ (2 / q) := by rw [hMdef]; exact truncation_sq hT0 hδ
    rw [show (3 / δ) * (T : ℝ) = 3 * T / δ by ring] at hr
    have e : 64 * L ^ 2 * M ^ 2 * Λ =
        μ ^ 2 * σ ^ 2 * (64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Λ * (3 * T / δ) ^ (2 / q)) := by
      rw [hM2]; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hn]; have : (0 : ℝ) ≤ t0 := by positivity
    linarith
  have hb1 : 4 * t0 * Real.sqrt (Δ / ε) ≤ n := by
    have h2 : 0 ≤ 1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε) := by positivity
    have h3 : 0 ≤ ((64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Λ) ^ q * (3 / δ) ^ 2) ^ (1 / (q - 2)) := by
      positivity
    have h4 : 4 * t0 * Real.sqrt (Δ / ε) ≤ 44 * (L / μ) * Real.sqrt (Δ / ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _); linarith
    rw [hn]; have : (0 : ℝ) ≤ t0 := by positivity
    linarith
  have hb2 : 1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε) ≤ n := by
    have h1 : 0 ≤ 44 * (L / μ) * Real.sqrt (Δ / ε) := by positivity
    have h3 : 0 ≤ ((64 * (L / μ) ^ 2 * (ν / σ) ^ 2 * Λ) ^ q * (3 / δ) ^ 2) ^ (1 / (q - 2)) := by
      positivity
    rw [hn]; have : (0 : ℝ) ≤ t0 := by positivity
    linarith
  obtain ⟨hburn, hacc⟩ := core_tuning (T := (T : ℝ)) (t0 := (t0 : ℝ)) (β := β) (N :=
    start + Λ / lam + 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) +
      8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ)
    hμ hμL hσ hM hΛ1 hΔ hε hTr ht0r (by rw [hTβ]; nlinarith) hn hR hs2 hlamdef hρ hb1 hb2
    (by rw [hstart])
  obtain ⟨s0, hs0⟩ : ∃ s0 : State E, s0 = (0, x0, 0, 0, 0) := ⟨_, rfl⟩
  have hinv0 : Invariant f m μ L lam M β start t0 s0 := by
    rw [hs0]
    refine ⟨le_rfl, Or.inl rfl, fun _ => ?_⟩
    show weight t0 0 * (f x0 - m) ≤ start + 0 / lam + 16 * L / μ ^ 2 * M ^ 2 * 0 +
      8 * ((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + t0) * β / μ
    have hw0 : weight t0 0 = ((t0 : ℝ) - 1) * ((t0 : ℝ) - 2) := by simp [weight]
    rw [hw0, hstart]
    simp only [Nat.cast_zero, zero_div, mul_zero, add_zero, zero_mul]
    exact mul_le_mul_of_nonneg_left hx0 (mul_nonneg (by linarith) (by linarith))
  let EA := {ξ : Fin T → Ω | Λ < (iterateSamples (transition f g P0 μ lam M t0 T) T s0 ξ).2.2.1}
  let EB := {ξ : Fin T → Ω | T * (2 * σ ^ 2 / M ^ 2) + Λ <
    (iterateSamples (transition f g P0 μ lam M t0 T) T s0 ξ).2.2.2.1}
  let EC := {ξ : Fin T → Ω | 1 ≤ |(iterateSamples (transition f g P0 μ lam M t0 T) T s0 ξ).2.2.2.2|}
  have hsub : {ξ | ε < f (iterateSamples (plainStep g μ t0) T (0, x0) ξ).2 - m} ⊆
      EA ∪ EB ∪ EC := by
    intro ξ hξ
    by_contra hnot
    simp only [Set.mem_union, not_or, EA, EB, EC, Set.mem_ofPred_eq, not_lt] at hnot
    obtain ⟨⟨hA, hB⟩, hC⟩ := hnot
    have hC' := lt_of_not_ge hC
    obtain ⟨z, hz⟩ : ∃ z, z = iterateSamples (transition f g P0 μ lam M t0 T) T s0 ξ := ⟨_, rfl⟩
    rw [← hz] at hA hB hC'
    have hinvz : Invariant f m μ L lam M β start t0 z := by
      rw [hz]
      exact stopped_invariant (Good f μ lam M t0 T) (Invariant f m μ L lam M β start t0)
        (sgdStep f g P0 μ lam M t0)
        (fun s hs _ ω => invariant_step hgr hlip hpl hμ hL.le hlam hM ht03 hLη hbias s hs ω)
        T s0 hinv0 ξ
    have hT' : z.1 ≤ T := by
      have := stopped_time_le (f := f) (g := g) (P0 := P0) (μ := μ) (lam := lam) (M := M)
        (t0 := t0) (T := T) T s0 ξ
      rw [← hz, hs0] at this; simpa using this
    obtain ⟨hgood, hbound⟩ :=
      final_state_bound z hμ hL hlam hM ht03 hβ0 hgrad hinvz hA hB hC' hT' hburn
    have hgood' : Good f μ lam M t0 T
        (iterateSamples (stopUnless (Good f μ lam M t0 T) (sgdStep f g P0 μ lam M t0)) T s0 ξ) := by
      have : z = iterateSamples (stopUnless (Good f μ lam M t0 T) (sgdStep f g P0 μ lam M t0)) T s0 ξ :=
        hz
      rw [← this]; exact hgood
    have heq := (stopped_compare (Good f μ lam M t0 T) (sgdStep f g P0 μ lam M t0) T s0 ξ).resolve_right
      (fun h => h hgood')
    have hplain := sgdStep_plain (f := f) (g := g) (P0 := P0) (μ := μ) (lam := lam) (M := M)
      (t0 := t0) T s0 ξ
    have hZeq : iterateSamples (sgdStep f g P0 μ lam M t0) T s0 ξ = z := heq.trans hz.symm
    rw [hZeq, hs0] at hplain
    have htime := plainStep_time g μ t0 T (0, x0) ξ
    have hx : (iterateSamples (plainStep g μ t0) T (0, x0) ξ).2 = z.2.1 := by
      rw [← hplain]
    have ht : z.1 = T := by
      have := congrArg Prod.fst hplain
      simp only at this
      rw [this, htime]; simp
    rw [ht] at hbound
    have hw : weight t0 T = (n - 1) * (n - 2) := by rw [hn]; simp only [weight]
    rw [hw] at hbound
    have hWpos : 0 < (n - 1) * (n - 2) := by
      have : 4 ≤ n := by rw [hn]; linarith
      exact mul_pos (by linarith) (by linarith)
    have hr : f z.2.1 - m ≤ ε := by
      have h1 : f z.2.1 - m ≤ (start + Λ / lam + 16 * L / μ ^ 2 * M ^ 2 *
          (T * (2 * σ ^ 2 / M ^ 2) + Λ) + 8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ) /
            ((n - 1) * (n - 2)) := by
        rw [le_div_iff₀ hWpos]; linarith
      exact h1.trans hacc
    simp only [Set.mem_ofPred_eq] at hξ
    rw [hx] at hξ
    linarith
  have hA := tail_martingale P0 hg hgm hlam.le hM.le hdr h2i hvar hcomp s0 (by rw [hs0]) Λ
  have hB := tail_square (μ := μ) (lam := lam) (t0 := t0) (T := T) P0 hg hgm hM h2i hvar s0 (by rw [hs0]) Λ
  have hC := tail_exceed (μ := μ) (lam := lam) (t0 := t0) (T := T) P0 hg hgm hM hν
    (by linarith) hqi hqm s0 (by rw [hs0])
  have hexp : Real.exp (-Λ) = δ / 3 := by
    rw [hΛ, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hpc : (T : ℝ) * (ν ^ q / M ^ q) = δ / 3 := by
    rw [hMq]; field_simp
  rw [hexp] at hA hB
  rw [hpc] at hC
  calc (Measure.pi fun _ : Fin T => (P0 : Measure Ω))
        {ξ | ε < f (iterateSamples (plainStep g μ t0) T (0, x0) ξ).2 - m}
      ≤ (Measure.pi fun _ : Fin T => (P0 : Measure Ω)) (EA ∪ EB ∪ EC) := measure_mono hsub
    _ ≤ (Measure.pi fun _ : Fin T => (P0 : Measure Ω)) EA +
        (Measure.pi fun _ : Fin T => (P0 : Measure Ω)) EB +
        (Measure.pi fun _ : Fin T => (P0 : Measure Ω)) EC :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) :=
      add_le_add (add_le_add hA hB) hC
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

end Assembly

lemma plainStep_measurable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (μ : ℝ) (t0 : ℕ) :
    Measurable (fun z : (ℕ × E) × Ω => plainStep g μ t0 z.1 z.2) := by
  have ht : Measurable (fun z : (ℕ × E) × Ω => z.1.1) := measurable_fst.fst
  have hx : Measurable (fun z : (ℕ × E) × Ω => z.1.2) := measurable_fst.snd
  exact (ht.add_const 1).prodMk (hx.sub (((measurable_of_countable (stepSize μ t0)).comp ht).smul
    (hg.comp (hx.prodMk measurable_snd))))

lemma convergence : Convergence spec (fun p _ => ⌈44 * (p.L / p.μ) * Real.sqrt (p.Δ / p.ε) +
    1024 * p.σ ^ 2 * (p.L / p.μ + Real.log (3 / p.δ)) / (p.μ * p.ε) +
    ((64 * (p.L / p.μ) ^ 2 * (p.ν / p.σ) ^ 2 * Real.log (3 / p.δ)) ^ p.q * (3 / p.δ) ^ 2) ^
      (1 / (p.q - 2))⌉₊) := by
  apply convergence_of_call_budget (S := spec)
  refine ⟨fun pub => ScheduledSgd.method (stepSize pub.μ (offset pub.L pub.μ)) pub.x0, ?_, ?_⟩
  · rintro p ⟨hμ, hμL, hσ, hν, hq, hΔ, hε, hδ, hδ1⟩ K hK f O hadm
    rcases hadm with ⟨g, P0, P, hIID, hO, hgr, hlip, hbdd, hpl, hx0, hg, hgi, hmean, h2i, hvar,
      hqi, hqm⟩
    subst hO
    obtain ⟨B, hBdef⟩ : ∃ B, B = 44 * (p.L / p.μ) * Real.sqrt (p.Δ / p.ε) +
      1024 * p.σ ^ 2 * (p.L / p.μ + Real.log (3 / p.δ)) / (p.μ * p.ε) +
      ((64 * (p.L / p.μ) ^ 2 * (p.ν / p.σ) ^ 2 * Real.log (3 / p.δ)) ^ p.q * (3 / p.δ) ^ 2) ^
        (1 / (p.q - 2)) := ⟨_, rfl⟩
    rw [← hBdef] at hK
    have hΛ1 := one_le_log_three_div hδ hδ1
    have hBpos : 0 < B := by
      rw [hBdef]
      have h1 : 0 ≤ 44 * (p.L / p.μ) * Real.sqrt (p.Δ / p.ε) := by
        have : 0 < p.L := hμ.trans_le hμL
        positivity
      have h2 : 0 ≤ 1024 * p.σ ^ 2 * (p.L / p.μ + Real.log (3 / p.δ)) / (p.μ * p.ε) := by
        have : 0 < p.L := hμ.trans_le hμL
        positivity
      have h3 : 0 < ((64 * (p.L / p.μ) ^ 2 * (p.ν / p.σ) ^ 2 * Real.log (3 / p.δ)) ^ p.q *
          (3 / p.δ) ^ 2) ^ (1 / (p.q - 2)) := by
        have : 0 < p.L := hμ.trans_le hμL
        have : 0 < Real.log (3 / p.δ) := by linarith
        positivity
      linarith
    have hBK : B ≤ K := (Nat.le_ceil B).trans (by exact_mod_cast hK)
    have hK1 : 1 ≤ K := by
      have : (0 : ℝ) < K := hBpos.trans_le hBK
      exact_mod_cast this
    have hfin := finite_accuracy f g P0 p.x0 K hμ hμL hσ hν hq hΔ hε hδ hδ1 hK1 hgr hlip hbdd hpl
      hx0 hg hgi hmean h2i hvar hqi hqm (hBdef ▸ hBK)
    have hΦ : MeasurePreserving (fun (ξ : ℕ → p.Ω) (i : Fin K) => ξ i.val)
        (P : Measure (ℕ → p.Ω)) (Measure.pi fun _ : Fin K => (P0 : Measure p.Ω)) := by
      simpa only [Nat.zero_add] using FixedBatchConfidence.iid_finite_block_law hIID 0 K
    have hfm : Measurable f := by
      exact (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
    have hit : Measurable (fun ξ : Fin K → p.Ω =>
        (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0) ξ).2) :=
      ((GapStrongGrowth.iterateSamples_measurable (plainStep_measurable hg p.μ (offset p.L p.μ)) K).comp
        (measurable_const.prodMk measurable_id)).snd
    have hAset : MeasurableSet {ξ : Fin K → p.Ω | p.ε <
        f (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0) ξ).2 - ⨅ y, f y} :=
      measurableSet_lt measurable_const ((hfm.comp hit).sub_const _)
    have hres : (fun seed : Unit × (ℕ → p.Ω) =>
        execute ({ Seed := fun _ => p.Ω
                   law := P
                   answer := fun _ (_, x) seed => g x seed } : Oracle p.E p.E)
          (ScheduledSgd.method (stepSize p.μ (offset p.L p.μ)) p.x0) (fun _ => K) seed.1 seed.2) =
        fun seed => (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0)
          (fun i => seed.2 i)).2 := by
      funext ⟨⟨⟩, ξ⟩
      exact execute_plain g p.μ (offset p.L p.μ) p.x0 K P ξ
    change spec.successful p f
      (fun seed : Unit × (ℕ → p.Ω) =>
        execute ({ Seed := fun _ => p.Ω
                   law := P
                   answer := fun _ (_, x) seed => g x seed } : Oracle p.E p.E)
          (ScheduledSgd.method (stepSize p.μ (offset p.L p.μ)) p.x0) (fun _ => K) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod (P : Measure (ℕ → p.Ω)), inferInstance⟩
    rw [hres]
    refine ⟨hit.comp (hΦ.measurable.comp measurable_snd), ?_⟩
    have hsnd := measurePreserving_snd (μ := (Measure.dirac () : Measure Unit))
      (ν := (P : Measure (ℕ → p.Ω)))
    have h1 := hsnd.measure_preimage_le {ξ : ℕ → p.Ω | p.ε <
      f (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0) (fun i => ξ i)).2 - ⨅ y, f y}
    refine h1.trans ?_
    rw [show {ξ : ℕ → p.Ω | p.ε <
      f (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0) (fun i => ξ i)).2 - ⨅ y, f y} =
      (fun (ξ : ℕ → p.Ω) (i : Fin K) => ξ i.val) ⁻¹' {ξ : Fin K → p.Ω | p.ε <
        f (iterateSamples (plainStep g p.μ (offset p.L p.μ)) K (0, p.x0) ξ).2 - ⨅ y, f y} from rfl,
      hΦ.measure_preimage hAset.nullMeasurableSet]
    exact hfin
  · intro p hp
    obtain ⟨hμ, hμL, -⟩ := hp
    refine ⟨stepSize p.μ (offset p.L p.μ), fun t => ?_, rfl⟩
    simp only [stepSize]
    have h3 : (3 : ℝ) ≤ (offset p.L p.μ : ℝ) := by exact_mod_cast (offset_bounds hμ hμL).2.2
    have ht : (0 : ℝ) ≤ t := t.cast_nonneg
    exact div_pos (by norm_num) (mul_pos hμ (by linarith))

end OracleTemplate.HeavyTailedPL
