import LongTails.Proofs.HessianPLInstance
import LongTails.Proofs.RelativeHessianAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Proofs.HessianPLHardness

open scoped BigOperators RealInnerProductSpace
open Classical OracleTemplate MeasureTheory
open RelativeHessianScaling RelativeHessianInstance RelativeHessianSimulation
open RelativeHessianExposure
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound
open HessianPLWell HessianPLLocalized HessianPLInstance
open LongTails.Setups.HighDimensionalHessianLipschitzPL

section Exposure

variable {d m : ℕ} {S : Type*}

lemma good_gap (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (π : Fin (m + 1) ↪ Fin d)
    (hn : ¬bad query output update initial T π) :
    (m : ℝ) - (T + 1 : ℕ) ≤
      RelativeHessianLocalized.value (axes π) (output (actual π query update initial T)) -
        (m + 1 : ℕ) * bottom := by
  have hs : actual π query update initial T = simulate π query update initial T := by
    apply coupling
    intro t ht hx i hi
    let j : Fin (T + 1) := ⟨t, by omega⟩
    have ho : observe query output update initial T j π =
        query (simulate π query update initial t) := by
      simp [observe, observation, j, ht]
    have h := not_bad_small query output update initial T π hn j
      (by simpa only [ho] using hx) i hi
    simpa only [ho] using h
  rw [hs]
  apply value_unfinished (axes_orthonormal π) _ (T + 1)
  intro hx i hi
  rw [axes_inner]
  let j : Fin (T + 1) := ⟨T, by omega⟩
  have ho : observe query output update initial T j π =
      output (simulate π query update initial T) := by
    simp [observe, observation, j]
  have hr := RelativeHessianLocalized.radius_pos m
  have h := not_bad_small query output update initial T π hn j
    (by rw [ho]; linarith) i (by dsimp [j]; omega)
  rw [ho] at h
  linarith

lemma gap_average (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D) :
    3 * ((m : ℝ) - (T + 1 : ℕ)) * Fintype.card (CoordinateWords d m) ≤
      4 * ∑ w : CoordinateWords d m,
        (RelativeHessianLocalized.value (axes (coordinateEmbedding w))
          (output (actual (coordinateEmbedding w) query update initial T)) -
            (m + 1 : ℕ) * bottom) := by
  have hb := RelativeHessianAveraging.bad_fraction query output update initial T hT D hD hd hsize
  have hgap0 : (0 : ℝ) ≤ (m : ℝ) - (T + 1 : ℕ) := by
    have h : ((T + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hT
    linarith
  have hp (w : CoordinateWords d m) :
      ((m : ℝ) - (T + 1 : ℕ)) *
        (1 - if bad query output update initial T (coordinateEmbedding w) then 1 else 0) ≤
      RelativeHessianLocalized.value (axes (coordinateEmbedding w))
        (output (actual (coordinateEmbedding w) query update initial T)) -
          (m + 1 : ℕ) * bottom := by
    by_cases hw : bad query output update initial T (coordinateEmbedding w)
    · simp only [hw, ite_true, sub_self, mul_zero]
      exact sub_nonneg.mpr (value_lower (axes_orthonormal _) _)
    · simp only [hw, ite_false, sub_zero, mul_one]
      exact good_gap query output update initial T (coordinateEmbedding w) hw
  have hs := Finset.sum_le_sum
    (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords d m))) => hp w)
  have hl : (∑ w : CoordinateWords d m, ((m : ℝ) - (T + 1 : ℕ)) *
      (1 - if bad query output update initial T (coordinateEmbedding w) then 1 else 0)) =
      ((m : ℝ) - (T + 1 : ℕ)) * (Fintype.card (CoordinateWords d m) -
        ∑ w : CoordinateWords d m,
          if bad query output update initial T (coordinateEmbedding w) then (1 : ℝ) else 0) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  rw [hl] at hs
  have hprod := mul_nonneg hgap0 (sub_nonneg.mpr hb)
  nlinarith

end Exposure

abbrev Alg (q : Params) := Algorithm (EuclideanSpace ℝ (Fin q.d))
  (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin q.d))) (EuclideanSpace ℝ (Fin q.d))

noncomputable def error (q : Params) {m : ℕ} (a β : ℝ) (A : Alg q) (T : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) (w : CoordinateWords q.d m) : ℝ :=
  scaled a β (coordinateEmbedding w)
    (execute (oracle a β (coordinateEmbedding w)) A (fun _ => T) seed ξ) -
      a * ((m + 1 : ℕ) * bottom)

lemma pointwise_average (q : Params) {m : ℕ} {a β : ℝ} (ha : 0 ≤ a)
    (A : Alg q) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ q.d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D)
    (seed : A.Seed) (ξ : ℕ → Unit) :
    3 * (a * ((m : ℝ) - (T + 1 : ℕ))) * Fintype.card (CoordinateWords q.d m) ≤
      4 * ∑ w : CoordinateWords q.d m, error q a β A T seed ξ w := by
  have h := gap_average (normalizedQuery β A) (fun state => β • A.output state)
    (normalizedUpdate a β A) (A.initial seed) T hT D hD hd hsize
  have hs := mul_le_mul_of_nonneg_left h ha
  have he : ∀ w : CoordinateWords q.d m, error q a β A T seed ξ w =
      a * (RelativeHessianLocalized.value (axes (coordinateEmbedding w))
        (β • A.output (actual (coordinateEmbedding w) (normalizedQuery β A)
          (normalizedUpdate a β A) (A.initial seed) T)) - (m + 1 : ℕ) * bottom) := by
    intro w
    unfold error scaled
    rw [execute_normalized]
    ring
  simp only [he, ← Finset.mul_sum]
  linarith

lemma exists_failure (q : Params) {m : ℕ} {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
    (A : Alg q) (P : ProbabilityMeasure (A.Seed × (ℕ → Unit))) (T : ℕ) (hT : T < m)
    (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ q.d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D)
    (hgap : 4 * q.ε < 3 * (a * ((m : ℝ) - (T + 1 : ℕ)))) :
    ∃ w : CoordinateWords q.d m, ¬ spec.successful q (scaled a β (coordinateEmbedding w))
      (fun ω : A.Seed × (ℕ → Unit) =>
        execute (oracle a β (coordinateEmbedding w)) A (fun _ => T) ω.1 ω.2) P := by
  by_contra h
  push Not at h
  have hint (w : CoordinateWords q.d m) :
      Integrable (fun ω : A.Seed × (ℕ → Unit) => error q a β A T ω.1 ω.2 w)
          (P : Measure (A.Seed × (ℕ → Unit))) ∧
        ∫ ω : A.Seed × (ℕ → Unit), error q a β A T ω.1 ω.2 w
          ∂(P : Measure (A.Seed × (ℕ → Unit))) ≤ q.ε := by
    obtain ⟨_, xstar, hmin, hi, hle⟩ := h w
    have hv := minimum_value ha hβ (coordinateEmbedding w) hmin
    rw [hv] at hi hle
    exact ⟨hi, hle⟩
  have hl := finite_integral_lower P
    (fun ω : A.Seed × (ℕ → Unit) => fun _ : Unit => fun w : CoordinateWords q.d m =>
      error q a β A T ω.1 ω.2 w)
    (24 * (a * ((m : ℝ) - (T + 1 : ℕ))) * Fintype.card (CoordinateWords q.d m))
    (fun _ w => (hint w).1) (fun ω => by
      have hp := pointwise_average q (β := β) ha A T hT D hD hd hsize ω.1 ω.2
      simp only [Fintype.sum_unique]
      linarith)
  simp only [Fintype.sum_unique] at hl
  have hu : (∑ w : CoordinateWords q.d m,
      ∫ ω : A.Seed × (ℕ → Unit), error q a β A T ω.1 ω.2 w ∂(P : Measure _)) ≤
      Fintype.card (CoordinateWords q.d m) * q.ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords q.d m, q.ε := Finset.sum_le_sum (fun w _ => (hint w).2)
      _ = _ := by simp
  have hmd : m + 1 ≤ q.d := by
    have hh : ((m + 1 : ℕ) : ℝ) ≤ q.d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords q.d m) := by
    exact_mod_cast coordinateWords_card_pos q.d m hmd
  have hstrict := mul_lt_mul_of_pos_right hgap hc
  nlinarith

section Tuning

noncomputable def theta (q : Params) : ℝ := q.H ^ 2 * q.Δ / q.μ ^ 3

noncomputable def limit (q : Params) : ℕ := ⌊theta q ^ (1 / 4 : ℝ) / 2 ^ 39⌋₊

def links (b : ℕ) : ℕ := 2 * b + 2

noncomputable def amplitude (q : Params) (b : ℕ) : ℝ := q.Δ / (4 * (links b + 1 : ℕ))

noncomputable def frequency (q : Params) (b : ℕ) : ℝ :=
  2 ^ 6 * (links b + 1 : ℕ) * Real.sqrt (q.μ / q.Δ)

lemma quarter_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  have h : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, h, Real.rpow_one]

lemma gap_pos {q : Params} (hq : spec.valid q) : 0 < q.Δ := by
  obtain ⟨_, _, hε, hΔ, _, _⟩ := hq
  linarith

lemma theta_nonneg {q : Params} (hq : spec.valid q) : 0 ≤ theta q := by
  obtain ⟨_, _, _, _, hθ, _⟩ := hq
  have h : (0 : ℝ) ≤ 2 ^ 160 := by positivity
  exact h.trans hθ

lemma quarter_large {q : Params} (hq : spec.valid q) : 2 ^ 40 ≤ theta q ^ (1 / 4 : ℝ) := by
  have hθ : 2 ^ 160 ≤ theta q := hq.2.2.2.2.1
  have h4 := quarter_pow (theta_nonneg hq)
  have h0 : 0 ≤ theta q ^ (1 / 4 : ℝ) := Real.rpow_nonneg (theta_nonneg hq) _
  have hp : ((2 : ℝ) ^ 40) ^ 4 ≤ (theta q ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [h4]
    norm_num at hθ ⊢
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp hp

lemma count_le {q : Params} (hq : spec.valid q) {b : ℕ} (hb : b ≤ limit q) :
    ((links b + 1 : ℕ) : ℝ) ≤ theta q ^ (1 / 4 : ℝ) / 2 ^ 36 := by
  have hl := quarter_large hq
  have hbcast : (b : ℝ) ≤ (limit q : ℝ) := by exact_mod_cast hb
  have hb' : (b : ℝ) ≤ theta q ^ (1 / 4 : ℝ) / 2 ^ 39 :=
    hbcast.trans (Nat.floor_le (div_nonneg (by linarith [show (0 : ℝ) ≤ 2 ^ 40 by positivity])
      (by positivity)))
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 39)).mp hb'
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 36)]
  unfold links
  push_cast
  norm_num at hl hmul ⊢
  linarith

lemma count_pos (b : ℕ) : (1 : ℝ) ≤ ((links b + 1 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_pos (links b)

lemma count_fourth {q : Params} (hq : spec.valid q) {b : ℕ} (hb : b ≤ limit q) :
    2 ^ 144 * ((links b + 1 : ℕ) : ℝ) ^ 4 ≤ theta q := by
  have hc := count_le hq hb
  have h0 : (0 : ℝ) ≤ ((links b + 1 : ℕ) : ℝ) := by positivity
  have hp := pow_le_pow_left₀ h0 hc 4
  rw [div_pow, quarter_pow (theta_nonneg hq), le_div_iff₀ (by positivity)] at hp
  have he : ((2 : ℝ) ^ 36) ^ 4 = 2 ^ 144 := by norm_num
  rw [he] at hp
  linarith

lemma amplitude_pos {q : Params} (hq : spec.valid q) (b : ℕ) : 0 < amplitude q b := by
  unfold amplitude
  have := count_pos b
  exact div_pos (gap_pos hq) (by linarith)

lemma frequency_pos {q : Params} (hq : spec.valid q) (b : ℕ) : 0 < frequency q b := by
  unfold frequency
  have h1 := count_pos b
  have h2 : 0 < Real.sqrt (q.μ / q.Δ) := Real.sqrt_pos.mpr (div_pos hq.2.1 (gap_pos hq))
  have h3 : (0 : ℝ) < ((links b + 1 : ℕ) : ℝ) := by linarith
  positivity

lemma gap_budget (q : Params) (b : ℕ) :
    amplitude q b * (4 * (links b + 1 : ℕ)) ≤ q.Δ := by
  unfold amplitude
  have h := count_pos b
  have hne : (4 * ((links b + 1 : ℕ) : ℝ)) ≠ 0 := by linarith
  rw [div_mul_cancel₀ _ hne]

lemma frequency_sq {q : Params} (hq : spec.valid q) (b : ℕ) :
    frequency q b ^ 2 = 2 ^ 12 * ((links b + 1 : ℕ) : ℝ) ^ 2 * (q.μ / q.Δ) := by
  unfold frequency
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos hq.2.1 (gap_pos hq)).le]
  norm_num

lemma pl_budget {q : Params} (hq : spec.valid q) (b : ℕ) :
    2 ^ 10 * q.μ * (links b + 1 : ℕ) ≤ amplitude q b * frequency q b ^ 2 := by
  rw [frequency_sq hq]
  unfold amplitude
  have h := count_pos b
  have hΔ := gap_pos hq
  have hN : ((links b + 1 : ℕ) : ℝ) ≠ 0 := by linarith
  have he : q.Δ / (4 * ((links b + 1 : ℕ) : ℝ)) *
      (2 ^ 12 * ((links b + 1 : ℕ) : ℝ) ^ 2 * (q.μ / q.Δ)) =
      2 ^ 10 * q.μ * ((links b + 1 : ℕ) : ℝ) := by
    field_simp
    ring
  rw [he]

lemma hessian_budget {q : Params} (hq : spec.valid q) {b : ℕ} (hb : b ≤ limit q) :
    2 ^ 56 * amplitude q b * frequency q b ^ 3 ≤ q.H := by
  have hH := hq.1
  have hμ := hq.2.1
  have hΔ := gap_pos hq
  have ha := amplitude_pos hq b
  have hf := frequency_pos hq b
  have h4 := count_fourth hq hb
  have hN := count_pos b
  have hNne : ((links b + 1 : ℕ) : ℝ) ≠ 0 := by linarith
  have hsq : (2 ^ 56 * amplitude q b * frequency q b ^ 3) ^ 2 =
      2 ^ 144 * ((links b + 1 : ℕ) : ℝ) ^ 4 * (q.μ ^ 3 / q.Δ) := by
    have he : (2 ^ 56 * amplitude q b * frequency q b ^ 3) ^ 2 =
        2 ^ 112 * amplitude q b ^ 2 * (frequency q b ^ 2) ^ 3 := by ring
    rw [he, frequency_sq hq]
    unfold amplitude
    field_simp
    ring
  have hθ : theta q * (q.μ ^ 3 / q.Δ) = q.H ^ 2 := by
    unfold theta
    field_simp
  have hle : (2 ^ 56 * amplitude q b * frequency q b ^ 3) ^ 2 ≤ q.H ^ 2 := by
    rw [hsq, ← hθ]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  exact (pow_le_pow_iff_left₀ (by positivity) hH.le (by norm_num)).mp hle

lemma failure_gap {q : Params} (hq : spec.valid q) (b : ℕ) :
    4 * q.ε < 3 * (amplitude q b * ((links b : ℝ) - (b + 1 : ℕ))) := by
  obtain ⟨_, _, hε, hΔε, _, _⟩ := hq
  have hN := count_pos b
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have he : amplitude q b * ((links b : ℝ) - (b + 1 : ℕ)) =
      q.Δ * ((b : ℝ) + 1) / (4 * (2 * (b : ℝ) + 3)) := by
    unfold amplitude links
    push_cast
    have h3 : (2 * (b : ℝ) + 2 + 1) ≠ 0 := by linarith
    have h3' : (2 * (b : ℝ) + 3) ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  have hfrac : q.Δ / 12 ≤ q.Δ * ((b : ℝ) + 1) / (4 * (2 * (b : ℝ) + 3)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

lemma dimension_budget {q : Params} (hq : spec.valid q) {b : ℕ} (hb : b ≤ limit q) :
    0 < (q.d : ℝ) / 2 ∧ (q.d : ℝ) / 2 + (links b + 1 : ℕ) ≤ q.d ∧
    4 * (b + 1 : ℕ) * (links b + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius (links b)) ^ 2 / (1 / 20) ^ 2) ≤ (q.d : ℝ) / 2 := by
  have hd : theta q ≤ q.d := hq.2.2.2.2.2
  have hθ : 2 ^ 160 ≤ theta q := hq.2.2.2.2.1
  have h4 := count_fourth hq hb
  have hN := count_pos b
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((links b + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hNdef] at h4 hN ⊢
  have hN4 : N ≤ N ^ 4 := le_self_pow₀ hN (by norm_num)
  have hbN : ((b + 1 : ℕ) : ℝ) ≤ N := by
    rw [hNdef]
    unfold links
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) b]
  have hd0 : (0 : ℝ) < q.d := by
    have h : (0 : ℝ) < 2 ^ 160 := by positivity
    linarith
  refine ⟨by linarith, by nlinarith, ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by linarith
  calc
    _ = 6400 * 2 ^ 120 * (b + 1 : ℕ) * N ^ 3 := by
      rw [hNdef]
      unfold RelativeHessianLocalized.radius
      ring
    _ ≤ 6400 * 2 ^ 120 * N ^ 4 := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbN (pow_nonneg hN0 3))
        (by norm_num : (0 : ℝ) ≤ 6400 * 2 ^ 120)
      nlinarith
    _ ≤ _ := by
      norm_num at h4 hθ ⊢
      linarith

lemma limit_large {q : Params} (hq : spec.valid q) : 2 ≤ limit q := by
  have hl := quarter_large hq
  unfold limit
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)]
  norm_num at hl ⊢
  linarith

lemma valid_nonempty : ∃ q : Params, spec.valid q := by
  refine ⟨⟨2 ^ 160, 1, 1, 2 ^ 160, 1⟩, ?_⟩
  norm_num [spec]

end Tuning

lemma hard (q : Params) (hq : spec.valid q) (A : Alg q) (b : Fin 1 → ℕ)
    (hb : b 0 ≤ limit q) :
    ∃ (f : EuclideanSpace ℝ (Fin q.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin q.d))
        (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin q.d)))),
      spec.admissible q f O ∧
      ¬ spec.successful q f (fun ω : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b ω.1 ω.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have heq : b = fun _ => b 0 := funext (fun i => congrArg b (Subsingleton.elim i 0))
  obtain ⟨hD, hd, hsize⟩ := dimension_budget hq hb
  have hT : b 0 < links (b 0) := by unfold links; omega
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨w, hw⟩ := exists_failure q (amplitude_pos hq (b 0)).le (frequency_pos hq (b 0))
    A P (b 0) hT ((q.d : ℝ) / 2) hD hd hsize (failure_gap hq (b 0))
  let π := coordinateEmbedding w
  refine ⟨scaled (amplitude q (b 0)) (frequency q (b 0)) π,
    oracle (amplitude q (b 0)) (frequency q (b 0)) π, ?_, ?_⟩
  · exact HessianPLInstance.admissible q (amplitude_pos hq (b 0)).le (frequency_pos hq (b 0))
      hq.2.1.le (hessian_budget hq hb) (pl_budget hq (b 0)) (gap_budget q (b 0)) π
  · have hout : (fun ω : A.Seed × (ℕ → Unit) =>
        execute (oracle (amplitude q (b 0)) (frequency q (b 0)) π) A b ω.1 ω.2) =
        (fun ω : A.Seed × (ℕ → Unit) =>
          execute (oracle (amplitude q (b 0)) (frequency q (b 0)) π) A (fun _ => b 0) ω.1 ω.2) := by
      funext ω
      exact congrArg
        (fun c => execute (oracle (amplitude q (b 0)) (frequency q (b 0)) π) A c ω.1 ω.2) heq
    change ¬ spec.successful q (scaled (amplitude q (b 0)) (frequency q (b 0)) π) _ P
    erw [hout]
    exact hw

end LongTails.Proofs.HessianPLHardness
