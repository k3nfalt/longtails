import LongTails.Proofs.GapNoiseTuning
import LongTails.Proofs.ProjectedClippedBudget

open scoped BigOperators

namespace LongTails.Proofs.GapNoiseBudget

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseTuning

set_option exponentiation.threshold 1024

lemma stageBatch_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    (stageBatch t s : ℝ) ≤ 1 + 2 ^ 120 *
      (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) *
      (t.σ ^ 2 / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ^ 2) +
        t.v / (stageScale t s * stageShift t s)) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hr := stageRegularization_pos t hR hε s
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hτ := stageShift_pos t h0 h1 hR hG s
  unfold stageBatch
  rw [Nat.cast_max, Nat.cast_one]
  have hn : 0 ≤ 2 ^ 120 *
      (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) *
      (t.σ ^ 2 / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ^ 2) +
        t.v / (stageScale t s * stageShift t s)) := by positivity
  exact max_le (by linarith) (by linarith [(Nat.ceil_lt_add_one hn).le])

lemma pilotBatch_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    (pilotBatch t s : ℝ) ≤ 1 + 2 ^ 40 *
      (t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 +
        t.v * t.R * effectiveCurvature t / stageScale t s) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hS := stageScale_pos t h0 h1 hR hG hε s
  unfold pilotBatch
  rw [Nat.cast_max, Nat.cast_one]
  have hn : 0 ≤ 2 ^ 40 * (t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 +
      t.v * t.R * effectiveCurvature t / stageScale t s) := by positivity
  exact max_le (by linarith) (by linarith [(Nat.ceil_lt_add_one hn).le])

lemma finalBatch_upper (t : Tuning) (hR : 0 ≤ t.R) (hε : 0 < t.ε) (hv : 0 ≤ t.v) :
    (finalBatch t : ℝ) ≤ 1 + 2 ^ 60 * (t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε) := by
  unfold finalBatch
  rw [Nat.cast_max, Nat.cast_one]
  have hn : 0 ≤ 2 ^ 60 * (t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε) := by positivity
  exact max_le (by linarith) (by linarith [(Nat.ceil_lt_add_one hn).le])

lemma stageScale_ratio_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    stageScale t s / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤
      2 ^ 81 * stages t * OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hh := OracleTemplate.ProjectedClippedExtragradient.localScale_ratio_upper (geometry t) h0 hb.le hR hG hε s
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 ^ 40)
  unfold stageScale stages
  change 2 ^ 40 * OracleTemplate.ProjectedClippedExtragradient.localScale (geometry t) s /
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤ _
  convert hm using 1 <;> ring

lemma stageSteps_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    (stageSteps t s : ℝ) ≤ 2 ^ 130 * stages t *
      OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) := by
  have hh := stageSteps_upper t h0 h1 hR hG hε s
  have hm := mul_le_mul_of_nonneg_left (stageScale_ratio_upper t h0 h1 hR hG hε s)
    (by positivity : (0 : ℝ) ≤ 2 ^ 49)
  simp only [mul_div_assoc] at hh hm
  nlinarith only [hh, hm]

lemma initialization_cost {N m p k : ℝ} (hN : 1 ≤ N) (hm : 0 ≤ m) (hp : 0 ≤ p) (hk : 1 ≤ k) :
    (m + p * k + 2) * N + m + p * k ≤ 2 * N * k * (m + p + 1) := by
  have ha : 0 ≤ m + p * k := by positivity
  have hi : m + p * k ≤ N * (m + p * k) := by nlinarith [mul_nonneg (by linarith : 0 ≤ N - 1) ha]
  have hb : m + p * k + 1 ≤ k * (m + p + 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ k - 1) (by linarith : 0 ≤ m + 1)]
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * N)
  nlinarith only [hi, hh]

lemma trialCalls_upper (t : Tuning) (s : ℕ) (hN : 0 < stageSteps t s) :
    (trialCalls t s : ℝ) ≤ 2 * (stageSteps t s : ℝ) * ((pilotGroups t s : ℝ) + 1) *
      ((stageBatch t s : ℝ) + pilotBatch t s + 1) := by
  have hn : (1 : ℝ) ≤ stageSteps t s := by exact_mod_cast hN
  have hh := initialization_cost hn (Nat.cast_nonneg (stageBatch t s)) (Nat.cast_nonneg (pilotBatch t s))
    (show (1 : ℝ) ≤ (pilotGroups t s : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) (pilotGroups t s)])
  unfold trialCalls
  push_cast
  nlinarith only [hh]

lemma batch_work_algebra {r S d τ b R σ v : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hd : 0 < d) (hτ : 0 < τ) :
    S / r * (3 + 2 ^ 120 * (1 + b * d) * (σ ^ 2 / (r * S * d ^ 2) + v / (S * τ)) +
      2 ^ 40 * (σ ^ 2 * b ^ 2 / S ^ 2 + v * R * b / S)) =
      3 * S / r + 2 ^ 120 * (1 + b * d) * (σ ^ 2 / (r ^ 2 * d ^ 2) + v / (r * τ)) +
        2 ^ 40 * (σ ^ 2 * b ^ 2 / (r * S) + v * R * b / r) := by
  field_simp

lemma trialCalls_expanded (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    (trialCalls t s : ℝ) ≤ 2 ^ 50 * ((pilotGroups t s : ℝ) + 1) *
      (3 * stageScale t s / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s +
        2 ^ 120 * (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) *
          (t.σ ^ 2 / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ^ 2 *
            OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ^ 2) +
            t.v / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageShift t s)) +
        2 ^ 40 * (t.σ ^ 2 * effectiveCurvature t ^ 2 /
          (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s) +
          t.v * t.R * effectiveCurvature t / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s)) := by
  have hr := stageRegularization_pos t hR hε s
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hd := stageRadius_pos t hR s
  have hτ := stageShift_pos t h0 h1 hR hG s
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hm := stageBatch_upper t h0 h1 hR hG hε hv s
  have hp := pilotBatch_upper t h0 h1 hR hG hε hv s
  have hN := stageSteps_upper t h0 h1 hR hG hε s
  have ht := trialCalls_upper t s (stageSteps_pos t h0 h1 hR hG hε s)
  have hprod := mul_le_mul hN (add_le_add_right (add_le_add hm hp) 1)
    (by positivity : 0 ≤ 1 + ((stageBatch t s : ℝ) + pilotBatch t s)) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 2 * ((pilotGroups t s : ℝ) + 1))
  have he := batch_work_algebra (σ := t.σ) (v := t.v) (b := effectiveCurvature t) (R := t.R) hr hS hd hτ
  calc
    _ ≤ 2 * (stageSteps t s : ℝ) * ((pilotGroups t s : ℝ) + 1) *
        ((stageBatch t s : ℝ) + pilotBatch t s + 1) := ht
    _ ≤ _ := by
      have he2 := congrArg (fun z : ℝ => 2 ^ 50 * ((pilotGroups t s : ℝ) + 1) * z) he
      ring_nf at hmul he2 ⊢
      linarith only [hmul, he2]

lemma pilot_variance_cancellation {r S d b : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hd : 0 < d) (hb : 0 ≤ b) (hscale : r * (1 + b * d) ^ 4 ≤ S) :
    b ^ 2 / (r * S) ≤ 1 / (r ^ 2 * d ^ 2) := by
  have hx : 0 ≤ b * d := mul_nonneg hb hd.le
  have hp : (b * d) ^ 2 ≤ (1 + b * d) ^ 4 := by
    nlinarith [sq_nonneg ((b * d) ^ 2), mul_nonneg hx (sq_nonneg (b * d))]
  have hh := mul_le_mul_of_nonneg_left hp hr.le
  apply (div_le_div_iff₀ (by positivity : 0 < r * S) (by positivity : 0 < r ^ 2 * d ^ 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hh.trans hscale) hr.le]

lemma stageScale_fourth (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
      (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ^ 4 ≤
        stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hd := stageRadius_pos t hR s
  have hr := stageRegularization_pos t hR hε s
  have ha : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) *
      (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) := by positivity
  have hz : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
      (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ^ 4 := by positivity
  unfold stageScale OracleTemplate.ProjectedClippedExtragradient.localScale
  change _ ≤ 2 ^ 40 * (2 ^ 20 * (OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) *
    (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) +
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
    (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ^ 4))
  linarith only [ha, hz]

lemma stage_variance_identity (t : Tuning) (hR : 0 < t.R) (s : ℕ) :
    t.σ ^ 2 / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ^ 2 *
      OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ^ 2) =
        2 ^ 40 * (stages t : ℝ) ^ 2 * t.σ ^ 2 / t.ε ^ 2 := by
  have he := OracleTemplate.ProjectedClippedExtragradient.regularization_radius (geometry t) hR s
  change _ = t.ε / (2 ^ 20 * stages t) at he
  rw [← mul_pow, he]
  ring_nf
  simp only [inv_inv]
  ring

lemma stage_gap_identity (t : Tuning) (hR : 0 < t.R) (s : ℕ) :
    t.v / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageShift t s) =
      2 ^ 120 * (stages t : ℝ) ^ 2 * t.v * t.R * (1 + effectiveCurvature t * t.R) / t.ε := by
  have he := OracleTemplate.ProjectedClippedExtragradient.regularization_radius (geometry t) hR s
  change _ = t.ε / (2 ^ 20 * stages t) at he
  unfold stageShift
  rw [← mul_div_assoc, he]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

noncomputable def noiseWork (t : Tuning) : ℝ :=
  (1 + effectiveCurvature t * t.R) * t.σ ^ 2 / t.ε ^ 2 +
    (1 + effectiveCurvature t * t.R) ^ 2 * t.v * t.R / t.ε

lemma noiseWork_nonneg (t : Tuning) (hb : 0 ≤ effectiveCurvature t) (hR : 0 ≤ t.R)
    (hv : 0 ≤ t.v) (hε : 0 ≤ t.ε) : 0 ≤ noiseWork t := by
  unfold noiseWork
  positivity

lemma update_noise_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) *
      (t.σ ^ 2 / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ^ 2 *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ^ 2) +
        t.v / (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageShift t s)) ≤
      2 ^ 120 * (stages t : ℝ) ^ 2 * noiseWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hdR := OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le s
  change OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ≤ t.R at hdR
  rw [stage_variance_identity t hR s, stage_gap_identity t hR s]
  calc
    _ ≤ (1 + effectiveCurvature t * t.R) *
        (2 ^ 120 * (stages t : ℝ) ^ 2 * t.σ ^ 2 / t.ε ^ 2 +
          2 ^ 120 * (stages t : ℝ) ^ 2 * t.v * t.R * (1 + effectiveCurvature t * t.R) / t.ε) := by
      gcongr <;> norm_num
    _ = _ := by unfold noiseWork; ring

lemma pilot_noise_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    t.σ ^ 2 * effectiveCurvature t ^ 2 /
      (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s) +
      t.v * t.R * effectiveCurvature t / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤
        2 ^ 40 * (stages t : ℝ) ^ 2 * noiseWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hr := stageRegularization_pos t hR hε s
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hJ : (1 : ℝ) ≤ stages t := by exact_mod_cast stages_pos t
  have hJ0 : (0 : ℝ) < stages t := by linarith
  have hσ := mul_le_mul_of_nonneg_left
    (pilot_variance_cancellation hr hS hd hb.le (stageScale_fourth t h0 h1 hR hG hε s)) (sq_nonneg t.σ)
  have hσ' : t.σ ^ 2 * effectiveCurvature t ^ 2 /
      (OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s) ≤
        2 ^ 40 * (stages t : ℝ) ^ 2 * t.σ ^ 2 / t.ε ^ 2 := by
    rw [← stage_variance_identity t hR s]
    convert hσ using 1 <;> ring
  have hrl := OracleTemplate.ProjectedClippedExtragradient.regularization_lower (geometry t) hR hε s
  change t.ε / (2 ^ 20 * stages t * t.R) ≤ _ at hrl
  have hv' : t.v * t.R * effectiveCurvature t /
      OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤
      2 ^ 20 * stages t * (effectiveCurvature t * t.R) * (t.v * t.R / t.ε) := by
    calc
      _ ≤ t.v * t.R * effectiveCurvature t / (t.ε / (2 ^ 20 * stages t * t.R)) := by
        gcongr
      _ = _ := by field_simp
  have hq : 1 ≤ 1 + effectiveCurvature t * t.R := by
    linarith [mul_nonneg hb.le hR.le]
  have hbq : effectiveCurvature t * t.R ≤ (1 + effectiveCurvature t * t.R) ^ 2 := by
    nlinarith [sq_nonneg (effectiveCurvature t * t.R)]
  have hJ2 : (stages t : ℝ) ≤ (stages t : ℝ) ^ 2 := by nlinarith
  have hv'' : 2 ^ 20 * stages t * (effectiveCurvature t * t.R) * (t.v * t.R / t.ε) ≤
      2 ^ 40 * (stages t : ℝ) ^ 2 * (1 + effectiveCurvature t * t.R) ^ 2 * (t.v * t.R / t.ε) := by
    gcongr <;> norm_num
  have hσ'' : 2 ^ 40 * (stages t : ℝ) ^ 2 * t.σ ^ 2 / t.ε ^ 2 ≤
      2 ^ 40 * (stages t : ℝ) ^ 2 * ((1 + effectiveCurvature t * t.R) * t.σ ^ 2 / t.ε ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hq
      (by positivity : 0 ≤ 2 ^ 40 * (stages t : ℝ) ^ 2 * t.σ ^ 2 / t.ε ^ 2)
    convert hh using 1 <;> ring
  have hh := add_le_add (hσ'.trans hσ'') (hv'.trans hv'')
  unfold noiseWork
  convert hh using 1
  ring

lemma trialCalls_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    (trialCalls t s : ℝ) ≤ 2 ^ 292 * ((pilotGroups t s : ℝ) + 1) * (stages t : ℝ) ^ 2 *
      (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hW := noiseWork_nonneg t hb.le hR.le hv hε.le
  have hJ : (1 : ℝ) ≤ stages t := by exact_mod_cast stages_pos t
  have hJ2 : (stages t : ℝ) ≤ (stages t : ℝ) ^ 2 := by nlinarith
  have hdet := stageScale_ratio_upper t h0 h1 hR hG hε s
  have hu := update_noise_upper t h0 h1 hR hG hε hv s
  have hp := pilot_noise_upper t h0 h1 hR hG hε hv s
  have ht := trialCalls_expanded t h0 h1 hR hG hε hv s
  have hdet' := mul_le_mul_of_nonneg_right hJ2 (by linarith :
    0 ≤ OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t))
  have hw' : 0 ≤ (stages t : ℝ) ^ 2 * noiseWork t := by positivity
  have hd' : 0 ≤ (stages t : ℝ) ^ 2 * OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) := by positivity
  have hc := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hdet (by norm_num : (0 : ℝ) ≤ 3))
      (mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 ^ 120)))
    (mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 ^ 40))
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 ^ 50 * ((pilotGroups t s : ℝ) + 1))
  have hf : 3 * (2 ^ 81 * (stages t : ℝ) * OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) +
      2 ^ 120 * (2 ^ 120 * (stages t : ℝ) ^ 2 * noiseWork t) +
      2 ^ 40 * (2 ^ 40 * (stages t : ℝ) ^ 2 * noiseWork t) ≤
      2 ^ 242 * (stages t : ℝ) ^ 2 *
        (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) := by
    nlinarith only [hdet', hw', hd']
  have hf' := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 ^ 50 * ((pilotGroups t s : ℝ) + 1))
  ring_nf at ht hm hf' ⊢
  linarith only [ht, hm, hf']

noncomputable def logWork (t : Tuning) : ℝ :=
  1 + Real.log ((2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) / t.δ)

lemma curvature_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) :
    OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε ≤
      OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hh := OracleTemplate.ProjectedClippedExtragradient.curvature_work (geometry t) hb.le hR.le hε
  change OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε *
    (1 + effectiveCurvature t * t.R) ≤ _ at hh
  have hn : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε := by positivity
  nlinarith [mul_nonneg hn (mul_nonneg hb.le hR.le)]

lemma logWork_comparison (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    1 ≤ logWork t ∧
      OracleTemplate.ProjectedClippedExtragradient.logScale (geometry t) ≤ logWork t ∧
      OracleTemplate.ProjectedClippedExtragradient.confidenceScale (geometry t) ≤ logWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hC := curvature_work_upper t h0 h1 hR hG hε
  have hn : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε := by positivity
  have hx : 2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) ≤
      (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) / t.δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hz : 1 ≤ (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) / t.δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold logWork
    linarith [Real.log_nonneg hz]
  · have hh := Real.log_le_log (by positivity : 0 < 2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε)
      ((show 2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε ≤
        2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) by linarith).trans hx)
    simpa only [OracleTemplate.ProjectedClippedExtragradient.logScale, logWork, geometry, add_comm] using add_le_add_left hh 1
  · have hh := Real.log_le_log (by positivity : 0 < (2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε) / t.δ)
      (div_le_div_of_nonneg_right (by linarith :
        2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε ≤
          2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) hδ.le)
    simpa only [OracleTemplate.ProjectedClippedExtragradient.confidenceScale, logWork, geometry, add_comm] using add_le_add_left hh 1

lemma stages_log_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (stages t : ℝ) ≤ 64 * logWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hh := OracleTemplate.ProjectedClippedExtragradient.stageCount_log_upper (geometry t) hc.le hR.le hε
  have hm := (logWork_comparison t h0 h1 hR hG hε hδ hδ1).2.1
  change (stages t : ℝ) ≤ _ at hh
  linarith

lemma outerGroups_log_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (outerGroups t : ℝ) + 1 ≤ 128 * logWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hh := OracleTemplate.ProjectedClippedExtragradient.repetitions_log_upper (geometry t) hc.le hR.le hε hδ hδ1
  have hm := logWork_comparison t h0 h1 hR hG hε hδ hδ1
  change (outerGroups t : ℝ) ≤ _ at hh
  linarith [hm.1, hm.2.2]

lemma stages_algebra_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) :
    (stages t : ℝ) ≤ 64 * (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hC := curvature_work_upper t h0 h1 hR hG hε
  have hn : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε := by positivity
  have hh := OracleTemplate.ProjectedClippedExtragradient.stageCount_log_upper (geometry t) hc.le hR.le hε
  have hl := Real.log_le_sub_one_of_pos (by positivity :
    0 < 2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε)
  change (stages t : ℝ) ≤ 64 * (1 + Real.log (2 + OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) * t.R / t.ε)) at hh
  linarith

lemma pilot_log_algebra {N D δ : ℝ} (hN : 0 ≤ N) (hD : 1 ≤ D)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hND : N ≤ 2 ^ 136 * (2 + D) ^ 2) :
    (⌈Real.log (4096 * (N + 1)) / Real.log 2⌉₊ : ℝ) + 2 ≤
      1024 * (1 + Real.log ((2 + D) / δ)) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2p : 0 < Real.log 2 := by linarith
  have hz : 1 ≤ (2 + D) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl : 0 ≤ Real.log ((2 + D) / δ) := Real.log_nonneg hz
  have hbase : 2 + D ≤ (2 + D) / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < 2 + D) hbase
  have hx : 4096 * (N + 1) ≤ 2 ^ 149 * (2 + D) ^ 2 := by nlinarith [sq_nonneg D]
  have hh := Real.log_le_log (by positivity : 0 < 4096 * (N + 1)) hx
  rw [Real.log_mul (by norm_num : (2 : ℝ) ^ 149 ≠ 0) (by positivity), Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hq : Real.log (4096 * (N + 1)) / Real.log 2 ≤ 149 + 4 * Real.log ((2 + D) / δ) := by
    rw [div_le_iff₀ h2p]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) hl]
  have hn := (Nat.ceil_lt_add_one (div_nonneg
    (Real.log_nonneg (by linarith : 1 ≤ 4096 * (N + 1))) h2p.le)).le
  linarith

lemma pilotGroups_log_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) (s : ℕ) :
    (pilotGroups t s : ℝ) + 1 ≤ 1024 * logWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hN := stageSteps_work_upper t h0 h1 hR hG hε s
  have hJ := stages_algebra_upper t h0 h1 hR hG hε
  have hm := mul_le_mul_of_nonneg_right hJ (by linarith :
    0 ≤ OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t))
  have hND : (stageSteps t s : ℝ) ≤ 2 ^ 136 *
      (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) ^ 2 := by
    nlinarith only [hN, hm, hD]
  have hh := pilot_log_algebra (Nat.cast_nonneg (stageSteps t s)) hD hδ hδ1 hND
  unfold pilotGroups logWork
  push_cast
  linarith

lemma stageCalls_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    (hδ : 0 < t.δ) (hδ1 : t.δ < 1) (s : ℕ) :
    (stageCalls t s : ℝ) ≤ 2 ^ 321 *
      (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t ^ 4 := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hW := noiseWork_nonneg t hb.le hR.le hv hε.le
  have hL := (logWork_comparison t h0 h1 hR hG hε hδ hδ1).1
  have ht := trialCalls_work_upper t h0 h1 hR hG hε hv s
  have hJ := stages_log_upper t h0 h1 hR hG hε hδ hδ1
  have hp := pilotGroups_log_upper t h0 h1 hR hG hε hδ hδ1 s
  have ho := outerGroups_log_upper t h0 h1 hR hG hε hδ hδ1
  unfold stageCalls
  push_cast
  calc
    _ ≤ (2 ^ 292 * (1024 * logWork t) * (64 * logWork t) ^ 2 *
        (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t)) *
        (128 * logWork t) := by
      apply mul_le_mul _ ho (by positivity) (by positivity)
      exact ht.trans (by gcongr)
    _ = _ := by ring

lemma finalCalls_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (finalCalls t : ℝ) ≤ 2 ^ 69 *
      (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hW := noiseWork_nonneg t hb.le hR.le hv hε.le
  have hL := (logWork_comparison t h0 h1 hR hG hε hδ hδ1).1
  have hm := finalBatch_upper t hR.le hε hv
  have ho := outerGroups_log_upper t h0 h1 hR hG hε hδ hδ1
  have hq : 1 ≤ 1 + effectiveCurvature t * t.R := by linarith [mul_nonneg hb.le hR.le]
  have hq2 : 1 ≤ (1 + effectiveCurvature t * t.R) ^ 2 := one_le_pow₀ hq
  have hn : t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε ≤ noiseWork t := by
    unfold noiseWork
    have ha := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ t.σ ^ 2 / t.ε ^ 2)
    have hb' := mul_le_mul_of_nonneg_right hq2 (by positivity : 0 ≤ t.v * t.R / t.ε)
    ring_nf at ha hb' ⊢
    linarith only [ha, hb']
  have hm' : (finalBatch t : ℝ) ≤ 2 ^ 61 *
      (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) := by
    linarith
  have hh := mul_le_mul hm' ho (by positivity) (by positivity)
  have hone : 1 ≤ (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t - 1)
      (by linarith : 0 ≤ logWork t - 1)]
  unfold finalCalls
  push_cast
  nlinarith only [hh, hone]

lemma runCalls_uniform (t : Tuning) (U : ℝ) (hU : ∀ s, (stageCalls t s : ℝ) ≤ U)
    (s n : ℕ) : (runCalls t s n : ℝ) ≤ (n : ℝ) * U + finalCalls t := by
  induction n generalizing s with
  | zero => simp [runCalls]
  | succ n ih =>
    simp only [runCalls, Nat.cast_add, Nat.cast_succ]
    linarith [ih (s + 1), hU s]

lemma runCalls_work_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (runCalls t 0 (stages t) : ℝ) ≤ 2 ^ 328 *
      (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t ^ 5 := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le hR.le hG hε
  have hW := noiseWork_nonneg t hb.le hR.le hv hε.le
  have hL := (logWork_comparison t h0 h1 hR hG hε hδ hδ1).1
  have hJ := stages_log_upper t h0 h1 hR hG hε hδ hδ1
  have hh := runCalls_uniform t _ (stageCalls_work_upper t h0 h1 hR hG hε hv hδ hδ1) 0 (stages t)
  have hf := finalCalls_work_upper t h0 h1 hR hG hε hv hδ hδ1
  have hp : logWork t ≤ logWork t ^ 5 := by
    have hn := one_le_pow₀ hL (n := 4)
    nlinarith [mul_le_mul_of_nonneg_left hn (by linarith : 0 ≤ logWork t)]
  have hm := mul_le_mul_of_nonneg_right hJ (by positivity : 0 ≤ 2 ^ 321 *
    (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t ^ 4)
  have hfp := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 ^ 69 *
    (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t))
  have hn : 0 ≤ (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t ^ 5 := by positivity
  nlinarith only [hh, hf, hm, hfp, hn]

noncomputable def radiusWork (t : Tuning) (R : ℝ) : ℝ :=
  (t.L0 + t.L1 * t.G) * (1 + t.L1 * R) ^ 2 * R / t.ε + (1 + t.L1 * R) ^ 4

noncomputable def radiusNoise (t : Tuning) (R : ℝ) : ℝ :=
  (1 + t.L1 * R) * t.σ ^ 2 / t.ε ^ 2 + (1 + t.L1 * R) ^ 2 * t.v * R / t.ε

noncomputable def radiusLog (t : Tuning) (R : ℝ) : ℝ :=
  1 + Real.log ((2 + radiusWork t R) / t.δ)

lemma radiusWork_one (t : Tuning) (R : ℝ) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) : 1 ≤ radiusWork t R := by
  have hq : 1 ≤ 1 + t.L1 * R := by linarith [mul_nonneg h1 hR.le]
  have hh := one_le_pow₀ hq (n := 4)
  have hn : 0 ≤ (t.L0 + t.L1 * t.G) * (1 + t.L1 * R) ^ 2 * R / t.ε := by positivity
  unfold radiusWork
  linarith

lemma radius_conversion (t : Tuning) (R : ℝ) (htR : t.R = 2 * R)
    (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (hv : 0 ≤ t.v) :
    OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) ≤ 16 * radiusWork t R ∧
      noiseWork t ≤ 8 * radiusNoise t R := by
  have htR0 : 0 < t.R := by rw [htR]; positivity
  have hb := effectiveCurvature_bounds t h0 h1 hG htR0
  have hb0 := hb.1
  have hq : 1 + effectiveCurvature t * t.R ≤ 2 * (1 + t.L1 * R) := by
    nlinarith [hb.2.1]
  have hq0 : 0 ≤ 1 + effectiveCurvature t * t.R := by positivity
  have hC : t.L0 + effectiveCurvature t * t.G ≤ 2 * (t.L0 + t.L1 * t.G) := by
    nlinarith [hb.2.2, mul_nonneg h1 hG]
  constructor
  · unfold OracleTemplate.ProjectedClippedExtragradient.deterministicWork geometry
    change (t.L0 + effectiveCurvature t * t.G) * (1 + effectiveCurvature t * t.R) ^ 2 * t.R / t.ε +
      (1 + effectiveCurvature t * t.R) ^ 4 ≤ _
    calc
      _ ≤ (2 * (t.L0 + t.L1 * t.G)) * (2 * (1 + t.L1 * R)) ^ 2 * (2 * R) / t.ε +
          (2 * (1 + t.L1 * R)) ^ 4 := by
        gcongr
        exact htR.le
      _ = _ := by unfold radiusWork; ring
  · have hs : 0 ≤ (1 + t.L1 * R) * t.σ ^ 2 / t.ε ^ 2 := by positivity
    unfold noiseWork
    calc
      _ ≤ (2 * (1 + t.L1 * R)) * t.σ ^ 2 / t.ε ^ 2 +
          (2 * (1 + t.L1 * R)) ^ 2 * t.v * (2 * R) / t.ε := by
        gcongr
        exact htR.le
      _ ≤ _ := by
        unfold radiusNoise
        ring_nf at hs ⊢
        linarith only [hs]

lemma radius_log_conversion (t : Tuning) (R : ℝ) (htR : t.R = 2 * R)
    (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (hv : 0 ≤ t.v) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    1 ≤ radiusLog t R ∧ logWork t ≤ 4 * radiusLog t R := by
  have hD := radiusWork_one t R h0 h1 hR hG hε
  have htR0 : 0 < t.R := by rw [htR]; positivity
  have hb := (effectiveCurvature_bounds t h0 h1 hG htR0).1
  have hDg := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le htR0.le hG hε
  have hc := (radius_conversion t R htR h0 h1 hR hG hε hv).1
  have hz : 1 ≤ (2 + radiusWork t R) / t.δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl := Real.log_nonneg hz
  have hx : (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) / t.δ ≤
      16 * ((2 + radiusWork t R) / t.δ) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ]
    linarith
  have hh := Real.log_le_log (by positivity :
    0 < (2 + OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t)) / t.δ) hx
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity)] at hh
  have h16 : Real.log (16 : ℝ) ≤ 3 := by
    have he : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  unfold radiusLog logWork
  constructor <;> linarith

lemma runCalls_radius_upper (t : Tuning) (R : ℝ) (htR : t.R = 2 * R)
    (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (hv : 0 ≤ t.v) (hδ : 0 < t.δ) (hδ1 : t.δ < 1) :
    (runCalls t 0 (stages t) : ℝ) ≤ 2 ^ 350 *
      ((t.L0 + t.L1 * t.G + t.v) * R * (1 + t.L1 * R) ^ 2 / t.ε +
        (1 + t.L1 * R) ^ 4 + t.σ ^ 2 * (1 + t.L1 * R) / t.ε ^ 2) *
      (1 + Real.log ((2 + (t.L0 + t.L1 * t.G) * R * (1 + t.L1 * R) ^ 2 / t.ε +
        (1 + t.L1 * R) ^ 4) / t.δ)) ^ 5 := by
  have htR0 : 0 < t.R := by rw [htR]; positivity
  have hb := (effectiveCurvature_bounds t h0 h1 hG htR0).1
  have hD := OracleTemplate.ProjectedClippedExtragradient.deterministicWork_one (geometry t) h0.le hb.le htR0.le hG hε
  have hW := noiseWork_nonneg t hb.le htR0.le hv hε.le
  have hL := (logWork_comparison t h0 h1 htR0 hG hε hδ hδ1).1
  have hN : 0 ≤ radiusNoise t R := by unfold radiusNoise; positivity
  have hDr := radiusWork_one t R h0 h1 hR hG hε
  have hc := radius_conversion t R htR h0 h1 hR hG hε hv
  have hl := radius_log_conversion t R htR h0 h1 hR hG hε hv hδ hδ1
  have hLr : 0 ≤ radiusLog t R := by linarith [hl.1]
  have hs : OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t ≤
      16 * (radiusWork t R + radiusNoise t R) := by linarith [hc.1, hc.2]
  calc
    _ ≤ 2 ^ 328 * (OracleTemplate.ProjectedClippedExtragradient.deterministicWork (geometry t) + noiseWork t) * logWork t ^ 5 :=
      runCalls_work_upper t h0 h1 htR0 hG hε hv hδ hδ1
    _ ≤ 2 ^ 328 * (16 * (radiusWork t R + radiusNoise t R)) * (4 * radiusLog t R) ^ 5 := by gcongr; exact hl.2
    _ ≤ 2 ^ 350 * (radiusWork t R + radiusNoise t R) * radiusLog t R ^ 5 := by
      have hn : 0 ≤ (radiusWork t R + radiusNoise t R) * radiusLog t R ^ 5 := by positivity
      nlinarith only [hn]
    _ = _ := by
      unfold radiusLog radiusWork radiusNoise
      congr 2 <;> ring

end LongTails.Proofs.GapNoiseBudget
