import LongTails.Algorithms.GapNoisePastExtragradient
import LongTails.Proofs.ProjectedClippedTuning
import LongTails.Proofs.GapNoiseTwoCenter

namespace LongTails.Proofs.GapNoiseTuning

open LongTails.Algorithms.GapNoisePastExtragradient

lemma effectiveCurvature_bounds (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hG : 0 ≤ t.G) (hR : 0 < t.R) :
    0 < effectiveCurvature t ∧ effectiveCurvature t * t.R ≤ 1 + t.L1 * t.R ∧
      t.L0 + effectiveCurvature t * t.G ≤ 2 * t.L0 + t.L1 * t.G :=
  GapNoiseTwoCenter.positive_curvature_envelope h0 h1 hG hR

lemma stages_pos (t : Tuning) : 0 < stages t :=
  OracleTemplate.ProjectedClippedExtragradient.stageCount_pos (geometry t)

lemma stageRadius_pos (t : Tuning) (hR : 0 < t.R) (s : ℕ) :
    0 < OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s :=
  OracleTemplate.ProjectedClippedExtragradient.radius_pos (geometry t) hR s

lemma stageRegularization_pos (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε) (s : ℕ) :
    0 < OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s :=
  OracleTemplate.ProjectedClippedExtragradient.regularization_pos (geometry t) hR hε s

lemma stageScale_lower (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤ stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hc := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t)
    h0 hb.le hR.le hG hε.le
  have hr := stageRegularization_pos t hR hε s
  have hs := OracleTemplate.ProjectedClippedExtragradient.localScale_lower (geometry t)
    hc.le hb.le hR hε s
  unfold stageScale
  nlinarith

lemma stageScale_pos (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) : 0 < stageScale t s :=
  (stageRegularization_pos t hR hε s).trans_le (stageScale_lower t h0 h1 hR hG hε s)

lemma stageScale_smoothness (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    t.L0 + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s +
      effectiveCurvature t * t.ε + 67 * effectiveCurvature t *
        OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ≤ stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hr := stageRegularization_pos t hR hε s
  have hd := stageRadius_pos t hR s
  have hs := OracleTemplate.ProjectedClippedExtragradient.localScale_smoothness
    (geometry t) h0.le hb.le hR hG hε s
  change t.L0 + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s +
    effectiveCurvature t * t.ε + 3 * effectiveCurvature t *
      OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
      OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s ≤ _ at hs
  unfold stageScale
  have hn : 0 ≤ effectiveCurvature t *
      OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
      OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s := by positivity
  nlinarith [mul_nonneg hb.le hε.le]

lemma stageScale_root_envelope (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    effectiveCurvature t * (OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) + t.ε) ≤
      stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hC := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hr := OracleTemplate.ProjectedClippedExtragradient.rootBound_curvature
    (geometry t) h0.le hb.le hR.le hG hε.le
  have hs := (OracleTemplate.ProjectedClippedExtragradient.scale_component_bounds
    (geometry t) hC.le hb.le hR hε s).1
  change t.L0 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) +
    effectiveCurvature t * t.ε ≤ 16 * OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) at hr
  change 2 ^ 20 * OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) *
    (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ≤ _ at hs
  have hn := mul_nonneg hC.le (mul_nonneg hb.le hd.le)
  unfold stageScale
  nlinarith

lemma stageScale_coercivity (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    2 * effectiveCurvature t * (OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) + t.ε +
      65 * OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s +
      132 * (t.L0 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)) *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ≤ stageScale t s := by
  let b := effectiveCurvature t
  let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s
  let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s
  let M := OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)
  have hb : 0 < b := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < d := stageRadius_pos t hR s
  have hr : 0 < r := stageRegularization_pos t hR hε s
  have hM : 0 ≤ M := by dsimp [M, OracleTemplate.ProjectedClippedExtragradient.rootBound, geometry]; positivity
  have hco := OracleTemplate.ProjectedClippedExtragradient.localScale_coercivity
    (geometry t) h0.le hb.le hR hG hε s
  change 4 * b * (M + t.ε + 3 * r * d + 12 * (t.L0 + b * M) * d) ≤ _ at hco
  have hB : M + t.ε + 65 * r * d + 132 * (t.L0 + b * M) * d ≤
      32 * (M + t.ε + 3 * r * d + 12 * (t.L0 + b * M) * d) := by
    nlinarith [mul_nonneg hr.le hd.le, mul_nonneg (by positivity : 0 ≤ t.L0 + b * M) hd.le]
  have hm := mul_le_mul_of_nonneg_left hB hb.le
  have hs : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.localScale (geometry t) s := by
    have hn : 0 ≤ 4 * b * (M + t.ε + 3 * r * d + 12 * (t.L0 + b * M) * d) := by positivity
    exact hn.trans hco
  change 2 * b * (M + t.ε + 65 * r * d + 132 * (t.L0 + b * M) * d) ≤
    2 ^ 40 * OracleTemplate.ProjectedClippedExtragradient.localScale (geometry t) s
  nlinarith

lemma stageScale_distance (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * effectiveCurvature t *
      (66 * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ^ 2 ≤
      4 * stageScale t s * (OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s /
        (1 + 132 * effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s)) := by
  let b := effectiveCurvature t
  let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s
  let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s
  have hb : 0 < b := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < d := stageRadius_pos t hR s
  have hr : 0 < r := stageRegularization_pos t hR hε s
  have hC := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hs := (OracleTemplate.ProjectedClippedExtragradient.scale_component_bounds
    (geometry t) hC.le hb.le hR hε s).2
  change 2 ^ 20 * r * (1 + b * d) ^ 4 ≤ _ at hs
  have hq : 0 ≤ b * d := mul_nonneg hb.le hd.le
  have hpoly : 1089 * (b * d) * (1 + 132 * (b * d)) ≤ 2 ^ 20 * (1 + b * d) ^ 4 := by
    nlinarith [sq_nonneg (b * d), sq_nonneg ((b * d) ^ 2), mul_nonneg hq (sq_nonneg (b * d))]
  have hm := mul_le_mul_of_nonneg_left hpoly hr.le
  have hs0 : 0 ≤ OracleTemplate.ProjectedClippedExtragradient.localScale (geometry t) s :=
    (by positivity : 0 ≤ 2 ^ 20 * r * (1 + b * d) ^ 4).trans hs
  have hbound : r * (1089 * (b * d) * (1 + 132 * (b * d))) ≤ stageScale t s := by
    unfold stageScale
    nlinarith
  change r * b * (66 * d) ^ 2 ≤ 4 * stageScale t s * (d / (1 + 132 * b * d))
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 1 + 132 * b * d)]
  convert mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ 4 * d) using 1 <;> ring

lemma stageScale_operator_slope (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    4 * (t.L0 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)) ≤
      stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hC := OracleTemplate.ProjectedClippedExtragradient.curvature_pos (geometry t) h0 hb.le hR.le hG hε.le
  have hr := OracleTemplate.ProjectedClippedExtragradient.rootBound_curvature
    (geometry t) h0.le hb.le hR.le hG hε.le
  have hs := (OracleTemplate.ProjectedClippedExtragradient.scale_component_bounds
    (geometry t) hC.le hb.le hR hε s).1
  change t.L0 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) +
    effectiveCurvature t * t.ε ≤ 16 * OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) at hr
  change 2 ^ 20 * OracleTemplate.ProjectedClippedExtragradient.curvature (geometry t) *
    (1 + effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) ≤ _ at hs
  have hn := mul_nonneg hC.le (mul_nonneg hb.le hd.le)
  unfold stageScale
  nlinarith [mul_nonneg hb.le hε.le]

lemma stageScale_query {E : Type*} [NormedAddCommGroup E]
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (s : ℕ) (anchor center x : E)
    (ha : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * ‖center - anchor‖ ≤
      t.ε + 3 * OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s)
    (hx : ‖x - center‖ ≤ 64 * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) :
    t.L0 + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s +
      effectiveCurvature t * OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
        ‖x - anchor‖ ≤ stageScale t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hr := stageRegularization_pos t hR hε s
  have ht := norm_sub_le_norm_sub_add_norm_sub x center anchor
  have ht' := mul_le_mul_of_nonneg_left ht hr.le
  have hx' := mul_le_mul_of_nonneg_left hx hr.le
  have hb' := mul_le_mul_of_nonneg_left (show
      OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * ‖x - anchor‖ ≤
        t.ε + 67 * OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
          OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s by nlinarith) hb.le
  have hs := stageScale_smoothness t h0 h1 hR hG hε s
  nlinarith

lemma rootBound_ge (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) :
    t.G ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hn : 0 ≤ 16 * (t.L0 + effectiveCurvature t * t.G) * t.R +
      t.ε * (1 + 8 * effectiveCurvature t * t.R) := by positivity
  change t.G ≤ t.G + 16 * (t.L0 + effectiveCurvature t * t.G) * t.R +
    t.ε * (1 + 8 * effectiveCurvature t * t.R)
  linarith

lemma stageScale_oracle_shift {E : Type*} [NormedAddCommGroup E]
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (s : ℕ) (anchor center x Fs : E) (hFs : ‖Fs‖ ≤ t.G)
    (ha : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s * ‖center - anchor‖ ≤
      t.ε + 3 * OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
        OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s)
    (hx : ‖x - center‖ ≤ 64 * OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s) :
    effectiveCurvature t * (‖Fs‖ + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s *
      ‖x - anchor‖) ≤ stageScale t s := by
  let b := effectiveCurvature t
  let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s
  let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s
  let M := OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)
  have hb : 0 < b := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hr : 0 < r := stageRegularization_pos t hR hε s
  have hd : 0 < d := stageRadius_pos t hR s
  have hM : t.G ≤ M := rootBound_ge t h0 h1 hR hG hε
  have hdist := norm_sub_le_norm_sub_add_norm_sub x center anchor
  have hm := mul_le_mul_of_nonneg_left hdist hr.le
  have hx' := mul_le_mul_of_nonneg_left hx hr.le
  have hbound : ‖Fs‖ + r * ‖x - anchor‖ ≤ M + t.ε + 67 * r * d := by
    change r * ‖center - anchor‖ ≤ t.ε + 3 * r * d at ha
    change r * ‖x - center‖ ≤ r * (64 * d) at hx'
    nlinarith
  have hbound' := mul_le_mul_of_nonneg_left hbound hb.le
  have hco := stageScale_coercivity t h0 h1 hR hG hε s
  change 2 * b * (M + t.ε + 65 * r * d + 132 * (t.L0 + b * M) * d) ≤ _ at hco
  have hM0 := hG.trans hM
  have hn : 0 ≤ b * (t.L0 + b * M) * d := by positivity
  have hr' : 0 ≤ b * r * d := by positivity
  have hε' : 0 ≤ b * t.ε := by positivity
  have hM' : 0 ≤ b * M := by positivity
  change b * (‖Fs‖ + r * ‖x - anchor‖) ≤ _
  nlinarith

lemma stageSteps_pos (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) : 0 < stageSteps t s := by
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hr := stageRegularization_pos t hR hε s
  unfold stageSteps
  exact Nat.ceil_pos.mpr (by positivity)

lemma stageShift_pos (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (s : ℕ) : 0 < stageShift t s := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd := stageRadius_pos t hR s
  have hJ : 0 < (stages t : ℝ) := Nat.cast_pos.mpr (stages_pos t)
  unfold stageShift
  positivity

lemma stageBatch_pos (t : Tuning) (s : ℕ) : 0 < stageBatch t s := by
  unfold stageBatch
  omega

lemma pilotBatch_pos (t : Tuning) (s : ℕ) : 0 < pilotBatch t s := by
  unfold pilotBatch
  omega

lemma finalBatch_pos (t : Tuning) : 0 < finalBatch t := by
  unfold finalBatch
  omega

lemma pilotBatch_relative (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    2 ^ 20 * (t.σ ^ 2 / (stageScale t s / effectiveCurvature t) ^ 2 +
      t.v * (66 * t.R) / (stageScale t s / effectiveCurvature t)) ≤ (pilotBatch t s : ℝ) := by
  have hb := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hc : 2 ^ 40 * (t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 +
      t.v * t.R * effectiveCurvature t / stageScale t s) ≤ (pilotBatch t s : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right _ _))
  have ha : 0 ≤ t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 := by positivity
  have hn : 0 ≤ t.v * t.R * effectiveCurvature t / stageScale t s := by positivity
  have he : t.σ ^ 2 / (stageScale t s / effectiveCurvature t) ^ 2 +
      t.v * (66 * t.R) / (stageScale t s / effectiveCurvature t) =
      t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 +
        66 * (t.v * t.R * effectiveCurvature t / stageScale t s) := by field_simp
  rw [he]
  nlinarith

lemma pilotGroups_confidence (t : Tuning) (s : ℕ) :
    (1 / 2 : ℝ) ^ (pilotGroups t s + 1) ≤ 1 / (16384 * ((stageSteps t s : ℝ) + 1)) := by
  have hu : 0 < 4096 * ((stageSteps t s : ℝ) + 1) := by positivity
  have hh := OracleTemplate.ProjectedClippedExtragradient.dyadic_cover hu
  unfold pilotGroups
  rw [one_div_pow, pow_succ, pow_succ]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

lemma outerGroups_confidence (t : Tuning) (hδ : 0 < t.δ) :
    (1 / 2 : ℝ) ^ (outerGroups t + 1) ≤ t.δ / (2 * stages t) := by
  have hh := OracleTemplate.ProjectedClippedExtragradient.repetitions_confidence (geometry t) hδ
  change (1 / 2 : ℝ) ^ outerGroups t ≤ t.δ / (2 * stages t) at hh
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (outerGroups t)]

lemma stageSteps_lower (t : Tuning) (s : ℕ) :
    2 ^ 48 * stageScale t s / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s ≤
      (stageSteps t s : ℝ) := Nat.le_ceil _

lemma stageSteps_upper (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (s : ℕ) :
    (stageSteps t s : ℝ) ≤ 2 ^ 49 * stageScale t s /
      OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s := by
  have hS := stageScale_pos t h0 h1 hR hG hε s
  have hr := stageRegularization_pos t hR hε s
  have hrS := stageScale_lower t h0 h1 hR hG hε s
  have hratio : 1 ≤ stageScale t s / OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s :=
    (le_div_iff₀ hr).mpr (by simpa using hrS)
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 ^ 48 * stageScale t s /
    OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s)).le
  unfold stageSteps
  simp only [mul_div_assoc] at hc ⊢
  nlinarith

lemma stageBatch_terms (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (s : ℕ) :
    let b := effectiveCurvature t
    let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s
    let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s
    let S := stageScale t s
    2 ^ 120 * (1 + b * d) * t.σ ^ 2 ≤ (stageBatch t s : ℝ) * r * S * d ^ 2 ∧
      2 ^ 120 * (1 + b * d) * t.v ≤ (stageBatch t s : ℝ) * S * stageShift t s := by
  dsimp only
  let b := effectiveCurvature t
  let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) s
  let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) s
  let S := stageScale t s
  let τ := stageShift t s
  have hb : 0 < b := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < d := stageRadius_pos t hR s
  have hr : 0 < r := stageRegularization_pos t hR hε s
  have hS : 0 < S := stageScale_pos t h0 h1 hR hG hε s
  have hτ : 0 < τ := stageShift_pos t h0 h1 hR hG s
  have hbudget : 2 ^ 120 * (1 + b * d) * (t.σ ^ 2 / (r * S * d ^ 2) + t.v / (S * τ)) ≤
      (stageBatch t s : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hn1 : 0 ≤ 2 ^ 120 * (1 + b * d) * (t.σ ^ 2 / (r * S * d ^ 2)) := by positivity
  have hn2 : 0 ≤ 2 ^ 120 * (1 + b * d) * (t.v / (S * τ)) := by positivity
  have hfirst : 2 ^ 120 * (1 + b * d) * (t.σ ^ 2 / (r * S * d ^ 2)) ≤ (stageBatch t s : ℝ) := by nlinarith
  have hsecond : 2 ^ 120 * (1 + b * d) * (t.v / (S * τ)) ≤ (stageBatch t s : ℝ) := by nlinarith
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < r * S * d ^ 2)] at hfirst
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < S * τ)] at hsecond
  constructor <;> nlinarith

lemma enlarge_generalized_parameter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → E} {L0 L1 b : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 L1)
    (hb : L1 ≤ b) : OracleTemplate.GeneralizedMonotone.Hyp F L0 b := by
  refine ⟨hF.L0_pos, hF.L1_nonneg.trans hb, hF.cont, hF.mono, ?_⟩
  intro x y M hM
  have hx := hM 0 (by simp)
  simp only [zero_smul, add_zero] at hx
  have hM0 := (norm_nonneg (F x)).trans hx
  have h1 := mul_le_mul_of_nonneg_right hb hM0
  have h2 := mul_le_mul_of_nonneg_right (show L0 + L1 * M ≤ L0 + b * M by linarith)
    (norm_nonneg (x - y))
  exact (hF.lip x y M hM).trans h2

lemma probe_radius_bounds {b d : ℝ} (hb : 0 ≤ b) (hd : 0 < d) :
    0 < d / (1 + 132 * b * d) ∧ d / (1 + 132 * b * d) ≤ d ∧
      b * (d / (1 + 132 * b * d)) ≤ 1 / 2 := by
  have hden : 0 < 1 + 132 * b * d := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hb (sq_nonneg d)]
  · rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [mul_nonneg hb hd.le]

lemma shift_geometry {d R J b τ : ℝ} (hd : 0 < d) (hR : 0 < R) (hdR : d ≤ R)
    (hJ : 1 ≤ J) (hb : 0 ≤ b)
    (hτ : τ = d / (2 ^ 100 * J * R * (1 + b * R))) :
    τ ≤ 1 / 2 ∧ τ * R ≤ d / 512 ∧ τ * R ≤ (d / (1 + 132 * b * d)) / 2 := by
  have hJpos : 0 < J := by linarith
  have hq : 0 ≤ b * R := mul_nonneg hb hR.le
  have hden : 0 < 2 ^ 100 * J * (1 + b * R) := by positivity
  have hsmall : 0 < 2 * (1 + 132 * b * d) := by positivity
  have he : τ * R = d / (2 ^ 100 * J * (1 + b * R)) := by rw [hτ]; field_simp
  have hJq := mul_le_mul_of_nonneg_right hJ (by positivity : 0 ≤ 1 + b * R)
  have hbd := mul_le_mul_of_nonneg_left hdR hb
  have hden512 : 512 ≤ 2 ^ 100 * J * (1 + b * R) := by nlinarith
  have hdenprobe : 2 * (1 + 132 * b * d) ≤ 2 ^ 100 * J * (1 + b * R) := by nlinarith
  have h512 : τ * R ≤ d / 512 := by
    rw [he]
    exact div_le_div_of_nonneg_left hd.le (by norm_num) hden512
  refine ⟨by nlinarith, h512, ?_⟩
  rw [he]
  calc
    _ ≤ d / (2 * (1 + 132 * b * d)) := div_le_div_of_nonneg_left hd.le hsmall hdenprobe
    _ = _ := by field_simp

lemma shift_floor_bound {d R J q A B t : ℝ} (hd : 0 < d) (hR : 0 < R) (hdR : d ≤ R)
    (hJ : 1 ≤ J) (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAbound : A ≤ 2 ^ 20 * J * d) (hBbound : B ≤ R)
    (ht : t = d / (2 ^ 100 * J * R * (1 + q))) :
    t ^ 2 * (A + B) ^ 2 + 2 * t * A * B ≤ d ^ 2 / 2 ^ 78 := by
  have hJpos : 0 < J := by linarith
  have hden : 0 < 2 ^ 100 * J * R * (1 + q) := by positivity
  have htp : 0 < t := by rw [ht]; positivity
  have hAR : A ≤ 2 ^ 20 * J * R :=
    hAbound.trans (mul_le_mul_of_nonneg_left hdR (by positivity))
  have hTA : t * A ≤ d / 2 ^ 80 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ hden]
    have hm := mul_le_mul_of_nonneg_left hAR hd.le
    have hn := mul_nonneg (by positivity : 0 ≤ 2 ^ 20 * J * d * R) hq
    nlinarith
  have hTBJ : J * (t * B) ≤ d / 2 ^ 100 := by
    rw [ht, div_mul_eq_mul_div, ← mul_div_assoc, div_le_iff₀ hden]
    have hm := mul_le_mul_of_nonneg_left hBbound (mul_nonneg hJpos.le hd.le)
    have hn := mul_nonneg (by positivity : 0 ≤ J * d * R) hq
    nlinarith
  have hTB : t * B ≤ d / 2 ^ 100 := by
    have hm := mul_le_mul_of_nonneg_right hJ (mul_nonneg htp.le hB)
    nlinarith
  have hsum : t * A + t * B ≤ d / 2 ^ 79 := by nlinarith
  have hcross : t * A * B ≤ d ^ 2 / 2 ^ 80 := by
    have hm := mul_le_mul_of_nonneg_right hAbound (mul_nonneg htp.le hB)
    have hn := mul_le_mul_of_nonneg_right hTBJ (by positivity : 0 ≤ 2 ^ 20 * d)
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ t * A + t * B) hsum 2
  nlinarith [sq_nonneg d]

lemma batch_noise_bound {K k σ batch r S d : ℝ} (hS : 0 < S) (hm : 0 < batch)
    (hK : K ≤ 2 ^ 20 * k) (hnoise : 2 ^ 120 * k * σ ^ 2 ≤ batch * r * S * d ^ 2) :
    K * (1 / (16384 * S)) ^ 2 * σ ^ 2 / batch ≤ r * d ^ 2 / (2 ^ 128 * S) := by
  have hKσ := mul_le_mul_of_nonneg_right hK (sq_nonneg σ)
  have hraw : K * σ ^ 2 ≤ (batch * r * S * d ^ 2) / 2 ^ 100 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 100)]
    nlinarith
  calc
    _ = (K * σ ^ 2) / (2 ^ 28 * S ^ 2 * batch) := by field_simp; ring
    _ ≤ ((batch * r * S * d ^ 2) / 2 ^ 100) / (2 ^ 28 * S ^ 2 * batch) :=
      div_le_div_of_nonneg_right hraw (by positivity)
    _ = _ := by field_simp

lemma batch_gap_bound {K k v batch S t : ℝ} (hS : 0 < S) (hk : 0 ≤ k) (hv : 0 ≤ v)
    (hK : K ≤ 2 ^ 20 * k) (hgap : 2 ^ 120 * k * v ≤ batch * S * t) :
    K * (1 / (16384 * S)) * v ≤ batch * t := by
  have hKv := mul_le_mul_of_nonneg_right hK hv
  have hkv := mul_nonneg hk hv
  have he : K * (1 / (16384 * S)) * v = (K * v) / (16384 * S) := by ring
  rw [he, div_le_iff₀ (by positivity : 0 < 16384 * S)]
  nlinarith

lemma initial_batch_reserve {D S r d τ v gap σ batch k : ℝ}
    (hS : 0 < S) (hD : S ≤ D) (hrS : r ≤ S) (hm : 0 < batch)
    (hk : 1 ≤ k) (hv : 0 ≤ v) (hgap : 0 ≤ gap)
    (hnoise : 2 ^ 120 * k * σ ^ 2 ≤ batch * r * S * d ^ 2)
    (hbatchGap : 2 ^ 120 * k * v ≤ batch * S * τ)
    (hnormalized : τ * S * gap ≤ D ^ 2 * d ^ 2) :
    24 * (1 / (16384 * D)) ^ 2 * ((σ ^ 2 + v * gap) / batch) ≤ d ^ 2 / 16 := by
  have hDpos := hS.trans_le hD
  have hrs : r * S ≤ D ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hrS hS.le
    have hs := pow_le_pow_left₀ hS.le hD 2
    nlinarith
  have hupper := mul_le_mul_of_nonneg_left hrs (by positivity : 0 ≤ batch * d ^ 2)
  have hkσ := mul_le_mul_of_nonneg_right hk (sq_nonneg σ)
  have hσ : 2 ^ 120 * σ ^ 2 ≤ batch * D ^ 2 * d ^ 2 := by nlinarith
  have hnorm := mul_le_mul_of_nonneg_left hnormalized hm.le
  have hvbatch := mul_le_mul_of_nonneg_right hbatchGap hgap
  have hkgap := mul_le_mul_of_nonneg_right hk (mul_nonneg hv hgap)
  have hg : 2 ^ 120 * v * gap ≤ batch * D ^ 2 * d ^ 2 := by nlinarith
  have hV : 2 ^ 119 * (σ ^ 2 + v * gap) ≤ batch * D ^ 2 * d ^ 2 := by nlinarith
  have hn : 0 ≤ σ ^ 2 + v * gap := by positivity
  have he : 24 * (1 / (16384 * D)) ^ 2 * ((σ ^ 2 + v * gap) / batch) =
      24 * (σ ^ 2 + v * gap) / (2 ^ 28 * D ^ 2 * batch) := by field_simp; ring
  rw [he, div_le_iff₀ (by positivity : 0 < 2 ^ 28 * D ^ 2 * batch)]
  nlinarith

lemma large_initial_gap_bound {b d S D τ R gap : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hS : 0 < S) (hSD : S ≤ D) (hτ : 0 ≤ τ) (hgap : b * gap ≤ 2 * R * D)
    (hshift : τ * R ≤ d / 512) (hlarge : 1 / 256 ≤ b * d) :
    τ * S * gap ≤ D ^ 2 * d ^ 2 := by
  have hD : 0 < D := hS.trans_le hSD
  have h1 := mul_le_mul_of_nonneg_left hgap (mul_nonneg hτ hS.le)
  have h2 := mul_le_mul_of_nonneg_right hlarge hd.le
  have h3 : 2 * τ * R ≤ b * d ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hS.le hD.le)
  have h5 := mul_le_mul_of_nonneg_right hSD hD.le
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ b * d ^ 2)
  apply (mul_le_mul_iff_right₀ hb).mp
  nlinarith

lemma initial_epsilon_bound {d R J r S ε q : ℝ} (hd : 0 ≤ d) (hR : 0 < R)
    (hdR : d ≤ R) (hJ : 0 < J) (hr : 0 < r) (hrS : r ≤ S) (hq : 0 ≤ q)
    (hε : ε = 2 ^ 20 * J * r * d) :
    (d / (2 ^ 100 * J * R * (1 + q))) * ε * (1 + 8 * q) * d / S ≤ d ^ 2 / 2 ^ 77 := by
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hden : 0 < 1 + q := by positivity
  have hd' : d / R ≤ 1 := (div_le_one hR).mpr hdR
  have hq' : (1 + 8 * q) / (1 + q) ≤ 8 := by
    rw [div_le_iff₀ hden]
    linarith
  calc
    _ ≤ (d / (2 ^ 100 * J * R * (1 + q))) * ε * (1 + 8 * q) * d / r :=
      div_le_div_of_nonneg_left (by positivity) hr hrS
    _ = d ^ 2 * (d / R) * ((1 + 8 * q) / (1 + q)) / 2 ^ 80 := by
      rw [hε]
      field_simp
    _ ≤ d ^ 2 * 1 * 8 / 2 ^ 80 := by gcongr
    _ = d ^ 2 / 2 ^ 77 := by ring

lemma small_initial_gap_bound {d R J r S ε q τ gap : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hdR : d ≤ R) (hJ : 1 ≤ J) (hr : 0 < r) (hrS : r ≤ S) (hq : 0 ≤ q)
    (hε : ε = 2 ^ 20 * J * r * d) (hτ : τ = d / (2 ^ 100 * J * R * (1 + q)))
    (hgap : gap ≤ ε * R + 3 * S * R * d + ε * (1 + 8 * q) * d) :
    τ * gap ≤ S * d ^ 2 := by
  have hJpos : 0 < J := by linarith
  have hS : 0 < S := hr.trans_le hrS
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have ht : τ ≤ d / (2 ^ 100 * J * R) := by
    rw [hτ]
    apply div_le_div_of_nonneg_left hd.le (by positivity)
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 ^ 100 * J * R) hq]
  have hfirst : τ * ε * R ≤ S * d ^ 2 / 2 ^ 80 := by
    have hm := mul_le_mul_of_nonneg_right ht (mul_nonneg hε0 hR.le)
    have he : (d / (2 ^ 100 * J * R)) * (ε * R) = r * d ^ 2 / 2 ^ 80 := by
      rw [hε]
      field_simp
    rw [he] at hm
    have hr' := mul_le_mul_of_nonneg_right hrS (sq_nonneg d)
    nlinarith
  have hτR : τ * R ≤ d / 2 ^ 100 := by
    have hm := mul_le_mul_of_nonneg_right ht hR.le
    have he : d / (2 ^ 100 * J * R) * R = d / (2 ^ 100 * J) := by field_simp
    rw [he] at hm
    have hd' : d / (2 ^ 100 * J) ≤ d / 2 ^ 100 :=
      div_le_div_of_nonneg_left hd.le (by norm_num) (by nlinarith)
    exact hm.trans hd'
  have hsecond := mul_le_mul_of_nonneg_right hτR (by positivity : 0 ≤ 3 * S * d)
  have hthird := initial_epsilon_bound hd.le hR hdR hJpos hr hrS hq hε
  rw [← hτ, div_le_iff₀ hS] at hthird
  have htotal := mul_le_mul_of_nonneg_left hgap hτ0
  nlinarith [mul_nonneg hS.le (sq_nonneg d)]

lemma stage_accumulated_drift {r S d N floor noise : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hN : 0 ≤ N) (hNupper : N ≤ 2 ^ 49 * S / r)
    (hfloor : floor ≤ r * d ^ 2 / 2 ^ 78)
    (hnoise : noise ≤ r * d ^ 2 / (2 ^ 128 * S)) :
    N * (2 * (1 / (16384 * S)) * floor + noise) ≤ d ^ 2 / 4 := by
  have hfloor' := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ 2 * (1 / (16384 * S)))
  have hstep : 2 * (1 / (16384 * S)) * floor + noise ≤ r * d ^ 2 / (2 ^ 90 * S) := by
    have he : 2 * (1 / (16384 * S)) * (r * d ^ 2 / 2 ^ 78) +
        r * d ^ 2 / (2 ^ 128 * S) ≤ r * d ^ 2 / (2 ^ 90 * S) := by
      field_simp
      nlinarith [mul_nonneg hr.le (sq_nonneg d)]
    linarith
  calc
    _ ≤ N * (r * d ^ 2 / (2 ^ 90 * S)) := mul_le_mul_of_nonneg_left hstep hN
    _ ≤ (2 ^ 49 * S / r) * (r * d ^ 2 / (2 ^ 90 * S)) :=
      mul_le_mul_of_nonneg_right hNupper (div_nonneg (mul_nonneg hr.le (sq_nonneg d))
        (mul_nonneg (by norm_num) hS.le))
    _ = d ^ 2 / 2 ^ 41 := by field_simp
    _ ≤ d ^ 2 / 4 := by nlinarith [sq_nonneg d]

lemma stage_accumulated_weight {r S N : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hN : 2 ^ 48 * S / r ≤ N) : 2 ^ 23 ≤ (r / (2 ^ 25 * S)) * N := by
  have hh := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ r / (2 ^ 25 * S))
  have he : (r / (2 ^ 25 * S)) * (2 ^ 48 * S / r) = 2 ^ 23 := by field_simp
  rwa [he] at hh

lemma tuned_drift_sum {E : Type*} [NormedAddCommGroup E]
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hG : 0 ≤ t.G)
    (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (p anchor s : E)
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε)
    (hps : ‖p - s‖ ≤ t.R) :
    let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j
    let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j
    let S := stageScale t j
    let b := effectiveCurvature t
    let τ := stageShift t j
    let floor := r * (τ ^ 2 * ‖p - anchor + (p - s)‖ ^ 2 + 2 * τ * (‖p - anchor‖ * ‖p - s‖))
    (stageSteps t j : ℝ) * (2 * (1 / (16384 * S)) * floor +
      (30 + 4096 * b * (66 * d)) * (1 / (16384 * S)) ^ 2 * t.σ ^ 2 / stageBatch t j) ≤ d ^ 2 / 4 := by
  let r := OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j
  let d := OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j
  let S := stageScale t j
  let b := effectiveCurvature t
  let τ := stageShift t j
  have hr : 0 < r := stageRegularization_pos t hR hε j
  have hd : 0 < d := stageRadius_pos t hR j
  have hS : 0 < S := stageScale_pos t h0 h1 hR hG hε j
  have hb : 0 < b := (effectiveCurvature_bounds t h0 h1 hG hR).1
  have hJ : 1 ≤ (stages t : ℝ) := Nat.one_le_cast.mpr (stages_pos t)
  have hrd : r * d = t.ε / (2 ^ 20 * stages t) :=
    OracleTemplate.ProjectedClippedExtragradient.regularization_radius (geometry t) hR j
  have heps : t.ε = 2 ^ 20 * (stages t : ℝ) * r * d := by
    have hh := (eq_div_iff (by positivity : (2 : ℝ) ^ 20 * stages t ≠ 0)).mp hrd
    nlinarith
  have hA : ‖p - anchor‖ ≤ 2 ^ 20 * (stages t : ℝ) * d := by
    apply (mul_le_mul_iff_left₀ hr).mp
    change r * ‖p - anchor‖ ≤ t.ε at hres
    nlinarith
  have hf := shift_floor_bound hd hR (OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le j)
    hJ (mul_nonneg hb.le hR.le) (norm_nonneg (p - anchor)) (norm_nonneg (p - s)) hA hps
    (show τ = d / (2 ^ 100 * (stages t : ℝ) * t.R * (1 + b * t.R)) from rfl)
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (p - anchor) (p - s)) 2
  have hf' := mul_le_mul_of_nonneg_left hf hr.le
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hr.le (sq_nonneg τ))
  have hfloor : r * (τ ^ 2 * ‖p - anchor + (p - s)‖ ^ 2 +
      2 * τ * (‖p - anchor‖ * ‖p - s‖)) ≤ r * d ^ 2 / 2 ^ 78 := by nlinarith
  have hK : 30 + 4096 * b * (66 * d) ≤ 2 ^ 20 * (1 + b * d) := by nlinarith [mul_pos hb hd]
  have hbatch := stageBatch_terms t h0 h1 hR hG hε hv j
  have hnoise := batch_noise_bound hS (Nat.cast_pos.mpr (stageBatch_pos t j)) hK hbatch.1
  exact stage_accumulated_drift hr hS (Nat.cast_nonneg _) (stageSteps_upper t h0 h1 hR hG hε j) hfloor hnoise

end LongTails.Proofs.GapNoiseTuning
