import LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
import LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants
import LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
import LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronSuccess
open Classical LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
open scoped RealInnerProductSpace
noncomputable def goodCenter (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension) : Weights P.dimension :=
  WithLp.toLp 2 (-(η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2 +
    (((P.count : ℝ) * P.noiseScale * H + 2 * P.radius * P.noiseScale) / P.margin) • u,
    P.noiseScale * (H / P.radius + η * H + 3 / 2))
lemma good_event_separates (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w a : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hu : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hv : |w.ofLp.2| ≤ P.noiseScale * H / P.radius)
    (hq : negative data w.ofLp.1 ≤ P.noiseScale * H)
    (ha : ‖a - goodCenter P data η H u w‖ ≤ P.noiseScale / 2) :
    Separates data (WithLp.toLp 2
      (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + a) := by
  let b := goodCenter P data η H u w
  have he : ‖a.ofLp.1 - b.ofLp.1‖ ≤ P.noiseScale / 2 := by
    simpa only [WithLp.fst, WithLp.ofLp_sub, Prod.fst_sub] using
      (WithLp.norm_fst_le _ (a - b)).trans ha
  have hr : |a.ofLp.2 - b.ofLp.2| ≤ P.noiseScale / 2 := by
    simpa only [WithLp.snd, WithLp.ofLp_sub, Prod.snd_sub, Real.norm_eq_abs] using
      (WithLp.norm_snd_le _ (a - b)).trans ha
  have hg := selected_inner_lower P data w.ofLp.1 w.ofLp.1 w.ofLp.2
  have hgl := mul_le_mul_of_nonneg_left hg hη
  have hql := mul_le_mul_of_nonneg_left hq hη
  have hvl := (abs_le.mp hv).1
  have hrl := (abs_le.mp hr).1
  have hb2 : b.ofLp.2 = P.noiseScale * (H / P.radius + η * H + 3 / 2) := rfl
  rw [hb2] at hrl
  have hdiv : P.noiseScale * (H / P.radius) = P.noiseScale * H / P.radius := by ring
  have hout : 0 < w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫ + a.ofLp.2 := by
    nlinarith
  intro i
  have hbase := negative_component P data w.ofLp.1 i
  have hqn := mul_le_mul_of_nonneg_left hq (show 0 ≤ (P.count : ℝ) by positivity)
  let t := ((P.count : ℝ) * P.noiseScale * H + 2 * P.radius * P.noiseScale) / P.margin
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htδ : t * P.margin = (P.count : ℝ) * P.noiseScale * H + 2 * P.radius * P.noiseScale :=
    div_mul_cancel₀ _ hδ.ne'
  have hum := mul_le_mul_of_nonneg_left (hu i) ht
  have herr := neg_le_of_abs_le (abs_real_inner_le_norm (data i) (a.ofLp.1 - b.ofLp.1))
  have hnorm := mul_le_mul (hR i) he (norm_nonneg _) hRp.le
  have hx : w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2 + a.ofLp.1 =
      w.ofLp.1 + t • u + (a.ofLp.1 - b.ofLp.1) := by
    dsimp [b, goodCenter, t]
    rw [neg_smul]
    abel
  have hproj : 0 < ⟪data i, w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2 + a.ofLp.1⟫ := by
    rw [hx, inner_add_right, inner_add_right, real_inner_smul_right]
    nlinarith
  change 0 < ((WithLp.toLp 2
    (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
      w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + a).ofLp.2) * _
  simpa only [WithLp.ofLp_add, WithLp.ofLp_toLp, Prod.fst_add, Prod.snd_add] using mul_pos hout hproj
lemma weights_norm_le_components {d : ℕ} (w : Weights d) :
    ‖w‖ ≤ ‖w.ofLp.1‖ + |w.ofLp.2| := by
  have he : ‖w‖ ^ 2 = ‖w.ofLp.1‖ ^ 2 + w.ofLp.2 ^ 2 := by
    simpa using WithLp.prod_norm_sq_eq_of_L2 w
  nlinarith [norm_nonneg w, norm_nonneg w.ofLp.1, abs_nonneg w.ofLp.2,
    sq_abs w.ofLp.2, mul_nonneg (norm_nonneg w.ofLp.1) (abs_nonneg w.ofLp.2)]
lemma goodCenter_norm (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hv : |w.ofLp.2| ≤ P.noiseScale * H / P.radius) :
    ‖goodCenter P data η H u w‖ ≤ P.noiseScale *
      (2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2) := by
  let t := ((P.count : ℝ) * P.noiseScale * H + 2 * P.radius * P.noiseScale) / P.margin
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hout : 0 ≤ P.noiseScale * (H / P.radius + η * H + 3 / 2) := by positivity
  have hvR := mul_le_mul_of_nonneg_right hv hRp.le
  rw [div_mul_cancel₀ _ hRp.ne'] at hvR
  have hg := norm_selected_le P data w.ofLp.1 w.ofLp.2 hR
  have hvg := mul_le_mul_of_nonneg_left hg (abs_nonneg w.ofLp.2)
  have hηg := mul_le_mul_of_nonneg_left (hvg.trans hvR) hη
  have hsp : ‖-(η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2 + t • u‖ ≤
      η * P.noiseScale * H + t := by
    calc
      _ ≤ ‖-(η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2‖ + ‖t • u‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_neg, abs_mul, abs_of_nonneg hη, abs_of_nonneg ht, hu, mul_one]
        nlinarith
  have hb := weights_norm_le_components (goodCenter P data η H u w)
  change ‖goodCenter P data η H u w‖ ≤
    ‖-(η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2 + t • u‖ +
      |P.noiseScale * (H / P.radius + η * H + 3 / 2)| at hb
  rw [abs_of_nonneg hout] at hb
  have htEq : t = P.noiseScale * (((P.count : ℝ) * H + 2 * P.radius) / P.margin) := by
    dsimp [t]
    ring
  rw [htEq] at hsp hb
  nlinarith
lemma good_scalar_bounds (p q v R σ H : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hR : 0 < R) (hσ : 0 ≤ σ) (hH : 0 ≤ H)
    (hg : p * q + R ^ 2 * v ^ 2 ≤ σ ^ 2 * H ^ 2) :
    |v| ≤ σ * H / R ∧ (q ≤ σ * H ∨ p ≤ σ * H) := by
  have htarget : 0 ≤ σ * H := mul_nonneg hσ hH
  constructor
  · rw [le_div_iff₀ hR]
    have hsq : (|v| * R) ^ 2 ≤ (σ * H) ^ 2 := by
      nlinarith [mul_nonneg hp hq, sq_abs v]
    exact (sq_le_sq₀ (mul_nonneg (abs_nonneg v) hR.le) htarget).mp hsq
  · by_cases hh : q ≤ σ * H
    · exact Or.inl hh
    · right
      by_contra! hbad
      have hq' : σ * H < q := lt_of_not_ge hh
      have h1 := mul_lt_mul_of_pos_right hbad (htarget.trans_lt hq')
      have h2 := mul_le_mul_of_nonneg_left hq'.le htarget
      nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg v)]
lemma hinge_ball_exists (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hv : |w.ofLp.2| ≤ P.noiseScale * H / P.radius)
    (hh : negative data w.ofLp.1 ≤ P.noiseScale * H ∨ positive data w.ofLp.1 ≤ P.noiseScale * H) :
    ∃ b : Weights P.dimension, ‖b‖ ≤ P.noiseScale *
      (2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2) ∧
      ∀ a : Weights P.dimension, ‖a - b‖ ≤ P.noiseScale / 2 →
        Separates data (WithLp.toLp 2
          (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
            w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + a) := by
  rcases hh with hq | hp
  · refine ⟨goodCenter P data η H u w, goodCenter_norm P data η H u w hη hH hσ hδ hRp hR hu hv, ?_⟩
    intro a ha
    exact good_event_separates P data η H u w a hη hH hσ hδ hRp hR hmargin hv hq ha
  · have hvn : |(-w).ofLp.2| ≤ P.noiseScale * H / P.radius := by
      simpa [WithLp.ofLp_neg] using hv
    have hqn : negative data (-w).ofLp.1 ≤ P.noiseScale * H := by
      simpa [WithLp.ofLp_neg, negative_neg] using hp
    refine ⟨-goodCenter P data η H u (-w), ?_, ?_⟩
    · simpa only [norm_neg] using goodCenter_norm P data η H u (-w) hη hH hσ hδ hRp hR hu hvn
    · intro a ha
      have hnorm : ‖-a - goodCenter P data η H u (-w)‖ = ‖a - -goodCenter P data η H u (-w)‖ := by
        rw [show -a - goodCenter P data η H u (-w) = -(a - -goodCenter P data η H u (-w)) by abel,
          norm_neg]
      have hs := good_event_separates P data η H u (-w) (-a) hη hH hσ hδ hRp hR hmargin
        hvn hqn (hnorm.trans_le ha)
      rw [proposal_neg] at hs
      have hEq : -(WithLp.toLp 2
          (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
            w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) : Weights P.dimension) + -a =
          -(WithLp.toLp 2
          (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
            w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + a) := by abel
      rw [hEq, separates_neg_iff] at hs
      exact hs
lemma good_ball_exists (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hg : positive data w.ofLp.1 * negative data w.ofLp.1 + P.radius ^ 2 * w.ofLp.2 ^ 2 ≤
      P.noiseScale ^ 2 * H ^ 2) :
    ∃ b : Weights P.dimension, ‖b‖ ≤ P.noiseScale *
      (2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2) ∧
      ∀ a : Weights P.dimension, ‖a - b‖ ≤ P.noiseScale / 2 →
        Separates data (WithLp.toLp 2
          (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
            w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + a) := by
  have hb := good_scalar_bounds (positive data w.ofLp.1) (negative data w.ofLp.1)
    w.ofLp.2 P.radius P.noiseScale H (positive_nonneg P data w.ofLp.1)
    (negative_nonneg P data w.ofLp.1) hRp hσ.le hH hg
  exact hinge_ball_exists P data η H u w hη hH hσ hδ hRp hR hu hmargin hb.1 hb.2
open MeasureTheory ProbabilityTheory
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
lemma hinge_success_probability (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hv : |w.ofLp.2| ≤ P.noiseScale * H / P.radius)
    (hh : negative data w.ofLp.1 ≤ P.noiseScale * H ∨ positive data w.ofLp.1 ≤ P.noiseScale * H) :
    let C := 2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2
    ENNReal.ofReal (((1 / 2 : ℝ) / (2 * Real.sqrt (P.dimension + 1))) ^ (P.dimension + 1) *
      Real.exp (-C ^ 2 - (1 / 2 : ℝ) ^ 2)) ≤
    stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
      (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  dsimp only
  rcases hinge_ball_exists P data η H u w hη hH hσ hδ hRp hR hu hmargin hv hh with ⟨b, hb, hball⟩
  have hd : 0 < Module.finrank ℝ (Weights P.dimension) := by rw [weights_finrank]; omega
  have h := scaled_gaussian_ball_lower b P.noiseScale (1 / 2)
    (2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2)
    hd hσ (by norm_num) (by positivity) hb
  rw [weights_finrank] at h
  push_cast at h
  apply h.trans
  exact measure_mono fun z hz => hball (P.noiseScale • z) (by simpa only [Set.mem_ofPred_eq, mul_one_div] using hz)

lemma good_success_probability (P : Public) (data : Data P) (η H : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hg : positive data w.ofLp.1 * negative data w.ofLp.1 + P.radius ^ 2 * w.ofLp.2 ^ 2 ≤
      P.noiseScale ^ 2 * H ^ 2) :
    let C := 2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2
    ENNReal.ofReal (((1 / 2 : ℝ) / (2 * Real.sqrt (P.dimension + 1))) ^ (P.dimension + 1) *
      Real.exp (-C ^ 2 - (1 / 2 : ℝ) ^ 2)) ≤
    stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
      (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  have hb := good_scalar_bounds (positive data w.ofLp.1) (negative data w.ofLp.1)
    w.ofLp.2 P.radius P.noiseScale H (positive_nonneg P data w.ofLp.1)
    (negative_nonneg P data w.ofLp.1) hRp hσ.le hH hg
  exact hinge_success_probability P data η H u w hη hH hσ hδ hRp hR hu hmargin hb.1 hb.2
lemma small_escape_hinge_bounds (P : Public) (data : Data P) (η : ℝ)
    (w : Weights P.dimension) (hη : 0 ≤ η) (hR : 0 < P.radius) (hσ : 0 ≤ P.noiseScale)
    (hv : |w.ofLp.2| ≤ P.noiseScale)
    (he : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η w.ofLp.1 w.ofLp.2) :
    |w.ofLp.2| ≤ P.noiseScale * (P.radius + 4 * η * P.radius ^ 2) / P.radius ∧
    (negative data w.ofLp.1 ≤ P.noiseScale * (P.radius + 4 * η * P.radius ^ 2) ∨
      positive data w.ofLp.1 ≤ P.noiseScale * (P.radius + 4 * η * P.radius ^ 2)) := by
  have ht : 0 ≤ 4 * η * P.radius ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hv ht
  constructor
  · rw [le_div_iff₀ hR]
    have hr := mul_le_mul_of_nonneg_right hv hR.le
    nlinarith [mul_nonneg hσ ht]
  · rcases he with ⟨hpos, hq⟩ | ⟨hneg, hp⟩
    · left
      rw [abs_of_pos hpos] at hb
      nlinarith [mul_nonneg hσ hR.le]
    · right
      rw [abs_of_neg hneg] at hb
      nlinarith [mul_nonneg hσ hR.le]
lemma small_escape_success_probability (P : Public) (data : Data P) (η κ : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫) (hv : |w.ofLp.2| ≤ P.noiseScale)
    (he : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η w.ofLp.1 w.ofLp.2) :
    let H := P.radius + 4 * η * P.radius ^ 2
    let C := 2 * κ * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2
    ENNReal.ofReal (((1 / 2 : ℝ) / (2 * Real.sqrt (P.dimension + 1))) ^ (P.dimension + 1) *
      Real.exp (-C ^ 2 - (1 / 2 : ℝ) ^ 2)) ≤
    stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
      (w.ofLp.1 + (κ * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + κ * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  have hb := small_escape_hinge_bounds P data η w hη hRp hσ.le hv he
  exact hinge_success_probability P data κ (P.radius + 4 * η * P.radius ^ 2) u w
    hκ (by positivity) hσ hδ hRp hR hu hmargin hb.1 hb.2
open LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants
lemma hinge_probability_common (P : Public) (data : Data P) (η H M : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin)
    (hRp : 0 < P.radius) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (hv : |w.ofLp.2| ≤ P.noiseScale * H / P.radius)
    (hh : negative data w.ofLp.1 ≤ P.noiseScale * H ∨
      positive data w.ofLp.1 ≤ P.noiseScale * H)
    (hM : 4 ≤ M)
    (hC : 2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2 ≤
      64 * (P.dimension + 1) * M) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 * M ^ 2)) ≤
      stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
        (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
          w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  have hb := hinge_success_probability P data η H u w hη hH hσ hδ hRp hR hu hmargin hv hh
  apply le_trans _ hb
  apply ENNReal.ofReal_le_ofReal
  have hl := good_probability_common (P.dimension + 1) M
    (2 * η * H + ((P.count : ℝ) * H + 2 * P.radius) / P.margin + H / P.radius + 2)
    (by simp) hM (by positivity) (by simpa using hC)
  push_cast at hl
  convert hl using 1
  ring_nf
lemma tuned_good_success_probability (P : Public) (data : Data P) (η : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hg : η ^ 2 * (positive data w.ofLp.1 * negative data w.ofLp.1 +
      P.radius ^ 2 * w.ofLp.2 ^ 2) ≤ 48 * P.noiseScale ^ 2 * (P.dimension + 1)) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) ≤
      stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
        (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
          w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hRp : 0 < P.radius := lt_of_lt_of_le hδ hδR
  have hη := (tuned_step_bounds P.count P.radius P.margin η hn hδ hδR htune).1
  let H := Real.sqrt (48 * (P.dimension + 1)) / η
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHs : H ^ 2 = 48 * (P.dimension + 1) / η ^ 2 := by
    dsimp [H]
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hg' : positive data w.ofLp.1 * negative data w.ofLp.1 +
      P.radius ^ 2 * w.ofLp.2 ^ 2 ≤ P.noiseScale ^ 2 * H ^ 2 := by
    rw [hHs, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hη)]
    nlinarith
  have hb := good_scalar_bounds (positive data w.ofLp.1) (negative data w.ofLp.1)
    w.ofLp.2 P.radius P.noiseScale H (positive_nonneg P data w.ofLp.1)
    (negative_nonneg P data w.ofLp.1) hRp hσ.le hH hg'
  apply hinge_probability_common P data η H _ u w hη.le hH hσ hδ hRp hR hu hmargin hb.1 hb.2
  · have hk : 1 ≤ P.radius / P.margin := (le_div_iff₀ hδ).2 (by simpa using hδR)
    have hn2 : 4 ≤ ((P.count : ℝ) + 1) ^ 2 := by nlinarith
    have hk2 : 1 ≤ (P.radius / P.margin) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk2 (sq_nonneg ((P.count : ℝ) + 1))]
  · exact tuned_center_bound P.count P.radius P.margin η (P.dimension + 1)
      hn hδ hδR (by simp) htune
lemma tuned_small_escape_success_probability (P : Public) (data : Data P) (η κ : ℝ)
    (u : Features P.dimension) (w : Weights P.dimension)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hκ : 0 ≤ κ) (hκη : κ ≤ η) (hv : |w.ofLp.2| ≤ P.noiseScale)
    (he : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η w.ofLp.1 w.ofLp.2) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) ≤
      stdGaussian (Weights P.dimension) {z | Separates data (WithLp.toLp 2
        (w.ofLp.1 + (κ * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
          w.ofLp.2 + κ * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z)} := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hRp : 0 < P.radius := lt_of_lt_of_le hδ hδR
  have hs := tuned_step_bounds P.count P.radius P.margin η hn hδ hδR htune
  have hη : 0 < η := hs.1
  have hb := small_escape_hinge_bounds P data η w hs.1.le hRp hσ.le hv he
  have hH : 0 ≤ P.radius + 4 * η * P.radius ^ 2 := by positivity
  apply hinge_probability_common P data κ (P.radius + 4 * η * P.radius ^ 2) _ u w
    hκ hH hσ hδ hRp hR hu hmargin hb.1 hb.2
  · have hk : 1 ≤ P.radius / P.margin := (le_div_iff₀ hδ).2 (by simpa using hδR)
    have hn2 : 4 ≤ ((P.count : ℝ) + 1) ^ 2 := by nlinarith
    have hk2 : 1 ≤ (P.radius / P.margin) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk2 (sq_nonneg ((P.count : ℝ) + 1))]
  · have hHle := small_hinge_parameter_le η P.radius (P.dimension + 1)
      hs.1 hRp.le (by simp) hs.2.1
    exact (hinge_center_mono P.count P.radius P.margin η κ
      (Real.sqrt (48 * (P.dimension + 1)) / η) (P.radius + 4 * η * P.radius ^ 2)
      (by positivity) hRp hδ hκ hκη hH hHle).trans
      (tuned_center_bound P.count P.radius P.margin η (P.dimension + 1) hn hδ hδR (by simp) htune)
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialPaths
open LongTails.Proofs.NoisyBatchQuadraticPerceptronTrials
open LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
open LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
lemma exit_block_success_probability (P : Public) (data : Data P) (η : ℝ)
    (u : Features P.dimension) (t K B : ℕ) (x : Fin t → Weights P.dimension)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2)
    (hv : (pastPoint P data η t x).ofLp.2 ≠ 0)
    (hexit : ¬Retained data η (pastPoint P data η t x)) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) ≤
      (Measure.pi (fun _ : Fin B => stdGaussian (Weights P.dimension)))
        {y | Separates data (pastPoint P data η (t + B) (Fin.append x y))} := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hs := tuned_step_bounds P.count P.radius P.margin η hn hδ hδR htune
  have hBp : 0 < B := by omega
  by_cases hsep : Separates data (pastPoint P data η t x)
  · have hall : {y : Fin B → Weights P.dimension |
        Separates data (pastPoint P data η (t + B) (Fin.append x y))} = Set.univ :=
      Set.eq_univ_of_forall fun y => block_separation_persists P data η t B x y hsep
    rw [hall, measure_univ]
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    have hp : 0 ≤ 25000 * (P.dimension + 1 : ℝ) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2 := by positivity
    nlinarith
  by_cases hg : η ^ 2 * (positive data (pastPoint P data η t x).ofLp.1 *
      negative data (pastPoint P data η t x).ofLp.1 + P.radius ^ 2 *
      (pastPoint P data η t x).ofLp.2 ^ 2) ≤ 48 * P.noiseScale ^ 2 * (P.dimension + 1)
  · exact block_one_step_probability P data η t B hBp x _
      (tuned_good_success_probability P data η u _ hσ hδ hδR hR hu hmargin htune hg)
  let ε : ℝ := 1 / (64 * ((K + 1 : ℕ) : ℝ))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have ht := tuned_escape_noise P.count η P.margin (by positivity) hs.1 hδ K hK
  have hc := tuned_block_probability (P.dimension + 1) P.count P.radius P.margin η
    (by simp) hn hδ hδR htune K B hK hB
  push_cast at hc
  by_cases he : Escape data η (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2
  · by_cases hvsmall : |(pastPoint P data η t x).ofLp.2| ≤ P.noiseScale
    · exact block_one_step_probability P data η t B hBp x _
        (tuned_small_escape_success_probability P data η η u _ hσ hδ hδR hR hu hmargin htune
          hs.1.le le_rfl hvsmall he)
    · apply (ENNReal.ofReal_le_ofReal hc).trans
      simpa only [ε, Nat.cast_add, Nat.cast_one] using block_current_escape_probability P data u η P.margin ε K t B x (by omega)
        hs.1.le hδ hs.2.1 hε ht.2.1 ht.2.2 ht.1 hR hu hmargin hs.2.2 hσ.le he
        (le_of_not_ge hvsmall)
  have hproposal : Escape data η
      ((pastPoint P data η t x).ofLp.1 + (η * (pastPoint P data η t x).ofLp.2) •
        selected data (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2)
      ((pastPoint P data η t x).ofLp.2 + η * ⟪selected data (pastPoint P data η t x).ofLp.1
        (pastPoint P data η t x).ofLp.2, (pastPoint P data η t x).ofLp.1⟫) := by
    by_contra hh
    exact hexit ⟨hsep, hv, lt_of_not_ge hg, he, hh⟩
  let b : Weights P.dimension := WithLp.toLp 2
    ((pastPoint P data η t x).ofLp.1 + (η * (pastPoint P data η t x).ofLp.2) •
      selected data (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2,
    (pastPoint P data η t x).ofLp.2 + η * ⟪selected data (pastPoint P data η t x).ofLp.1
      (pastPoint P data η t x).ofLp.2, (pastPoint P data η t x).ofLp.1⟫)
  have hb : Escape data η b.ofLp.1 b.ofLp.2 := hproposal
  by_cases hvsmall : |b.ofLp.2| ≤ P.noiseScale
  · apply block_one_step_probability P data η t B hBp x
    have hh := tuned_small_escape_success_probability P data η 0 u b hσ hδ hδR hR hu hmargin
      htune (by norm_num) hs.1.le hvsmall hb
    simpa only [zero_mul, zero_smul, add_zero, WithLp.toLp_ofLp] using hh
  · apply (ENNReal.ofReal_le_ofReal hc).trans
    simpa only [ε, Nat.cast_add, Nat.cast_one] using block_proposal_escape_probability P data u η P.margin ε K t B x b (by omega)
      hs.1.le hδ hs.2.1 hε ht.2.1 ht.2.2 ht.1 hR hu hmargin hs.2.2 hσ.le rfl hsep hb
      (le_of_not_ge hvsmall)
lemma tested_exit_block_success (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (t K B : ℕ) (S : Set P.noise.Ω)
    (hS : HistoryEvent P t S)
    (hstate : ∀ ω ∈ S, (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 ≠ 0 ∧
      ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) *
        (P.noise.law : Measure P.noise.Ω) S ≤
      (P.noise.law : Measure P.noise.Ω) (S ∩
        {ω | Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point}) := by
  rcases hS with ⟨A, hA, hSA⟩
  let G : Set (Fin t → Weights P.dimension) := {x |
    (pastPoint P data η t x).ofLp.2 ≠ 0 ∧ ¬Retained data η (pastPoint P data η t x)}
  have hmp := measurable_pastPoint P data η t
  have hm : Measurable (fun x : Fin t → Weights P.dimension => (pastPoint P data η t x).ofLp.2) := by
    fun_prop
  have hG : MeasurableSet G :=
    (measurableSet_eq_fun hm measurable_const).compl.inter
      ((measurableSet_retained P data η).compl.preimage hmp)
  have hSG : S = {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A ∩ G} := by
    ext ω
    constructor
    · intro hω
      have ha : (fun j : Fin t => P.noise.sample j ω) ∈ A := by
        have ha := hω
        rw [hSA] at ha
        exact ha
      refine ⟨ha, ?_⟩
      have hh := hstate ω hω
      simpa only [G, Set.mem_ofPred_eq, batch_point_factor] using hh
    · intro hω
      rw [hSA]
      exact hω.1
  have hh := tested_block_success_lower P data η h t B (A ∩ G) (hA.inter hG) _
    (fun x hx => exit_block_success_probability P data η u t K B x hσ hδ hδR hR hu hmargin
      htune hK hB hx.2.1 hx.2.2)
  simpa only [hSG, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.ofPred_and] using hh
end LongTails.Proofs.NoisyBatchQuadraticPerceptronSuccess
