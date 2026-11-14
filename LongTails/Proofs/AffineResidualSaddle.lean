import LongTails.Algorithms.AffineResidualSaddle
import LongTails.Proofs.AffineResidualEntropy
import LongTails.Proofs.AffineSoftmaxResidual
import LongTails.Proofs.ComponentEnvelopeExecution
import LongTails.Proofs.SmoothFiniteMaximumGeometry
import LongTails.Proofs.AffineSoftmaxRegularization
import LongTails.Proofs.ExtragradientStep

namespace LongTails.Proofs.AffineResidualSaddle

open scoped RealInnerProductSpace
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineResidualSaddle

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Nonempty ι] in
lemma coordinateReply_sum (r : ι → ℝ) (i : ι) :
    ∑ j, coordinateReply j (r j) i = (Fintype.card ι : ℝ) * r i := by
  classical
  simp [coordinateReply]

lemma coordinateReply_mean (r : ι → ℝ) (i : ι) :
    (∑ j, coordinateReply j (r j) i) / Fintype.card ι = r i := by
  rw [coordinateReply_sum]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Nonempty ι] in
lemma coordinateReply_square_sum (r : ι → ℝ) (i : ι) :
    ∑ j, (coordinateReply j (r j) i) ^ 2 = (Fintype.card ι : ℝ) ^ 2 * (r i) ^ 2 := by
  classical
  simp [coordinateReply, mul_pow]

lemma coordinateReply_centered_square (r : ι → ℝ) (i : ι) :
    (∑ j, (coordinateReply j (r j) i - r i) ^ 2) / Fintype.card ι =
      ((Fintype.card ι : ℝ) - 1) * (r i) ^ 2 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, coordinateReply_square_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [mul_assoc (2 : ℝ), ← Finset.mul_sum, ← Finset.sum_mul, coordinateReply_sum]
  field_simp
  ring

lemma coordinateReply_weighted_variance (p r : ι → ℝ) :
    (∑ j, ∑ i, p i * (coordinateReply j (r j) i - r i) ^ 2) / Fintype.card ι =
      ((Fintype.card ι : ℝ) - 1) * ∑ i, p i * (r i) ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, mul_div_assoc, coordinateReply_centered_square]
  ring

lemma coordinateReply_variance_bound {p r : ι → ℝ} {D : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D) :
    (∑ j, ∑ i, p i * (coordinateReply j (r j) i - r i) ^ 2) / Fintype.card ι ≤
      (Fintype.card ι : ℝ) * D ^ 2 := by
  have hm : 0 ≤ (Fintype.card ι : ℝ) - 1 := by
    have h : 1 ≤ Fintype.card ι := Fintype.card_pos
    have h' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
    linarith
  have hs : (∑ i, p i * (r i) ^ 2) ≤ D ^ 2 := by
    calc
      _ ≤ ∑ i, p i * D ^ 2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by nlinarith [(hr i).1, (hr i).2]) (hp i)
      _ = _ := by rw [← Finset.sum_mul, hpsum, one_mul]
  rw [coordinateReply_weighted_variance]
  calc
    _ ≤ ((Fintype.card ι : ℝ) - 1) * D ^ 2 := mul_le_mul_of_nonneg_left hs hm
    _ ≤ _ := by nlinarith [sq_nonneg D]

omit [Nonempty ι] in
lemma coordinateReply_bounds {r : ι → ℝ} {D : ℝ} (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D)
    (hD : 0 ≤ D) (j i : ι) :
    0 ≤ coordinateReply j (r j) i ∧ coordinateReply j (r j) i ≤ (Fintype.card ι : ℝ) * D := by
  classical
  by_cases h : i = j
  · simp only [coordinateReply, h, ite_true]
    exact ⟨mul_nonneg (Nat.cast_nonneg _) (hr j).1,
      mul_le_mul_of_nonneg_left (hr j).2 (Nat.cast_nonneg _)⟩
  · simp only [coordinateReply, h, ite_false]
    exact ⟨le_rfl, mul_nonneg (Nat.cast_nonneg _) hD⟩

lemma coordinateReply_centered_bound {r : ι → ℝ} {D : ℝ}
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D) (hD : 0 ≤ D) (j i : ι) :
    |r i - coordinateReply j (r j) i| ≤ (Fintype.card ι : ℝ) * D := by
  have hb := coordinateReply_bounds hr hD j i
  have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd := mul_le_mul_of_nonneg_right hm hD
  apply abs_le.mpr
  constructor <;> linarith [(hr i).1, (hr i).2]

lemma coordinateReply_weighted_second (p r : ι → ℝ) :
    (∑ j, ∑ i, p i * (coordinateReply j (r j) i) ^ 2) / Fintype.card ι =
      (Fintype.card ι : ℝ) * ∑ i, p i * (r i) ^ 2 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, coordinateReply_square_sum]
  field_simp

lemma coordinateReply_second_bound {p r : ι → ℝ} {D : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ D) :
    (∑ j, ∑ i, p i * (coordinateReply j (r j) i) ^ 2) / Fintype.card ι ≤
      (Fintype.card ι : ℝ) * D ^ 2 := by
  rw [coordinateReply_weighted_second]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i, p i * D ^ 2 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [(hr i).1, (hr i).2]) (hp i)
    _ = _ := by rw [← Finset.sum_mul, hpsum, one_mul]

noncomputable def potential (μ τ : ℝ) (u v : State ι E) : ℝ :=
  μ / 2 * ‖u.point - v.point‖ ^ 2 +
    τ * AffineResidualEntropy.divergence u.probability v.probability

noncomputable def pairing (g : E) (b : ι → ℝ) (u v : State ι E) : ℝ :=
  ⟪g, u.point - v.point⟫ + ∑ i, b i * (u.probability i - v.probability i)

noncomputable def regularizer (anchor : E) (μ τ : ℝ) (u : State ι E) : ℝ :=
  μ / 2 * ‖u.point - anchor‖ ^ 2 + τ * ∑ i, u.probability i * Real.log (u.probability i)

omit [Nonempty ι] in
lemma pairing_chain (g : E) (b : ι → ℝ) (u v w : State ι E) :
    pairing g b u w = pairing g b u v + pairing g b v w := by
  simp only [pairing, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  ring

omit [Nonempty ι] in
lemma pairing_add (g h : E) (b d : ι → ℝ) (u v : State ι E) :
    pairing (g + h) (fun i => b i + d i) u v = pairing g b u v + pairing h d u v := by
  simp only [pairing, inner_add_left, add_mul, Finset.sum_add_distrib]
  ring

omit [Nonempty ι] in
lemma regularizer_identity (anchor : E) (μ τ : ℝ) (u v : State ι E) :
    regularizer anchor μ τ u - regularizer anchor μ τ v =
      pairing (μ • (v.point - anchor)) (fun i => τ * Real.log (v.probability i)) u v +
        potential μ τ u v := by
  have hn : ‖u.point - anchor‖ ^ 2 = ‖u.point - v.point‖ ^ 2 +
      2 * ⟪v.point - anchor, u.point - v.point⟫ + ‖v.point - anchor‖ ^ 2 := by
    rw [show u.point - anchor = (u.point - v.point) + (v.point - anchor) by abel,
      norm_add_sq_real, real_inner_comm (u.point - v.point) (v.point - anchor)]
  have he : (∑ i, u.probability i * Real.log (u.probability i)) -
      (∑ i, v.probability i * Real.log (v.probability i)) =
        (∑ i, Real.log (v.probability i) * (u.probability i - v.probability i)) +
          AffineResidualEntropy.divergence u.probability v.probability := by
    unfold AffineResidualEntropy.divergence
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold regularizer pairing potential
  simp only [real_inner_smul_left, mul_assoc, ← Finset.mul_sum]
  rw [hn]
  nlinarith [congrArg (fun z : ℝ => τ * z) he]

omit [Nonempty ι] [InnerProductSpace ℝ E] in
lemma potential_nonneg {μ τ : ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ)
    {u v : State ι E} (hu : ∀ i, 0 ≤ u.probability i) (hv : ∀ i, 0 < v.probability i)
    (husum : ∑ i, u.probability i = 1) (hvsum : ∑ i, v.probability i = 1) :
    0 ≤ potential μ τ u v := by
  have h := AffineResidualEntropy.divergence_nonneg hu hv husum hvsum
  unfold potential
  positivity

omit [Nonempty ι] in
lemma potential_three_point (μ τ : ℝ) (u x y : State ι E) :
    potential μ τ u x - potential μ τ u y - potential μ τ y x =
      μ * ⟪u.point - y.point, y.point - x.point⟫ +
        τ * ∑ i, (u.probability i - y.probability i) *
          (Real.log (y.probability i) - Real.log (x.probability i)) := by
  have hn : ‖u.point - x.point‖ ^ 2 = ‖u.point - y.point‖ ^ 2 +
      2 * ⟪u.point - y.point, y.point - x.point⟫ + ‖y.point - x.point‖ ^ 2 := by
    rw [show u.point - x.point = (u.point - y.point) + (y.point - x.point) by abel,
      norm_add_sq_real]
  have he := AffineResidualEntropy.divergence_three_point
    u.probability x.probability y.probability
  unfold potential
  rw [hn]
  nlinarith [congrArg (fun z : ℝ => τ * z) he]

omit [Nonempty ι] in
lemma potential_gradient_pairing (μ τ : ℝ) (u x y : State ι E) :
    pairing (μ • (y.point - x.point))
      (fun i => τ * (Real.log (y.probability i) - Real.log (x.probability i))) u y =
        potential μ τ u x - potential μ τ u y - potential μ τ y x := by
  rw [potential_three_point]
  unfold pairing
  rw [real_inner_smul_left, real_inner_comm (y.point - x.point) (u.point - y.point),
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Nonempty ι] in
lemma prox_model_bound (anchor : E) (μ τ : ℝ) {η : ℝ} (hη : 0 < η)
    (u state next : State ι E) (g : E) (b : ι → ℝ)
    (hnormal : 0 ≤ pairing g b u next +
      1 / 2 * pairing (μ • (next.point - anchor))
        (fun i => τ * Real.log (next.probability i)) u next +
      1 / η * pairing (μ • (next.point - state.point))
        (fun i => τ * (Real.log (next.probability i) - Real.log (state.probability i))) u next) :
    η * (-pairing g b u next +
      (regularizer anchor μ τ next - regularizer anchor μ τ u) / 2) ≤
        potential μ τ u state - (1 + η / 2) * potential μ τ u next -
          potential μ τ next state := by
  rw [potential_gradient_pairing] at hnormal
  have hr := regularizer_identity anchor μ τ u next
  have hh := mul_nonneg hη.le hnormal
  have he : η * (1 / η) = 1 := by field_simp
  nlinarith [congrArg (fun z : ℝ => η / 2 * z) hr,
    congrArg (fun z : ℝ => z * (potential μ τ u state - potential μ τ u next -
      potential μ τ next state)) he]

omit [Nonempty ι] in
lemma two_model_bound (anchor : E) (μ τ η : ℝ)
    (u state predicted next : State ι E) (a g : E) (d b : ι → ℝ)
    (hpred : η * (-pairing a d next predicted +
      (regularizer anchor μ τ predicted - regularizer anchor μ τ next) / 2) ≤
        potential μ τ next state - (1 + η / 2) * potential μ τ next predicted -
          potential μ τ predicted state)
    (hnext : η * (-pairing (a + g) (fun i => d i + b i) u next +
      (regularizer anchor μ τ next - regularizer anchor μ τ u) / 2) ≤
        potential μ τ u state - (1 + η / 2) * potential μ τ u next -
          potential μ τ next state) :
    η * (-pairing (a + g) (fun i => d i + b i) u predicted +
      (regularizer anchor μ τ predicted - regularizer anchor μ τ u) / 2) ≤
        potential μ τ u state - (1 + η / 2) * potential μ τ u next -
          potential μ τ predicted state - (1 + η / 2) * potential μ τ next predicted +
            η * pairing g b predicted next := by
  have he : η * (-pairing (a + g) (fun i => d i + b i) u predicted +
      (regularizer anchor μ τ predicted - regularizer anchor μ τ u) / 2) =
      η * (-pairing a d next predicted +
        (regularizer anchor μ τ predicted - regularizer anchor μ τ next) / 2) +
      η * (-pairing (a + g) (fun i => d i + b i) u next +
        (regularizer anchor μ τ next - regularizer anchor μ τ u) / 2) +
      η * pairing g b predicted next := by
    rw [pairing_add, pairing_add, pairing_chain a d u next predicted,
      pairing_chain g b u predicted next]
    ring
  rw [he]
  have h := add_le_add_right (add_le_add hpred hnext) (η * pairing g b predicted next)
  convert h using 1 <;> ring

lemma quadratic_perturbation {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η) (b d : E) :
    η * ⟪b, d⟫ - a / 2 * ‖d‖ ^ 2 ≤ η ^ 2 * ‖b‖ ^ 2 / (2 * a) := by
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm b d) hη
  apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
  nlinarith [sq_nonneg (a * ‖d‖ - η * ‖b‖),
    mul_le_mul_of_nonneg_left hi ha.le]

lemma nonnegative_perturbation {μ τ κ η : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hκ : 0 < κ) (hη : 0 ≤ η)
    {u v : State ι E} (hu : ∀ i, 0 ≤ u.probability i) (hv : ∀ i, 0 < v.probability i)
    (husum : ∑ i, u.probability i = 1) (hvsum : ∑ i, v.probability i = 1)
    (g : E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    η * (⟪g, v.point - u.point⟫ + ∑ i, (v.probability i - u.probability i) * b i) -
      κ * potential μ τ u v ≤
      η ^ 2 * ‖g‖ ^ 2 / (2 * (κ * μ)) +
        η ^ 2 / (κ * τ) * ∑ i, v.probability i * (b i) ^ 2 := by
  have hp := quadratic_perturbation (mul_pos hκ hμ) hη g (v.point - u.point)
  rw [norm_sub_rev v.point u.point] at hp
  have hd := AffineResidualEntropy.entropy_nonnegative_step
    (fun i => η * b i / (κ * τ)) hv hvsum hu husum
    (fun i => div_nonneg (mul_nonneg hη (hb i)) (mul_pos hκ hτ).le)
  have hs := AffineResidualEntropy.scaled_step (mul_pos hκ hτ) hd
  unfold potential
  nlinarith

lemma signed_perturbation {μ τ κ η : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hκ : 0 < κ) (hη : 0 ≤ η)
    {u v : State ι E} (hu : ∀ i, 0 ≤ u.probability i) (hv : ∀ i, 0 < v.probability i)
    (husum : ∑ i, u.probability i = 1) (hvsum : ∑ i, v.probability i = 1)
    (g : E) (b : ι → ℝ) (hb : ∀ i, |η * b i / (κ * τ)| ≤ 1) :
    η * (⟪g, v.point - u.point⟫ + ∑ i, (v.probability i - u.probability i) * b i) -
      κ * potential μ τ u v ≤
      η ^ 2 * ‖g‖ ^ 2 / (2 * (κ * μ)) +
        η ^ 2 / (κ * τ) * ∑ i, v.probability i * (b i) ^ 2 := by
  have hp := quadratic_perturbation (mul_pos hκ hμ) hη g (v.point - u.point)
  rw [norm_sub_rev v.point u.point] at hp
  have hd := AffineResidualEntropy.entropy_signed_step
    (fun i => η * b i / (κ * τ)) hv hvsum hu husum hb
  have hs := AffineResidualEntropy.scaled_step (mul_pos hκ hτ) hd
  unfold potential
  nlinarith


omit [Fintype ι] [Nonempty ι] in
lemma predictorScores_gradient [CompleteSpace E] (s : Snapshot ι E) (τ η : ℝ)
    (state : State ι E) (x : E) (i : ι) :
    HasGradientAt (fun y => predictorScores s τ η state y i) (s.field i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hi := (hasFDerivAt_const (s.field i) x).inner ℝ
    ((hasFDerivAt_id x).sub_const s.anchor)
  convert (hi.const_add (s.value i)).add_const (τ / η * Real.log (state.probability i)) using 1
  · ext y
    simp [predictorScores, affine]
  · ext y
    simp [fderivInnerCLM_apply, InnerProductSpace.toDual_apply_apply]

lemma predictorObjective_gradient [CompleteSpace E] (s : Snapshot ι E) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η) (μ : ℝ) (state : State ι E) (x : E) :
    HasGradientAt (predictorObjective s τ μ η state)
      ((∑ i, gibbsWeight (τ * (1 + 1 / η)) (predictorScores s τ η state x) i • s.field i) +
        μ • (x - s.anchor) + (μ / η) • (x - state.point)) x := by
  have ht : τ * (1 + 1 / η) ≠ 0 := ne_of_gt (by positivity)
  have hg := SmoothFiniteMaximumGeometry.smoothValue_gradient
    (fun i y => predictorScores s τ η state y i) s.field ht
    (fun i => predictorScores_gradient s τ η state x i)
  have h := AffineSoftmaxRegularization.regularized_hasGradientAt
    (AffineSoftmaxRegularization.regularized_hasGradientAt hg μ s.anchor) (μ / η) state.point
  convert h using 1
  · ext y
    simp only [predictorObjective, RecursiveEnvelopeGeometry.regularized]
    congr 1
    ring
  · rfl

lemma predictorObjective_continuous (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) : Continuous (predictorObjective s τ μ η state) := by
  have ha i : Continuous (predictorScores s τ η state · i) := by
    unfold predictorScores affine
    fun_prop
  have he : Continuous (fun x => ∑ i, Real.exp
      (predictorScores s τ η state x i / (τ * (1 + 1 / η)))) := by
    fun_prop
  have hn x : (∑ i, Real.exp
      (predictorScores s τ η state x i / (τ * (1 + 1 / η)))) ≠ 0 :=
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  have hl := he.log hn
  unfold predictorObjective smoothValue
  fun_prop

lemma predictor_mem_min {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (s : Snapshot ι E) (τ μ η : ℝ) (state : State ι E) :
    (predictor C s τ μ η state).point ∈ C ∧
      IsMinOn (predictorObjective s τ μ η state) C (predictor C s τ μ η state).point := by
  exact Classical.epsilon_spec
    (hC.exists_isMinOn hne (predictorObjective_continuous s τ μ η state).continuousOn)

lemma predictor_probability_pos (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (i : ι) : 0 < (predictor C s τ μ η state).probability i :=
  LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_pos _ _ _

lemma predictor_probability_sum (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) : ∑ i, (predictor C s τ μ η state).probability i = 1 :=
  LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_sum _ _

lemma gibbs_stationarity {θ : ℝ} (hθ : θ ≠ 0) (scores : ι → ℝ) :
    ∃ c : ℝ, ∀ i, θ * Real.log (gibbsWeight θ scores i) - scores i = c := by
  refine ⟨-θ * Real.log (∑ j, Real.exp (scores j / θ)), ?_⟩
  intro i
  rw [LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_log]
  field_simp
  ring

lemma predictor_dual_stationarity (C : Set E) (s : Snapshot ι E) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η) (μ : ℝ) (state : State ι E) :
    let v := predictor C s τ μ η state
    ∃ c : ℝ, ∀ i, -affine s i v.point + τ * Real.log (v.probability i) +
      τ / η * (Real.log (v.probability i) - Real.log (state.probability i)) = c := by
  let v := predictor C s τ μ η state
  have ht : τ * (1 + 1 / η) ≠ 0 := ne_of_gt (by positivity)
  obtain ⟨c, hc⟩ := gibbs_stationarity ht (predictorScores s τ η state v.point)
  refine ⟨c, fun i => ?_⟩
  have hi : τ * (1 + 1 / η) * Real.log (v.probability i) -
      (affine s i v.point + τ / η * Real.log (state.probability i)) = c := hc i
  convert hi using 1
  ring

lemma predictor_primal_optimality [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (μ : ℝ)
    (state : State ι E) {u : E} (hu : u ∈ C) :
    let v := predictor C s τ μ η state
    0 ≤ ⟪(∑ i, v.probability i • s.field i) + μ • (v.point - s.anchor) +
      (μ / η) • (v.point - state.point), u - v.point⟫ := by
  let v := predictor C s τ μ η state
  have hv := predictor_mem_min hC hne s τ μ η state
  have hg := predictorObjective_gradient s hτ hη μ state v.point
  exact OracleTemplate.NearZeroSum.minimizer_gradient_normal hconv hv.1 hv.2
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr hg.hasFDerivAt.hasFDerivWithinAt) u hu

lemma correction_probability_pos (project : E → E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state predicted : State ι E) (g : E) (b : ι → ℝ) (i : ι) :
    0 < (correction project s τ μ η state predicted g b).probability i := by
  dsimp only [LongTails.Algorithms.AffineResidualSaddle.correction]
  exact LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_pos _ _ _

lemma correction_probability_sum (project : E → E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state predicted : State ι E) (g : E) (b : ι → ℝ) :
    ∑ i, (correction project s τ μ η state predicted g b).probability i = 1 :=
  LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_sum _ _

lemma correction_dual_stationarity (project : E → E) (s : Snapshot ι E) {τ η : ℝ}
    (hτ : 0 < τ) (hη : 0 < η) (μ : ℝ) (state predicted : State ι E)
    (g : E) (b : ι → ℝ) :
    let n := correction project s τ μ η state predicted g b
    ∃ c : ℝ, ∀ i, τ / η * (Real.log (n.probability i) - Real.log (state.probability i)) +
      τ / 2 * Real.log (n.probability i) + τ / 2 * Real.log (predicted.probability i) -
        affine s i predicted.point + b i = c := by
  let n := correction project s τ μ η state predicted g b
  have ht : τ * (1 / η + 1 / 2) ≠ 0 := ne_of_gt (by positivity)
  obtain ⟨c, hc⟩ := gibbs_stationarity ht (fun i => τ / η * Real.log (state.probability i) +
    affine s i predicted.point - τ / 2 * Real.log (predicted.probability i) - b i)
  refine ⟨c, fun i => ?_⟩
  have hi : τ * (1 / η + 1 / 2) * Real.log (n.probability i) -
      (τ / η * Real.log (state.probability i) + affine s i predicted.point -
        τ / 2 * Real.log (predicted.probability i) - b i) = c := hc i
  convert hi using 1
  ring

omit [Nonempty ι] in
lemma correction_primal_optimality {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η) (τ : ℝ)
    (state predicted : State ι E) (g : E) (b : ι → ℝ) :
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state predicted g b
    n.point ∈ C ∧ ∀ u ∈ C,
      0 ≤ ⟪(μ / η) • (n.point - state.point) + (μ / 2) • (n.point - s.anchor) +
        (∑ i, predicted.probability i • s.field i) + (μ / 2) • (predicted.point - s.anchor) + g,
          u - n.point⟫ := by
  let w := μ * (1 / η + 1 / 2)
  let a := (μ / η) • state.point + μ • s.anchor - (μ / 2) • predicted.point -
    (∑ i, predicted.probability i • s.field i) - g
  let z := w⁻¹ • a
  let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state predicted g b
  have hw : 0 < w := by dsimp [w]; positivity
  have hn : n.point = OracleTemplate.SaddlePoint.project C z := rfl
  have hp := OracleTemplate.SaddlePoint.project_spec hne hC hconv z
  refine ⟨hp.1, fun u hu => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hp.2 u hu) hw.le
  rw [← real_inner_smul_left] at hh
  have he : w • (z - n.point) = -((μ / η) • (n.point - state.point) +
      (μ / 2) • (n.point - s.anchor) + (∑ i, predicted.probability i • s.field i) +
        (μ / 2) • (predicted.point - s.anchor) + g) := by
    dsimp only [z]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
    dsimp [a, w]
    module
  change ⟪w • (z - n.point), u - n.point⟫ ≤ w * 0 at hh
  rw [he, inner_neg_left] at hh
  linarith

lemma correction_normal {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {μ τ η : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hη : 0 < η)
    (state predicted : State ι E) (g : E) (b : ι → ℝ)
    (u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state predicted g b
    0 ≤ pairing ((∑ i, predicted.probability i • s.field i) +
        (μ / 2) • (predicted.point - s.anchor) + g)
      (fun i => -affine s i predicted.point + τ / 2 * Real.log (predicted.probability i) + b i) u n +
      1 / 2 * pairing (μ • (n.point - s.anchor))
        (fun i => τ * Real.log (n.probability i)) u n +
      1 / η * pairing (μ • (n.point - state.point))
        (fun i => τ * (Real.log (n.probability i) - Real.log (state.probability i))) u n := by
  let project := OracleTemplate.SaddlePoint.project C
  let n := correction project s τ μ η state predicted g b
  have hp := (correction_primal_optimality hC hne hconv s hμ hη τ state predicted g b).2
    u.point hu
  obtain ⟨c, hc⟩ := correction_dual_stationarity project s hτ hη μ state predicted g b
  have hn := correction_probability_sum project s τ μ η state predicted g b
  have hd : (∑ i, (τ / η * (Real.log (n.probability i) - Real.log (state.probability i)) +
      τ / 2 * Real.log (n.probability i) + τ / 2 * Real.log (predicted.probability i) -
        affine s i predicted.point + b i) * (u.probability i - n.probability i)) = 0 := by
    dsimp only [n]
    simp_rw [hc]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, husum, hn, sub_self, mul_zero]
  change 0 ≤ pairing _ _ u n + 1 / 2 * pairing _ _ u n + 1 / η * pairing _ _ u n
  change 0 ≤ ⟪(μ / η) • (n.point - state.point) + (μ / 2) • (n.point - s.anchor) +
    (∑ i, predicted.probability i • s.field i) + (μ / 2) • (predicted.point - s.anchor) + g,
      u.point - n.point⟫ at hp
  dsimp only [n, project] at hd hp ⊢
  simp only [pairing, inner_add_left, real_inner_smul_left, add_mul, sub_mul,
    neg_mul, mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum] at hd hp ⊢
  simp only [div_eq_mul_inv] at hd hp ⊢
  nlinarith

lemma correction_model_bound {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {μ τ η : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hη : 0 < η)
    (state predicted : State ι E) (g : E) (b : ι → ℝ)
    (u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state predicted g b
    let a := (∑ i, predicted.probability i • s.field i) + (μ / 2) • (predicted.point - s.anchor) + g
    let d := fun i => -affine s i predicted.point + τ / 2 * Real.log (predicted.probability i) + b i
    η * (-pairing a d u n + (regularizer s.anchor μ τ n - regularizer s.anchor μ τ u) / 2) ≤
      potential μ τ u state - (1 + η / 2) * potential μ τ u n - potential μ τ n state :=
  prox_model_bound s.anchor μ τ hη u state _ _ _
    (correction_normal hC hne hconv s hμ hτ hη state predicted g b u hu husum)

lemma predictor_normal [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (μ : ℝ)
    (state u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let v := predictor C s τ μ η state
    0 ≤ pairing ((∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor))
      (fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i)) u v +
      1 / 2 * pairing (μ • (v.point - s.anchor))
        (fun i => τ * Real.log (v.probability i)) u v +
      1 / η * pairing (μ • (v.point - state.point))
        (fun i => τ * (Real.log (v.probability i) - Real.log (state.probability i))) u v := by
  let v := predictor C s τ μ η state
  have hp := predictor_primal_optimality hC hne hconv s hτ hη μ state hu
  obtain ⟨c, hc⟩ := predictor_dual_stationarity C s hτ hη μ state
  have hv := predictor_probability_sum C s τ μ η state
  have hd : (∑ i, (-affine s i v.point + τ * Real.log (v.probability i) +
      τ / η * (Real.log (v.probability i) - Real.log (state.probability i))) *
        (u.probability i - v.probability i)) = 0 := by
    dsimp only [v]
    simp_rw [hc]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, husum, hv, sub_self, mul_zero]
  dsimp only [v] at hd hp ⊢
  simp only [pairing, inner_add_left, real_inner_smul_left, add_mul, sub_mul,
    neg_mul, mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, div_eq_mul_inv] at hd hp ⊢
  nlinarith

lemma step_model_bound [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {μ τ η : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hη : 0 < η)
    (state : State ι E) (g : E) (b : ι → ℝ)
    (u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let v := predictor C s τ μ η state
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b
    let a := (∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor)
    let d := fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i)
    η * (-pairing (a + g) (fun i => d i + b i) u v +
      (regularizer s.anchor μ τ v - regularizer s.anchor μ τ u) / 2) ≤
        potential μ τ u state - (1 + η / 2) * potential μ τ u n -
          potential μ τ v state - (1 + η / 2) * potential μ τ n v +
            η * pairing g b v n := by
  let v := predictor C s τ μ η state
  let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b
  let a := (∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor)
  let d := fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i)
  have hnmem := (correction_primal_optimality hC hne hconv s hμ hη τ state v g b).1
  have hnprob := correction_probability_sum (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b
  have hp := prox_model_bound s.anchor μ τ hη n state v a d
    (predictor_normal hC hne hconv s hτ hη μ state n hnmem hnprob)
  have hc := correction_model_bound hC hne hconv s hμ hτ hη state v g b u hu husum
  exact two_model_bound s.anchor μ τ η u state v n a g d b hp hc

lemma step_perturbation_bound [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) {μ τ η : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hη : 0 < η)
    (state : State ι E) (g : E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let v := predictor C s τ μ η state
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b
    let a := (∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor)
    let d := fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i)
    η * (-pairing (a + g) (fun i => d i + b i) u v +
      (regularizer s.anchor μ τ v - regularizer s.anchor μ τ u) / 2) ≤
        potential μ τ u state - (1 + η / 2) * potential μ τ u n - potential μ τ v state +
          η ^ 2 * ‖g‖ ^ 2 / (2 * ((1 + η / 2) * μ)) +
            η ^ 2 / ((1 + η / 2) * τ) * ∑ i, v.probability i * (b i) ^ 2 := by
  let v := predictor C s τ μ η state
  let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b
  have hs := step_model_bound hC hne hconv s hμ hτ hη state g b u hu husum
  have hp := nonnegative_perturbation hμ hτ (by positivity : 0 < 1 + η / 2) hη.le
    (fun i => (correction_probability_pos (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b i).le)
    (predictor_probability_pos C s τ μ η state)
    (correction_probability_sum (OracleTemplate.SaddlePoint.project C) s τ μ η state v g b)
    (predictor_probability_sum C s τ μ η state) g b hb
  have he : pairing g b v n = ⟪g, v.point - n.point⟫ +
      ∑ i, (v.probability i - n.probability i) * b i := by
    unfold pairing
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← he] at hp
  dsimp only at hs ⊢
  dsimp only [v, n] at hp
  linarith

lemma stepPlan_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ η D : ℝ) (state : State ι E) (seed : StepSeed) (reply : ι × E → ℝ × E) :
    Program.cost reply (stepPlan C project s τ μ η D state seed) = 2 := by
  simp [stepPlan, Program.cost]

end LongTails.Proofs.AffineResidualSaddle
