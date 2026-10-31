import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Model (L : ℝ) (f : E → ℝ) (g : E → E) : Prop where
  pos : 0 < L
  lower : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y
  upper : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2

lemma Model.bregman {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪g y, x - y⟫) := by
  let z := x - (1 / L) • (g x - g y)
  have h1 := h.upper x z
  have h2 := h.lower y z
  have hz : z - x = -(1 / L) • (g x - g y) := by simp [z]
  have hzy : z - y = (x - y) - (1 / L) • (g x - g y) := by dsimp [z]; abel
  rw [hz, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at h1
  rw [hzy, inner_sub_right, inner_smul_right] at h2
  have he : ⟪g x, g x - g y⟫ - ⟪g y, g x - g y⟫ = ‖g x - g y‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hp := h.pos
  have hn : L ≠ 0 := ne_of_gt hp
  have h3 : L * (1 / L) = 1 := by field_simp
  have h4 : L ^ 2 * (1 / L) ^ 2 = 1 := by field_simp
  have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * L)
  have h6 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * L)
  field_simp [hn] at h5 h6
  nlinarith

lemma Model.cocoercive {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ L * ⟪g x - g y, x - y⟫ := by
  have h1 := h.bregman x y
  have h2 := h.bregman y x
  rw [norm_sub_rev (g y) (g x)] at h2
  have he : ⟪g x - g y, x - y⟫ = -⟪g x, y - x⟫ - ⟪g y, x - y⟫ := by
    rw [inner_sub_left, ← inner_neg_right (g x), neg_sub]
  rw [he]
  nlinarith

lemma Model.lipschitz {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g) (x y : E) :
    ‖g x - g y‖ ≤ L * ‖x - y‖ := by
  have h1 := h.cocoercive x y
  have h2 := mul_le_mul_of_nonneg_left (real_inner_le_norm (g x - g y) (x - y)) h.pos.le
  have hn := norm_nonneg (g x - g y)
  by_cases hz : ‖g x - g y‖ = 0
  · rw [hz]; exact mul_nonneg h.pos.le (norm_nonneg _)
  · have hp : 0 < ‖g x - g y‖ := lt_of_le_of_ne hn (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := ‖g x - g y‖) _ hp
    nlinarith [h1.trans h2]

lemma Model.monotone {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g) (x y : E) :
    0 ≤ ⟪g x - g y, x - y⟫ := by
  have hc := h.cocoercive x y
  exact nonneg_of_mul_nonneg_right (le_trans (sq_nonneg _) hc) h.pos

lemma exists_zero [CompleteSpace E] {G : E → E} {μ M : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M)
    (hm : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ∀ x y, ‖G x - G y‖ ≤ M * ‖x - y‖) : ∃ x, G x = 0 := by
  have hM : 0 < M := lt_of_lt_of_le hμ hμM
  let s := μ / M ^ 2
  let q := 1 - μ ^ 2 / M ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hq0 : 0 ≤ q := by
    dsimp [q]
    have hh : μ ^ 2 / M ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    have hh : 0 < μ ^ 2 / M ^ 2 := by positivity
    linarith
  let T : E → E := fun x => x - s • G x
  have hT : ∀ x y, ‖T x - T y‖ ^ 2 ≤ q * ‖x - y‖ ^ 2 := by
    intro x y
    have he : T x - T y = (x - y) - s • (G x - G y) := by dsimp [T]; module
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have h1 := mul_le_mul_of_nonneg_left (hm x y) (by positivity : 0 ≤ 2 * s)
    have h2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hl x y) 2) (sq_nonneg s)
    have h3 : s ^ 2 * M ^ 2 = s * μ := by dsimp [s]; field_simp
    have h4 : q = 1 - s * μ := by dsimp [q, s]; ring
    rw [mul_pow] at h2
    rw [← mul_assoc, h3] at h2
    have hi : ⟪x - y, G x - G y⟫ = ⟪G x - G y, x - y⟫ := real_inner_comm _ _
    rw [hi, h4]
    nlinarith
  let K : NNReal := ⟨Real.sqrt q, Real.sqrt_nonneg _⟩
  have hK : LipschitzWith K T := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    change ‖T x - T y‖ ≤ Real.sqrt q * ‖x - y‖
    rw [← Real.sqrt_sq (norm_nonneg (T x - T y)),
      ← Real.sqrt_sq (norm_nonneg (x - y)), ← Real.sqrt_mul hq0]
    exact Real.sqrt_le_sqrt (hT x y)
  have hc : ContractingWith K T := by
    refine ⟨?_, hK⟩
    have hh : Real.sqrt q < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hq1
    exact hh
  let x := ContractingWith.fixedPoint T hc
  refine ⟨x, ?_⟩
  have hf : T x = x := ContractingWith.fixedPoint_isFixedPt hc
  have hz : s • G x = 0 := by
    dsimp [T] at hf
    exact sub_eq_self.mp hf
  exact (smul_eq_zero.mp hz).resolve_left hs.ne'

lemma Model.exists_regularized_zero [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c : E) : ∃ x, g x + μ • (x - c) = 0 := by
  apply exists_zero hμ (show μ ≤ L + μ by linarith [h.pos])
  · intro x y
    have he : (g x + μ • (x - c)) - (g y + μ • (y - c)) =
        (g x - g y) + μ • (x - y) := by module
    rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [h.monotone x y]
  · intro x y
    have he : (g x + μ • (x - c)) - (g y + μ • (y - c)) =
        (g x - g y) + μ • (x - y) := by module
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ, add_mul]
    exact add_le_add (h.lipschitz x y) le_rfl

noncomputable def regularized (f : E → ℝ) (μ : ℝ) (c x : E) : ℝ :=
  f x + μ / 2 * ‖x - c‖ ^ 2

noncomputable def prox (g : E → E) (μ : ℝ) (c : E) : E :=
  Classical.epsilon fun x => g x + μ • (x - c) = 0

noncomputable def envelope (f : E → ℝ) (g : E → E) (μ : ℝ) (c : E) : ℝ :=
  regularized f μ c (prox g μ c)

noncomputable def envelopeField (g : E → E) (μ : ℝ) (c : E) : E :=
  μ • (c - prox g μ c)

lemma squared_shift (x y c : E) :
    ‖y - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, y - x⟫ + ‖y - x‖ ^ 2 := by
  have he : y - c = (x - c) + (y - x) := by abel
  rw [he, norm_add_sq_real]

lemma Model.regularized_lower {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (c x y : E) :
    regularized f μ c x + ⟪g x + μ • (x - c), y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤
      regularized f μ c y := by
  unfold regularized
  rw [squared_shift x y c, inner_add_left, real_inner_smul_left]
  linarith [h.lower x y]

lemma Model.regularized_upper {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (c x y : E) :
    regularized f μ c y ≤ regularized f μ c x +
      ⟪g x + μ • (x - c), y - x⟫ + (L + μ) / 2 * ‖y - x‖ ^ 2 := by
  unfold regularized
  rw [squared_shift x y c, inner_add_left, real_inner_smul_left]
  linarith [h.upper x y]

lemma Model.prox_stationary [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c : E) : g (prox g μ c) + μ • (prox g μ c - c) = 0 :=
  Classical.epsilon_spec (h.exists_regularized_zero hμ c)

lemma Model.prox_field [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c : E) : g (prox g μ c) = envelopeField g μ c := by
  have hh := h.prox_stationary hμ c
  unfold envelopeField
  have he : μ • (c - prox g μ c) = -(μ • (prox g μ c - c)) := by module
  rw [he]
  exact eq_neg_of_add_eq_zero_left hh

lemma Model.prox_growth [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    envelope f g μ c + μ / 2 * ‖x - prox g μ c‖ ^ 2 ≤ regularized f μ c x := by
  have hh := h.regularized_lower (μ := μ) c (prox g μ c) x
  rw [h.prox_stationary hμ, inner_zero_left, add_zero] at hh
  exact hh

lemma Model.prox_minimum [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    envelope f g μ c ≤ regularized f μ c x := by
  have hh := h.prox_growth hμ c x
  have hn : 0 ≤ μ / 2 * ‖x - prox g μ c‖ ^ 2 := by positivity
  linarith

lemma envelope_support_identity (f : E → ℝ) (μ : ℝ) (x y p q : E) :
    regularized f μ y q - regularized f μ x p - ⟪μ • (x - p), y - x⟫ =
      f q - f p - ⟪μ • (x - p), q - p⟫ +
        μ / 2 * ‖(q - p) - (y - x)‖ ^ 2 := by
  unfold regularized
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  ring

lemma Model.envelope_lower [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (x y : E) :
    envelope f g μ x + ⟪envelopeField g μ x, y - x⟫ ≤ envelope f g μ y := by
  have hh := h.lower (prox g μ x) (prox g μ y)
  rw [h.prox_field hμ] at hh
  have he := envelope_support_identity f μ x y (prox g μ x) (prox g μ y)
  change envelope f g μ y - envelope f g μ x - ⟪envelopeField g μ x, y - x⟫ = _ at he
  have hn : 0 ≤ μ / 2 * ‖(prox g μ y - prox g μ x) - (y - x)‖ ^ 2 := by positivity
  change f (prox g μ x) + ⟪μ • (x - prox g μ x), prox g μ y - prox g μ x⟫ ≤ _ at hh
  linarith

lemma Model.envelope_upper [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (x y : E) :
    envelope f g μ y ≤ envelope f g μ x +
      ⟪envelopeField g μ x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 := by
  have hh := h.prox_minimum hμ y (prox g μ x)
  have he := envelope_support_identity f μ x y (prox g μ x) (prox g μ x)
  simp only [sub_self, inner_zero_right, zero_sub, norm_neg, zero_add] at he
  change regularized f μ y (prox g μ x) - envelope f g μ x -
    ⟪envelopeField g μ x, y - x⟫ = μ / 2 * ‖y - x‖ ^ 2 at he
  linarith

lemma Model.envelope_model [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) : Model μ (envelope f g μ) (envelopeField g μ) :=
  ⟨hμ, h.envelope_lower hμ, h.envelope_upper hμ⟩

lemma Model.envelope_min_value [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) {xs : E} (hm : ∀ x, f xs ≤ f x) :
    envelope f g μ xs = f xs ∧ ∀ x, f xs ≤ envelope f g μ x := by
  have hlo : ∀ x, f xs ≤ envelope f g μ x := by
    intro x
    unfold envelope regularized
    have hn : 0 ≤ μ / 2 * ‖prox g μ x - x‖ ^ 2 := by positivity
    linarith [hm (prox g μ x)]
  refine ⟨le_antisymm ?_ (hlo xs), hlo⟩
  simpa [regularized] using h.prox_minimum hμ xs xs

lemma Model.envelope_initial_gap [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (xs x : E) :
    envelope f g μ x - f xs ≤ μ / 2 * ‖x - xs‖ ^ 2 := by
  have hh := h.prox_minimum hμ x xs
  simpa [regularized, norm_sub_rev xs x, sub_le_iff_le_add, add_comm] using hh

lemma Model.regularized_distance [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    μ * ‖x - prox g μ c‖ ≤ ‖g x + μ • (x - c)‖ := by
  let p := prox g μ c
  have hm := h.monotone x p
  have hs := h.prox_stationary hμ c
  have he : g x + μ • (x - c) = (g x - g p) + μ • (x - p) := by
    have hh : g p = -(μ • (p - c)) := eq_neg_of_add_eq_zero_left hs
    rw [hh]
    module
  have hi : μ * ‖x - p‖ ^ 2 ≤ ⟪g x + μ • (x - c), x - p⟫ := by
    rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith
  have hc := real_inner_le_norm (g x + μ • (x - c)) (x - p)
  by_cases hz : ‖x - p‖ = 0
  · change μ * ‖x - p‖ ≤ _
    rw [hz, mul_zero]
    exact norm_nonneg _
  · have hp : 0 < ‖x - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change μ * ‖x - p‖ ≤ _
    apply le_of_mul_le_mul_right (a := ‖x - p‖) _ hp
    nlinarith [hi.trans hc]

lemma Model.regularized_oracle_bound [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    ‖g x‖ ≤ 2 * ‖g x + μ • (x - c)‖ + μ * ‖c - prox g μ c‖ := by
  have hd := h.regularized_distance hμ c x
  have ht : ‖x - c‖ ≤ ‖x - prox g μ c‖ + ‖prox g μ c - c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have he : g x = (g x + μ • (x - c)) - μ • (x - c) := by abel
  calc
    ‖g x‖ = ‖(g x + μ • (x - c)) - μ • (x - c)‖ := by rw [← he]
    _ ≤ ‖g x + μ • (x - c)‖ + ‖μ • (x - c)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖g x + μ • (x - c)‖ + μ * ‖c - prox g μ c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
      rw [norm_sub_rev (prox g μ c) c] at ht
      nlinarith [mul_le_mul_of_nonneg_left ht hμ.le]

lemma recovery {μ β : ℝ} {f : E → ℝ} {g : E → E}
    (hμ : 0 < μ) {xs c x : E} (hm : ∀ y, f xs ≤ f y)
    (hx : regularized f μ c x - envelope f g μ c ≤ β ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2) :
    f x - f xs ≤ (1 + β ^ 2) * (envelope f g μ c - f xs) := by
  have he : μ / 2 * ‖c - prox g μ c‖ ^ 2 ≤ envelope f g μ c - f xs := by
    unfold envelope regularized
    rw [norm_sub_rev c (prox g μ c)]
    linarith [hm (prox g μ c)]
  have hh := mul_le_mul_of_nonneg_left he (sq_nonneg β)
  have hn : 0 ≤ μ / 2 * ‖x - c‖ ^ 2 := by positivity
  unfold regularized at hx
  nlinarith

end LongTails.Proofs.RecursiveEnvelopeGeometry
