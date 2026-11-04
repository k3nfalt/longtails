import LongTails.Proofs.SharpDistanceInner
import LongTails.Proofs.SharpDistanceParameters
import LongTails.Proofs.SharpEnvelopeConvergence

namespace LongTails.Proofs.SharpDistanceConvergence

open OracleTemplate LongTails.Algorithms.SharpDistanceEnvelope
open LongTails.Algorithms.SharpEnvelope (smoothness precision momentum)
open RecursiveEnvelopeGeometry RecursiveEnvelopeExecution SharpEnvelopeParameters
open SharpEnvelopeConvergence (tower tower_model tower_min)
open SharpDistanceParameters (iterations)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma prox_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {b d i : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b) (hi : i ≤ d)
    (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (gradientPlan L b d (iterations b) i x) k -
      (tower f g L b i).2 x‖ ≤ precision b d i * ‖(tower f g L b i).2 x‖)
    (x : E) (call : ℕ) :
    let μ := smoothness L b (i + 1)
    let p := prox (tower f g L b i).2 μ x
    let z := evalAt reply (proxPlan L b d (iterations b) i x) call
    ‖z - p‖ ≤ precision b d (i + 1) * ‖x - p‖ ∧
      regularized (tower f g L b i).1 μ x z - (tower f g L b (i + 1)).1 x ≤
        (2 * precision b d (i + 1)) ^ 2 * μ / 2 * ‖x - p‖ ^ 2 := by
  have hb1 : 1 ≤ b := by omega
  have hμ := smoothness_pos h.pos hb1 (i + 1)
  have hrel := smoothness_succ L hb1 i
  have ht0 : 0 < momentum b := by unfold momentum; positivity
  have hτ : 0 < 1 / (8 * ((d : ℝ) + 1)) := by positivity
  have hτ1 : 1 / (8 * ((d : ℝ) + 1)) ≤ 1 / 8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsc := sharp_scale hb1 hμ hrel
  have hsc' : smoothness L b (i + 1) / (smoothness L b i + smoothness L b (i + 1)) =
      4 * momentum b ^ 2 := by
    have hsum : 0 < smoothness L b i + smoothness L b (i + 1) :=
      add_pos (smoothness_pos h.pos hb1 i) hμ
    field_simp at hsc ⊢
    nlinarith only [hsc]
  have hh := SharpDistanceInner.inner_accuracy (tower_model h hb1 i) hμ ht0
    (precision_pos hb1 d i).le (precision_small hb1 hi) hτ hτ1
    (sharp_small hb hd) (sharp_noise hb hi hd) hsc'
    (gradientPlan L b d (iterations b) i) reply herr x (iterations b) (iterations b) call
    (SharpDistanceParameters.warm_transient hb hi hμ hrel)
    (SharpDistanceParameters.refinement_transient hb hd)
  have ht := precision_transfer hb1 hi
  have hβ := precision_pos hb1 d i
  have hβnext := precision_pos hb1 d (i + 1)
  have hmono : precision b d i ≤ precision b d (i + 1) := by
    nlinarith [mul_nonneg hτ.le hβ.le]
  have hs := pow_le_pow_left₀ hβ.le hmono 2
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ 2 * smoothness L b (i + 1) *
      ‖x - prox (tower f g L b i).2 (smoothness L b (i + 1)) x‖ ^ 2 by positivity)
  refine ⟨hh.1.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _)), ?_⟩
  change regularized (tower f g L b i).1 (smoothness L b (i + 1)) x
    (evalAt reply (proxPlan L b d (iterations b) i x) call) -
    envelope (tower f g L b i).1 (tower f g L b i).2 (smoothness L b (i + 1)) x ≤ _
  calc
    _ ≤ 2 * smoothness L b (i + 1) * precision b d i ^ 2 *
        ‖x - prox (tower f g L b i).2 (smoothness L b (i + 1)) x‖ ^ 2 := hh.2
    _ ≤ _ := by nlinarith only [hm]

lemma gradient_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {b d : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b)
    (reply : ℕ → E → E) (herr : ∀ k x, ‖reply k x - g x‖ ≤ precision b d 0 * ‖g x‖)
    (i : ℕ) (hi : i ≤ d) :
    ∀ call x, ‖evalAt reply (gradientPlan L b d (iterations b) i x) call -
      (tower f g L b i).2 x‖ ≤ precision b d i * ‖(tower f g L b i).2 x‖ := by
  induction i with
  | zero => exact herr
  | succ i ih =>
      have hi' : i ≤ d := by omega
      have he := ih hi'
      intro call x
      let μ := smoothness L b (i + 1)
      let p := prox (tower f g L b i).2 μ x
      let z := evalAt reply (proxPlan L b d (iterations b) i x) call
      have hμ : 0 < μ := smoothness_pos h.pos (by omega : 1 ≤ b) _
      have hn := (prox_accuracy h hb hd hi' reply he x call).1
      rw [SharpDistanceExecution.evalAt_gradientPlan]
      change ‖μ • (x - z) - μ • (x - p)‖ ≤ precision b d (i + 1) * ‖μ • (x - p)‖
      have hid : μ • (x - z) - μ • (x - p) = μ • (p - z) := by module
      rw [hid, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_sub_rev p z]
      change ‖z - p‖ ≤ precision b d (i + 1) * ‖x - p‖ at hn
      nlinarith

noncomputable def multiplier (b d : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => multiplier b d i * (1 + (2 * precision b d (i + 1)) ^ 2)

lemma multiplier_nonneg (b d i : ℕ) : 0 ≤ multiplier b d i := by
  induction i with
  | zero => norm_num [multiplier]
  | succ i ih => exact mul_nonneg ih (by positivity)

lemma precision_square_small {b d i : ℕ} (hb : 16 ≤ b)
    (hd : 16 * ((d : ℝ) + 1) ≤ b) (hi : i ≤ d) :
    (2 * precision b d i) ^ 2 ≤ 1 / (2 * ((d : ℝ) + 1)) := by
  have hb1 : 1 ≤ b := by omega
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hβ0 := precision_pos hb1 d i
  have hβ1 := precision_small hb1 hi
  have hβ := precision_upper hb1 hi
  have hp : (b : ℝ) ≤ (b : ℝ) ^ 12 := by
    simpa using pow_le_pow_right₀ hbR (show 1 ≤ 12 by omega)
  have hle : 1 / (50 * (b : ℝ) ^ 12) ≤ 1 / (2 * ((d : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hh := hβ.trans hle
  nlinarith

lemma multiplier_le {b d i : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b)
    (hi : i ≤ d) : multiplier b d i ≤ 1 + (i : ℝ) / ((d : ℝ) + 1) := by
  induction i with
  | zero => simp [multiplier]
  | succ i ih =>
      have hi' : i ≤ d := by omega
      have hp := ih hi'
      have hiR : (i : ℝ) ≤ d := by exact_mod_cast hi'
      have hD : (0 : ℝ) < d + 1 := by positivity
      have hfrac : (i : ℝ) / ((d : ℝ) + 1) ≤ 1 := (div_le_one hD).mpr (by linarith)
      have hmult : multiplier b d i ≤ 2 := by linarith
      have hβ := precision_square_small hb hd hi
      have hinc := mul_le_mul hmult hβ (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      change multiplier b d i * (1 + (2 * precision b d (i + 1)) ^ 2) ≤ _
      push_cast
      have he : 2 * (1 / (2 * ((d : ℝ) + 1))) = 1 / ((d : ℝ) + 1) := by field_simp
      rw [he] at hinc
      rw [add_div]
      nlinarith only [hp, hinc]

lemma recovery_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {xs : E} (hm : ∀ x, f xs ≤ f x) {b d : ℕ}
    (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b)
    (reply : ℕ → E → E) (herr : ∀ k x, ‖reply k x - g x‖ ≤ precision b d 0 * ‖g x‖)
    (i : ℕ) (hi : i ≤ d) (x : E) (call : ℕ) :
    f (evalAt reply (recoveryPlan L b d (iterations b) i x) call) - f xs ≤
      multiplier b d i * ((tower f g L b i).1 x - f xs) := by
  induction i generalizing x call with
  | zero => simp [recoveryPlan, evalAt, tower, multiplier]
  | succ i ih =>
      have hi' : i ≤ d := by omega
      have he := gradient_accuracy h hb hd reply herr i hi'
      have ha := (prox_accuracy h hb hd hi' reply he x call).2
      have hmin := tower_min h hm (by omega : 1 ≤ b) i
      have hr := recovery (smoothness_pos h.pos (by omega : 1 ≤ b) (i + 1))
        (xs := xs) (by simpa only [hmin.1] using hmin.2) ha
      rw [hmin.1] at hr
      rw [SharpDistanceExecution.evalAt_recoveryPlan]
      apply (ih hi' _ _).trans
      have hh := mul_le_mul_of_nonneg_left hr (multiplier_nonneg b d i)
      simpa only [multiplier, tower, mul_assoc] using hh

lemma plan_accuracy {L R ε : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {xs x0 : E} (hm : ∀ x, f xs ≤ f x) (hdist : ‖x0 - xs‖ ≤ R)
    {b d : ℕ} (hb : 16 ≤ b) (hd : 16 * ((d : ℝ) + 1) ≤ b) (hd1 : 1 ≤ d)
    (hscale : smoothness L b d * R ^ 2 ≤ ε)
    (reply : ℕ → E → E) (herr : ∀ k x, ‖reply k x - g x‖ ≤ precision b d 0 * ‖g x‖) :
    f (evalAt reply (recoveryPlan L b d (iterations b) d x0) 0) - f xs ≤ ε := by
  have ha := recovery_accuracy h hm hb hd reply herr d le_rfl x0 0
  have hmult := multiplier_le hb hd (i := d) le_rfl
  have hfrac : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hmult2 : multiplier b d d ≤ 2 := by linarith
  have hmin := tower_min h hm (by omega : 1 ≤ b) d
  have hgap0 : 0 ≤ (tower f g L b d).1 x0 - f xs := sub_nonneg.mpr (hmin.2 x0)
  have hgap : (tower f g L b d).1 x0 - f xs ≤ smoothness L b d / 2 * R ^ 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hh := (tower_model h (by omega : 1 ≤ b) j).envelope_initial_gap
      (smoothness_pos h.pos (by omega : 1 ≤ b) (j + 1)) xs x0
    rw [(tower_min h hm (by omega : 1 ≤ b) j).1] at hh
    have hn := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    have hcoef : 0 ≤ smoothness L b (j + 1) / 2 :=
      div_nonneg (smoothness_pos h.pos (by omega : 1 ≤ b) _).le (by norm_num)
    have hp := mul_le_mul_of_nonneg_left hn hcoef
    exact hh.trans hp
  have hh := mul_le_mul_of_nonneg_right hmult2 hgap0
  nlinarith

end LongTails.Proofs.SharpDistanceConvergence
