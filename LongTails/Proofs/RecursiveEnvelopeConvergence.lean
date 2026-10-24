import LongTails.Proofs.RecursiveEnvelopeExecution
import LongTails.Proofs.RecursiveEnvelopeInner
import LongTails.Proofs.RecursiveEnvelopeTuning

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RecursiveEnvelopeConvergence

open OracleTemplate LongTails.Algorithms.RecursiveEnvelope
open RecursiveEnvelopeGeometry RecursiveEnvelopeExecution RecursiveEnvelopeInner RecursiveEnvelopeTuning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def tower (f : E → ℝ) (g : E → E) (L : ℝ) (d : ℕ) :
    ℕ → (E → ℝ) × (E → E)
  | 0 => (f, g)
  | i + 1 =>
      let previous := tower f g L d i
      let μ := levelSmoothness L d (i + 1)
      (envelope previous.1 previous.2 μ, envelopeField previous.2 μ)

lemma tower_model {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g) (d i : ℕ) :
    Model (levelSmoothness L d i) (tower f g L d i).1 (tower f g L d i).2 := by
  induction i with
  | zero => simpa [tower, levelSmoothness_zero] using h
  | succ i ih => exact ih.envelope_model (levelSmoothness_pos h.pos _ _)

lemma tower_min {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {xs : E} (hm : ∀ x, f xs ≤ f x) (d i : ℕ) :
    (tower f g L d i).1 xs = f xs ∧ ∀ x, f xs ≤ (tower f g L d i).1 x := by
  induction i with
  | zero => exact ⟨rfl, hm⟩
  | succ i ih =>
      have hh := (tower_model h d i).envelope_min_value (levelSmoothness_pos h.pos d (i + 1))
        (xs := xs) (by simpa only [ih.1] using ih.2)
      simpa only [tower, ih.1] using hh

lemma prox_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {d i : ℕ} (hd : 1 ≤ d) (hi : i ≤ d) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (gradientPlan L d (2048 * d * 2 ^ d) i x) k -
      (tower f g L d i).2 x‖ ≤ levelError d i * ‖(tower f g L d i).2 x‖)
    (x : E) (call : ℕ) :
    regularized (tower f g L d i).1 (levelSmoothness L d (i + 1)) x
      (evalAt reply (proxPlan L d (2048 * d * 2 ^ d) i x) call) -
      (tower f g L d (i + 1)).1 x ≤ levelError d (i + 1) ^ 2 *
        levelSmoothness L d (i + 1) / 2 *
        ‖x - prox (tower f g L d i).2 (levelSmoothness L d (i + 1)) x‖ ^ 2 := by
  let m := 2048 * d * 2 ^ d
  have hh := inner_accuracy (tower_model h d i) (levelSmoothness_pos h.pos d (i + 1))
    (levelError_pos d i).le (levelError_small hi)
    (fun k y => evalAt reply (gradientPlan L d m i y) (call + m ^ i * k))
    (fun k y => herr _ _) x m 0 (inner_transient h.pos hd hi)
  rw [levelError_succ]
  unfold proxPlan
  have he := evalAt_innerPlan reply (gradientPlan L d m i)
    (levelSmoothness L d i + levelSmoothness L d (i + 1))
    (levelSmoothness L d (i + 1)) (2 * levelError d i) x m call 0 (x, x)
  simp only [mul_zero, add_zero] at he
  rw [← he] at hh
  exact hh

lemma gradient_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {d : ℕ} (hd : 1 ≤ d) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖reply k x - g x‖ ≤ levelError d 0 * ‖g x‖)
    (i : ℕ) (hi : i ≤ d) :
    ∀ call x, ‖evalAt reply (gradientPlan L d (2048 * d * 2 ^ d) i x) call -
      (tower f g L d i).2 x‖ ≤ levelError d i * ‖(tower f g L d i).2 x‖ := by
  induction i with
  | zero => exact herr
  | succ i ih =>
      have hi' : i ≤ d := by omega
      have he := ih hi'
      intro call x
      let μ := levelSmoothness L d (i + 1)
      let p := prox (tower f g L d i).2 μ x
      let z := evalAt reply (proxPlan L d (2048 * d * 2 ^ d) i x) call
      have hμ : 0 < μ := levelSmoothness_pos h.pos _ _
      have ha := prox_accuracy h hd hi' reply he x call
      have hg := (tower_model h d i).prox_growth hμ x z
      have hb : 0 < levelError d (i + 1) := levelError_pos _ _
      have hn : ‖z - p‖ ≤ levelError d (i + 1) * ‖x - p‖ := by
        have hs : ‖z - p‖ ^ 2 ≤ (levelError d (i + 1) * ‖x - p‖) ^ 2 := by
          change regularized (tower f g L d i).1 μ x z -
            envelope (tower f g L d i).1 (tower f g L d i).2 μ x ≤
              levelError d (i + 1) ^ 2 * μ / 2 * ‖x - p‖ ^ 2 at ha
          change _ + μ / 2 * ‖z - p‖ ^ 2 ≤ _ at hg
          nlinarith
        nlinarith only [hs, norm_nonneg (z - p), mul_nonneg hb.le (norm_nonneg (x - p))]
      rw [evalAt_gradientPlan]
      change ‖μ • (x - z) - μ • (x - p)‖ ≤ levelError d (i + 1) * ‖μ • (x - p)‖
      have hid : μ • (x - z) - μ • (x - p) = μ • (p - z) := by module
      rw [hid, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_sub_rev p z]
      nlinarith

noncomputable def multiplier (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => multiplier d i * (1 + levelError d (i + 1) ^ 2)

lemma multiplier_nonneg (d i : ℕ) : 0 ≤ multiplier d i := by
  induction i with
  | zero => norm_num [multiplier]
  | succ i ih => exact mul_nonneg ih (by positivity)

lemma multiplier_le {d i : ℕ} (hi : i ≤ d) :
    multiplier d i ≤ 1 + 2 * levelError d i ^ 2 := by
  induction i with
  | zero => simp only [multiplier]; nlinarith [sq_nonneg (levelError d 0)]
  | succ i ih =>
      have hp := ih (by omega)
      have hb := levelError_small hi
      have hb0 := levelError_pos d (i + 1)
      have he := levelError_succ d i
      have hh := mul_le_mul_of_nonneg_right hp
        (by positivity : 0 ≤ 1 + levelError d (i + 1) ^ 2)
      change multiplier d i * (1 + levelError d (i + 1) ^ 2) ≤ _
      have hsq : levelError d (i + 1) ^ 2 ≤ 1 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (levelError d i))
      nlinarith

lemma recovery_accuracy {L : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {xs : E} (hm : ∀ x, f xs ≤ f x) {d : ℕ} (hd : 1 ≤ d)
    (reply : ℕ → E → E) (herr : ∀ k x, ‖reply k x - g x‖ ≤ levelError d 0 * ‖g x‖)
    (i : ℕ) (hi : i ≤ d) (x : E) (call : ℕ) :
    f (evalAt reply (recoveryPlan L d (2048 * d * 2 ^ d) i x) call) - f xs ≤
      multiplier d i * ((tower f g L d i).1 x - f xs) := by
  induction i generalizing x call with
  | zero => simp [recoveryPlan, evalAt, tower, multiplier]
  | succ i ih =>
      have hi' : i ≤ d := by omega
      have he := gradient_accuracy h hd reply herr i hi'
      have ha := prox_accuracy h hd hi' reply he x call
      have hmin := tower_min h hm d i
      have hr := recovery (levelSmoothness_pos h.pos d (i + 1))
        (xs := xs) (by simpa only [hmin.1] using hmin.2) ha
      rw [hmin.1] at hr
      rw [evalAt_recoveryPlan]
      apply (ih hi' _ _).trans
      have hh := mul_le_mul_of_nonneg_left hr (multiplier_nonneg d i)
      simpa only [multiplier, tower, mul_assoc] using hh

lemma plan_accuracy {L R ε : ℝ} {f : E → ℝ} {g : E → E} (h : Model L f g)
    {xs x0 : E} (hm : ∀ x, f xs ≤ f x) (hdist : ‖x0 - xs‖ ≤ R)
    {d : ℕ} (hd : 1 ≤ d) (hscale : levelSmoothness L d d * R ^ 2 ≤ ε)
    (reply : ℕ → E → E) (herr : ∀ k x, ‖reply k x - g x‖ ≤ levelError d 0 * ‖g x‖) :
    f (evalAt reply (recoveryPlan L d (2048 * d * 2 ^ d) d x0) 0) - f xs ≤ ε := by
  have ha := recovery_accuracy h hm hd reply herr d le_rfl x0 0
  have hmult := multiplier_le (d := d) le_rfl
  have hb := levelError_small (d := d) le_rfl
  have hb0 := levelError_pos d d
  have hmult2 : multiplier d d ≤ 2 := by nlinarith
  have hmin := tower_min h hm d d
  have hgap0 : 0 ≤ (tower f g L d d).1 x0 - f xs := sub_nonneg.mpr (hmin.2 x0)
  have hgap : (tower f g L d d).1 x0 - f xs ≤ levelSmoothness L d d / 2 * R ^ 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hh := (tower_model h (j + 1) j).envelope_initial_gap
      (levelSmoothness_pos h.pos (j + 1) (j + 1)) xs x0
    rw [(tower_min h hm (j + 1) j).1] at hh
    have hn := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    have hcoef : 0 ≤ levelSmoothness L (j + 1) (j + 1) / 2 :=
      div_nonneg (levelSmoothness_pos h.pos _ _).le (by norm_num)
    have hp := mul_le_mul_of_nonneg_left hn hcoef
    exact hh.trans hp
  have hh := mul_le_mul_of_nonneg_right hmult2 hgap0
  nlinarith

end LongTails.Proofs.RecursiveEnvelopeConvergence
