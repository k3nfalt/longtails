import LongTails.Algorithms.ParameterFreeNsgdm
import LongTails.Proofs.GdConvex

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ParameterFreeNsgdmRun

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def mixStep (α : ℝ) (t : ℕ) (m r : E) : E :=
  if t = 0 then r else (1 - α) • m + α • r

noncomputable def runStep (α η : ℝ) (g : E → Ω → E) (s : E × E × ℕ) (ω : Ω) : E × E × ℕ :=
  let m' := mixStep α s.2.2 s.2.1 (g s.1 ω)
  (s.1 - (η / ‖m'‖) • m', m', s.2.2 + 1)

noncomputable def run (α η : ℝ) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) : ℕ → E × E × ℕ
  | 0 => (x0, 0, 0)
  | n + 1 => runStep α η g (run α η g x0 ξ n) (ξ n)

omit [CompleteSpace E] in
lemma run_time (α η : ℝ) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (n : ℕ) :
    (run α η g x0 ξ n).2.2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, runStep, ih]

omit [CompleteSpace E] in
lemma run_momentum_succ (α η : ℝ) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (n : ℕ) :
    (run α η g x0 ξ (n + 1)).2.1 =
      mixStep α n (run α η g x0 ξ n).2.1 (g (run α η g x0 ξ n).1 (ξ n)) := by
  simp [run, runStep, run_time]

omit [CompleteSpace E] in
lemma run_point_succ (α η : ℝ) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (n : ℕ) :
    (run α η g x0 ξ (n + 1)).1 =
      (run α η g x0 ξ n).1 - (η / ‖(run α η g x0 ξ (n + 1)).2.1‖) • (run α η g x0 ξ (n + 1)).2.1 := by
  simp only [run, runStep]

omit [CompleteSpace E] in
lemma normalized_move_norm (η : ℝ) (hη : 0 ≤ η) (x m : E) :
    ‖(x - (η / ‖m‖) • m) - x‖ ≤ η := by
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg hη (norm_nonneg _))]
  by_cases hm : m = 0
  · simp [hm, hη]
  · have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
    rw [div_mul_cancel₀ _ hpos.ne']

omit [CompleteSpace E] in
lemma normalized_move_inner (η : ℝ) (hη : 0 ≤ η) (x m v : E) :
    ⟪v, (x - (η / ‖m‖) • m) - x⟫ ≤ -(η * ‖v‖) + 2 * η * ‖m - v‖ := by
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right]
  by_cases hm : m = 0
  · subst hm
    simp only [norm_zero, div_zero, inner_zero_right, mul_zero, neg_zero, zero_sub, norm_neg]
    nlinarith [norm_nonneg v, hη]
  · have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
    have h1 : ⟪v, m⟫ = ‖m‖ ^ 2 - ⟪m - v, m⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
    have h2 : ⟪m - v, m⟫ ≤ ‖m - v‖ * ‖m‖ := real_inner_le_norm _ _
    have h3 : ‖v‖ ≤ ‖m‖ + ‖m - v‖ := by
      have := norm_sub_le m (m - v)
      simpa using this
    have h4 : -(η / ‖m‖ * ⟪v, m⟫) = -(η * ‖m‖) + (η / ‖m‖) * ⟪m - v, m⟫ := by
      rw [h1]; field_simp; ring
    rw [h4]
    have h5 : (η / ‖m‖) * ⟪m - v, m⟫ ≤ η * ‖m - v‖ := by
      calc (η / ‖m‖) * ⟪m - v, m⟫ ≤ (η / ‖m‖) * (‖m - v‖ * ‖m‖) :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg hη hpos.le)
        _ = η * ‖m - v‖ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 hη]

lemma descent_step {f : E → ℝ} {L : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    (η : ℝ) (hη : 0 ≤ η) (x m : E) :
    f (x - (η / ‖m‖) • m) ≤ f x - η * ‖gradient f x‖ + 2 * η * ‖m - gradient f x‖ +
      L / 2 * η ^ 2 := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - (η / ‖m‖) • m)
  have h1 := normalized_move_inner η hη x m (gradient f x)
  have h2 := normalized_move_norm η hη x m
  have h3 : L / 2 * ‖(x - (η / ‖m‖) • m) - x‖ ^ 2 ≤ L / 2 * η ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith


noncomputable def weight (α : ℝ) (t s : ℕ) : ℝ :=
  if s = 0 then (1 - α) ^ t else α * (1 - α) ^ (t - s)

noncomputable def sampleNoise (g : E → Ω → E) (grad : E → E) (x : E) (ω : Ω) : E :=
  g x ω - grad x

noncomputable def noisePart (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω)
    (t : ℕ) : E :=
  ∑ s ∈ Finset.range (t + 1), weight α t s • sampleNoise g grad (run α η g x0 ξ s).1 (ξ s)

noncomputable def biasPart (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω)
    (t : ℕ) : E :=
  (run α η g x0 ξ (t + 1)).2.1 - grad (run α η g x0 ξ t).1 - noisePart α η g grad x0 ξ t

lemma weight_succ (α : ℝ) (t s : ℕ) (hs : s ≤ t) :
    weight α (t + 1) s = (1 - α) * weight α t s := by
  unfold weight
  by_cases h : s = 0
  · simp [h, pow_succ, mul_comm]
  · simp only [h, ↓reduceIte]
    rw [show t + 1 - s = (t - s) + 1 by omega, pow_succ]
    ring

lemma weight_last (α : ℝ) (t : ℕ) : weight α (t + 1) (t + 1) = α := by
  simp [weight]

omit [CompleteSpace E] in
lemma noisePart_succ (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    noisePart α η g grad x0 ξ (t + 1) = (1 - α) • noisePart α η g grad x0 ξ t +
      α • sampleNoise g grad (run α η g x0 ξ (t + 1)).1 (ξ (t + 1)) := by
  unfold noisePart
  rw [Finset.sum_range_succ (n := t + 1), weight_last, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [weight_succ α t s (by omega), mul_smul]

omit [CompleteSpace E] in
lemma biasPart_zero (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω) :
    biasPart α η g grad x0 ξ 0 = 0 := by
  simp [biasPart, noisePart, weight, sampleNoise, run, runStep, mixStep]

omit [CompleteSpace E] in
lemma biasPart_succ (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    biasPart α η g grad x0 ξ (t + 1) = (1 - α) • biasPart α η g grad x0 ξ t +
      (1 - α) • (grad (run α η g x0 ξ t).1 - grad (run α η g x0 ξ (t + 1)).1) := by
  unfold biasPart
  rw [noisePart_succ, run_momentum_succ α η g x0 ξ (t + 1)]
  simp only [mixStep, Nat.succ_ne_zero, ↓reduceIte, sampleNoise]
  module

omit [CompleteSpace E] in
lemma biasPart_norm_le {grad : E → E} {L : ℝ} (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    ‖biasPart α η g grad x0 ξ t‖ ≤ L * η * (1 - α) / α := by
  induction t with
  | zero =>
      rw [biasPart_zero, norm_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg hL hη) (by linarith)) hα0.le
  | succ t ih =>
      rw [biasPart_succ]
      have hmove : ‖(run α η g x0 ξ t).1 - (run α η g x0 ξ (t + 1)).1‖ ≤ η := by
        rw [norm_sub_rev, run_point_succ]
        exact normalized_move_norm η hη _ _
      have hgrad : ‖grad (run α η g x0 ξ t).1 - grad (run α η g x0 ξ (t + 1)).1‖ ≤ L * η :=
        (hlip _ _).trans (mul_le_mul_of_nonneg_left hmove hL)
      have h1 : 0 ≤ 1 - α := by linarith
      calc ‖(1 - α) • biasPart α η g grad x0 ξ t +
            (1 - α) • (grad (run α η g x0 ξ t).1 - grad (run α η g x0 ξ (t + 1)).1)‖
          ≤ (1 - α) * ‖biasPart α η g grad x0 ξ t‖ +
            (1 - α) * ‖grad (run α η g x0 ξ t).1 - grad (run α η g x0 ξ (t + 1)).1‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1]
        _ ≤ (1 - α) * (L * η * (1 - α) / α) + (1 - α) * (L * η) := by
            gcongr
        _ = L * η * (1 - α) / α := by
            field_simp
            ring

omit [CompleteSpace E] in
lemma momentum_error_le {grad : E → E} {L : ℝ} (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    ‖(run α η g x0 ξ (t + 1)).2.1 - grad (run α η g x0 ξ t).1‖ ≤
      ‖noisePart α η g grad x0 ξ t‖ + L * η * (1 - α) / α := by
  have h : (run α η g x0 ξ (t + 1)).2.1 - grad (run α η g x0 ξ t).1 =
      noisePart α η g grad x0 ξ t + biasPart α η g grad x0 ξ t := by
    unfold biasPart; abel
  rw [h]
  exact (norm_add_le _ _).trans (by gcongr; exact biasPart_norm_le hlip hL hα0 hα1 hη g x0 ξ t)

lemma descent_sum {f : E → ℝ} {L : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {α η : ℝ} (hη : 0 ≤ η) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (T : ℕ) :
    η * ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖ ≤
      f x0 - f (run α η g x0 ξ T).1 +
      2 * η * ∑ t ∈ Finset.range T, ‖(run α η g x0 ξ (t + 1)).2.1 - gradient f (run α η g x0 ξ t).1‖ +
      T * (L / 2 * η ^ 2) := by
  induction T with
  | zero => simp [run]
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
      have hstep := descent_step hg hlip hL η hη (run α η g x0 ξ T).1 (run α η g x0 ξ (T + 1)).2.1
      rw [← run_point_succ] at hstep
      push_cast
      linarith

end LongTails.Proofs.ParameterFreeNsgdmRun
