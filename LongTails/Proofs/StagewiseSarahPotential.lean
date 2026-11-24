import LongTails.Proofs.StagewiseSarahProcess
import LongTails.Proofs.GdConvex
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace OracleTemplate.StagewiseSarah

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (f : E → ℝ) (g : E → Ω → E) (L Lbar μ σ fstar : ℝ) : Prop where
  hμ : 0 < μ
  grad : ∀ x, HasGradientAt f (gradient f x) x
  smooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  lower : ∀ x, fstar ≤ f x
  pl : ∀ x, 2 * μ * (f x - fstar) ≤ ‖gradient f x‖ ^ 2
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  varInt : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2
  mssInt : ∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p
  mss : ∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ Lbar ^ 2 * ‖x - y‖ ^ 2

structure Good (L Lbar μ : ℝ) (e : Epoch) : Prop where
  hB : 1 ≤ e.B
  hη : 0 < e.η
  hL : e.η * L ≤ 1 / 2
  hbar : 4 * Lbar ^ 2 * e.η ^ 2 * e.m ≤ 1
  hμ : ((e.m : ℝ) + 1) * (e.η * μ) ≤ 1 / 2

noncomputable def gain (μ : ℝ) (e : Epoch) : ℝ := (1 - e.η * μ) ^ (e.m + 1)

noncomputable def noise (σ : ℝ) (e : Epoch) : ℝ := e.η * ((e.m : ℝ) + 1) * σ ^ 2 / e.B

noncomputable def after (μ σ : ℝ) : List Epoch → ℝ → ℝ
  | [], a => a
  | e :: rest, a => after μ σ rest (gain μ e * (a + noise σ e))

noncomputable def slope (μ : ℝ) : List Epoch → ℝ
  | [] => 1
  | e :: rest => slope μ rest * gain μ e

lemma after_affine (μ σ : ℝ) (l : List Epoch) (a : ℝ) :
    after μ σ l a = slope μ l * a + after μ σ l 0 := by
  induction l generalizing a with
  | nil => simp [after, slope]
  | cons e rest ih =>
    simp only [after, slope]
    rw [ih, ih (gain μ e * (0 + noise σ e))]
    ring

section GoodFacts

variable {L Lbar μ : ℝ} {e : Epoch}

lemma Good.step_small (h : Good L Lbar μ e) (hμ : 0 < μ) : e.η * μ ≤ 1 / 2 := by
  have h1 := h.hμ
  have h2 : 0 ≤ e.η * μ := mul_nonneg h.hη.le hμ.le
  have h3 : (0 : ℝ) ≤ e.m := Nat.cast_nonneg _
  nlinarith

lemma Good.theta_bounds (h : Good L Lbar μ e) (hμ : 0 < μ) :
    1 / 2 ≤ 1 - e.η * μ ∧ 1 - e.η * μ ≤ 1 := by
  have h1 := h.step_small hμ
  have h2 : 0 ≤ e.η * μ := mul_nonneg h.hη.le hμ.le
  constructor <;> linarith

lemma Good.pow_bounds (h : Good L Lbar μ e) (hμ : 0 < μ) (k : ℕ) (hk : k ≤ e.m + 1) :
    1 / 2 ≤ (1 - e.η * μ) ^ k ∧ (1 - e.η * μ) ^ k ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := h.theta_bounds hμ
  refine ⟨?_, pow_le_one₀ (by linarith) hhi⟩
  have hb := one_add_mul_le_pow (a := -(e.η * μ)) (by linarith) k
  have h2 : 0 ≤ e.η * μ := mul_nonneg h.hη.le hμ.le
  have hk' : (k : ℝ) ≤ (e.m : ℝ) + 1 := by exact_mod_cast hk
  have h3 : (k : ℝ) * (e.η * μ) ≤ ((e.m : ℝ) + 1) * (e.η * μ) :=
    mul_le_mul_of_nonneg_right hk' h2
  have h4 := h.hμ
  have he : (1 + -(e.η * μ)) = 1 - e.η * μ := by ring
  rw [he] at hb
  linarith

lemma Good.gain_bounds (h : Good L Lbar μ e) (hμ : 0 < μ) :
    1 / 2 ≤ gain μ e ∧ gain μ e ≤ 1 := h.pow_bounds hμ (e.m + 1) le_rfl

lemma Good.noise_nonneg (h : Good L Lbar μ e) (σ : ℝ) : 0 ≤ noise σ e := by
  unfold noise
  have := h.hη
  positivity

lemma slope_nonneg (hμ : 0 < μ) (l : List Epoch) (hl : ∀ e ∈ l, Good L Lbar μ e) :
    0 ≤ slope μ l := by
  induction l with
  | nil => simp [slope]
  | cons e rest ih =>
    simp only [slope]
    have h1 := ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have h2 := ((hl e List.mem_cons_self).gain_bounds hμ).1
    exact mul_nonneg h1 (by linarith)

lemma after_zero_nonneg (hμ : 0 < μ) (σ : ℝ) (l : List Epoch)
    (hl : ∀ e ∈ l, Good L Lbar μ e) : 0 ≤ after μ σ l 0 := by
  induction l with
  | nil => simp [after]
  | cons e rest ih =>
    simp only [after]
    have hr : ∀ e' ∈ rest, Good L Lbar μ e' := fun e' he' => hl e' (List.mem_cons_of_mem _ he')
    rw [after_affine]
    have h1 := slope_nonneg hμ rest hr
    have h2 := ((hl e List.mem_cons_self).gain_bounds hμ).1
    have h3 := (hl e List.mem_cons_self).noise_nonneg σ
    have h4 := ih hr
    have h5 : 0 ≤ gain μ e * (0 + noise σ e) := by
      rw [zero_add]
      exact mul_nonneg (by linarith) h3
    nlinarith [mul_nonneg h1 h5]

end GoodFacts

section Moments

variable {p : Measure Ω} [IsProbabilityMeasure p]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integral_norm_add_sq {W : Ω → E} (u : E) (hW : Integrable W p)
    (hW0 : ∫ ω, W ω ∂p = 0) (hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) p) :
    Integrable (fun ω => ‖u + W ω‖ ^ 2) p ∧
      ∫ ω, ‖u + W ω‖ ^ 2 ∂p = ‖u‖ ^ 2 + ∫ ω, ‖W ω‖ ^ 2 ∂p := by
  have he : (fun ω => ‖u + W ω‖ ^ 2) = fun ω => ‖u‖ ^ 2 + 2 * ⟪u, W ω⟫ + ‖W ω‖ ^ 2 := by
    funext ω
    exact norm_add_sq_real u (W ω)
  have hin : Integrable (fun ω => ⟪u, W ω⟫) p := Integrable.const_inner (𝕜 := ℝ) u hW
  have h0 : ∫ ω, ⟪u, W ω⟫ ∂p = 0 := by
    rw [integral_inner hW u, hW0, inner_zero_right]
  have h1 : Integrable (fun ω => ‖u‖ ^ 2 + 2 * ⟪u, W ω⟫) p :=
    (integrable_const _).add (hin.const_mul 2)
  rw [he]
  refine ⟨h1.add hW2, ?_⟩
  rw [integral_add h1 hW2, integral_add (integrable_const _) (hin.const_mul 2),
    integral_const_mul, h0]
  simp

variable {f : E → ℝ} {g : E → Ω → E} {L Lbar μ σ fstar : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.noise_step (H : Hyp p f g L Lbar μ σ fstar) (u x : E) :
    Integrable (fun ω => ‖u + (g x ω - gradient f x)‖ ^ 2) p ∧
      ∫ ω, ‖u + (g x ω - gradient f x)‖ ^ 2 ∂p ≤ ‖u‖ ^ 2 + σ ^ 2 := by
  have hW : Integrable (fun ω => g x ω - gradient f x) p := (H.int x).sub (integrable_const _)
  have hW0 : ∫ ω, (g x ω - gradient f x) ∂p = 0 := by
    rw [integral_sub (H.int x) (integrable_const _), H.mean x]
    simp
  obtain ⟨h1, h2⟩ := integral_norm_add_sq u hW hW0 (H.varInt x)
  refine ⟨h1, ?_⟩
  rw [h2]
  linarith [H.var x]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.diff_step (H : Hyp p f g L Lbar μ σ fstar) (u x y : E) :
    Integrable (fun ω => ‖u + ((g y ω - g x ω) - (gradient f y - gradient f x))‖ ^ 2) p ∧
      ∫ ω, ‖u + ((g y ω - g x ω) - (gradient f y - gradient f x))‖ ^ 2 ∂p ≤
        ‖u‖ ^ 2 + Lbar ^ 2 * ‖y - x‖ ^ 2 := by
  set c := gradient f y - gradient f x with hc
  have hD : Integrable (fun ω => g y ω - g x ω) p := (H.int y).sub (H.int x)
  have hDc : ∫ ω, (g y ω - g x ω) ∂p = c := by
    rw [integral_sub (H.int y) (H.int x), H.mean, H.mean]
  have hW : Integrable (fun ω => (g y ω - g x ω) - c) p := hD.sub (integrable_const _)
  have hW0 : ∫ ω, ((g y ω - g x ω) - c) ∂p = 0 := by
    rw [integral_sub hD (integrable_const _), hDc]
    simp
  have he : (fun ω => ‖(g y ω - g x ω) - c‖ ^ 2) =
      fun ω => ‖g y ω - g x ω‖ ^ 2 - 2 * ⟪g y ω - g x ω, c⟫ + ‖c‖ ^ 2 := by
    funext ω
    exact norm_sub_sq_real _ _
  have hin : Integrable (fun ω => ⟪g y ω - g x ω, c⟫) p :=
    Integrable.inner_const (𝕜 := ℝ) hD c
  have hI0 : ∫ ω, ⟪g y ω - g x ω, c⟫ ∂p = ‖c‖ ^ 2 := by
    have h := integral_inner (𝕜 := ℝ) hD c
    have hcomm : (fun ω => ⟪g y ω - g x ω, c⟫) = fun ω => ⟪c, g y ω - g x ω⟫ := by
      funext ω
      exact real_inner_comm _ _
    rw [hcomm, h, hDc, real_inner_self_eq_norm_sq]
  have h1 : Integrable (fun ω => ‖g y ω - g x ω‖ ^ 2 - 2 * ⟪g y ω - g x ω, c⟫) p :=
    (H.mssInt y x).sub (hin.const_mul 2)
  have hW2 : Integrable (fun ω => ‖(g y ω - g x ω) - c‖ ^ 2) p := by
    rw [he]
    exact h1.add (integrable_const _)
  have hWle : ∫ ω, ‖(g y ω - g x ω) - c‖ ^ 2 ∂p ≤ Lbar ^ 2 * ‖y - x‖ ^ 2 := by
    rw [he, integral_add h1 (integrable_const _), integral_sub (H.mssInt y x) (hin.const_mul 2),
      integral_const_mul, hI0]
    simp only [integral_const, probReal_univ, one_smul]
    nlinarith [H.mss y x, sq_nonneg ‖c‖]
  obtain ⟨h2, h3⟩ := integral_norm_add_sq u hW hW0 hW2
  refine ⟨h2, ?_⟩
  rw [h3]
  linarith

end Moments

section Descent

variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {L Lbar μ σ fstar : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.descent (H : Hyp p f g L Lbar μ σ fstar) {η : ℝ} (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2)
    (x v : E) :
    f (x - η • v) - fstar ≤ (1 - η * μ) * (f x - fstar) - η / 4 * ‖v‖ ^ 2 +
      η / 2 * ‖v - gradient f x‖ ^ 2 := by
  have h := Gradient.smooth_upper_bound H.grad H.smooth x (x - η • v)
  rw [show x - η • v - x = -(η • v) by abel] at h
  simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at h
  rw [real_inner_comm v (gradient f x)] at h
  have hsq := norm_sub_sq_real v (gradient f x)
  have hpl := H.pl x
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have h1 : η * (2 * μ * (f x - fstar)) ≤ η * ‖gradient f x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hpl hη
  have h2 : η * L * (η * ‖v‖ ^ 2) ≤ 1 / 2 * (η * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hηL (mul_nonneg hη hv)
  rw [hsq]
  nlinarith

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.gap_nonneg (H : Hyp p f g L Lbar μ σ fstar) (x : E) : 0 ≤ f x - fstar :=
  sub_nonneg.mpr (H.lower x)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.final_step (H : Hyp p f g L Lbar μ σ fstar) {e : Epoch} (he : Good L Lbar μ e)
    (y w : E) :
    f (y - e.η • w) - fstar ≤ gain μ e *
      ((f y - fstar) / (1 - e.η * μ) ^ e.m + e.η * ‖w - gradient f y‖ ^ 2) := by
  have hd := H.descent he.hη.le he.hL y w
  obtain ⟨hlo, hhi⟩ := he.theta_bounds H.hμ
  have hpm := (he.pow_bounds H.hμ e.m (Nat.le_succ _)).1
  have hg := (he.gain_bounds H.hμ).1
  have hpos : 0 < (1 - e.η * μ) ^ e.m := by linarith
  have hge : gain μ e * ((f y - fstar) / (1 - e.η * μ) ^ e.m) = (1 - e.η * μ) * (f y - fstar) := by
    unfold gain
    rw [pow_succ]
    field_simp
  have hN : 0 ≤ ‖w - gradient f y‖ ^ 2 := sq_nonneg _
  have hV : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hη := he.hη
  rw [mul_add, hge]
  nlinarith [mul_nonneg hη.le hN, mul_nonneg hη.le hV,
    mul_le_mul_of_nonneg_right hg (mul_nonneg hη.le hN)]

end Descent

lemma inner_step_real {θ P d d' V N η Lbar k m : ℝ} (hθ : 1 / 2 ≤ θ * P) (hθ1 : θ * P ≤ 1)
    (hP : 0 < P) (hθ0 : 0 < θ) (hη : 0 ≤ η) (hV : 0 ≤ V) (hN : 0 ≤ N) (hkm : k ≤ m)
    (hbar : 4 * Lbar ^ 2 * η ^ 2 * m ≤ 1)
    (hd : d' ≤ θ * d - η / 4 * V + η / 2 * N) :
    d' / (θ * P) + η * k * (N + Lbar ^ 2 * η ^ 2 * V) ≤ d / P + η * (k + 1) * N := by
  have hθP : 0 < θ * P := mul_pos hθ0 hP
  have h1 : d' / (θ * P) ≤ (θ * d - η / 4 * V + η / 2 * N) / (θ * P) :=
    div_le_div_of_nonneg_right hd hθP.le
  have h2 : (θ * d - η / 4 * V + η / 2 * N) / (θ * P) =
      d / P - η / 4 * V / (θ * P) + η / 2 * N / (θ * P) := by
    field_simp
  have hinv1 : 1 ≤ 1 / (θ * P) := by
    rw [le_div_iff₀ hθP]
    linarith
  have hinv2 : 1 / (θ * P) ≤ 2 := by
    rw [div_le_iff₀ hθP]
    linarith
  have hV' : 0 ≤ η / 4 * V := by positivity
  have hN' : 0 ≤ η / 2 * N := by positivity
  have h3 : η / 4 * V ≤ η / 4 * V / (θ * P) := by
    have := mul_le_mul_of_nonneg_left hinv1 hV'
    calc η / 4 * V = η / 4 * V * 1 := by ring
      _ ≤ η / 4 * V * (1 / (θ * P)) := this
      _ = η / 4 * V / (θ * P) := by ring
  have h4 : η / 2 * N / (θ * P) ≤ η * N := by
    have := mul_le_mul_of_nonneg_left hinv2 hN'
    calc η / 2 * N / (θ * P) = η / 2 * N * (1 / (θ * P)) := by ring
      _ ≤ η / 2 * N * 2 := this
      _ = η * N := by ring
  have h5 : η * k * (Lbar ^ 2 * η ^ 2 * V) ≤ η / 4 * V := by
    have hk1 : Lbar ^ 2 * η ^ 2 * k ≤ Lbar ^ 2 * η ^ 2 * m :=
      mul_le_mul_of_nonneg_left hkm (by positivity)
    have hk2 : 4 * (Lbar ^ 2 * η ^ 2 * k) ≤ 1 := by linarith
    have hk3 := mul_le_mul_of_nonneg_right hk2 (mul_nonneg hη hV)
    nlinarith
  rw [h2] at h1
  nlinarith

end OracleTemplate.StagewiseSarah
