import LongTails.Algorithms.MultilevelPipeline
import LongTails.Proofs.MultilevelWorkerSchedule
import LongTails.Proofs.DistributedBatchedSgd
import LongTails.Proofs.GeneralNormClipping
import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.LeonAccuracy

namespace LongTails.Proofs.MultilevelTrajectory

open MeasureTheory
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultilevelTransport (Bits)
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.DistributedQuantization (message receive)

lemma objective_smooth (p : Params) (μ : ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Point p → p.Ω → Point p) (hL : 0 < p.L)
    (hor : IsStochasticGradient (Point p) p.Ω μ f g p.σ)
    (hm : ∀ x y, Integrable (fun ξ => ‖g x ξ - g y ξ‖^2) (μ : Measure _) ∧
      (∫ ξ, ‖g x ξ - g y ξ‖^2 ∂(μ : Measure _)) ≤ p.L^2 * ‖x-y‖^2)
    (x y : Point p) : ‖gradient f x - gradient f y‖ ≤ p.L * ‖x-y‖ := by
  have h := (OracleTemplate.GeneralNormClipping.norm_integral_sq_le
    ((hor.integrable x).sub (hor.integrable y)) (hm x y).1).trans (hm x y).2
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hor.integrable x) (hor.integrable y), hor.unbiased, hor.unbiased] at h
  rw [← mul_pow] at h
  exact le_of_sq_le_sq h (by positivity)

lemma stride_pos (p : Params) (hL : 0 < p.L) (he : 0 < p.ε) : 0 < stride p := by
  unfold stride precision
  positivity

lemma gap_budget (p : Params) (he : 0 < p.ε) : 2*p.L*p.Δ ≤ wanted p * precision p ^ 2 := by
  have hh : 0 < precision p := by unfold precision; positivity
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mp
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

lemma displacement (p : Params) (bits : ℕ → Bits) (hη : 0 ≤ stride p) (s d : ℕ) :
    ‖iterate p bits (s+d) - iterate p bits s‖ ≤ d * stride p := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep := OracleTemplate.NormalizedStorm.stormStep_dist hη (iterate p bits (s+d)) (estimate p bits (s+d))
    have htri := norm_sub_le_norm_sub_add_norm_sub (iterate p bits (s+d+1)) (iterate p bits (s+d)) (iterate p bits s)
    change ‖iterate p bits (s+d+1) - iterate p bits (s+d)‖ ≤ _ at hstep
    rw [← Nat.add_assoc, Nat.cast_succ]
    linarith

lemma central_descent (p : Params) (bits : ℕ → Bits) (hL : 0 < p.L) (he : 0 < p.ε)
    (f : Point p → ℝ) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x-y‖) (t : ℕ) :
    let v := estimate p bits
    let x := iterate p bits
    stride p * (∑ k ∈ Finset.range t, ‖v k‖) ≤ f p.x0 - f (x t) +
      3 * stride p * (∑ k ∈ Finset.range t, ‖v k - gradient f (x k)‖) + t * (p.L / 2 * stride p^2) := by
  intro v x
  have hη := (stride_pos p hL he).le
  induction t with
  | zero => simp [x, iterate]
  | succ t ih =>
    have hd := ParameterFreeNsgdmRun.descent_step hg hlip hL.le (stride p) hη (x t) (v t)
    change f (x (t+1)) ≤ _ at hd
    have ht := mul_le_mul_of_nonneg_left (norm_sub_norm_le (v t) (gradient f (x t))) hη
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_succ]
    linarith

lemma estimated_sum (p : Params) (bits : ℕ → Bits) (hL : 0 < p.L) (he : 0 < p.ε)
    (f : Point p → ℝ) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x-y‖)
    (a : ℝ) (ha : ∀ x, a ≤ f x) (hgap : f p.x0 - a ≤ p.Δ) :
    (∑ i : Fin (wanted p), ‖estimate p bits i‖) ≤ wanted p * precision p +
      3 * ∑ i : Fin (wanted p), ‖estimate p bits i - gradient f (iterate p bits i)‖ := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖estimate p bits k‖),
    Fin.sum_univ_eq_sum_range (fun k => ‖estimate p bits k - gradient f (iterate p bits k)‖)]
  have hd := central_descent p bits hL he f hg hlip (wanted p)
  dsimp only at hd
  have g := gap_budget p he
  have hη := stride_pos p hL he
  have hid : stride p * p.L = precision p := div_mul_cancel₀ _ hL.ne'
  have hg₂ : 2*p.Δ ≤ wanted p * precision p * stride p := by
    apply le_of_mul_le_mul_right (a := p.L) _ hL
    calc
      2 * p.Δ * p.L = 2*p.L*p.Δ := by ring
      _ ≤ _ := g
      _ = _ := by rw [mul_assoc _ (stride p), hid]; ring
  have hquad : p.L/2 * stride p ^ 2 = precision p * stride p / 2 := by rw [← hid]; ring
  rw [hquad] at hd
  apply le_of_mul_le_mul_left (a := stride p) _ hη
  linarith [ha (iterate p bits (wanted p))]

lemma codec_error (p : Params) (δ : ℝ) (hδ : 0 < δ) (x : Point p)
    (hrange : 2*(p.d+1 : ℝ)*‖x‖ ≤ δ * ((2 ^ width p - 1 : ℕ) : ℝ)) :
    ‖receive p.d (width p) (δ / (p.d+1)) (message p.d (width p) (δ / (p.d+1)) x) - x‖ ≤ δ := by
  have hd : 0 < (p.d : ℝ) + 1 := by positivity
  have hcoord (i : Fin p.d) : |x i| ≤ δ / (p.d+1) * ((2 ^ width p - 1 : ℕ) : ℝ) / 2 := by
    have hx : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hx hd.le]
  have hb := DistributedQuantization.message_error p.d (width p) _ (div_pos hδ hd) x hcoord
  refine le_of_sq_le_sq (hb.trans ?_) hδ.le
  field_simp
  nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg (p.d : ℝ)), mul_nonneg (sq_nonneg δ) (Nat.cast_nonneg p.d)]

noncomputable def gridPoint (p : Params) (bits : ℕ → Bits) (k : ℕ) : Point p :=
  p.x0 + receive p.d (width p) (pointSpacing p)
    (message p.d (width p) (pointSpacing p) (iterate p bits k - p.x0))

lemma grid_size (p : Params) :
    4*(p.d+1)*(height p+1)*radiusUnits p ≤ 2^width p-1 := by
  let A : ℕ := 2 + p.d + wanted p + fullBatch p
  have hJ : height p ≤ Nat.log 4 (fullBatch p) :=
    (min_le_right _ _).trans (Nat.log_mono_right (Nat.div_le_self _ _))
  have hPow : 4^height p ≤ fullBatch p :=
    (Nat.pow_le_pow_right (by decide) hJ).trans (Nat.pow_log_le_self 4 (by unfold fullBatch; omega))
  have hs := hJ.trans (Nat.log_le_self _ _)
  have hd : p.d+1 ≤ A := by dsimp [A]; omega
  have hj : height p+1 ≤ A := by dsimp [A]; omega
  have hk : wanted p+2 ≤ A := by dsimp [A]; omega
  have ht : fullBatch p + 4^height p + 1 ≤ 2*A := by dsimp [A]; omega
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hR : radiusUnits p ≤ 68*A^2 := by
    unfold radiusUnits
    calc
      _ ≤ 4*A + 32*A*(2*A) := by gcongr
      _ ≤ _ := by nlinarith [Nat.mul_le_mul_left A ha]
  have hG : 4*(p.d+1)*(height p+1)*radiusUnits p ≤ 272*A^4 := by
    calc
      _ ≤ 4*A*A*(68*A^2) := by gcongr
      _ = _ := by ring
  have hl : A ≤ 2^(Nat.log2 A)*2 := by
    simpa [Nat.log2_eq_log_two,pow_succ] using (Nat.lt_pow_succ_log_self (b:=2) (by decide) A).le
  have hm := Nat.pow_le_pow_left hl 4
  have he : 2^(width p) = 16384 * (2^Nat.log2 A)^4 := by
    change 2^(14 + 4*Nat.log2 A) = _
    rw [pow_add,Nat.mul_comm 4, pow_mul]
    norm_num
  rw [he]
  have hp : 0 < (2^Nat.log2 A)^4 := by positivity
  rw [mul_pow] at hm
  norm_num at hm
  omega


lemma point_error (p : Params) (hL : 0 < p.L) (he : 0 < p.ε)
    (b : ℕ → Bits) (k : ℕ) (hk : k ≤ wanted p) :
    ‖gridPoint p b k - iterate p b k‖ ≤ stride p := by
  have hη := stride_pos p hL he
  have hd : ‖iterate p b k - p.x0‖ ≤ (wanted p : ℝ)*stride p := by
    have h := displacement p b hη.le 0 k
    simpa [iterate] using h.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hη.le)
  have hm : 2*(p.d+1)*wanted p ≤ 4*(p.d+1)*(height p+1)*radiusUnits p := by
    unfold radiusUnits
    nlinarith [Nat.zero_le ((p.d+1)*height p*(wanted p+1)),
      Nat.zero_le ((p.d+1)*(height p+1)*(32*(height p+1)*(fullBatch p+4^height p+1)))]
  have hs : 2*((p.d:ℝ)+1)*(wanted p : ℝ) ≤ (2^width p-1 : ℕ) := by exact_mod_cast hm.trans (grid_size p)
  have hquant := codec_error p _ hη (iterate p b k - p.x0) (by
    have h := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*((p.d:ℝ)+1))
    linarith only [h, mul_le_mul_of_nonneg_right hs hη.le])
  unfold gridPoint pointSpacing
  convert hquant using 2
  abel

lemma value_error (p : Params) (he : 0 < p.ε) (x : Point p) :
    let R := radiusUnits p * precision p
    let q := receive p.d (width p) (valueSpacing p)
      (message p.d (width p) (valueSpacing p) (OracleTemplate.clip R x))
    ‖q - OracleTemplate.clip R x‖ ≤ precision p / (height p+1 : ℕ) := by
  intro R q
  have hδ : 0 < precision p := by unfold precision; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hm : 0 < ((height p+1 : ℕ) : ℝ) := by positivity
  have hr := OracleTemplate.norm_clip_le hR x
  have hb : 2*(p.d+1)*(height p+1)*radiusUnits p ≤ (2^width p-1 : ℕ) :=
    le_trans (by gcongr; norm_num) (grid_size p)
  have hs : 2*((p.d:ℝ)+1)*((height p+1:ℕ):ℝ)*(radiusUnits p:ℝ) ≤ ((2^width p-1:ℕ):ℝ) := by exact_mod_cast hb
  have hc := codec_error p _ (div_pos hδ hm) (OracleTemplate.clip R x) (by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    have hn := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*((p.d:ℝ)+1)*((height p+1:ℕ):ℝ) by positivity)
    dsimp [R] at hn
    linarith only [hn, mul_le_mul_of_nonneg_right hs hδ.le])
  simpa only [q, valueSpacing, div_div, Nat.cast_add, Nat.cast_one] using hc

lemma grid_displacement (p : Params) (hL : 0 < p.L) (he : 0 < p.ε)
    (b : ℕ → Bits) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ wanted p) :
    ‖gridPoint p b t - gridPoint p b s‖ ≤ ((t-s : ℕ)+2 : ℝ) * stride p := by
  have h := displacement p b (stride_pos p hL he).le s (t-s)
  rw [Nat.add_sub_of_le hst] at h
  have hu := point_error p hL he b t ht
  have hv := point_error p hL he b s (hst.trans ht)
  rw [norm_sub_rev] at hv
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (gridPoint p b t) (iterate p b t) (gridPoint p b s)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (iterate p b t) (iterate p b s) (gridPoint p b s)
  linarith

lemma grid_gradient (p : Params) (hL : 0 < p.L) (he : 0 < p.ε) (f : Point p → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ p.L*‖x-y‖)
    (a : ℝ) (ha : ∀ x, a ≤ f x) (hgap : f p.x0-a ≤ p.Δ)
    (b : ℕ → Bits) {k : ℕ} (hk : k ≤ wanted p) :
    ‖gradient f (gridPoint p b k)‖ ≤ (2*(wanted p : ℝ)+1)*precision p := by
  have hδ : 0 < precision p := by unfold precision; positivity
  have hK : (1:ℝ) ≤ wanted p := by exact_mod_cast (le_max_left 1 _ : 1 ≤ wanted p)
  have hinit := DistributedSmoothNonconvex.initial_gradient_bound hL hg hlip a ha hgap
  have hi : ‖gradient f p.x0‖ ≤ wanted p * precision p := by
    refine le_of_sq_le_sq ((hinit.trans (gap_budget p he)).trans ?_) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hK) (by positivity : (0:ℝ) ≤ wanted p)) (sq_nonneg (precision p))]
  have hd := displacement p b (stride_pos p hL he).le 0 k
  simp only [Nat.zero_add,iterate] at hd
  have hx := point_error p hL he b k hk
  have htri := norm_sub_le_norm_sub_add_norm_sub (gridPoint p b k) (iterate p b k) p.x0
  have hb := hlip (gridPoint p b k) p.x0
  have hn := norm_sub_norm_le (gradient f (gridPoint p b k)) (gradient f p.x0)
  have hmul : p.L * stride p = precision p := by unfold stride; field_simp
  have hr := mul_le_mul_of_nonneg_left ((htri.trans (add_le_add hx hd)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (stride_pos p hL he).le) _)) hL.le
  rw [mul_add, mul_left_comm p.L (wanted p : ℝ), hmul] at hr
  linarith

end LongTails.Proofs.MultilevelTrajectory
