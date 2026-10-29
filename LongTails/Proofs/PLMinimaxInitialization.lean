import LongTails.Proofs.PLMinimaxEnvelope
import LongTails.Proofs.FairLocationExistence

open Set InnerProductSpace
open LongTails.Setups.WeaklyConvexHeavyTailed
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}

lemma Hyp.primalGradient_lipschitz (H : Hyp f gx gy L μ) (z x x' : E) (y : F) :
    ‖(gx x y + (2 * L) • (x - z)) - (gx x' y + (2 * L) • (x' - z))‖ ≤
      (3 * L) * ‖x - x'‖ := by
  have he : (gx x y + (2 * L) • (x - z)) - (gx x' y + (2 * L) • (x' - z)) =
      (gx x y - gx x' y) + (2 * L) • (x - x') := by simp only [smul_sub]; abel
  rw [he]
  have hh := norm_add_le (gx x y - gx x' y) ((2 * L) • (x - x'))
  rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ 2 * L by linarith [H.hL])] at hh
  have hl := H.lipx x x' y y
  simp only [sub_self, norm_zero, add_zero] at hl
  linarith

lemma Hyp.primalGradient_monotone (H : Hyp f gx gy L μ) (z x x' : E) (y : F) :
    L * ‖x - x'‖ ^ 2 ≤
      ⟪(gx x y + (2 * L) • (x - z)) - (gx x' y + (2 * L) • (x' - z)), x - x'⟫ := by
  have he : (gx x y + (2 * L) • (x - z)) - (gx x' y + (2 * L) • (x' - z)) =
      (gx x y - gx x' y) + (2 * L) • (x - x') := by simp only [smul_sub]; abel
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hi := real_inner_le_norm (gx x' y - gx x y) (x - x')
  rw [inner_sub_left, norm_sub_rev (gx x' y) (gx x y)] at hi
  have hl := H.lipx x x' y y
  simp only [sub_self, norm_zero, add_zero] at hl
  have hh := mul_le_mul_of_nonneg_right hl (norm_nonneg (x - x'))
  rw [inner_sub_left]
  nlinarith

lemma Hyp.primalGradient_step (H : Hyp f gx gy L μ) (z x x' : E) (y : F) :
    ‖(x - (1 / (9 * L)) • (gx x y + (2 * L) • (x - z))) -
      (x' - (1 / (9 * L)) • (gx x' y + (2 * L) • (x' - z)))‖ ≤
      (17 / 18 : ℝ) * ‖x - x'‖ := by
  have ha : 0 < 1 / (9 * L) := by have := H.hL; positivity
  have hs : (1 / (9 * L)) * (3 * L) ^ 2 ≤ L := by
    have := H.hL
    field_simp
    nlinarith
  have ht : (1 / (9 * L)) * L ≤ 1 := by
    have he : (1 / (9 * L)) * L = 1 / 9 := by field_simp [H.hL.ne']
    rw [he]
    norm_num
  have hh := RadialFairLocation.monotone_step_contraction ha hs ht x x'
    (gx x y + (2 * L) • (x - z)) (gx x' y + (2 * L) • (x' - z))
    (H.primalGradient_lipschitz z x x' y) (H.primalGradient_monotone z x x' y)
  convert hh using 1
  congr 1
  field_simp [H.hL.ne']
  ring

lemma Hyp.dual_lower [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ) (z : E) (y y' : F) :
    dual f L z y + ⟪gy (innerPrimal f L z y) y, y' - y⟫ - L * ‖y' - y‖ ^ 2 ≤
      dual f L z y' := by
  have hh := Gradient.smooth_upper_bound (f := fun y => -dual f L z y)
    (oracle := fun y => -gy (innerPrimal f L z y) y) (L := 2 * L)
    (fun y => TwoSidedPL.hasGradientAt_neg' (H.dual_hasGradient z y))
    (fun a b => by rw [neg_sub_neg, norm_sub_rev]; exact H.dual_gradient_lipschitz z a b) y y'
  simp only [inner_neg_left] at hh
  linarith

lemma Hyp.dual_ascent [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ) (z : E) (y v : F) :
    dual f L z (y + (1 / (2 * L)) • v) ≥ dual f L z y +
      (‖gy (innerPrimal f L z y) y‖ ^ 2 - ‖v - gy (innerPrimal f L z y) y‖ ^ 2) / (4 * L) := by
  have hh := H.dual_lower z y (y + (1 / (2 * L)) • v)
  rw [add_sub_cancel_left, inner_smul_right, norm_smul,
    Real.norm_of_nonneg (show 0 ≤ 1 / (2 * L) by have := H.hL; positivity)] at hh
  have he := norm_sub_sq_real v (gy (innerPrimal f L z y) y)
  rw [real_inner_comm (gy (innerPrimal f L z y) y) v] at he
  have hL := H.hL
  field_simp at hh ⊢
  nlinarith

lemma Hyp.dual_ascent_gap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : Hyp f gx gy L μ) (z : E) (y v : F) {S : ℝ}
    (hgap : envelope f L z - dual f L z y ≤ S)
    (herr : ‖v - gy (innerPrimal f L z y) y‖ ^ 2 ≤ μ * S) :
    envelope f L z - dual f L z (y + (1 / (2 * L)) • v) ≤ (1 - μ / (4 * L)) * S := by
  have ha := H.dual_ascent z y v
  have hp := H.envelope_sub_dual z y
  have hpl : 2 * μ * (envelope f L z - dual f L z y) ≤
      ‖gy (innerPrimal f L z y) y‖ ^ 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * μ by linarith [H.hμ])).mp hp
    nlinarith
  have hh : (‖gy (innerPrimal f L z y) y‖ ^ 2 -
      ‖v - gy (innerPrimal f L z y) y‖ ^ 2) / (4 * L) ≤
      dual f L z (y + (1 / (2 * L)) • v) - dual f L z y := by linarith
  have hh' := (div_le_iff₀ (show 0 < 4 * L by linarith [H.hL])).mp hh
  have hs := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 4 * L - 2 * μ by linarith [H.hL, H.hμL])
  have he : (4 * L) * ((1 - μ / (4 * L)) * S) = (4 * L - μ) * S := by
    field_simp [H.hL.ne']
  have hL := H.hL
  nlinarith

lemma Hyp.dual_gradient_error [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ)
    (z x : E) (y : F) :
    ‖gy x y - gy (innerPrimal f L z y) y‖ ≤ ‖gx x y + (2 * L) • (x - z)‖ := by
  have hh := H.lipy x (innerPrimal f L z y) y y
  simp only [sub_self, norm_zero, add_zero] at hh
  exact hh.trans (proxObj_residual_distance (H.slice_weak y) (H.innerPrimal_stationary z y) x)

lemma Hyp.primalSequence_distance [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ)
    (z : E) (y : F) (u : ℕ → E)
    (hu : ∀ n, u (n + 1) = u n - (1 / (9 * L)) • (gx (u n) y + (2 * L) • (u n - z)))
    (n : ℕ) :
    ‖u n - innerPrimal f L z y‖ ≤ (17 / 18 : ℝ) ^ n * ‖u 0 - innerPrimal f L z y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := H.primalGradient_step z (u n) (innerPrimal f L z y) y
    rw [H.innerPrimal_stationary z y, smul_zero, sub_zero, ← hu n] at hh
    have hs := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 17 / 18)
    exact hh.trans (by simpa only [pow_succ] using (by nlinarith [hs] :
      (17 / 18 : ℝ) * ‖u n - innerPrimal f L z y‖ ≤
        (17 / 18 : ℝ) ^ n * (17 / 18) * ‖u 0 - innerPrimal f L z y‖))

lemma Hyp.primalSequence_residual [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ)
    (z : E) (y : F) (u : ℕ → E)
    (hu : ∀ n, u (n + 1) = u n - (1 / (9 * L)) • (gx (u n) y + (2 * L) • (u n - z)))
    (n : ℕ) :
    ‖gx (u n) y + (2 * L) • (u n - z)‖ ≤
      3 * (17 / 18 : ℝ) ^ n * ‖gx (u 0) y + (2 * L) • (u 0 - z)‖ := by
  have hh := H.primalGradient_lipschitz z (u n) (innerPrimal f L z y) y
  rw [H.innerPrimal_stationary z y, sub_zero] at hh
  have hd := H.primalSequence_distance z y u hu n
  have hi := proxObj_residual_distance (H.slice_weak y) (H.innerPrimal_stationary z y) (u 0)
  have hn := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3 * L by linarith [H.hL])
  have hn' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 3 * (17 / 18 : ℝ) ^ n by positivity)
  nlinarith

lemma Hyp.dual_gradient_gap [FiniteDimensional ℝ E]
    (H : Hyp f gx gy L μ) (z : E) (y : F) :
    ‖gy (innerPrimal f L z y) y‖ ^ 2 ≤ 4 * L * (envelope f L z - dual f L z y) := by
  have ha := H.dual_ascent z y (gy (innerPrimal f L z y) y)
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at ha
  have hb := H.dual_le_envelope z (y + (1 / (2 * L)) • gy (innerPrimal f L z y) y)
  have hh : ‖gy (innerPrimal f L z y) y‖ ^ 2 / (4 * L) ≤ envelope f L z - dual f L z y := by linarith
  have hc := (div_le_iff₀ (show 0 < 4 * L by linarith [H.hL])).mp hh
  nlinarith

omit [CompleteSpace E] in
lemma norm_add_square_bound (u v : E) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real]
  nlinarith [real_inner_le_norm u v, sq_nonneg (‖u‖ - ‖v‖)]

lemma Hyp.approximate_dual_gradient_gap [FiniteDimensional ℝ E]
    (H : Hyp f gx gy L μ) (z x : E) (y : F) {S : ℝ}
    (hS : 0 ≤ S) (hgap : envelope f L z - dual f L z y ≤ S)
    (hres : ‖gx x y + (2 * L) • (x - z)‖ ^ 2 ≤ μ * S) :
    ‖gy x y‖ ^ 2 ≤ 10 * L * S := by
  have he := H.dual_gradient_error z x y
  have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
  have hg := H.dual_gradient_gap z y
  have hg' := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 4 * L by linarith [H.hL])
  have hn := norm_add_square_bound (gy x y - gy (innerPrimal f L z y) y)
    (gy (innerPrimal f L z y) y)
  rw [sub_add_cancel] at hn
  have hm := mul_le_mul_of_nonneg_right H.hμL hS
  nlinarith

lemma Hyp.primal_warm_start [FiniteDimensional ℝ E]
    (H : Hyp f gx gy L μ) (z x : E) (y : F) {S : ℝ}
    (hS : 0 ≤ S) (hgap : envelope f L z - dual f L z y ≤ S)
    (hres : ‖gx x y + (2 * L) • (x - z)‖ ^ 2 ≤ μ * S) :
    ‖gx x (y + (1 / (2 * L)) • gy x y) + (2 * L) • (x - z)‖ ^ 2 ≤
      16 * L * ((1 - μ / (4 * L)) * S) := by
  let y' := y + (1 / (2 * L)) • gy x y
  have hl := H.lipx x x y' y
  simp only [sub_self, norm_zero, zero_add] at hl
  have he : ‖y' - y‖ = (1 / (2 * L)) * ‖gy x y‖ := by
    dsimp [y']
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by have := H.hL; positivity)]
  rw [he] at hl
  have hl' : ‖gx x y' - gx x y‖ ≤ ‖gy x y‖ / 2 := by
    convert hl using 1
    field_simp [H.hL.ne']
  have hl2 := pow_le_pow_left₀ (norm_nonneg _) hl' 2
  have hn := norm_add_square_bound (gx x y' - gx x y) (gx x y + (2 * L) • (x - z))
  have hid : (gx x y' - gx x y) + (gx x y + (2 * L) • (x - z)) =
      gx x y' + (2 * L) • (x - z) := by abel
  rw [hid] at hn
  have hg := H.approximate_dual_gradient_gap z x y hS hgap hres
  have hm := mul_le_mul_of_nonneg_right H.hμL hS
  have he' : 16 * L * ((1 - μ / (4 * L)) * S) = (16 * L - 4 * μ) * S := by
    field_simp [H.hL.ne']
    ring
  rw [he']
  change ‖gx x y' + (2 * L) • (x - z)‖ ^ 2 ≤ _
  nlinarith

lemma Hyp.max_quadratic_growth [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    (x : E) (y : F) :
    ∃ v, (∀ y', f x y' ≤ f x v) ∧
      μ * ‖y - v‖ ^ 2 ≤ 16 * (LongTails.Setups.StochasticTwoSidedPL.maxValue f x - f x y) := by
  obtain ⟨u, hu⟩ := H.attain x
  have hg : ∀ v, HasGradientAt (fun y => -f x y) (-gy x v) v :=
    fun v => TwoSidedPL.hasGradientAt_neg' (H.hgy x v)
  have he : ∀ v, gradient (fun y => -f x y) v = -gy x v := fun v => (hg v).gradient
  obtain ⟨v, hv, hd⟩ := PLHessian.quad_growth (f := fun v => -f x v) H.hL H.hμ H.hμL
    (fun v => by rw [he]; exact hg v)
    (fun a b => by
      rw [he, he, neg_sub_neg, norm_sub_rev]
      simpa using H.lipy x x a b)
    (u := u) (fun v _ => neg_le_neg (hu v)) (fun v => by
      rw [he, norm_neg]
      simpa only [neg_sub_neg] using H.ply x v u) y
  refine ⟨v, fun y' => ?_, ?_⟩
  · have hh := hv (mem_univ y')
    simpa using hh
  · rw [H.max_value_eq hu]
    simpa only [neg_sub_neg] using hd

lemma Hyp.initial_value_gradient [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    (x0 : E) {Δ : ℝ}
    (hgap : ∀ x, LongTails.Setups.StochasticTwoSidedPL.maxValue f x0 -
      LongTails.Setups.StochasticTwoSidedPL.maxValue f x ≤ Δ) :
    ‖gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue f) x0‖ ^ 2 ≤ 8 * L ^ 2 / μ * Δ := by
  have hg : ∀ x, HasGradientAt (LongTails.Setups.StochasticTwoSidedPL.maxValue f)
      (gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue f) x) x := by
    intro x
    obtain ⟨y, hy⟩ := H.attain x
    rw [(H.value_hasGradient hy).gradient]
    exact H.value_hasGradient hy
  have hpos : 0 < 4 * L ^ 2 / μ := by have := H.hL; have := H.hμ; positivity
  have hd := Gradient.descent hpos hg H.value_gradient_lipschitz x0
  have hl := hgap (x0 - (1 / (4 * L ^ 2 / μ)) •
    gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue f) x0)
  have hh : ‖gradient (LongTails.Setups.StochasticTwoSidedPL.maxValue f) x0‖ ^ 2 /
      (2 * (4 * L ^ 2 / μ)) ≤ Δ := by linarith
  have hm := (div_le_iff₀ (show 0 < 2 * (4 * L ^ 2 / μ) by positivity)).mp hh
  convert hm using 1
  ring

lemma Hyp.initial_primal_gradient [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    (x0 : E) (y0 : F) {Δ D : ℝ}
    (hgap : ∀ x, LongTails.Setups.StochasticTwoSidedPL.maxValue f x0 -
      LongTails.Setups.StochasticTwoSidedPL.maxValue f x ≤ Δ)
    (hinner : LongTails.Setups.StochasticTwoSidedPL.maxValue f x0 - f x0 y0 ≤ D) :
    ‖gx x0 y0‖ ^ 2 ≤ (16 * L ^ 2 / μ) * Δ + (32 * L ^ 2 / μ) * D := by
  obtain ⟨y, hy, hd⟩ := H.max_quadratic_growth x0 y0
  have hl := H.lipx x0 x0 y0 y
  simp only [sub_self, norm_zero, zero_add] at hl
  have hl2 := pow_le_pow_left₀ (norm_nonneg _) hl 2
  have hv := H.initial_value_gradient x0 hgap
  rw [(H.value_hasGradient hy).gradient] at hv
  have hn := norm_add_square_bound (gx x0 y0 - gx x0 y) (gx x0 y)
  rw [sub_add_cancel] at hn
  have hd' : μ * ‖y0 - y‖ ^ 2 ≤ 16 * D := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hd' (sq_nonneg L)
  have hnorm := mul_le_mul_of_nonneg_left hl2 H.hμ.le
  have hμ := H.hμ
  field_simp at hv ⊢
  have hn' := mul_le_mul_of_nonneg_left hn H.hμ.le
  nlinarith

lemma Hyp.initial_dual_gap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : Hyp f gx gy L μ) (x0 : E) (y0 : F) {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 0 ≤ D)
    (hgap : ∀ x, LongTails.Setups.StochasticTwoSidedPL.maxValue f x0 -
      LongTails.Setups.StochasticTwoSidedPL.maxValue f x ≤ Δ)
    (hinner : LongTails.Setups.StochasticTwoSidedPL.maxValue f x0 - f x0 y0 ≤ D) :
    envelope f L x0 - dual f L x0 y0 ≤ 32 * L / μ * (Δ + D) := by
  have hm := weakProx_min H.hL H.value_continuous H.value_weak x0 (mem_univ x0)
  change envelope f L x0 ≤ proxObj (LongTails.Setups.StochasticTwoSidedPL.maxValue f) L x0 x0 at hm
  simp only [proxObj, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero] at hm
  have hd := proxObj_gap_bound H.hL (H.slice_weak y0) x0 x0 (innerPrimal f L x0 y0)
  change proxObj (fun x => f x y0) L x0 x0 - dual f L x0 y0 ≤ _ at hd
  simp only [proxObj, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero, smul_zero] at hd
  have hg := H.initial_primal_gradient x0 y0 hgap hinner
  have hh : envelope f L x0 - dual f L x0 y0 ≤ D + ‖gx x0 y0‖ ^ 2 / (2 * L) := by linarith
  have hL := H.hL
  have hμ := H.hμ
  have hμL := H.hμL
  have hh' := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp
    (show envelope f L x0 - dual f L x0 y0 - D ≤ ‖gx x0 y0‖ ^ 2 / (2 * L) by linarith)
  have hg' : μ * ‖gx x0 y0‖ ^ 2 ≤ 16 * L ^ 2 * Δ + 32 * L ^ 2 * D := by
    field_simp at hg
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hh' hμ.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  have hLD := mul_le_mul_of_nonneg_right hμL hD
  nlinarith [mul_nonneg hL.le hΔ, mul_nonneg hL.le hD]

lemma Hyp.primalSequence_accuracy [FiniteDimensional ℝ E] (H : Hyp f gx gy L μ)
    (z : E) (y : F) (u : ℕ → E)
    (hu : ∀ n, u (n + 1) = u n - (1 / (9 * L)) • (gx (u n) y + (2 * L) • (u n - z)))
    (N : ℕ) {S : ℝ} (hS : 0 ≤ S)
    (hi : ‖gx (u 0) y + (2 * L) • (u 0 - z)‖ ^ 2 ≤ 16 * L * S)
    (hN : 144 * L * ((17 / 18 : ℝ) ^ N) ^ 2 ≤ μ) :
    ‖gx (u N) y + (2 * L) • (u N - z)‖ ^ 2 ≤ μ * S := by
  have hr := H.primalSequence_residual z y u hu N
  have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 9 * ((17 / 18 : ℝ) ^ N) ^ 2 by positivity)
  have hn := mul_le_mul_of_nonneg_right hN hS
  nlinarith

lemma Hyp.initialization_rounds [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : Hyp f gx gy L μ) (z : E) (N : ℕ) (S : ℕ → ℝ) (y : ℕ → F) (u : ℕ → ℕ → E)
    (hS : ∀ j, 0 ≤ S j) (hSn : ∀ j, S (j + 1) = (1 - μ / (4 * L)) * S j)
    (hN : 144 * L * ((17 / 18 : ℝ) ^ N) ^ 2 ≤ μ)
    (hu : ∀ j n, u j (n + 1) = u j n - (1 / (9 * L)) •
      (gx (u j n) (y j) + (2 * L) • (u j n - z)))
    (hy : ∀ j, y (j + 1) = y j + (1 / (2 * L)) • gy (u j N) (y j))
    (hstart : ∀ j, u (j + 1) 0 = u j N)
    (hgap : envelope f L z - dual f L z (y 0) ≤ S 0)
    (hres : ‖gx (u 0 0) (y 0) + (2 * L) • (u 0 0 - z)‖ ^ 2 ≤ 16 * L * S 0) :
    ∀ j, envelope f L z - dual f L z (y j) ≤ S j ∧
      ‖gx (u j 0) (y j) + (2 * L) • (u j 0 - z)‖ ^ 2 ≤ 16 * L * S j ∧
      ‖gx (u j N) (y j) + (2 * L) • (u j N - z)‖ ^ 2 ≤ μ * S j := by
  intro j
  induction j with
  | zero => exact ⟨hgap, hres, H.primalSequence_accuracy z (y 0) (u 0) (hu 0) N (hS 0) hres hN⟩
  | succ j ih =>
    have he := H.dual_gradient_error z (u j N) (y j)
    have he2 := (pow_le_pow_left₀ (norm_nonneg _) he 2).trans ih.2.2
    have hg := H.dual_ascent_gap z (y j) (gy (u j N) (y j)) ih.1 he2
    rw [← hy j, ← hSn j] at hg
    have hr := H.primal_warm_start z (u j N) (y j) (hS j) ih.1 ih.2.2
    rw [← hy j, ← hSn j, ← hstart j] at hr
    exact ⟨hg, hr, H.primalSequence_accuracy z (y (j + 1)) (u (j + 1))
      (hu (j + 1)) N (hS (j + 1)) hr hN⟩

end OracleTemplate.PLMinimax
