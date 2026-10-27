import LongTails.Algorithms.PLMinimaxCubic
import LongTails.Proofs.TwoSidedPLEnvelope
import LongTails.Proofs.CappedCubicModel
import LongTails.Proofs.PLMinimaxTracking

open Set InnerProductSpace
open LongTails.Setups.NonconvexPLSecondOrder
open LongTails.Setups.WeaklyConvexHeavyTailed (proxObj)
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma envelopeCubicModel_exists_min [ProperSpace E] (g : E) (B : E →L[ℝ] E)
    {M : ℝ} (hM : 0 < M) : ∃ s, ∀ v, envelopeCubicModel g B M s ≤ envelopeCubicModel g B M v := by
  have hc : Continuous (envelopeCubicModel g B M) := by unfold envelopeCubicModel; fun_prop
  apply TwoSidedPL.exists_min_of_growth (envelopeCubicModel g B M) hc.lowerSemicontinuous
    0 (1 + 6 * ‖g‖ / M + 3 * ‖B‖ / M)
  intro s hs
  simp only [sub_zero] at hs
  have h₁ : 0 ≤ 6 * ‖g‖ / M := by positivity
  have h₂ : 0 ≤ 3 * ‖B‖ / M := by positivity
  have hr : 1 < ‖s‖ := by linarith
  have hscale : 6 * ‖g‖ + 3 * ‖B‖ < M * ‖s‖ := by
    have hh : (6 * ‖g‖ + 3 * ‖B‖) / M < ‖s‖ := by rw [add_div]; linarith
    simpa only [mul_comm] using (div_lt_iff₀ hM).mp hh
  have hquad := mul_le_mul_of_nonneg_right hscale.le (sq_nonneg ‖s‖)
  have hgi := (abs_le.mp (abs_real_inner_le_norm g s)).1
  have hBi := (abs_le.mp (abs_real_inner_le_norm s (B s))).1
  have hBn := mul_le_mul_of_nonneg_left (B.le_opNorm s) (norm_nonneg s)
  have hgr := mul_le_mul_of_nonneg_left (show ‖s‖ ≤ ‖s‖ ^ 2 by nlinarith) (norm_nonneg g)
  simp only [envelopeCubicModel, inner_zero_right, map_zero, norm_zero,
    zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero]
  nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg ‖s‖)]

lemma envelopeCubicStep_min [ProperSpace E] (g : E) (B : E →L[ℝ] E)
    {M : ℝ} (hM : 0 < M) (v : E) :
    envelopeCubicModel g B M (envelopeCubicStep g B M) ≤ envelopeCubicModel g B M v :=
  Classical.epsilon_spec (envelopeCubicModel_exists_min g B hM) v

lemma envelopeCubicStep_stationary [ProperSpace E]
    (g : E) (B : E →L[ℝ] E) {M : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫) :
    g + B (envelopeCubicStep g B M) +
      (M * ‖envelopeCubicStep g B M‖) • envelopeCubicStep g B M = 0 := by
  let s := envelopeCubicStep g B M
  have hm : IsMinOn (LongTails.Proofs.CappedCubicModel.model B g 0 M) univ s := by
    intro v _
    simpa [LongTails.Proofs.CappedCubicModel.model, envelopeCubicModel] using envelopeCubicStep_min g B hM v
  have hd := LongTails.Proofs.CappedCubicModel.model_hasFDerivAt B g 0 M s hB
  have hz := (hm.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero hd
  have hz' : innerSL ℝ (g + B s + (M * ‖s‖) • s) = 0 := by simpa using hz
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A (g + B s + (M * ‖s‖) • s)) hz'
  change ⟪g + B s + (M * ‖s‖) • s, g + B s + (M * ‖s‖) • s⟫ = 0 at hh
  rw [real_inner_self_eq_norm_sq] at hh
  have hn : ‖g + B s + (M * ‖s‖) • s‖ = 0 := by nlinarith [norm_nonneg (g + B s + (M * ‖s‖) • s)]
  exact norm_eq_zero.mp hn

lemma envelopeCubicStep_psd [ProperSpace E]
    (g : E) (B : E →L[ℝ] E) {M : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫) :
    ∀ h, 0 ≤ ⟪h, B h + (M * ‖envelopeCubicStep g B M‖) • h⟫ := by
  let s := envelopeCubicStep g B M
  have hstat := envelopeCubicStep_stationary g B hM hB
  by_cases hs : s = 0
  · have hg : g = 0 := by simpa only [show envelopeCubicStep g B M = 0 from hs,
      map_zero, norm_zero, mul_zero, zero_smul, add_zero] using hstat
    intro h
    change 0 ≤ ⟪h, B h + (M * ‖s‖) • h⟫
    simp only [hs, norm_zero, mul_zero, zero_smul, add_zero]
    by_contra ha
    have ha' : ⟪h, B h⟫ < 0 := lt_of_not_ge ha
    let c := M * ‖h‖ ^ 3 + 1
    have hc : 0 < c := by dsimp [c]; positivity
    let t := -⟪h, B h⟫ / c
    have ht : 0 < t := div_pos (neg_pos.mpr ha') hc
    have he : t * c = -⟪h, B h⟫ := div_mul_cancel₀ _ hc.ne'
    have hm := envelopeCubicStep_min g B hM (t • h)
    change envelopeCubicModel g B M s ≤ _ at hm
    simp only [hs, hg, envelopeCubicModel, inner_zero_left, map_zero, norm_zero, zero_pow (by decide : 3 ≠ 0),
      mul_zero, add_zero, zero_add, map_smul, real_inner_smul_left, inner_smul_right,
      norm_smul, Real.norm_of_nonneg ht.le] at hm
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have hh : 0 ≤ 3 * ⟪h, B h⟫ + 2 * M * t * ‖h‖ ^ 3 := by
      apply (mul_le_mul_iff_right₀ ht2).mp
      nlinarith
    dsimp [c] at he
    nlinarith
  · have hm : IsMinOn (LongTails.Proofs.CappedCubicModel.model B g 0 M)
        (Metric.closedBall 0 (‖s‖ + 1)) s := by
      intro v _
      simpa [LongTails.Proofs.CappedCubicModel.model, envelopeCubicModel] using envelopeCubicStep_min g B hM v
    have hh := LongTails.Proofs.CappedCubicModel.model_psd_of_stationarity B g s 0 M 0 (‖s‖ + 1)
      hs (by linarith) hB hm (by simpa using hstat)
    simpa using hh

lemma envelopeCubicStep_model_decrease [ProperSpace E]
    (g : E) (B : E →L[ℝ] E) {M : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫) :
    envelopeCubicModel g B M (envelopeCubicStep g B M) ≤ -M / 6 * ‖envelopeCubicStep g B M‖ ^ 3 := by
  let s := envelopeCubicStep g B M
  have hs := congrArg (fun v => ⟪s, v⟫) (envelopeCubicStep_stationary g B hM hB)
  have hp := envelopeCubicStep_psd g B hM hB s
  change envelopeCubicModel g B M s ≤ -M / 6 * ‖s‖ ^ 3
  change ⟪s, g + B s + (M * ‖s‖) • s⟫ = ⟪s, 0⟫ at hs
  change 0 ≤ ⟪s, B s + (M * ‖s‖) • s⟫ at hp
  simp only [inner_add_right, inner_smul_right, inner_zero_right, real_inner_self_eq_norm_sq] at hs hp
  rw [real_inner_comm g s] at hs
  unfold envelopeCubicModel
  nlinarith

lemma envelopeCubicStep_inexact_descent [ProperSpace E]
    (g G : E) (B A : E →L[ℝ] E) {M a b before after : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫)
    (hg : ‖g - G‖ ≤ a) (hH : ‖B - A‖ ≤ b)
    (htaylor : after ≤ before + ⟪G, envelopeCubicStep g B M⟫ +
      (1 / 2 : ℝ) * ⟪envelopeCubicStep g B M, A (envelopeCubicStep g B M)⟫ +
        M / 6 * ‖envelopeCubicStep g B M‖ ^ 3) :
    after - before ≤ -M / 3 * ‖envelopeCubicStep g B M‖ ^ 3 +
      a * ‖envelopeCubicStep g B M‖ + b / 2 * ‖envelopeCubicStep g B M‖ ^ 2 := by
  let s := envelopeCubicStep g B M
  have hm := envelopeCubicStep_model_decrease g B hM hB
  change envelopeCubicModel g B M s ≤ -M / 6 * ‖s‖ ^ 3 at hm
  unfold envelopeCubicModel at hm
  have hgi := real_inner_le_norm (G - g) s
  rw [inner_sub_left, norm_sub_rev G g] at hgi
  have hgn := mul_le_mul_of_nonneg_right hg (norm_nonneg s)
  have hhi := real_inner_le_norm s ((A - B) s)
  simp only [sub_apply, inner_sub_right] at hhi
  have hhn := (A - B).le_opNorm s
  have hH' : ‖A - B‖ ≤ b := by rwa [norm_sub_rev]
  have hhn' : ‖(A - B) s‖ ≤ b * ‖s‖ :=
    hhn.trans (mul_le_mul_of_nonneg_right hH' (norm_nonneg s))
  have hhscaled := mul_le_mul_of_nonneg_left hhn' (norm_nonneg s)
  change after ≤ before + ⟪G, s⟫ + (1 / 2 : ℝ) * ⟪s, A s⟫ + M / 6 * ‖s‖ ^ 3 at htaylor
  change after - before ≤ -M / 3 * ‖s‖ ^ 3 + a * ‖s‖ + b / 2 * ‖s‖ ^ 2
  change ‖s‖ * ‖A s - B s‖ ≤ ‖s‖ * (b * ‖s‖) at hhscaled
  nlinarith

lemma cubic_nonterminal_descent {M a b t r before after : ℝ}
    (hM : 0 ≤ M) (ht : 0 ≤ t) (hr : t ≤ r)
    (ha : a ≤ M * t ^ 2 / 24) (hb : b ≤ M * t / 12)
    (hd : after - before ≤ -M / 3 * r ^ 3 + a * r + b / 2 * r ^ 2) :
    after - before ≤ -M / 4 * r ^ 3 := by
  have hr0 : 0 ≤ r := ht.trans hr
  have hs : t ^ 2 ≤ r ^ 2 := by nlinarith
  have ha' : a * r ≤ M / 24 * r ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right ha hr0
    have h₂ := mul_le_mul_of_nonneg_left hs (mul_nonneg hM hr0)
    nlinarith
  have hb' : b / 2 * r ^ 2 ≤ M / 24 * r ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hb (sq_nonneg r)
    have h₂ := mul_le_mul_of_nonneg_left hr (mul_nonneg hM (sq_nonneg r))
    nlinarith
  linarith

lemma envelopeCubicStep_gradient_bound [ProperSpace E]
    (g G Gnext : E) (B A : E →L[ℝ] E) {M a b : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫)
    (hg : ‖g - G‖ ≤ a) (hH : ‖B - A‖ ≤ b)
    (htaylor : ‖Gnext - G - A (envelopeCubicStep g B M)‖ ≤
      M / 2 * ‖envelopeCubicStep g B M‖ ^ 2) :
    ‖Gnext‖ ≤ a + b * ‖envelopeCubicStep g B M‖ +
      (3 * M / 2) * ‖envelopeCubicStep g B M‖ ^ 2 := by
  let s := envelopeCubicStep g B M
  have hstat := envelopeCubicStep_stationary g B hM hB
  have he : Gnext = (Gnext - G - A s) + (G - g) + (A - B) s - (M * ‖s‖) • s := by
    change g + B s + (M * ‖s‖) • s = 0 at hstat
    simp only [sub_apply]
    have hz : -(g + B s + (M * ‖s‖) • s) = 0 := by rw [hstat, neg_zero]
    calc
      Gnext = Gnext + -(g + B s + (M * ‖s‖) • s) := by rw [hz, add_zero]
      _ = _ := by abel
  have hh : ‖(A - B) s‖ ≤ b * ‖s‖ := by
    have hn := (A - B).le_opNorm s
    rw [norm_sub_rev A B] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg s))
  have hgn : ‖G - g‖ ≤ a := by rwa [norm_sub_rev]
  have hn : ‖Gnext‖ ≤ ‖Gnext - G - A s‖ + ‖G - g‖ + ‖(A - B) s‖ + ‖(M * ‖s‖) • s‖ := by
    calc
      ‖Gnext‖ = ‖(Gnext - G - A s) + (G - g) + (A - B) s - (M * ‖s‖) • s‖ := congrArg norm he
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hM.le (norm_nonneg s))] at hn
  change ‖Gnext - G - A s‖ ≤ M / 2 * ‖s‖ ^ 2 at htaylor
  change ‖Gnext‖ ≤ a + b * ‖s‖ + (3 * M / 2) * ‖s‖ ^ 2
  nlinarith

lemma envelopeCubicStep_curvature_bound [ProperSpace E]
    (g : E) (B Anext : E →L[ℝ] E) {M b : ℝ} (hM : 0 < M)
    (hB : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫)
    (hH : ‖Anext - B‖ ≤ M * ‖envelopeCubicStep g B M‖ + b) (v : E) :
    -(2 * M * ‖envelopeCubicStep g B M‖ + b) * ‖v‖ ^ 2 ≤ ⟪v, Anext v⟫ := by
  let s := envelopeCubicStep g B M
  have hp := envelopeCubicStep_psd g B hM hB v
  change 0 ≤ ⟪v, B v + (M * ‖s‖) • v⟫ at hp
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have hn : ‖(B - Anext) v‖ ≤ (M * ‖s‖ + b) * ‖v‖ := by
    have hh := (B - Anext).le_opNorm v
    rw [norm_sub_rev B Anext] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg v))
  have hi := real_inner_le_norm v ((B - Anext) v)
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  simp only [sub_apply, inner_sub_right] at hi hh
  change -(2 * M * ‖s‖ + b) * ‖v‖ ^ 2 ≤ ⟪v, Anext v⟫
  nlinarith

lemma cubic_terminal_bounds {M a b t r ε η : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hrt : r ≤ t)
    (ha : a ≤ M * t ^ 2 / 24) (hb : b ≤ M * t / 12)
    (he : M * t ^ 2 ≤ ε / 16) (hη : M * t ≤ η / 4) :
    a + b * r + (3 * M / 2) * r ^ 2 ≤ ε / 8 ∧
      2 * M * r + b ≤ (25 / 48 : ℝ) * η := by
  have ht : 0 ≤ t := hr.trans hrt
  have hr2 : r ^ 2 ≤ t ^ 2 := by nlinarith
  have hmr := mul_le_mul_of_nonneg_left hrt hM
  have hmr2 := mul_le_mul_of_nonneg_left hr2 hM
  have hbr := mul_le_mul_of_nonneg_right hb hr
  have hmtr := mul_le_mul_of_nonneg_left hrt (mul_nonneg hM ht)
  constructor <;> nlinarith

lemma setup_envelope_hasGradient {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    HasGradientAt (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)
      (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z) z := by
  have H := setup_hyp hv hf
  rw [setup_envelope_gradient hv hf]
  exact weakEnvelope_hasGradient H.hL H.value_continuous H.value_weak z

lemma setup_envelope_gradient_derivative {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    HasFDerivAt (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L))
      (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z) z := by
  obtain ⟨A, hA, _⟩ := setup_envelope_quadratic_gradient hv hf z
  rw [hA.fderiv]
  exact hA

lemma setup_tuned_hessian_lipschitz {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z z' : p.E) :
    ‖fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z'‖ ≤
        (tuning p).smoothness * ‖z - z'‖ := by
  convert setup_envelope_hessian_lipschitz hv hf z z' using 1
  simp only [tuning]
  ring

lemma setup_jet_symmetric {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (w : Space p) (u v : p.E) :
    ⟪u, envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
      (tuning p).regularization v⟫ =
    ⟪envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
      (tuning p).regularization u, v⟫ := by
  exact (envelopeHessianApprox_symmetric p.L _ (tuning_positive hv).2.2.2.2.2.2.2.1
    (regularizedHessian_symmetric _
      (SpectralGradient.hessian_symmetric (fun a => (hf.1 a).differentiableAt) hf.2.1 w) p.L) u v).symm

lemma setup_cubic_descent {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance) :
    let g := (2 * p.L) • (z - w.fst)
    let B := envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
      (tuning p).regularization
    let d := envelopeCubicStep g B (tuning p).smoothness
    (tuning p).threshold ≤ ‖d‖ →
      envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L (z + d) -
        envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L z ≤
          -(tuning p).smoothness / 4 * ‖d‖ ^ 3 := by
  dsimp only
  intro hd
  have hp := tuning_positive hv
  obtain ⟨hg, hB⟩ := setup_jet_certificate hv hf z w hr
  have ht := LongTails.Proofs.CubicRegularization.objective_taylor
    (fun z => (setup_envelope_hasGradient hv hf z).hasFDerivAt)
    (setup_envelope_gradient_derivative hv hf) (setup_tuned_hessian_lipschitz hv hf) z
    (envelopeCubicStep ((2 * p.L) • (z - w.fst))
      (envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
        (tuning p).regularization) (tuning p).smoothness)
  have hupper := (abs_le.mp ht).2
  have hdec := envelopeCubicStep_inexact_descent
    (before := envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L z)
    (after := envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L
      (z + envelopeCubicStep ((2 * p.L) • (z - w.fst))
        (envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
          (tuning p).regularization) (tuning p).smoothness)) _ _ _ _ hp.1
    (setup_jet_symmetric hv hf w) hg hB (by linarith only [hupper])
  exact cubic_nonterminal_descent hp.1.le hp.2.2.2.2.1.le hd le_rfl le_rfl hdec

lemma setup_cubic_terminal {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance) :
    let g := (2 * p.L) • (z - w.fst)
    let B := envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
      (tuning p).regularization
    let d := envelopeCubicStep g B (tuning p).smoothness
    ‖d‖ ≤ (tuning p).threshold →
      ‖gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) (z + d)‖ ≤ p.ε / 8 ∧
      ∀ v, -((25 / 96 : ℝ) * (tuning p).curvature) * ‖v‖ ^ 2 ≤
        ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) (z + d) v, v⟫ := by
  dsimp only
  intro hd
  let g := (2 * p.L) • (z - w.fst)
  let B := envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L)
    (tuning p).regularization
  let d := envelopeCubicStep g B (tuning p).smoothness
  have hp := tuning_positive hv
  obtain ⟨hg, hB⟩ := setup_jet_certificate hv hf z w hr
  have hsym := setup_jet_symmetric hv hf w
  have ht := LongTails.Proofs.CubicRegularization.gradient_taylor
    (setup_envelope_gradient_derivative hv hf) (setup_tuned_hessian_lipschitz hv hf) z d
  have hgrad := envelopeCubicStep_gradient_bound g _
    (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) (z + d)) B _ hp.1 hsym hg hB
    (by convert ht using 1; ring)
  have hbounds := tuning_threshold_bounds hv
  have hterm := cubic_terminal_bounds hp.1.le (norm_nonneg d) hd le_rfl le_rfl
    hbounds.1 (show (tuning p).smoothness * (tuning p).threshold ≤
      ((tuning p).curvature / 2) / 4 by linarith only [hbounds.2.1])
  constructor
  · exact hgrad.trans hterm.1
  · intro v
    have hlip := setup_tuned_hessian_lipschitz hv hf (z + d) z
    rw [add_sub_cancel_left] at hlip
    have htriangle := dist_triangle
      (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) (z + d))
      (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z) B
    simp only [dist_eq_norm] at htriangle
    rw [norm_sub_rev (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z) B] at htriangle
    have hcurv := envelopeCubicStep_curvature_bound g B
      (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) (z + d))
      (b := (tuning p).hessianTolerance) hp.1 hsym
      (htriangle.trans (add_le_add hlip hB)) v
    rw [real_inner_comm] at hcurv
    have hscale := mul_le_mul_of_nonneg_right hterm.2 (sq_nonneg ‖v‖)
    change -(2 * (tuning p).smoothness * ‖d‖ +
      (tuning p).smoothness * (tuning p).threshold / 12) * ‖v‖ ^ 2 ≤
        ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) (z + d) v, v⟫ at hcurv
    change -((25 / 96 : ℝ) * (tuning p).curvature) * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) (z + d) v, v⟫
    linarith only [hcurv, hscale]

lemma setup_envelope_gap {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) :
    envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 -
      envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L z ≤ p.Δ := by
  have H := setup_hyp hv hf
  have hm := weakProx_min H.hL H.value_continuous H.value_weak p.x0 (mem_univ p.x0)
  change envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 ≤
    proxObj (value f) p.L p.x0 p.x0 at hm
  simp only [proxObj, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hm
  have hg := hf.2.2.2.2.2.2.1 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z)
  have hn := mul_nonneg H.hL.le
    (sq_nonneg ‖primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - z‖)
  change _ - (value f (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) +
    p.L * ‖primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - z‖ ^ 2) ≤ _
  calc
    _ ≤ value f p.x0 - (value f (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) +
        p.L * ‖primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z - z‖ ^ 2) := sub_le_sub_right hm _
    _ ≤ value f p.x0 - value f (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) :=
      sub_le_sub_left (le_add_of_nonneg_right hn) _
    _ ≤ p.Δ := hg

lemma cubic_segment_charge {M s mesh r D : ℝ} (hM : 0 < M) (hs : 0 < s)
    (hm : 0 < mesh) (hr : s ≤ r) (hD : M / 4 * r ^ 3 ≤ D) :
    ((max 1 ⌈r / mesh⌉₊ : ℕ) : ℝ) ≤ (8 / (M * s ^ 3) + 4 / (M * mesh ^ 3)) * D := by
  have hr0 : 0 ≤ r := hs.le.trans hr
  have hp := pow_le_pow_left₀ hs.le hr 3
  have hsp := mul_le_mul_of_nonneg_left hp (show 0 ≤ M / 4 by positivity)
  have h₁ : 2 ≤ 8 / (M * s ^ 3) * D := by
    have hh : 2 ≤ (8 * D) / (M * s ^ 3) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hsp, hD])
    convert hh using 1; ring
  have h₂ : (r / mesh) ^ 3 ≤ 4 / (M * mesh ^ 3) * D := by
    have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 4 / (M * mesh ^ 3) by positivity)
    convert hh using 1
    field_simp
  calc
    _ ≤ 2 + (r / mesh) ^ 3 := segment_count_bound hr0 hm
    _ ≤ 8 / (M * s ^ 3) * D + 4 / (M * mesh ^ 3) * D := add_le_add h₁ h₂
    _ = _ := by ring

end OracleTemplate.PLMinimax
