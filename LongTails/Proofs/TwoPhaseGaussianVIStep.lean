import LongTails.Proofs.GaussianVariationalGuarantee

open MeasureTheory
namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

structure StepConstants (L μ : ℝ) (d : ℕ) : Prop where
  offset_ge : 2 ≤ offset L μ d
  step_pos : 0 < stepSize μ (offset L μ d) 0
  identity : stepSize μ (offset L μ d) 0 * (μ * offset L μ d) = 2
  smooth : stepSize μ (offset L μ d) 0 * L ≤ 1
  stable : stepSize μ (offset L μ d) 0 * (8 * smoothConst L μ d + μ) = 1
  nonneg : 0 ≤ smoothConst L μ d

lemma constants (h : Potential L μ V) : StepConstants L μ d := by
  have hm := h.pos
  have hl := h.L_pos
  have ht := tau_nonneg d ((one_le_div hm).mpr h.le)
  set A := smoothConst L μ d
  have hA : L ≤ A := by
    dsimp [A, smoothConst]
    nlinarith [mul_nonneg hl.le ht]
  have hA0 : 0 ≤ A := hl.le.trans hA
  set a := offset L μ d
  have ha : 2 ≤ a := by
    change 2 ≤ 16 * A / μ + 2
    linarith [div_nonneg (show 0 ≤ 16 * A by positivity) hm.le]
  set η := stepSize μ a 0
  have he := stepSize_pos hm ha 0
  have hid : η * (μ * a) = 2 := by
    simp [η, stepSize, ne_of_gt hm, show a ≠ 0 by linarith]
  have haf : μ * a = 16 * A + 2 * μ := by
    change μ * (16 * A / μ + 2) = _
    field_simp
  have hs : η * (8 * A + μ) = 1 := by rw [haf] at hid; linarith
  refine ⟨ha, he, hid, ?_, hs, hA0⟩
  calc η * L ≤ η * (8 * A + μ) := mul_le_mul_of_nonneg_left (by linarith) he.le
    _ = 1 := hs

noncomputable def energy (V : Point d → ℝ) (ms : Location d) (Cs : Scale d) (η : ℝ)
    (z : Location d × Scale d) : ℝ :=
  sqd z (ms, Cs) + (2 * η) * bregmanMean V ms Cs z.1 z.2

lemma warm_step (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (ho : IsOptimal V ms Cs) (z : Location d × Scale d) (hz : IsCholesky z.2) :
    let a := offset L μ d
    let η := stepSize μ a 0
    let p := stepAt V μ a 0 z
    let Q := energy V ms Cs η
    Integrable (fun ξ => Q (p ξ)) (noiseLaw d) ∧
      ∫ ξ, Q (p ξ) ∂noiseLaw d ≤ (1 - η * μ) * Q z + (η * μ) * (d / (2 * μ)) := by
  intro a η p Q
  have c := constants h
  have hm := h.pos
  have he : 0 < η := c.step_pos
  have hs := step_expectation h ho hz he c.smooth
  let r := fun ξ => sqd (p ξ) (ms, Cs)
  let D := fun ξ => bregmanMean V ms Cs (p ξ).1 (p ξ).2
  let G := fun ξ => gap V ms Cs (p ξ)
  have hiG : Integrable G (noiseLaw d) := hs.1
  have hir : Integrable r (noiseLaw d) := hs.2.1
  have hc ξ : IsCholesky (p ξ).2 := stepAt_cholesky hm c.offset_ge 0 hz ξ
  have hD ξ : D ξ ≤ G ξ := bregmanMean_le_objective h ho _ (hc ξ)
  have nn (y : Location d × Scale d) (hy : IsCholesky y.2) :
      0 ≤ bregmanMean V ms Cs y.1 y.2 :=
    (mul_nonneg (half_pos hm).le (sqDist_nonneg _ _ _ _)).trans
      (bregmanMean_lower h y.1 (isLower_sub hy.1 ho.1.1))
  have hiD : Integrable D (noiseLaw d) := by
    apply hiG.mono' (((measurable_bregmanMean h ms Cs).comp
      (measurable_step_fixed h η z)).aestronglyMeasurable)
    exact ae_of_all _ fun ξ => by
      change ‖bregmanMean V ms Cs (p ξ).1 (p ξ).2‖ ≤ G ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (nn _ (hc ξ))]
      exact hD ξ
  refine ⟨hir.addL (hiD.const_mul _), ?_⟩
  change (∫ ξ, r ξ + (2*η) * D ξ ∂noiseLaw d) ≤ _
  rw [integral_add hir (hiD.const_mul _), integral_const_mul]
  have hg := (integral_mono hiD hiG hD).trans hs.2.2
  change (∫ ξ, D ξ ∂noiseLaw d) ≤ 1 / (2*η) * ((1-η*μ)*sqd z (ms,Cs) -
    ∫ ξ, r ξ ∂noiseLaw d) + η * (4 * smoothConst L μ d * bregmanMean V ms Cs z.1 z.2 +
    2 * noiseConst L μ d) at hg
  have scaled := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*η by positivity)
  rw [mul_add, ← mul_assoc, mul_one_div_cancel (by positivity : 2*η ≠ 0), one_mul] at scaled
  have eqn : noiseConst L μ d = smoothConst L μ d * d := by
    unfold noiseConst smoothConst
    ring
  rw [eqn] at scaled
  have hstab : η * (8 * smoothConst L μ d + μ) = 1 := c.stable
  have hA := c.nonneg
  have hcoef : 8 * smoothConst L μ d * η^2 ≤ (1 - η*μ) * (2*η) := by
    nlinarith [mul_nonneg (show 0 ≤ η^2 by positivity) hA, congrArg (· * (2*η)) hstab]
  have hnoise : 4 * smoothConst L μ d * η^2 ≤ η / 2 := by
    nlinarith [congrArg (· * η) hstab, mul_nonneg (sq_nonneg η) hm.le]
  have hfloor : (η*μ) * (d / (2*μ)) = η/2*d := by field_simp
  rw [hfloor]
  dsimp only [Q, energy]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (nn z hz),
    mul_le_mul_of_nonneg_right hnoise (Nat.cast_nonneg (α := ℝ) d)]

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
