import LongTails.Proofs.PLHessianExpect
import LongTails.Proofs.RobustPLPotential

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RobustPLPotential

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma integral_inner_bias {ζ : Ω → E} (hi : Integrable ζ P) {B : ℝ}
    (hb : ‖∫ ω, ζ ω ∂P‖ ≤ B) (v : E) :
    |∫ ω, ⟪v, ζ ω⟫ ∂P| ≤ ‖v‖ * B := by
  rw [integral_inner hi v]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

omit [IsProbabilityMeasure P] in
lemma noise_moments {ζ : Ω → E} (hi : Integrable ζ P)
    (hi2 : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hi4 : Integrable (fun ω => ‖ζ ω‖ ^ 4) P)
    {B V Q η L : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hb : ‖∫ ω, ζ ω ∂P‖ ≤ B) (hv : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ V)
    (hq : (∫ ω, ‖ζ ω‖ ^ 4 ∂P) ≤ Q) (G : E) :
    let N := fun ω => L * η ^ 2 * ‖ζ ω‖ ^ 2 - η * ⟪G, ζ ω⟫
    Integrable N P ∧ Integrable (fun ω => N ω ^ 2) P ∧
    (∫ ω, N ω ∂P) ≤ L * η ^ 2 * V + η * ‖G‖ * B ∧
    (∫ ω, N ω ^ 2 ∂P) ≤ 2 * η ^ 2 * ‖G‖ ^ 2 * V + 2 * L ^ 2 * η ^ 4 * Q := by
  let N := fun ω => L * η ^ 2 * ‖ζ ω‖ ^ 2 - η * ⟪G, ζ ω⟫
  have hin : Integrable (fun ω => ⟪G, ζ ω⟫) P := hi.const_inner G
  have hNi : Integrable N P := (hi2.const_mul _).sub (hin.const_mul _)
  have hN2 (ω : Ω) : N ω ^ 2 ≤
      2 * η ^ 2 * ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 + 2 * L ^ 2 * η ^ 4 * ‖ζ ω‖ ^ 4 := by
    have hcs : ⟪G, ζ ω⟫ ^ 2 ≤ ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 := by
      have hh := abs_real_inner_le_norm G (ζ ω)
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [neg_abs_le ⟪G, ζ ω⟫]) (le_trans (le_abs_self _) hh)
    dsimp [N]
    nlinarith [sq_nonneg (η * ⟪G, ζ ω⟫ + L * η ^ 2 * ‖ζ ω‖ ^ 2)]
  have hmajor := (hi2.const_mul (2 * η ^ 2 * ‖G‖ ^ 2)).add
    (hi4.const_mul (2 * L ^ 2 * η ^ 4))
  have hN2i : Integrable (fun ω => N ω ^ 2) P := by
    apply hmajor.mono' (hNi.aestronglyMeasurable.pow 2)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hN2 ω
  refine ⟨hNi, hN2i, ?_, ?_⟩
  · change (∫ ω, L * η ^ 2 * ‖ζ ω‖ ^ 2 - η * ⟪G, ζ ω⟫ ∂P) ≤ _
    rw [integral_sub (hi2.const_mul _) (hin.const_mul _), integral_const_mul, integral_const_mul]
    have hh := integral_inner_bias hi hb G
    have hl : -(‖G‖ * B) ≤ ∫ ω, ⟪G, ζ ω⟫ ∂P := (abs_le.mp hh).1
    have hh1 := mul_le_mul_of_nonneg_left hv (mul_nonneg hL (sq_nonneg η))
    have hh2 := mul_le_mul_of_nonneg_left hl hη
    linarith
  · have hh := integral_mono hN2i hmajor hN2
    simp only [Pi.add_apply] at hh
    rw [integral_add (hi2.const_mul _) (hi4.const_mul _), integral_const_mul, integral_const_mul] at hh
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_left hv (by positivity))
      (mul_le_mul_of_nonneg_left hq (by positivity)))

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma raw_potential_step {f : E → ℝ} {ζ : Ω → E}
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    {L η lam b B V Q : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 2) (hlam : 0 ≤ lam) (hb : 0 < b)
    (hm : Measurable ζ) (hi : Integrable ζ P)
    (hi2 : Integrable (fun ω => ‖ζ ω‖ ^ 2) P) (hi4 : Integrable (fun ω => ‖ζ ω‖ ^ 4) P)
    (hB : ‖∫ ω, ζ ω ∂P‖ ≤ B) (hV : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ V)
    (hQ : (∫ ω, ‖ζ ω‖ ^ 4 ∂P) ≤ Q) (x u p0 : E) (hp0 : f p0 = f u) :
    let G := gradient f x
    let Φ := f x - f u
    let δ := η / 2 * ‖G‖ ^ 2
    let c := PLHessian.dhub b b (Φ - δ)
    let F := fun ω => PLHessian.distSq f u (x - η • (G + ζ ω)) +
      lam * PLHessian.hub b b (f (x - η • (G + ζ ω)) - f u)
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤
      ‖x - p0 - η • G‖ ^ 2 + 2 * η * ‖x - p0 - η • G‖ * B + η ^ 2 * V +
      lam * (PLHessian.hub b b (Φ - δ) + c * (L * η ^ 2 * V + η * ‖G‖ * B) +
        (η ^ 2 * ‖G‖ ^ 2 * V + L ^ 2 * η ^ 4 * Q) / b) := by
  let G := gradient f x
  let Φ := f x - f u
  let δ := η / 2 * ‖G‖ ^ 2
  let c := PLHessian.dhub b b (Φ - δ)
  let v := x - p0 - η • G
  let N := fun ω => L * η ^ 2 * ‖ζ ω‖ ^ 2 - η * ⟪G, ζ ω⟫
  have hNm := noise_moments hi hi2 hi4 hη hL hB hV hQ G
  have hNi : Integrable N P := hNm.1
  have hN2i : Integrable (fun ω => N ω ^ 2) P := hNm.2.1
  have hc : 0 ≤ c := PLHessian.dhub_nonneg hb _
  have hf (ω : Ω) : f (x - η • (G + ζ ω)) - f u ≤ Φ - δ + N ω := by
    have hh := HeavyTailedPL.noisy_step hgrad hlip hL hη hstep x (G + ζ ω)
    have he : G + ζ ω - gradient f x = ζ ω := by dsimp [G]; abel
    rw [he] at hh
    dsimp [Φ, δ, N, G]
    linarith
  have hh (ω : Ω) : PLHessian.hub b b (f (x - η • (G + ζ ω)) - f u) ≤
      PLHessian.hub b b (Φ - δ) + c * N ω + N ω ^ 2 / (2 * b) := by
    have h1 := PLHessian.hub_mono (a := b) hb (hf ω)
    have h2 := PLHessian.hub_taylor (a := b) hb (Φ - δ) (Φ - δ + N ω)
    rw [show Φ - δ + N ω - (Φ - δ) = N ω by ring] at h2
    linarith
  have hd (ω : Ω) : PLHessian.distSq f u (x - η • (G + ζ ω)) ≤
      ‖v‖ ^ 2 - 2 * η * ⟪v, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2 := by
    have h := PLHessian.distSq_le (u := u) (x - η • (G + ζ ω)) p0 hp0
    have he : x - η • (G + ζ ω) - p0 = v - η • ζ ω := by dsimp [v]; rw [smul_add]; abel
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    linarith
  let D := fun ω => ‖v‖ ^ 2 - 2 * η * ⟪v, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2
  let H := fun ω => PLHessian.hub b b (Φ - δ) + c * N ω + N ω ^ 2 / (2 * b)
  have hiin : Integrable (fun ω => ⟪v, ζ ω⟫) P := hi.const_inner v
  have hDi : Integrable D P := ((integrable_const _).sub (hiin.const_mul _)).add (hi2.const_mul _)
  have hHi : Integrable H P := ((integrable_const _).add (hNi.const_mul _)).add (hN2i.div_const _)
  let F := fun ω => PLHessian.distSq f u (x - η • (G + ζ ω)) +
      lam * PLHessian.hub b b (f (x - η • (G + ζ ω)) - f u)
  have hFbound (ω : Ω) : F ω ≤ D ω + lam * H ω :=
    add_le_add (hd ω) (mul_le_mul_of_nonneg_left (hh ω) hlam)
  have hFi : Integrable F P := by
    have hfc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hgrad z).continuousAt
    have hX : Measurable (fun ω => x - η • (G + ζ ω)) :=
      measurable_const.sub ((measurable_const.add hm).const_smul η)
    have hFm : Measurable F :=
      (PLHessian.distSq_continuous.measurable.comp hX).add
        (measurable_const.mul ((PLHessian.hub_continuous hb).measurable.comp
          ((hfc.measurable.comp hX).sub_const (f u))))
    apply (hDi.add (hHi.const_mul lam)).mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F ω from by
        dsimp [F, PLHessian.distSq]
        have := PLHessian.hub_nonneg (a := b) hb (f (x - η • (G + ζ ω)) - f u)
        positivity)]
      exact hFbound ω
  have hDint : (∫ ω, D ω ∂P) ≤ ‖v‖ ^ 2 + 2 * η * ‖v‖ * B + η ^ 2 * V := by
    have ha : Integrable (fun ω => ‖v‖ ^ 2 - 2 * η * ⟪v, ζ ω⟫) P :=
      (integrable_const _).sub (hiin.const_mul _)
    dsimp [D]
    rw [integral_add ha (hi2.const_mul _),
      integral_sub (integrable_const _) (hiin.const_mul _), integral_const_mul, integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul]
    have h1 := (abs_le.mp (integral_inner_bias hi hB v)).1
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * η by positivity)
    have h3 := mul_le_mul_of_nonneg_left hV (sq_nonneg η)
    linarith
  have hHint : (∫ ω, H ω ∂P) ≤ PLHessian.hub b b (Φ - δ) +
      c * (L * η ^ 2 * V + η * ‖G‖ * B) +
      (η ^ 2 * ‖G‖ ^ 2 * V + L ^ 2 * η ^ 4 * Q) / b := by
    have ha : Integrable (fun ω => PLHessian.hub b b (Φ - δ) + c * N ω) P :=
      (integrable_const _).add (hNi.const_mul _)
    dsimp [H]
    rw [integral_add ha (hN2i.div_const _),
      integral_add (integrable_const _) (hNi.const_mul _), integral_const_mul, integral_div,
      integral_const]
    simp only [probReal_univ, one_smul]
    have h1 := mul_le_mul_of_nonneg_left hNm.2.2.1 hc
    have h2 := div_le_div_of_nonneg_right hNm.2.2.2 (show 0 ≤ 2 * b by positivity)
    have he : (2 * η ^ 2 * ‖G‖ ^ 2 * V + 2 * L ^ 2 * η ^ 4 * Q) / (2 * b) =
        (η ^ 2 * ‖G‖ ^ 2 * V + L ^ 2 * η ^ 4 * Q) / b := by ring
    rw [he] at h2
    linarith
  refine ⟨hFi, ?_⟩
  have h := integral_mono hFi (hDi.add (hHi.const_mul lam)) hFbound
  simp only [Pi.add_apply] at h
  rw [integral_add hDi (hHi.const_mul lam), integral_const_mul] at h
  exact h.trans (add_le_add hDint (mul_le_mul_of_nonneg_left hHint hlam))

end OracleTemplate.RobustPLPotential
