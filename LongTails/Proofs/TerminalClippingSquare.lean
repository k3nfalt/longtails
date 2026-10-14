import LongTails.Proofs.TerminalClippingMartingale

set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

noncomputable def squareScale (q : Public) (D : ℝ) : ℝ :=
  104 * q.B * D / (4096 * Real.sqrt q.T * Real.log (8 / q.δ))

noncomputable def squareWeight (q : Public) (t : ℕ) : ℝ :=
  weight q.T t * (stepSize q.B q.δ q.T t) ^ 2 / tailWeight q.B q.δ q.T t

lemma squareScale_pos (q : Public) (D : ℝ) (hB : 0 < q.B) (hD : 0 < D)
    (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T) : 0 < squareScale q D := by
  have hq := confidence_pos hδ hδ1
  have ht : 0 < (q.T : ℝ) := by exact_mod_cast hT
  unfold squareScale
  positivity

lemma squareWeight_nonneg (q : Public) (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    {t : ℕ} (ht : t < q.T) : 0 ≤ squareWeight q t := by
  have hw : 0 ≤ weight q.T t := by linarith [(weight_bounds ht).1]
  exact div_nonneg (mul_nonneg hw (sq_nonneg _)) (tailWeight_pos hB hδ hδ1 ht).le

lemma squareWeight_after (q : Public) {t : ℕ} (ht : q.T ≤ t) : squareWeight q t = 0 := by
  simp [squareWeight, stepSize_after q.B q.δ ht]

lemma squared_clip_mgf {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (P : ProbabilityMeasure Ω)
    (hg : Measurable (Function.uncurry g))
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} {u : Vector q.d} {D : ℝ}
    (hD : 0 < D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D)
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    (s : ℕ × (Vector q.d × Vector q.d)) (hs : radiusGood q X u D s) :
    Integrable (fun ω => Real.exp
      (squareWeight q s.1 * ‖clippedSample q g s ω‖ ^ 2 / squareScale q D)) (P : Measure Ω) ∧
    (∫ ω, Real.exp (squareWeight q s.1 * ‖clippedSample q g s ω‖ ^ 2 / squareScale q D)
      ∂(P : Measure Ω)) ≤ Real.exp (2 / (q.T : ℝ)) := by
  by_cases ht : s.1 < q.T
  · let C := threshold q.B q.G q.T (s.2.1 - q.x0) (observableInfluence q s)
    let k := squareWeight q s.1
    let H := squareScale q D
    have hC : 0 ≤ C := (threshold_pos hB hG hT _ _).le
    have hk : 0 ≤ k := squareWeight_nonneg q hB hδ hδ1 ht
    have hH : 0 < H := squareScale_pos q D hB hD hδ hδ1 hT
    have hTr : 0 < (q.T : ℝ) := by exact_mod_cast hT
    have hq := confidence_pos hδ hδ1
    have hr : ‖q.x0 - u‖ ≤ Real.sqrt D := by
      nlinarith [Real.sq_sqrt hD.le, Real.sqrt_nonneg D, norm_nonneg (q.x0 - u)]
    have hx := radius_geometry hD.le (Real.sqrt_nonneg D) (Real.sq_sqrt hD.le).le hr hs.2
    have hM := local_moment_bound hD.le hGD hx
    have hC2 : C ^ 2 ≤ 26 * q.B ^ 2 * D * q.T :=
      (threshold_square hB hG hT _ _).trans (mul_le_mul_of_nonneg_right hM hTr.le)
    have hgs : Measurable (g s.2.1) := hg.comp (measurable_const.prodMk measurable_id)
    have hX : Measurable (fun ω => clip C (g s.2.1 ω)) := (measurable_clip C).comp hgs
    have hsecond := full_moment_clip_second hgs (hmi _ hs.1.1) hC
    have hm' := hsecond.2.trans ((hm _ hs.1.1).trans hM)
    have hkbound := squared_step_weight_bound hB hδ hδ1 ht
    have he : 4 / (4096 * q.B * Real.sqrt q.T * Real.log (8 / q.δ) * q.T) *
        (26 * q.B ^ 2 * D * q.T) = H := by
      dsimp [H, squareScale]
      field_simp; ring
    have he' : 4 / (4096 * q.B * Real.sqrt q.T * Real.log (8 / q.δ) * q.T) *
        (26 * q.B ^ 2 * D) = H / q.T := by
      dsimp [H, squareScale]
      field_simp; ring
    have hbound (ω : Ω) : k * ‖clippedSample q g s ω‖ ^ 2 ≤ H := by
      have hc : ‖clippedSample q g s ω‖ ^ 2 ≤ C ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hC (g s.2.1 ω)) 2
      have hh := mul_le_mul hkbound (hc.trans hC2) (sq_nonneg _) (by positivity)
      exact hh.trans_eq he
    have hi : Integrable (fun ω => k * ‖clippedSample q g s ω‖ ^ 2) (P : Measure Ω) :=
      hsecond.1.const_mul k
    have hmean : (∫ ω, k * ‖clippedSample q g s ω‖ ^ 2 ∂(P : Measure Ω)) ≤ H / q.T := by
      rw [integral_const_mul]
      exact ((mul_le_mul_of_nonneg_left hm' hk).trans
        (mul_le_mul_of_nonneg_right hkbound (by positivity))).trans_eq he'
    have hh := nonnegative_bounded_mgf ((hX.norm.pow_const 2).const_mul k) hi hH
      (fun _ => mul_nonneg hk (sq_nonneg _)) hbound hmean
    refine ⟨hh.1, hh.2.trans_eq ?_⟩
    congr 1
    field_simp
  · rw [squareWeight_after q (by omega : q.T ≤ s.1)]
    simp
    positivity

noncomputable def squareIncrement {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (D : ℝ)
    (s : ℕ × (Vector q.d × Vector q.d)) (ω : Ω) : ℝ :=
  squareWeight q s.1 * ‖clippedSample q g s ω‖ ^ 2 / squareScale q D - 2 / (q.T : ℝ)

lemma squareIncrement_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g)) (D : ℝ) :
    Measurable (Function.uncurry (squareIncrement q g D)) := by
  have hw : Measurable (fun z : (ℕ × (Vector q.d × Vector q.d)) × Ω => squareWeight q z.1.1) :=
    (measurable_of_countable (squareWeight q)).comp measurable_fst.fst
  exact ((hw.mul ((clippedSample_measurable q hg).norm.pow_const 2)).div_const _).sub_const _

lemma squareScale_accuracy_bound (q : Public) {D : ℝ} (hB : 0 < q.B) (hD : 0 ≤ D)
    (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T) :
    squareScale q D * (2 + Real.log (8 / q.δ)) ≤
      q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
  have hq := confidence_ge_one hδ hδ1
  have hqp := confidence_pos hδ hδ1
  have ht : 0 < Real.sqrt q.T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hs : 104 * (2 + Real.log (8 / q.δ)) / (4096 * Real.log (8 / q.δ)) ≤ Real.log (8 / q.δ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ q.B * D / Real.sqrt q.T by positivity)
  unfold squareScale
  convert hh using 1 <;> field_simp

end OracleTemplate.TerminalClipping
