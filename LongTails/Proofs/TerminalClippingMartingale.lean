import LongTails.Proofs.TerminalClippingRadius
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma influence_clip_bound {B G D c : ℝ} {T : ℕ}
    (hB : 0 < B) (hG : 0 < G) (hD : 0 ≤ D) (hT : 0 < T)
    (hc : 0 ≤ c) (hcT : c ≤ 4 / (T : ℝ))
    (hGD : G ^ 2 ≤ B ^ 2 * D) (x U d : E)
    (hx : ‖x‖ ≤ 5 * Real.sqrt D) (hd : ‖d‖ ≤ Real.sqrt D) :
    threshold B G T x U * ‖U - c • d‖ ≤ 50 * B * D / Real.sqrt T := by
  let C := threshold B G T x U
  have hC : 0 ≤ C := (threshold_pos hB hG hT x U).le
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hM := local_moment_bound hD hGD hx
  have hscale := local_mean_scale hB.le hD hGD hx
  have hCu : C * ‖U‖ ≤ 26 * B * D / Real.sqrt T := by
    have hh := (threshold_influence hB hT x U).trans
      (div_le_div_of_nonneg_right hM (by positivity))
    convert hh using 1; field_simp
  have hCb : C ≤ 6 * B * Real.sqrt D * Real.sqrt T :=
    (threshold_size x U).trans (mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg _))
  have hcd : c * ‖d‖ ≤ (4 / (T : ℝ)) * Real.sqrt D :=
    mul_le_mul hcT hd (norm_nonneg _) (by positivity)
  have hCd := mul_le_mul hCb hcd (mul_nonneg hc (norm_nonneg _)) (by positivity)
  have he : (6 * B * Real.sqrt D * Real.sqrt T) * ((4 / (T : ℝ)) * Real.sqrt D) =
      24 * B * D / Real.sqrt T := by
    apply (eq_div_iff (ne_of_gt hs)).mpr
    field_simp
    ring_nf
    simp only [Real.sq_sqrt hD, Real.sq_sqrt ht.le]; ring
  rw [he] at hCd
  have hv := norm_sub_le U (c • d)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at hv
  have hh := mul_le_mul_of_nonneg_left hv hC
  calc
    _ ≤ C * ‖U‖ + C * (c * ‖d‖) := by convert hh using 1; ring
    _ ≤ 26 * B * D / Real.sqrt T + 24 * B * D / Real.sqrt T := add_le_add hCu hCd
    _ = _ := by ring

lemma influence_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {B G D c : ℝ} {T : ℕ} (hB : 0 < B) (hG : 0 < G) (hD : 0 < D) (hT : 0 < T)
    (hc : 0 ≤ c) (hcT : c ≤ 4 / (T : ℝ)) (hGD : G ^ 2 ≤ B ^ 2 * D)
    (x U d : E) (hx : ‖x‖ ≤ 5 * Real.sqrt D) (hd : ‖d‖ ≤ Real.sqrt D)
    (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ B ^ 2 * ‖x‖ ^ 2 + G ^ 2) :
    let τ := Real.sqrt T / (400 * B * D)
    let C := threshold B G T x U
    let V := U - c • d
    Integrable (fun ω => Real.exp (-τ * ⟪clip C (g ω) - ∫ z, clip C (g z) ∂P, V⟫)) P ∧
    (∫ ω, Real.exp (-τ * ⟪clip C (g ω) - ∫ z, clip C (g z) ∂P, V⟫) ∂P) ≤
      Real.exp (τ ^ 2 * ‖V‖ ^ 2 * (26 * B ^ 2 * D)) := by
  let τ := Real.sqrt T / (400 * B * D)
  let C := threshold B G T x U
  let V := U - c • d
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hC : 0 ≤ C := (threshold_pos hB hG hT x U).le
  have hi := integrable_clip (P := P) hg hC
  have hs := full_moment_clip_second hg hmi hC
  have hm' := hs.2.trans (hm.trans (local_moment_bound hD.le hGD hx))
  have hj := influence_clip_bound hB hG hD.le hT hc hcT hGD x U d hx hd
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hsmall : 2 * τ * C * ‖V‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hj (show 0 ≤ 2 * τ by positivity)
    have he : 2 * τ * (50 * B * D / Real.sqrt T) = 1 / 4 := by
      dsimp [τ]
      field_simp; ring
    rw [he] at hh
    nlinarith
  exact centered_inner_mgf ((measurable_clip C).comp hg) hi hs.1 hτ V
    (fun ω => norm_clip_le hC (g ω)) hm' hsmall

noncomputable def observableInfluence (q : Public) (s : ℕ × (Vector q.d × Vector q.d)) : Vector q.d :=
  influenceScale q.B q.δ q.T s.1 • ((s.2.1 - q.x0) - s.2.2)

noncomputable def residualInfluence (q : Public) (u : Vector q.d)
    (s : ℕ × (Vector q.d × Vector q.d)) : Vector q.d :=
  observableInfluence q s -
    (weight q.T s.1 * stepSize q.B q.δ q.T s.1 / tailWeight q.B q.δ q.T 0) • (u - q.x0)

noncomputable def clippedSample {Ω : Type*} (q : Public) (g : Vector q.d → Ω → Vector q.d)
    (s : ℕ × (Vector q.d × Vector q.d)) (ω : Ω) : Vector q.d :=
  clip (threshold q.B q.G q.T (s.2.1 - q.x0) (observableInfluence q s)) (g s.2.1 ω)

lemma observableInfluence_measurable (q : Public) : Measurable (observableInfluence q) := by
  exact ((measurable_of_countable (influenceScale q.B q.δ q.T)).comp measurable_fst).smul
    ((measurable_snd.fst.sub_const q.x0).sub measurable_snd.snd)

lemma residualInfluence_measurable (q : Public) (u : Vector q.d) :
    Measurable (residualInfluence q u) := by
  exact (observableInfluence_measurable q).sub
    (((measurable_of_countable (fun t => weight q.T t * stepSize q.B q.δ q.T t /
      tailWeight q.B q.δ q.T 0)).comp measurable_fst).smul_const (u - q.x0))

lemma clippedSample_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (clippedSample q g)) := by
  have hc := (threshold_measurable q.B q.G q.T).comp
    ((measurable_snd.fst.sub_const q.x0).prodMk (observableInfluence_measurable q))
  exact measurable_variable_clip (hc.comp measurable_fst)
    (hg.comp (measurable_fst.snd.fst.prodMk measurable_snd))

lemma clippedSample_mean_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (P : ProbabilityMeasure Ω) :
    Measurable (fun s => ∫ ω, clippedSample q g s ω ∂(P : Measure Ω)) :=
  (clippedSample_measurable q hg).stronglyMeasurable.integral_prod_right.measurable

lemma clippedSample_centered_mgf {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (P : ProbabilityMeasure Ω)
    (hg : Measurable (Function.uncurry g))
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} {u : Vector q.d} {D : ℝ}
    (hD : 0 < D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D)
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    (s : ℕ × (Vector q.d × Vector q.d)) (hs : radiusGood q X u D s) :
    let τ := Real.sqrt q.T / (400 * q.B * D)
    Integrable (fun ω => Real.exp (-τ * ⟪clippedSample q g s ω -
      ∫ z, clippedSample q g s z ∂(P : Measure Ω), residualInfluence q u s⟫)) (P : Measure Ω) ∧
    (∫ ω, Real.exp (-τ * ⟪clippedSample q g s ω -
      ∫ z, clippedSample q g s z ∂(P : Measure Ω), residualInfluence q u s⟫) ∂(P : Measure Ω)) ≤
      Real.exp (τ ^ 2 * ‖residualInfluence q u s‖ ^ 2 * (26 * q.B ^ 2 * D)) := by
  by_cases ht : s.1 < q.T
  · have hstart' : ‖q.x0 - u‖ ≤ Real.sqrt D := by
      nlinarith [Real.sq_sqrt hD.le, Real.sqrt_nonneg D, norm_nonneg (q.x0 - u)]
    have hd : ‖u - q.x0‖ ≤ Real.sqrt D := by rw [norm_sub_rev]; exact hstart'
    have hx := radius_geometry hD.le (Real.sqrt_nonneg D) (Real.sq_sqrt hD.le).le hstart' hs.2
    have hc : 0 ≤ weight q.T s.1 * stepSize q.B q.δ q.T s.1 / tailWeight q.B q.δ q.T 0 := by
      have hw : 0 ≤ weight q.T s.1 := by linarith [(weight_bounds ht).1]
      exact div_nonneg (mul_nonneg hw (stepSize_pos hB hδ hδ1 ht).le)
        (tailWeight_pos hB hδ hδ1 hT).le
    exact influence_centered_mgf (hg.comp (measurable_const.prodMk measurable_id))
      (hmi _ hs.1.1) hB hG hD hT hc (optimizer_influence_bound hB hδ hδ1 ht) hGD
      (s.2.1 - q.x0) (observableInfluence q s) (u - q.x0) hx hd (hm _ hs.1.1)
  · have hv : residualInfluence q u s = 0 := by
      simp [residualInfluence, observableInfluence,
        influenceScale_after q.B q.δ (show q.T ≤ s.1 by omega),
        stepSize_after q.B q.δ (show q.T ≤ s.1 by omega)]
    simp [hv]

lemma trajectory_clipped_update {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (t : ℕ) :
    (trajectory q g projection ξ (t + 1)).2.1 = projection
      ((trajectory q g projection ξ t).2.1 - stepSize q.B q.δ q.T t •
        clippedSample q g (trajectory q g projection ξ t) (ξ t)) := by
  rw [trajectory]
  dsimp [transition, nextPoint, clippedSample, observableInfluence]
  rw [trajectory_time]
  congr 1
  module

noncomputable def martingaleIncrement {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (P : ProbabilityMeasure Ω) (u : Vector q.d) (D : ℝ)
    (s : ℕ × (Vector q.d × Vector q.d)) (ω : Ω) : ℝ :=
  let τ := Real.sqrt q.T / (400 * q.B * D);
  -τ * ⟪clippedSample q g s ω - ∫ z, clippedSample q g s z ∂(P : Measure Ω), residualInfluence q u s⟫ -
    τ ^ 2 * ‖residualInfluence q u s‖ ^ 2 * (26 * q.B ^ 2 * D)

lemma martingaleIncrement_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (P : ProbabilityMeasure Ω) (u : Vector q.d) (D : ℝ) :
    Measurable (Function.uncurry (martingaleIncrement q g P u D)) := by
  have hX := clippedSample_measurable q hg
  have hm : Measurable (fun z : (ℕ × (Vector q.d × Vector q.d)) × Ω =>
      ∫ ω, clippedSample q g z.1 ω ∂(P : Measure Ω)) :=
    (clippedSample_mean_measurable q hg P).comp measurable_fst
  have hv : Measurable (fun z : (ℕ × (Vector q.d × Vector q.d)) × Ω => residualInfluence q u z.1) :=
    (residualInfluence_measurable q u).comp measurable_fst
  exact (((hX.sub hm).inner hv).const_mul _).sub (((hv.norm.pow_const 2).const_mul _).mul_const _)

lemma influence_bias_local {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hgi : Integrable g P) (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {B G D c : ℝ} {T : ℕ} (hB : 0 < B) (hG : 0 < G) (hD : 0 ≤ D) (hT : 0 < T)
    (hc : 0 ≤ c) (hcT : c ≤ 4 / (T : ℝ)) (hGD : G ^ 2 ≤ B ^ 2 * D)
    (x U d : E) (hx : ‖x‖ ≤ 5 * Real.sqrt D) (hd : ‖d‖ ≤ Real.sqrt D)
    (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ B ^ 2 * ‖x‖ ^ 2 + G ^ 2) :
    ⟪(∫ ω, g ω ∂P) - ∫ ω, clip (threshold B G T x U) (g ω) ∂P, U - c • d⟫ ≤
      2 * B * Real.sqrt T * ‖U - c • d‖ ^ 2 + 26 * B * D / ((T : ℝ) * Real.sqrt T) := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hb := threshold_oracle_bias hg hgi hmi hB hG hT x U hm
  have hscale := local_mean_scale hB.le hD hGD hx
  have hb' := hb.trans (add_le_add
    (div_le_div_of_nonneg_right hscale (Real.sqrt_nonneg _)) le_rfl)
  have hh := influence_bias_bound (show 0 ≤ 6 * B * Real.sqrt D / Real.sqrt T by positivity)
    (show 0 < B * Real.sqrt T by positivity) (q := c • d)
    (show U = (U - c • d) + c • d by module) hb'
  have hn : ‖c • d‖ ^ 2 ≤ (4 / (T : ℝ)) ^ 2 * D := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
    have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [Real.sq_sqrt hD] at hd2
    exact mul_le_mul (pow_le_pow_left₀ hc hcT 2) hd2 (sq_nonneg _) (sq_nonneg _)
  have hterm := mul_le_mul_of_nonneg_left hn (show 0 ≤ B * Real.sqrt T / 2 by positivity)
  have he : (6 * B * Real.sqrt D / Real.sqrt T) ^ 2 / (2 * (B * Real.sqrt T)) +
      (B * Real.sqrt T / 2) * ((4 / (T : ℝ)) ^ 2 * D) =
      26 * B * D / ((T : ℝ) * Real.sqrt T) := by
    field_simp
    ring_nf
    have hs4 : (Real.sqrt (T : ℝ)) ^ 4 = (T : ℝ) ^ 2 := by
      calc
        _ = ((Real.sqrt (T : ℝ)) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt ht.le]
    simp only [Real.sq_sqrt hD, Real.sq_sqrt ht.le, hs4]; ring
  have hsum := add_le_add (le_refl ((6 * B * Real.sqrt D / Real.sqrt T) ^ 2 / (2 * (B * Real.sqrt T)))) hterm
  rw [he] at hsum
  nlinarith

lemma martingale_compensation_bound {B D T : ℝ} (hB : 0 < B) (hD : 0 < D) :
    Real.sqrt T / (400 * B * D) * (26 * B ^ 2 * D) ≤ B * Real.sqrt T := by
  have he : Real.sqrt T / (400 * B * D) * (26 * B ^ 2 * D) =
      (26 / 400 : ℝ) * (B * Real.sqrt T) := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right (show (26 / 400 : ℝ) ≤ 1 by norm_num)
    (show 0 ≤ B * Real.sqrt T by positivity)
  simpa only [one_mul] using hh

end OracleTemplate.TerminalClipping
