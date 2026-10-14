import LongTails.Proofs.HiddenConvexBudget
import LongTails.Proofs.SgdExecution

open Set Metric InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

section execution

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_safeguarded (g : E → Ω → E) (L σ R : ℝ) (x0 : E) (ξ : ℕ → Ω)
    (K call k : ℕ) (x z : E) :
    StochasticGradient.advance (fun j state => (safeguardedSimilarTriangles L σ R x0).update state
      (g (((safeguardedSimilarTriangles L σ R x0).query state).2) (ξ j))) K call (k, x, z) =
      (k + K, safeguardedRun g L σ R x0 K k x z (fun i => ξ (call + i))) := by
  dsimp only [safeguardedSimilarTriangles]
  induction K generalizing call k x z with
  | zero => simp [StochasticGradient.advance, safeguardedRun]
  | succ K ih =>
    rw [StochasticGradient.advance]
    change StochasticGradient.advance _ K (call + 1) (k + 1,
      mixPoint k x (dualStep L σ R x0 k z (g (mixPoint k x z) (ξ call))),
      dualStep L σ R x0 k z (g (mixPoint k x z) (ξ call))) = _
    rw [ih (call + 1) (k + 1)]
    simp only [safeguardedRun, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    have e1 : k + 1 + K = k + (K + 1) := by omega
    have e2 : (fun i : Fin K => ξ (call + 1 + (i : ℕ))) = (fun i : Fin K => ξ (call + ((i : ℕ) + 1))) := by
      funext i; congr 1; omega
    rw [e1, e2]

lemma execute_safeguarded [MeasurableSpace Ω] (p : ProbabilityMeasure Ω)
    (g : E → Ω → E) (L σ R : ℝ) (x0 : E) (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)), inferInstance⟩
              answer := fun _ (_, x) seed => g x seed }
      (safeguardedSimilarTriangles L σ R x0) (fun _ => K) () ξ =
      (safeguardedRun g L σ R x0 K 0 x0 x0 (fun i => ξ i)).1 := by
  erw [StochasticGradient.execute_advance]
  change (safeguardedSimilarTriangles L σ R x0).output
    (StochasticGradient.advance _ K 0 (0, x0, x0)) = _
  erw [advance_safeguarded]
  simp [safeguardedSimilarTriangles]

end execution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]
  {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E} {x0 : E} {R μ LJ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
omit [CompleteSpace E] [MeasurableSpace E] in
lemma energy_ge_gap (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ)
    (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (K : ℕ) {x z : E}
    (hx : x ∈ closedBall x0 (2 * R)) (hz : z ∈ closedBall x0 (2 * R)) :
    (K : ℝ) * ((K : ℝ) + 1) / 4 * (F x - F u) - 27 / 32 * stepScale L σ R K * R ^ 2 ≤
      energy F c J x0 L σ R u K (x, z) := by
  have hyB := mixPoint_mem K hx hz
  have hD := stepScale_pos hL hσ hR K
  unfold energy
  simp only
  rw [qField_eq hyB]
  have hq := hm.corr_small hR hμ hLJ hreg hu hyB
  have h3 : ‖z - u‖ ≤ 3 * R := by rw [norm_sub_rev]; exact norm_sub_le_three hz hu
  have hin : ⟪z - u, corr c J (mixPoint K x z) u⟫ ≤ 27 / 32 * R ^ 2 := by
    calc ⟪z - u, corr c J (mixPoint K x z) u⟫ ≤ ‖z - u‖ * ‖corr c J (mixPoint K x z) u‖ :=
          real_inner_le_norm _ _
      _ ≤ (3 * R) * (9 * R / 32) := mul_le_mul h3 hq (norm_nonneg _) (by positivity)
      _ = 27 / 32 * R ^ 2 := by ring
  have h2 : 0 ≤ stepScale L σ R K / 2 * ‖z - u‖ ^ 2 := by positivity
  have h4 := mul_le_mul_of_nonneg_left hin hD.le
  linarith

omit [BorelSpace E] [SecondCountableTopology E] in
omit [CompleteSpace E] [MeasurableSpace E] in
lemma energy_initial (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ)
    (hLJ : 0 ≤ LJ) (hreg : 32 * LJ * R ≤ μ) {u : E} (hu : u ∈ closedBall x0 R)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) :
    energy F c J x0 L σ R u 0 (x0, x0) ≤ 25 / 32 * stepScale L σ R 0 * R ^ 2 := by
  have hx0 : x0 ∈ closedBall x0 (2 * R) := mem_closedBall_self (by positivity)
  have hmix : mixPoint 0 x0 x0 = x0 := by rw [mixPoint_eq]; simp
  have hD := stepScale_pos hL hσ hR 0
  unfold energy
  simp only
  rw [hmix, qField_eq hx0]
  have hq := hm.corr_small hR hμ hLJ hreg hu hx0
  have h1 : ‖x0 - u‖ ≤ R := by rw [norm_sub_rev, ← dist_eq_norm]; exact hu
  have hsq : ‖x0 - u‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hin : -⟪x0 - u, corr c J x0 u⟫ ≤ 9 / 32 * R ^ 2 := by
    have e := neg_le_abs ⟪x0 - u, corr c J x0 u⟫
    have e2 := abs_real_inner_le_norm (x0 - u) (corr c J x0 u)
    have e3 : ‖x0 - u‖ * ‖corr c J x0 u‖ ≤ R * (9 * R / 32) :=
      mul_le_mul h1 hq (norm_nonneg _) hR.le
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left hin hD.le
  have h6 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ stepScale L σ R 0 / 2 by positivity)
  push_cast
  nlinarith

lemma expected_gap {u : E} {L σ : ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hreg : 32 * LJ * R ≤ μ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p F g σ)
    (hu : u ∈ closedBall x0 R) (hmin : IsMinOn F univ u) (K : ℕ) (hK : 0 < K) :
    Integrable (fun ξ => F (safeguardedRun g L σ R x0 K 0 x0 x0 ξ).1 - F u)
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, F (safeguardedRun g L σ R x0 K 0 x0 x0 ξ).1 - F u ∂Measure.pi (fun _ : Fin K => p)) ≤
      4 * (stepScale L σ R K * R ^ 2 * (20 + 6 * Real.log ((K : ℝ) + 1)) +
        σ * R * (K : ℝ) * Real.sqrt K / 2) / ((K : ℝ) * ((K : ℝ) + 1)) := by
  have hx0 : x0 ∈ closedBall x0 (2 * R) := mem_closedBall_self (by positivity)
  have hb := energy_bound hm hR hμ hLJ hreg hL hσ hF hlip ho hu hmin K 0 x0 x0 hx0 hx0
  simp only [zero_add] at hb
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  set A := (K : ℝ) * ((K : ℝ) + 1) / 4 with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set D := stepScale L σ R K with hD
  set V := fun ξ => energy F c J x0 L σ R u K (safeguardedRun g L σ R x0 K 0 x0 x0 ξ) with hV
  set G := fun ξ => F (safeguardedRun g L σ R x0 K 0 x0 x0 ξ).1 - F u with hG
  have hFm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have hGm : Measurable G :=
    (hFm.comp (((measurable_safeguardedRun ho.measurable L σ R x0 K 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin K → Ω => ((x0, x0), ξ)))).fst)).sub_const _
  have hbound : ∀ ξ, G ξ ≤ A⁻¹ * (V ξ + 27 / 32 * D * R ^ 2) := by
    intro ξ
    have hmem := safeguardedRun_mem (g := g) (L := L) (σ := σ) (x0 := x0) hR.le K 0 hx0 hx0 ξ
    have h := energy_ge_gap hm hR hμ hLJ hreg hu hL hσ K hmem.1 hmem.2
    rw [inv_mul_eq_div, le_div_iff₀ hA0]
    have e : G ξ * A = A * (F (safeguardedRun g L σ R x0 K 0 x0 x0 ξ).1 - F u) := by
      simp only [hG]; ring
    rw [e, ← hA, ← hD] at *
    simp only [hV]
    linarith
  have hVi := hb.1
  have hGi : Integrable G (Measure.pi fun _ : Fin K => p) :=
    ((hVi.add (integrable_const _)).const_mul A⁻¹).mono_nonneg hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => sub_nonneg.mpr (hmin (mem_univ _))))
      (Filter.Eventually.of_forall hbound)
  refine ⟨hGi, ?_⟩
  have hsum := stepCost_sum_le hL hσ hR (div_nonneg hLJ hμ.le) K
  have hinit := energy_initial hm hR hμ hLJ hreg hu hL hσ
  have hD0 : stepScale L σ R 0 ≤ D := stepScale_mono hσ hR (Nat.zero_le K)
  have hD0pos := stepScale_pos hL hσ hR 0
  have hMR : LJ / μ * R ≤ 1 / 32 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hμ (by norm_num)]
    linarith
  have hlog : 0 ≤ Real.log ((K : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hDpos : 0 < D := stepScale_pos hL hσ hR K
  have hterm1 : D * (192 * (LJ / μ) * R ^ 3 * Real.log ((K : ℝ) + 1)) ≤
      D * R ^ 2 * (6 * Real.log ((K : ℝ) + 1)) := by
    have : 192 * (LJ / μ) * R ^ 3 * Real.log ((K : ℝ) + 1) ≤
        R ^ 2 * (6 * Real.log ((K : ℝ) + 1)) := by
      have h := mul_le_mul_of_nonneg_left hMR (show 0 ≤ 192 * R ^ 2 * Real.log ((K : ℝ) + 1) by
        positivity)
      nlinarith
    nlinarith
  have hterm2 : D * (13312 * (LJ / μ) ^ 2 * R ^ 4) ≤ D * R ^ 2 * 13 := by
    have hM0 : 0 ≤ LJ / μ * R := by positivity
    have : (LJ / μ * R) ^ 2 ≤ (1 / 32) ^ 2 := pow_le_pow_left₀ hM0 hMR 2
    have : 13312 * (LJ / μ) ^ 2 * R ^ 4 ≤ R ^ 2 * 13 := by
      have e : 13312 * (LJ / μ) ^ 2 * R ^ 4 = 13312 * (LJ / μ * R) ^ 2 * R ^ 2 := by ring
      rw [e]
      nlinarith [sq_nonneg R]
    nlinarith
  have htotal : energy F c J x0 L σ R u 0 (x0, x0) +
      ∑ j ∈ Finset.range K, stepCost L σ R (LJ / μ) j + 27 / 32 * D * R ^ 2 ≤
      D * R ^ 2 * (20 + 6 * Real.log ((K : ℝ) + 1)) + σ * R * (K : ℝ) * Real.sqrt K / 2 := by
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have h1 := mul_le_mul_of_nonneg_right hD0 (show 0 ≤ 146 / 32 * R ^ 2 by positivity)
    nlinarith
  calc (∫ ξ, G ξ ∂Measure.pi (fun _ : Fin K => p))
      ≤ ∫ ξ, A⁻¹ * (V ξ + 27 / 32 * D * R ^ 2) ∂Measure.pi (fun _ : Fin K => p) :=
        integral_mono hGi ((hVi.add (integrable_const _)).const_mul _) hbound
    _ = A⁻¹ * ((∫ ξ, V ξ ∂Measure.pi (fun _ : Fin K => p)) + 27 / 32 * D * R ^ 2) := by
        rw [integral_const_mul, integral_add hVi (integrable_const _)]
        simp
    _ ≤ A⁻¹ * (energy F c J x0 L σ R u 0 (x0, x0) +
          ∑ j ∈ Finset.range K, stepCost L σ R (LJ / μ) j + 27 / 32 * D * R ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hA0.le)
        linarith [hb.2]
    _ ≤ A⁻¹ * (D * R ^ 2 * (20 + 6 * Real.log ((K : ℝ) + 1)) +
          σ * R * (K : ℝ) * Real.sqrt K / 2) :=
        mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hA0.le)
    _ = _ := by rw [hA]; field_simp

end OracleTemplate.LocalHiddenConvex
