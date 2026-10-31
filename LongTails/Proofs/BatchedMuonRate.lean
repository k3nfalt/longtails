import LongTails.Proofs.BatchedDirectionExecution
import LongTails.Proofs.MuonProcess
import LongTails.Proofs.MatrixSmooth
import LongTails.Proofs.MixedNoiseSelectors

namespace LongTails.Proofs.BatchedMuonRate

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Proofs.BatchedDirectionExecution
open LongTails.Proofs.MuonProcess

lemma adapted_sampledIterate {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {direction : Space m n → Space m n} (hdir : Measurable direction) (η : ℝ) (B : ℕ)
    (x0 : Space m n) {g : Space m n → Ω → Space m n} (hg : Measurable (Function.uncurry g))
    (t : ℕ) :
    Measurable[past (B * t)] (fun ξ => sampledIterate direction η B x0 g ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hle : B * t ≤ B * (t + 1) := Nat.mul_le_mul_left B (Nat.le_succ t)
      have ih' := ih.mono (past_mono hle) le_rfl
      have hsum : Measurable[past (B * (t + 1))] (fun ξ : ℕ → Ω =>
          ∑ j ∈ Finset.range B, g (sampledIterate direction η B x0 g ξ t) (ξ (B * t + j))) := by
        apply Finset.measurable_sum
        intro j hj
        have hj' : B * t + j < B * (t + 1) := by
          have := Finset.mem_range.mp hj
          rw [Nat.mul_succ]
          omega
        exact hg.comp (ih'.prodMk (measurable_eval_past hj'))
      exact ih'.sub ((hdir.comp (hsum.const_smul (1 / (B : ℝ)))).const_smul η)

lemma measurable_sampledIterate {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {direction : Space m n → Space m n} (hdir : Measurable direction) (η : ℝ) (B : ℕ)
    (x0 : Space m n) {g : Space m n → Ω → Space m n} (hg : Measurable (Function.uncurry g))
    (t : ℕ) : Measurable (fun ξ : ℕ → Ω => sampledIterate direction η B x0 g ξ t) :=
  (adapted_sampledIterate hdir η B x0 hg t).mono (past_le _) le_rfl

lemma integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω)
    (hF2 : Integrable (fun ω => (F ω) ^ 2) P) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ^ 2 ≤ ∫ ω, (F ω) ^ 2 ∂P := by
  have hi : Integrable F P := by
    apply ((integrable_const (1 : ℝ)).add hF2).mono' hF.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]
      change F ω ≤ 1 + (F ω) ^ 2
      nlinarith [sq_nonneg (F ω - 1)]
  refine ⟨hi, ?_⟩
  have hj := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 2)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hF0) hi (by simpa only [Function.comp_def, Real.rpow_two] using hF2)
  simpa only [Real.rpow_two] using hj

lemma batch_error_integral {m n : ℕ} {f : Space m n → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {B : ℕ} (hB : 0 < B) (t : ℕ) {X : (ℕ → model.Ω) → Space m n}
    (hX : Measurable[past (B * t)] X) :
    Integrable (fun ξ => nuclearNorm ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
        model.sample (X ξ) (ξ (B * t + j)) - gradient f (X ξ))) P ∧
      (∫ ξ, nuclearNorm ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
        model.sample (X ξ) (ξ (B * t + j)) - gradient f (X ξ)) ∂P) ≤ s / Real.sqrt B := by
  have hh := model_frozen_batch_bounds model h hB hX
  simp only [ValidatedMuonExecution.sampledEval_batchMeanPlan] at hh
  obtain ⟨hmem, hcond⟩ := hh
  let V := fun ξ : ℕ → model.Ω => nuclearNorm ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
    model.sample (X ξ) (ξ (B * t + j)) - gradient f (X ξ))
  have hVm : Measurable V := by
    have hXm : Measurable X := hX.mono (past_le _) le_rfl
    exact (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      (((Finset.measurable_sum (Finset.range B) (fun j _ => model.jointly_measurable.comp
        (hXm.prodMk (measurable_pi_apply (B * t + j))))).const_smul (1 / (B : ℝ))).sub
        ((measurable_gradient f).comp hXm))
  have hV2 : Integrable (fun ξ => V ξ ^ 2) P := hmem.integrable_sq
  have hsq : (∫ ξ, V ξ ^ 2 ∂P) ≤ s ^ 2 / B := by
    rw [← integral_condExp (past_le (B * t))]
    calc (∫ ξ, P[(fun ξ => V ξ ^ 2) | past (B * t)] ξ ∂P) ≤ ∫ _ξ, s ^ 2 / (B : ℝ) ∂P :=
          integral_mono_ae integrable_condExp (integrable_const _) hcond
      _ = s ^ 2 / B := by simp
  obtain ⟨hVi, hJ⟩ := integral_square_le P hVm (fun _ => nuclearNorm_nonneg _) hV2
  refine ⟨hVi, ?_⟩
  have hpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hI0 : 0 ≤ ∫ ξ, V ξ ∂P := integral_nonneg fun _ => nuclearNorm_nonneg _
  have hfinal : (∫ ξ, V ξ ∂P) ^ 2 ≤ (s / Real.sqrt B) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hpos.le]
    exact hJ.trans hsq
  exact (pow_le_pow_iff_left₀ hI0 (div_nonneg hs (Real.sqrt_nonneg _)) two_ne_zero).mp hfinal

lemma step_bound {m n : ℕ} {f : Space m n → ℝ} {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (x M : Space m n) :
    η * nuclearNorm (gradient f x) ≤
      f x - f (x - η • polar M) + 2 * η * nuclearNorm (M - gradient f x) + L / 2 * η ^ 2 := by
  have hd := MatrixSmooth.polar_descent hgrad hlip hL hη x M
  have ha := (MatrixSmooth.polar_alignment_deficit (gradient f x) M).2.2
  nlinarith

lemma gradient_drift {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ} {L η : ℝ} (hη : 0 ≤ η)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hL : 0 ≤ L) (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (t : ℕ) :
    nuclearNorm (gradient f (sampledIterate polar η B x0 g ξ t)) ≤
      nuclearNorm (gradient f x0) + L * (η * t) := by
  have hdist : ∀ t, spectralNorm (sampledIterate polar η B x0 g ξ t - x0) ≤ η * t := by
    intro t
    induction t with
    | zero => simp [sampledIterate, spectralNorm]
    | succ t ih =>
        simp only [sampledIterate]
        set M := (1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
          g (sampledIterate polar η B x0 g ξ t) (ξ (B * t + j))
        have hp : spectralNorm (η • polar M) ≤ η := by
          rw [MatrixSmooth.spectralNorm_smul, abs_of_nonneg hη]
          have := polar_mem M
          simp only [spectralBall, Set.mem_ofPred_eq] at this
          nlinarith
        have htri : spectralNorm (sampledIterate polar η B x0 g ξ t - η • polar M - x0) ≤
            spectralNorm (sampledIterate polar η B x0 g ξ t - x0) + spectralNorm (η • polar M) := by
          have he : sampledIterate polar η B x0 g ξ t - η • polar M - x0 =
              (sampledIterate polar η B x0 g ξ t - x0) + -(η • polar M) := by abel
          rw [he]
          unfold spectralNorm
          rw [map_add]
          calc _ ≤ ‖(operatorEquiv m n) (sampledIterate polar η B x0 g ξ t - x0)‖ +
                ‖(operatorEquiv m n) (-(η • polar M))‖ := norm_add_le _ _
            _ = _ := by rw [map_neg, norm_neg]
        push_cast
        nlinarith
  have hn := hlip (sampledIterate polar η B x0 g ξ t) x0
  have htri := nuclearNorm_add_le
    (gradient f (sampledIterate polar η B x0 g ξ t) - gradient f x0) (gradient f x0)
  rw [sub_add_cancel] at htri
  nlinarith [hdist t]

lemma average_gradient_bound {m n : ℕ} {f : Space m n → ℝ} {L Δ s η fmin : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hη : 0 < η)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (x0 : Space m n) (hgap : f x0 - fmin ≤ Δ)
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {B : ℕ} (hB : 0 < B) (T : ℕ) :
    (∀ t, Integrable (fun ξ =>
      nuclearNorm (gradient f (sampledIterate polar η B x0 model.sample ξ t))) P) ∧
    (∑ t ∈ Finset.range (T + 1), ∫ ξ,
      nuclearNorm (gradient f (sampledIterate polar η B x0 model.sample ξ t)) ∂P) ≤
      Δ / η + (T + 1) * (2 * (s / Real.sqrt B) + L / 2 * η) := by
  let X := fun t (ξ : ℕ → model.Ω) => sampledIterate polar η B x0 model.sample ξ t
  have hXa (t : ℕ) : Measurable[past (B * t)] (X t) :=
    adapted_sampledIterate (measurable_polar m n) η B x0 model.jointly_measurable t
  have hXm (t : ℕ) : Measurable (X t) := (hXa t).mono (past_le _) le_rfl
  let G := fun t ξ => nuclearNorm (gradient f (X t ξ))
  have hGm (t : ℕ) : Measurable (G t) :=
    (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      ((measurable_gradient f).comp (hXm t))
  have hGi (t : ℕ) : Integrable (G t) P := by
    apply Integrable.of_bound (hGm t).aestronglyMeasurable
      (nuclearNorm (gradient f x0) + L * (η * t))
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (nuclearNorm_nonneg _)]
      exact gradient_drift hη.le hlip hL B x0 model.sample ξ t
  let V := fun t (ξ : ℕ → model.Ω) => nuclearNorm ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
    model.sample (X t ξ) (ξ (B * t + j)) - gradient f (X t ξ))
  have hV (t : ℕ) := batch_error_integral hs model h hB t (hXa t)
  refine ⟨hGi, ?_⟩
  have hpoint (ξ : ℕ → model.Ω) :
      η * ∑ t ∈ Finset.range (T + 1), G t ξ ≤
        Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ + (T + 1) * (L / 2 * η ^ 2) := by
    have hstep (t : ℕ) : η * G t ξ ≤ f (X t ξ) - f (X (t + 1) ξ) + 2 * η * V t ξ +
        L / 2 * η ^ 2 := by
      have hs := step_bound hL hη.le hgrad hlip (X t ξ) ((1 / (B : ℝ)) •
        ∑ j ∈ Finset.range B, model.sample (X t ξ) (ξ (B * t + j)))
      simpa only [X, sampledIterate] using hs
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range (T + 1)) => hstep t)
    rw [← Finset.mul_sum] at hsum
    have htel : (∑ t ∈ Finset.range (T + 1), (f (X t ξ) - f (X (t + 1) ξ) + 2 * η * V t ξ +
        L / 2 * η ^ 2)) = f (X 0 ξ) - f (X (T + 1) ξ) +
          2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ + (T + 1) * (L / 2 * η ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub' (fun t => f (X t ξ)),
        ← Finset.mul_sum]
      simp
    rw [htel] at hsum
    have h0 : X 0 ξ = x0 := rfl
    rw [h0] at hsum
    linarith [hmin (X (T + 1) ξ)]
  have hVi : Integrable (fun ξ => ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    integrable_finsetSum _ (fun t _ => (hV t).1)
  have hGs : Integrable (fun ξ => ∑ t ∈ Finset.range (T + 1), G t ξ) P :=
    integrable_finsetSum _ (fun t _ => hGi t)
  have hL1 : Integrable (fun ξ => η * ∑ t ∈ Finset.range (T + 1), G t ξ) P := hGs.const_mul η
  have hR1 : Integrable (fun ξ => Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    (integrable_const Δ).add (hVi.const_mul (2 * η))
  have hR2 : Integrable (fun ξ => 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    hVi.const_mul (2 * η)
  have hR : Integrable (fun ξ => Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ +
      (T + 1) * (L / 2 * η ^ 2)) P := hR1.add (integrable_const _)
  have hint : (∫ ξ, η * ∑ t ∈ Finset.range (T + 1), G t ξ ∂P) ≤
      ∫ ξ, (Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ + (T + 1) * (L / 2 * η ^ 2)) ∂P :=
    integral_mono hL1 hR hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun t _ => hGi t), integral_add hR1
    (integrable_const _), integral_add (integrable_const Δ) hR2, integral_const_mul,
    integral_finsetSum _ (fun t _ => (hV t).1)] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hVsum : (∑ t ∈ Finset.range (T + 1), ∫ ξ, V t ξ ∂P) ≤ (T + 1) * (s / Real.sqrt B) := by
    calc _ ≤ ∑ _t ∈ Finset.range (T + 1), s / Real.sqrt B :=
          Finset.sum_le_sum fun t _ => (hV t).2
      _ = _ := by simp
  have hfin : η * ∑ t ∈ Finset.range (T + 1), ∫ ξ, G t ξ ∂P ≤
      η * (Δ / η + (T + 1) * (2 * (s / Real.sqrt B) + L / 2 * η)) := by
    rw [mul_add, mul_div_cancel₀ _ hη.ne']
    have h2 := mul_le_mul_of_nonneg_left hVsum (by positivity : (0 : ℝ) ≤ 2 * η)
    nlinarith
  exact le_of_mul_le_mul_left hfin hη

lemma uniform_output {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g))
    {direction : Space m n → Space m n} (hdir : Measurable direction) {η : ℝ} {B T : ℕ}
    {x0 : Space m n} {A : Algorithm (Space m n) (Space m n) (Space m n)}
    (draw : A.Seed → Fin (T + 1)) (hdraw : Measurable draw)
    (hlaw : Measure.map draw (A.law : Measure _) =
      (PMF.uniformOfFintype (Fin (T + 1))).toMeasure)
    (hA : ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 =
          LongTails.Setups.BatchedSpectralSmooth.batchedIterate direction η B x0 reply t) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        LongTails.Setups.BatchedSpectralSmooth.batchedIterate direction η B x0 reply (draw seed))
    (F : Space m n → ℝ) (hF : Measurable F)
    (hi : ∀ t, Integrable (fun ξ => F (sampledIterate direction η B x0 g ξ t)) (P : Measure _)) :
    let O : Oracle (Space m n) (Space m n) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let out := fun z : A.Seed × (ℕ → Ω) => execute O A (fun _ => B * (T + 1)) z.1 z.2
    Measurable out ∧ Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) ∧
      (∫ z, F (out z) ∂((A.law : Measure _).prod (P : Measure _))) =
        (∑ t ∈ Finset.range (T + 1), ∫ ξ, F (sampledIterate direction η B x0 g ξ t) ∂(P : Measure _)) /
          (T + 1) := by
  intro O out
  have hout : out = fun z => sampledIterate direction η B x0 g z.2 (draw z.1) := by
    funext z
    exact execute_eq_sampledIterate P g draw hA z.1 z.2
  have hX (t : ℕ) : Measurable (fun ξ : ℕ → Ω => sampledIterate direction η B x0 g ξ t) :=
    measurable_sampledIterate hdir η B x0 hg t
  have hjoint : Measurable (fun z : Fin (T + 1) × (ℕ → Ω) =>
      sampledIterate direction η B x0 g z.2 z.1) :=
    measurable_from_prod_countable_right fun k => hX k
  have hm : Measurable out := by
    rw [hout]
    exact hjoint.comp ((hdraw.comp measurable_fst).prodMk measurable_snd)
  let G := fun k : Fin (T + 1) => ∫ ξ, F (sampledIterate direction η B x0 g ξ k) ∂(P : Measure _)
  have hFm : Measurable (fun z : A.Seed × (ℕ → Ω) => F (out z)) := hF.comp hm
  have hbound : ∀ k : Fin (T + 1), ∫ ξ, ‖F (sampledIterate direction η B x0 g ξ k)‖ ∂(P : Measure _) ≤
      ∑ t : Fin (T + 1), ∫ ξ, ‖F (sampledIterate direction η B x0 g ξ t)‖ ∂(P : Measure _) := by
    intro k
    exact Finset.single_le_sum (f := fun t : Fin (T + 1) =>
      ∫ ξ, ‖F (sampledIterate direction η B x0 g ξ t)‖ ∂(P : Measure _))
      (fun t _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ k)
  have hint : Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall fun seed => by
        simpa only [hout] using hi (draw seed)
    · apply Integrable.of_bound (C := ∑ t : Fin (T + 1),
        ∫ ξ, ‖F (sampledIterate direction η B x0 g ξ t)‖ ∂(P : Measure _))
      · exact (hFm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun seed => by
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          simpa only [hout] using hbound (draw seed)
  refine ⟨hm, hint, ?_⟩
  rw [integral_prod _ hint]
  have hinner : (fun seed => ∫ ξ, F (out (seed, ξ)) ∂(P : Measure _)) = fun seed => G (draw seed) := by
    funext seed
    simp only [hout, G]
  rw [hinner, ← integral_map hdraw.aemeasurable (measurable_of_countable G).aestronglyMeasurable, hlaw,
    OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, F (sampledIterate direction η B x0 g ξ t)
    ∂(P : Measure _)) (T + 1)]
  push_cast
  ring

end LongTails.Proofs.BatchedMuonRate
