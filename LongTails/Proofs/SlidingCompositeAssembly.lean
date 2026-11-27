import LongTails.Setups.SlidingStochasticComposite
import LongTails.Proofs.SlidingCompositeInner
import LongTails.Proofs.SlidingCompositeOuter
import LongTails.Proofs.SlidingCompositeExecution
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.SgdConvex
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SlidingCompositeAssembly

open OracleTemplate OracleTemplate.SlidingStochasticComposite
open LongTails.Proofs.SlidingCompositeInner LongTails.Proofs.SlidingCompositeOuter
open LongTails.Proofs.SlidingCompositeExecution

lemma uniform_joint {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (F : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (F i) Q) :
    Integrable (fun w : ι × Ω => F w.1 w.2) ((PMF.uniformOfFintype ι).toMeasure.prod Q) ∧
      (∫ w : ι × Ω, F w.1 w.2 ∂((PMF.uniformOfFintype ι).toMeasure.prod Q)) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ ω, F i ω ∂Q := by
  have hme : Measurable (fun w : ι × Ω => F w.1 w.2) :=
    measurable_from_prod_countable_right hm
  have hint : Integrable (fun w : ι × Ω => F w.1 w.2)
      ((PMF.uniformOfFintype ι).toMeasure.prod Q) :=
    (integrable_prod_iff hme.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall hi, Integrable.of_finite⟩
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Finset.mul_sum]

variable {S B : Type*}

lemma iter_succ' (step : S → B → S) (k : ℕ) (s : S) (ξ : Fin (k + 1) → B) :
    iter step (k + 1) s ξ = step (iter step k s (fun i => ξ i.castSucc)) (ξ (Fin.last k)) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [iter, ih]
      rfl

lemma tail_preserving {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) :
    MeasurePreserving (fun b : Fin (N + 1) → Ω => fun j : Fin N => b j.succ)
      (Measure.pi fun _ : Fin (N + 1) => μ) (Measure.pi fun _ : Fin N => μ) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
  have h2 := (measurePreserving_snd (μ := μ) (ν := Measure.pi fun _ : Fin N => μ)).comp h
  convert h2 using 1
  funext b
  ext j
  simp [MeasurableEquiv.piFinSuccAbove_apply]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

lemma centers_eq_iter (ℓ D : ℝ) (N : ℕ) (gf : E → E) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω)
    (k : ℕ) :
    centers ℓ D N gf g x0 (blocks N ξ) k =
      iter (fun c (b : Fin (N + 1) → Ω) => innerRun ℓ D N g c (gf c) (fun j => b j.succ)) k x0
        (fun i : Fin k => fun j : Fin (N + 1) => ξ ((i : ℕ) * (N + 1) + j)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iter_succ', centers]
      simp only [Fin.val_castSucc]
      rw [← ih]
      congr 1
      funext j
      simp only [blocks, Fin.val_last, Fin.val_succ]
      congr 1
      omega


lemma run_param {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω P : Type*}
    (gg : E → Ω × P → E) (g' : P → E → Ω → E) (D : ℝ) (N k : ℕ) (x z : E) (c : P)
    (η : Fin N → Ω) (h : ∀ y ω, gg y (ω, c) = g' c y ω) :
    StochasticGradient.acceleratedRun gg D N k x z (fun j => (η j, c)) =
      StochasticGradient.acceleratedRun (g' c) D N k x z η := by
  induction N generalizing k x z with
  | zero => rfl
  | succ N ih =>
      simp only [StochasticGradient.acceleratedRun, h]
      exact ih _ _ _ _

section Main

open LongTails.Setups.SlidingStochasticComposite LongTails.Setups.StochasticSmoothAndConvex
open StochasticGradient

lemma gapAt_measurable {E : Type} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {f h : E → ℝ} {ℓ lower : ℝ}
    (hℓ : 0 ≤ ℓ) (hfc : Continuous f) (hhc : Continuous h)
    (hlow : ∀ x, lower ≤ f x + h x) :
    Measurable (gapAt f h ℓ) := by
  have hu : UpperSemicontinuous (fun c : E => ⨅ y, (f y + h y + ℓ * ‖y - c‖ ^ 2)) := by
    apply upperSemicontinuous_ciInf
    · intro c
      refine ⟨lower, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := hlow y
      have : 0 ≤ ℓ * ‖y - c‖ ^ 2 := by positivity
      linarith
    · intro y
      exact (continuous_const.add (continuous_const.mul
        ((continuous_const.sub continuous_id).norm.pow 2))).upperSemicontinuous
  exact ((hfc.add hhc).measurable).sub hu.measurable

noncomputable def compOracle (q : LongTails.Setups.SlidingStochasticComposite.Params)
    (I : LongTails.Setups.SlidingStochasticComposite.Instance q) (g : q.E → q.Ω → q.E)
    (P : ProbabilityMeasure (ℕ → q.Ω)) : Oracle q.E q.E 2 where
  Seed := fun _ => q.Ω
  law := P
  answer := fun _ q' ω => if q'.1 = 0 then gradient I.f q'.2 else g q'.2 ω

theorem successful_execution (q : LongTails.Setups.SlidingStochasticComposite.Params)
    (hv : LongTails.Setups.SlidingStochasticComposite.spec.valid q)
    (I : LongTails.Setups.SlidingStochasticComposite.Instance q)
    (O : Oracle q.E q.E 2)
    (hadm : LongTails.Setups.SlidingStochasticComposite.spec.admissible q I O) :
    let K := ⌈32 * q.ℓ * q.Δ / q.ε ^ 2⌉₊
    let N := ⌈4 * Real.sqrt (1 + q.L / q.ℓ) + 256 * q.σ ^ 2 / q.ε ^ 2⌉₊
    let D := q.ℓ * N * (N + 1) / 8
    let A := method q.ℓ D N K q.x0
    LongTails.Setups.SlidingStochasticComposite.spec.successful q I
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
        execute O A (fun i => if i = 0 then K + 1 else (K + 1) * N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  intro K N D A
  obtain ⟨hℓ, hL, hσ, hΔ, hε⟩ := hv
  obtain ⟨g, μ, P, hiid, hO, hf, hflip, hc, hh, hhlip, ⟨lower, hlow, hΔ0⟩, hgm, hgi, hgu,
    hgvi, hgv⟩ := hadm
  have hO' : O = compOracle q I g P := hO
  subst hO'
  have : IsProbabilityMeasure (μ : Measure q.Ω) := inferInstance
  have hfc : Continuous I.f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hhc : Continuous I.h := continuous_iff_continuousAt.mpr (fun x => (hh x).continuousAt)
  have ho : IsStochasticGradient q.E q.Ω (μ : Measure q.Ω) I.h g q.σ :=
    ⟨hgm, hgi, hgu, hgvi, hgv⟩
  have hLl : 0 ≤ q.L / q.ℓ := div_nonneg hL hℓ.le
  have hsq : 1 ≤ Real.sqrt (1 + q.L / q.ℓ) := Real.one_le_sqrt.mpr (by linarith)
  have hNreal : 4 * Real.sqrt (1 + q.L / q.ℓ) + 256 * q.σ ^ 2 / q.ε ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNge : (4 : ℝ) ≤ N := by
    have : 0 ≤ 256 * q.σ ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hN1 : 1 ≤ N := hN
  have hNL : 16 * (q.L + q.ℓ) ≤ q.ℓ * (N : ℝ) ^ 2 := by
    have h4 : 4 * Real.sqrt (1 + q.L / q.ℓ) ≤ N := by
      have : 0 ≤ 256 * q.σ ^ 2 / q.ε ^ 2 := by positivity
      linarith
    have hs2 : Real.sqrt (1 + q.L / q.ℓ) ^ 2 = 1 + q.L / q.ℓ :=
      Real.sq_sqrt (by linarith)
    have : 16 * (1 + q.L / q.ℓ) ≤ (N : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (1 + q.L / q.ℓ)]
    have e : 16 * (q.L + q.ℓ) = q.ℓ * (16 * (1 + q.L / q.ℓ)) := by field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this hℓ.le
  have hnoise : 8 * q.σ ^ 2 / (q.ℓ * (N + 1)) ≤ q.ε ^ 2 / (32 * q.ℓ) := by
    have h256 : 256 * q.σ ^ 2 / q.ε ^ 2 ≤ (N : ℝ) + 1 := by
      have : 0 ≤ 4 * Real.sqrt (1 + q.L / q.ℓ) := by positivity
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h256
    nlinarith
  let stepB : q.E → (Fin (N + 1) → q.Ω) → q.E :=
    fun c b => innerRun q.ℓ D N g c (gradient I.f c) (fun j => b j.succ)
  let τ := 8 * q.σ ^ 2 / (q.ℓ * (N + 1))
  have hgfm : Measurable (gradient I.f) := by
    have : Continuous (gradient I.f) :=
      LipschitzWith.continuous (K := ⟨q.ℓ, hℓ.le⟩) (LipschitzWith.of_dist_le_mul (fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hflip x y))
    exact this.measurable
  have hstepm : Measurable (Function.uncurry stepB) := by
    let gg : q.E → q.Ω × q.E → q.E := fun y ω => gradient I.f ω.2 + g y ω.1 + q.ℓ • (y - ω.2)
    have hgg : Measurable (Function.uncurry gg) := by
      have h1 : Measurable (fun v : q.E × (q.Ω × q.E) => g v.1 v.2.1) :=
        hgm.comp (measurable_fst.prodMk measurable_snd.fst)
      exact ((hgfm.comp measurable_snd.snd).add h1).add
        ((measurable_fst.sub measurable_snd.snd).const_smul _)
    have hrun := measurable_acceleratedRun hgg D N 0
    have hcomp : Measurable (fun v : q.E × (Fin (N + 1) → q.Ω) =>
        (acceleratedRun gg D N 0 v.1 v.1 (fun j => (v.2 j.succ, v.1))).1) :=
      (hrun.comp ((measurable_fst.prodMk measurable_fst).prodMk
        (Measurable.of_eval (fun j => ((measurable_pi_apply j.succ).comp measurable_snd).prodMk
          measurable_fst)))).fst
    convert hcomp using 1
    funext v
    simp only [Function.uncurry, stepB, innerRun]
    congr 1
    exact (run_param gg (fun c y ω => gradient I.f c + g y ω + q.ℓ • (y - c)) D N 0 v.1 v.1
      v.1 (fun j => v.2 j.succ) (fun y ω => rfl)).symm
  have hstep : ∀ c, Integrable (fun b => I.f (stepB c b) + I.h (stepB c b))
      (Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω)) ∧
      (∫ b, I.f (stepB c b) + I.h (stepB c b) ∂Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω)) ≤
        I.f c + I.h c - gapAt I.f I.h q.ℓ c / 2 + τ := by
    intro c
    have hin := inner_expected (p := (μ : Measure q.Ω)) hℓ hL hf hflip hc hh hhlip hlow ho N hN
      hNL c
    have htail := tail_preserving (μ : Measure q.Ω) N
    have hgc : Measurable (Function.uncurry
        (fun y ω => gradient I.f c + g y ω + q.ℓ • (y - c))) :=
      (measurable_const.add hgm).add ((measurable_fst.sub_const c).const_smul _)
    have hm : Measurable (fun η : Fin N → q.Ω => innerRun q.ℓ D N g c (gradient I.f c) η) :=
      ((measurable_acceleratedRun hgc D N 0).comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun η : Fin N → q.Ω => ((c, c), η)))).fst
    have hFm : Measurable (fun η : Fin N → q.Ω =>
        I.f (innerRun q.ℓ D N g c (gradient I.f c) η) + I.h (innerRun q.ℓ D N g c (gradient I.f c) η)) :=
      (hfc.measurable.comp hm).add (hhc.measurable.comp hm)
    refine ⟨?_, ?_⟩
    · exact (htail.integrable_comp hFm.aestronglyMeasurable).mpr hin.1
    · have he : (∫ b, I.f (stepB c b) + I.h (stepB c b)
          ∂Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω)) =
          ∫ η, I.f (innerRun q.ℓ D N g c (gradient I.f c) η) +
            I.h (innerRun q.ℓ D N g c (gradient I.f c) η) ∂Measure.pi fun _ : Fin N => (μ : Measure q.Ω) := by
        have hg2 := hFm.aestronglyMeasurable (μ := Measure.pi fun _ : Fin N => (μ : Measure q.Ω))
        rw [← htail.map_eq] at hg2
        rw [← htail.map_eq, integral_map htail.measurable.aemeasurable hg2]
      rw [he]
      exact hin.2
  have hgapm := gapAt_measurable (f := I.f) (h := I.h) hℓ.le hfc hhc hlow
  have hloss := lossSum_integral (r := τ) (F := I.f + I.h) hstepm
    (hgapm.div_const 2) (fun c => by have := gapAt_nonneg (f := I.f) (h := I.h) hℓ.le hlow c; linarith)
    hlow (Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω))
    (fun c => by
      have := hstep c
      refine ⟨by simpa only [Pi.add_apply] using this.1, ?_⟩
      simp only [Pi.add_apply]
      linarith [this.2]) (K + 1) q.x0
  let Pb := Measure.pi fun _ : Fin (K + 1) => Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω)
  let T : (ℕ → q.Ω) → (Fin (K + 1) → Fin (N + 1) → q.Ω) :=
    fun ξ i j => ξ ((i : ℕ) * (N + 1) + j)
  have hT : MeasurePreserving T (P : Measure (ℕ → q.Ω)) Pb := by
    have h1 := OracleTemplate.FiniteVariance.infinite_block_law (μ : Measure q.Ω)
      (P : Measure (ℕ → q.Ω)) hiid.independent (fun k => hiid.marginal k) (N + 1)
    have h2 := OracleTemplate.StochasticGradient.prefix_measurePreserving
      (Measure.pi fun _ : Fin (N + 1) => (μ : Measure q.Ω)) (K + 1)
    exact h2.comp h1
  let G : Fin (K + 1) → (Fin (K + 1) → Fin (N + 1) → q.Ω) → ℝ := fun κ β =>
    gapAt I.f I.h q.ℓ (iter stepB κ q.x0 (fun i : Fin κ => β (Fin.castLE κ.isLt.le i)))
  have hGm : ∀ κ, Measurable (G κ) := fun κ =>
    hgapm.comp ((measurable_iter hstepm κ).comp (measurable_const.prodMk
      (Measurable.of_eval (fun i => measurable_pi_apply _))))
  have hsum : ∀ β, ∑ κ, G κ β = 2 * lossSum stepB (fun c => gapAt I.f I.h q.ℓ c / 2) (K + 1) q.x0 β := by
    intro β
    rw [lossSum_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro κ _
    ring
  have hG0 : ∀ κ β, 0 ≤ G κ β := fun κ β => gapAt_nonneg hℓ.le hlow _
  have hGi : ∀ κ, Integrable (G κ) Pb := by
    intro κ
    refine Integrable.mono' (hloss.1.const_mul 2) (hGm κ).aestronglyMeasurable
      (Eventually.of_forall (fun β => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 κ β), ← hsum β]
    exact Finset.single_le_sum (fun j _ => hG0 j β) (Finset.mem_univ κ)
  have hres : ∀ (κ : Fin (K + 1)) (ξ : ℕ → q.Ω),
      execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) κ ξ =
        iter stepB κ.val q.x0 (fun i : Fin κ.val => T ξ (Fin.castLE κ.isLt.le i)) := by
    intro κ ξ
    exact (execute_eq q.ℓ D N K q.x0 (gradient I.f) g ξ hN1 P κ).trans (centers_eq_iter _ _ _ _ _ _ _ _)
  have hfun : (fun z : Fin (K + 1) × (ℕ → q.Ω) =>
      execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2) =
      fun z => iter stepB z.1.val q.x0 (fun i : Fin z.1.val => T z.2 (Fin.castLE z.1.isLt.le i)) := by
    funext z
    exact hres z.1 z.2
  have : Countable A.Seed := by change Countable (Fin (K + 1)); infer_instance
  have : MeasurableSingletonClass A.Seed := by
    change MeasurableSingletonClass (Fin (K + 1)); infer_instance
  refine ⟨?_, ?_, ?_⟩
  · change Measurable (fun z : Fin (K + 1) × (ℕ → q.Ω) =>
      execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2)
    rw [hfun]
    apply measurable_from_prod_countable_right
    intro κ
    show Measurable (fun y : ℕ → q.Ω =>
      iter stepB κ.val q.x0 (fun i : Fin κ.val => T y (Fin.castLE κ.isLt.le i)))
    exact (measurable_iter hstepm κ.val).comp (measurable_const.prodMk
      (Measurable.of_eval (fun i => (measurable_pi_apply _).comp hT.measurable)))
  · have hu := uniform_joint (P : Measure (ℕ → q.Ω)) (fun κ ξ => G κ (T ξ))
      (fun κ => (hGm κ).comp hT.measurable)
      (fun κ => (hT.integrable_comp (hGm κ).aestronglyMeasurable).mpr (hGi κ))
    change Integrable (fun z : Fin (K + 1) × (ℕ → q.Ω) => moreauGap I
      (execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2))
      ((PMF.uniformOfFintype (Fin (K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω)))
    have he : (fun z : Fin (K + 1) × (ℕ → q.Ω) => moreauGap I
        (execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2)) =
        fun z => G z.1 (T z.2) := by
      funext z
      rw [hres]
      rfl
    rw [he]
    exact hu.1
  · have hu := uniform_joint (P : Measure (ℕ → q.Ω)) (fun κ ξ => G κ (T ξ))
      (fun κ => (hGm κ).comp hT.measurable)
      (fun κ => (hT.integrable_comp (hGm κ).aestronglyMeasurable).mpr (hGi κ))
    have hval : (∫ z : Fin (K + 1) × (ℕ → q.Ω), moreauGap I
        (execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2)
        ∂((PMF.uniformOfFintype (Fin (K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω)))) =
        (Fintype.card (Fin (K + 1)) : ℝ)⁻¹ * ∑ κ, ∫ ξ, G κ (T ξ) ∂(P : Measure (ℕ → q.Ω)) := by
      rw [← hu.2]
      congr 1
      funext z
      rw [hres]
      rfl
    change (∫ z : Fin (K + 1) × (ℕ → q.Ω), moreauGap I
        (execute (compOracle q I g P) A (fun i => if i = 0 then K + 1 else (K + 1) * N) z.1 z.2)
        ∂((PMF.uniformOfFintype (Fin (K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω)))) ≤ _
    rw [hval]
    have htr : ∀ κ, (∫ ξ, G κ (T ξ) ∂(P : Measure (ℕ → q.Ω))) = ∫ β, G κ β ∂Pb := by
      intro κ
      have hg2 := (hGm κ).aestronglyMeasurable (μ := Pb)
      rw [← hT.map_eq] at hg2
      rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hg2]
    simp only [htr]
    rw [← integral_finsetSum _ (fun κ _ => hGi κ)]
    have hint2 : (∫ β, ∑ κ, G κ β ∂Pb) =
        2 * ∫ β, lossSum stepB (fun c => gapAt I.f I.h q.ℓ c / 2) (K + 1) q.x0 β ∂Pb := by
      rw [← integral_const_mul]
      congr 1
      funext β
      exact hsum β
    rw [hint2, Fintype.card_fin]
    have hb := hloss.2
    simp only [Pi.add_apply] at hb
    have hK1 : 32 * q.ℓ * q.Δ / q.ε ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hΔ' : I.f q.x0 + I.h q.x0 - lower ≤ q.Δ := hΔ0
    have hmain : 2 * (q.Δ + ((K + 1 : ℕ) : ℝ) * τ) / ((K : ℝ) + 1) ≤ q.ε ^ 2 / (8 * q.ℓ) := by
      push_cast
      have h1 : 2 * q.Δ / ((K : ℝ) + 1) ≤ q.ε ^ 2 / (16 * q.ℓ) := by
        rw [div_le_div_iff₀ hKpos (by positivity)]
        rw [div_le_iff₀ (by positivity)] at hK1
        nlinarith
      have h2 : 2 * τ ≤ q.ε ^ 2 / (16 * q.ℓ) := by
        have := hnoise
        have e : q.ε ^ 2 / (16 * q.ℓ) = 2 * (q.ε ^ 2 / (32 * q.ℓ)) := by field_simp; ring
        rw [e]; linarith
      have e2 : 2 * (q.Δ + ((K : ℝ) + 1) * τ) / ((K : ℝ) + 1) =
          2 * q.Δ / ((K : ℝ) + 1) + 2 * τ := by field_simp
      rw [e2]
      have e3 : q.ε ^ 2 / (8 * q.ℓ) = q.ε ^ 2 / (16 * q.ℓ) + q.ε ^ 2 / (16 * q.ℓ) := by
        field_simp; ring
      rw [e3]
      linarith
    calc ((((K + 1 : ℕ)) : ℝ))⁻¹ * (2 * ∫ β, lossSum stepB (fun c => gapAt I.f I.h q.ℓ c / 2)
          (K + 1) q.x0 β ∂Pb)
        ≤ (((K + 1 : ℕ) : ℝ))⁻¹ * (2 * (q.Δ + ((K + 1 : ℕ) : ℝ) * τ)) := by
          gcongr
          linarith
      _ = 2 * (q.Δ + ((K + 1 : ℕ) : ℝ) * τ) / ((K : ℝ) + 1) := by push_cast; field_simp
      _ ≤ q.ε ^ 2 / (8 * q.ℓ) := hmain

end Main

end LongTails.Proofs.SlidingCompositeAssembly
