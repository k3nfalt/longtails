import LongTails.Setups.BlockHeterogeneousNonconvex
import LongTails.Algorithms.BlockSgd
import LongTails.Proofs.AbcSgdRate
import LongTails.Proofs.Execution
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.BlockSgdRate

open LongTails.Setups.BlockHeterogeneousNonconvex LongTails.Algorithms.BlockSgd
open OracleTemplate.StochasticGradient

section Geometry

variable {d B : ℕ} (blk : Fin d → Fin B)

lemma blockProj_apply (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    blockProj blk j x i = if blk i = j then x i else 0 := rfl

noncomputable def precond (η : Fin B → ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => η (blk i) * x i)
      map_add' := by
        intro x y
        ext i
        simp [mul_add]
      map_smul' := by
        intro a x
        ext i
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

lemma precond_apply (η : Fin B → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    precond blk η x i = η (blk i) * x i := rfl

lemma inner_eq_sum (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫ = ∑ j, ⟪blockProj blk j x, blockProj blk j y⟫ := by
  simp only [PiLp.inner_apply, blockProj_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : ∀ j : Fin B, ⟪(if blk i = j then x i else 0), (if blk i = j then y i else 0)⟫ =
      if blk i = j then ⟪x i, y i⟫ else 0 := by
    intro j
    split_ifs <;> simp
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = ∑ j, ‖blockProj blk j x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum blk]
  simp only [real_inner_self_eq_norm_sq]

lemma blockProj_precond (η : Fin B → ℝ) (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) :
    blockProj blk j (precond blk η x) = η j • blockProj blk j x := by
  ext i
  simp only [blockProj_apply, precond_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

lemma inner_precond (η : Fin B → ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    ⟪v, precond blk η w⟫ = ∑ j, η j * ⟪blockProj blk j v, blockProj blk j w⟫ := by
  rw [inner_eq_sum blk]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [blockProj_precond, inner_smul_right]

lemma sum_norm_sq_le (η : Fin B → ℝ) (hη : ∀ j, 0 < η j) (a : Fin B → ℝ) :
    (∑ j, a j) ^ 2 ≤ (∑ j, 1 / η j) * ∑ j, η j * a j ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _; exact (one_div_pos.mpr (hη j)).le
  · intro j _; exact mul_nonneg (hη j).le (sq_nonneg _)
  · intro j _
    have := (hη j).ne'
    exact le_of_eq (by field_simp)

end Geometry

section Model

variable {d B : ℕ} (blk : Fin d → Fin B) {Ω : Type} [MeasurableSpace Ω]

structure BlockModel (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (p : Measure Ω)
    (L σ : Fin B → ℝ) (lower : ℝ) : Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  smooth : ∀ x y, |f y - f x - ⟪gradient f x, y - x⟫| ≤
    (1 / 2) * ∑ j, L j * ‖blockProj blk j (y - x)‖ ^ 2
  bdd : ∀ x, lower ≤ f x
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  varint : ∀ x j, Integrable (fun ω => ‖blockProj blk j (g x ω - gradient f x)‖ ^ 2) p
  var : ∀ x j, ∫ ω, ‖blockProj blk j (g x ω - gradient f x)‖ ^ 2 ∂p ≤ σ j ^ 2

lemma measurable_gradient (f : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

noncomputable def weightedGrad (η : Fin B → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j, η j * ‖blockProj blk j (gradient f x)‖ ^ 2

lemma measurable_weightedGrad (η : Fin B → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (weightedGrad blk η f) := by
  unfold weightedGrad
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact measurable_const.mul
    (((blockProj blk j).continuous.measurable.comp (measurable_gradient f)).norm.pow_const 2)

lemma weightedGrad_nonneg (η : Fin B → ℝ) (hη : ∀ j, 0 ≤ η j) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ weightedGrad blk η f x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hη j) (sq_nonneg _))

variable {blk}

lemma one_step {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ : Fin B → ℝ} {lower : ℝ}
    (hM : BlockModel blk f g p L σ lower) (hL : ∀ j, 0 ≤ L j) (η : Fin B → ℝ)
    (hη : ∀ j, 0 ≤ η j) (hηL : ∀ j, L j * η j ≤ 1) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => f (x - precond blk η (g x ω)) - lower) p ∧
    (∫ ω, f (x - precond blk η (g x ω)) - lower ∂p) ≤
      (f x - lower) - (1 / 2) * weightedGrad blk η f x +
        (1 / 2) * ∑ j, L j * η j ^ 2 * σ j ^ 2 := by
  set v := gradient f x with hvdef
  let noise := fun ω => g x ω - v
  let a := fun j => blockProj blk j v
  let n := fun j ω => blockProj blk j (noise ω)
  have hn : Integrable noise p := (hM.int x).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    rw [integral_sub (hM.int x) (integrable_const _), hM.mean, integral_const]
    simp [v]
  have hnj : ∀ j, Integrable (n j) p := fun j => (blockProj blk j).integrable_comp hn
  have hzj : ∀ j, ∫ ω, ⟪a j, n j ω⟫ ∂p = 0 := by
    intro j
    rw [integral_inner (hnj j)]
    have : ∫ ω, n j ω ∂p = blockProj blk j (∫ ω, noise ω ∂p) :=
      (blockProj blk j).integral_comp_comm hn
    rw [this, hz, map_zero, inner_zero_right]
  have hsq : ∀ j, Integrable (fun ω => ‖n j ω‖ ^ 2) p := fun j => hM.varint x j
  let T := fun ω => ∑ j, (-(η j * (‖a j‖ ^ 2 + ⟪a j, n j ω⟫)) +
    (1 / 2) * (L j * (η j ^ 2 * (‖a j‖ ^ 2 + 2 * ⟪a j, n j ω⟫ + ‖n j ω‖ ^ 2))))
  have hpt : ∀ ω, f (x - precond blk η (g x ω)) - lower ≤ (f x - lower) + T ω := by
    intro ω
    have hs := (abs_le.mp (hM.smooth x (x - precond blk η (g x ω)))).2
    have hgsplit : g x ω = v + noise ω := by simp [noise]
    have hyx : x - precond blk η (g x ω) - x = -(precond blk η (g x ω)) := by abel
    rw [hyx] at hs
    have h1 : ⟪gradient f x, -(precond blk η (g x ω))⟫ =
        -∑ j, η j * (‖a j‖ ^ 2 + ⟪a j, n j ω⟫) := by
      rw [inner_neg_right, ← hvdef, inner_precond]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hgsplit, map_add, inner_add_right, real_inner_self_eq_norm_sq]
    have h2 : ∑ j, L j * ‖blockProj blk j (-(precond blk η (g x ω)))‖ ^ 2 =
        ∑ j, L j * (η j ^ 2 * (‖a j‖ ^ 2 + 2 * ⟪a j, n j ω⟫ + ‖n j ω‖ ^ 2)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_neg, norm_neg, blockProj_precond, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hgsplit, map_add, norm_add_sq_real]
    rw [h1, h2] at hs
    have hT : -∑ j, η j * (‖a j‖ ^ 2 + ⟪a j, n j ω⟫) +
        1 / 2 * ∑ j, L j * (η j ^ 2 * (‖a j‖ ^ 2 + 2 * ⟪a j, n j ω⟫ + ‖n j ω‖ ^ 2)) = T ω := by
      simp only [T]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    linarith
  have hrepr : ∀ j, (fun ω => -(η j * (‖a j‖ ^ 2 + ⟪a j, n j ω⟫)) +
      (1 / 2) * (L j * (η j ^ 2 * (‖a j‖ ^ 2 + 2 * ⟪a j, n j ω⟫ + ‖n j ω‖ ^ 2)))) =
      fun ω => (-(η j * ‖a j‖ ^ 2) + (1 / 2) * (L j * (η j ^ 2 * ‖a j‖ ^ 2))) +
        ((L j * η j ^ 2 - η j) * ⟪a j, n j ω⟫ + (1 / 2) * (L j * η j ^ 2) * ‖n j ω‖ ^ 2) := by
    intro j; funext ω; ring
  have hterm : ∀ j, Integrable (fun ω => -(η j * (‖a j‖ ^ 2 + ⟪a j, n j ω⟫)) +
      (1 / 2) * (L j * (η j ^ 2 * (‖a j‖ ^ 2 + 2 * ⟪a j, n j ω⟫ + ‖n j ω‖ ^ 2)))) p := by
    intro j
    rw [hrepr j]
    exact (integrable_const _).add
      ((((hnj j).const_inner (a j)).const_mul _).add ((hsq j).const_mul _))
  have hTint : Integrable T p := integrable_finsetSum _ (fun j _ => hterm j)
  have hU : Integrable (fun ω => (f x - lower) + T ω) p := (integrable_const _).add hTint
  have hmeas : Measurable (fun ω => f (x - precond blk η (g x ω)) - lower) :=
    ((LongTails.Proofs.AbcSgdRate.f_continuous hM.grad).measurable.comp (measurable_const.sub
      ((precond blk η).continuous.measurable.comp
        (hM.meas.comp (measurable_const.prodMk measurable_id))))).sub_const _
  have hi : Integrable (fun ω => f (x - precond blk η (g x ω)) - lower) p :=
    hU.mono_nonneg hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (hM.bdd _)))
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  have hIT : ∫ ω, T ω ∂p = ∑ j, (-(η j * ‖a j‖ ^ 2) + (1 / 2) * (L j * (η j ^ 2 *
      (‖a j‖ ^ 2 + ∫ ω, ‖n j ω‖ ^ 2 ∂p)))) := by
    simp only [T]
    rw [integral_finsetSum _ (fun j _ => hterm j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : Integrable (fun ω => ⟪a j, n j ω⟫) p := (hnj j).const_inner (a j)
    have h12 : Integrable (fun ω => (L j * η j ^ 2 - η j) * ⟪a j, n j ω⟫ +
        (1 / 2) * (L j * η j ^ 2) * ‖n j ω‖ ^ 2) p := (h1.const_mul _).add ((hsq j).const_mul _)
    rw [hrepr j, integral_add (integrable_const _) h12,
      integral_add (h1.const_mul _) ((hsq j).const_mul _), integral_const_mul, integral_const_mul,
      hzj j, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have hfin : ∫ ω, T ω ∂p ≤ -(1 / 2) * weightedGrad blk η f x +
      (1 / 2) * ∑ j, L j * η j ^ 2 * σ j ^ 2 := by
    have hW : weightedGrad blk η f x = ∑ j, η j * ‖a j‖ ^ 2 := rfl
    rw [hIT, hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hv := hM.var x j
    have hk : 0 ≤ L j * η j ^ 2 := mul_nonneg (hL j) (sq_nonneg _)
    have hk2 : L j * η j ^ 2 ≤ η j := by
      have := mul_le_mul_of_nonneg_right (hηL j) (hη j)
      nlinarith
    have ha : 0 ≤ ‖a j‖ ^ 2 := sq_nonneg _
    have hvn : ∫ ω, ‖n j ω‖ ^ 2 ∂p ≤ σ j ^ 2 := hv
    nlinarith [mul_le_mul_of_nonneg_left hvn hk, mul_le_mul_of_nonneg_right hk2 ha]
  calc _ ≤ ∫ ω, (f x - lower) + T ω ∂p := integral_mono hi hU hpt
    _ = (f x - lower) + ∫ ω, T ω ∂p := by
        rw [integral_add (integrable_const _) hTint, integral_const]
        simp
    _ ≤ _ := by linarith

end Model

section Loss

variable {d B : ℕ} {blk : Fin d → Fin B} {Ω : Type} [MeasurableSpace Ω]

noncomputable def iter (blk : Fin d → Fin B) (η : Fin B → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ω) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x0
  | t + 1 => iter blk η g x0 ξ t - precond blk η (g (iter blk η g x0 ξ t) (ξ t))

omit [MeasurableSpace Ω] in
lemma iter_succ_shift (η : Fin B → ℝ) (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ω) (t : ℕ) :
    iter blk η g x0 ξ (t + 1) =
      iter blk η g (x0 - precond blk η (g x0 (ξ 0))) (fun i => ξ (i + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iter, ih]
    rfl

lemma iter_measurable {g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable (Function.uncurry g)) (η : Fin B → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (t : ℕ) : Measurable (fun ξ : ℕ → Ω => iter blk η g x0 ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact ih.sub ((precond blk η).continuous.measurable.comp (hg.comp (ih.prodMk (measurable_pi_apply t))))

noncomputable def loss (blk : Fin d → Fin B) (η : Fin B → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) :
    (K : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin K → Ω) → ℝ
  | 0, _, _ => 0
  | K + 1, x, ξ => weightedGrad blk η f x +
      loss blk η f g K (x - precond blk η (g x (ξ 0))) (fun i => ξ i.succ)

lemma measurable_loss {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    (h : Measurable (Function.uncurry g)) (η : Fin B → ℝ) (K : ℕ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin K → Ω) => loss blk η f g K z.1 z.2) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin (K + 1) → Ω) =>
        (z.1 - precond blk η (g z.1 (z.2 0)), fun i : Fin K => z.2 i.succ)) := by
      have hg : Measurable (fun z : EuclideanSpace ℝ (Fin d) × (Fin (K + 1) → Ω) =>
          g z.1 (z.2 0)) :=
        h.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub ((precond blk η).continuous.measurable.comp hg)).prodMk (by fun_prop)
    exact ((measurable_weightedGrad blk η f).comp measurable_fst).add (ih.comp ht)

omit [MeasurableSpace Ω] in
lemma loss_nonneg (η : Fin B → ℝ) (hη : ∀ j, 0 ≤ η j) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (K : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (ξ : Fin K → Ω) : 0 ≤ loss blk η f g K x ξ := by
  induction K generalizing x with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg (weightedGrad_nonneg blk η hη f x) (ih _ _)

omit [MeasurableSpace Ω] in
lemma loss_eq_sum (η : Fin B → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (K : ℕ)
    (x0 : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ω) :
    loss blk η f g K x0 (fun i : Fin K => ξ i) =
      ∑ t ∈ Finset.range K, weightedGrad blk η f (iter blk η g x0 ξ t) := by
  induction K generalizing x0 ξ with
  | zero => rfl
  | succ K ih =>
    rw [Finset.sum_range_succ', loss]
    have h := ih (x0 - precond blk η (g x0 (ξ 0))) (fun i => ξ (i + 1))
    have he : (fun i : Fin K => (fun i : Fin (K + 1) => ξ i) i.succ) =
        fun i : Fin K => (fun i => ξ (i + 1)) (i : ℕ) := by
      funext i; simp [Fin.val_succ]
    simp only [Fin.val_zero] at h ⊢
    rw [he, h]
    simp only [iter_succ_shift]
    rw [show iter blk η g x0 ξ 0 = x0 from rfl]
    ring

lemma loss_bound {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ : Fin B → ℝ} {lower : ℝ}
    (hM : BlockModel blk f g p L σ lower) (hL : ∀ j, 0 ≤ L j) (η : Fin B → ℝ)
    (hη : ∀ j, 0 ≤ η j) (hηL : ∀ j, L j * η j ≤ 1) (K : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (loss blk η f g K x) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, loss blk η f g K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      2 * (f x - lower) + K * ∑ j, L j * η j ^ 2 * σ j ^ 2 := by
  induction K generalizing x with
  | zero =>
    have h0 : loss blk η f g 0 x = fun _ => 0 := by funext ξ; rfl
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero, Nat.cast_zero, zero_mul, add_zero]
    have := sub_nonneg.mpr (hM.bdd x)
    linarith
  | succ K ih =>
    have hmp : Measurable (loss blk η f g (K + 1) x) :=
      (measurable_loss hM.meas η (K + 1)).of_uncurry_left
    let q := Measure.pi (fun _ : Fin K => p)
    let F := fun z : Ω × (Fin K → Ω) =>
      weightedGrad blk η f x + loss blk η f g K (x - precond blk η (g x z.1)) z.2
    let Bd := fun ω => weightedGrad blk η f x +
      (2 * (f (x - precond blk η (g x ω)) - lower) + K * ∑ j, L j * η j ^ 2 * σ j ^ 2)
    have hstep := one_step hM hL η hη hηL x
    have hBd : Integrable Bd p :=
      (integrable_const _).add ((hstep.1.const_mul _).add (integrable_const _))
    have hF : Measurable F := by
      have hx : Measurable (fun z : Ω × (Fin K → Ω) => x - precond blk η (g x z.1)) :=
        measurable_const.sub ((precond blk η).continuous.measurable.comp
          (hM.meas.comp (measurable_const.prodMk measurable_fst)))
      exact measurable_const.add ((measurable_loss hM.meas η K).comp (hx.prodMk measurable_snd))
    have hnonneg : ∀ z, 0 ≤ F z := fun z =>
      add_nonneg (weightedGrad_nonneg blk η hη f x) (loss_nonneg η hη _ _ _ _ _)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q :=
      fun ω => (integrable_const _).add (ih (x - precond blk η (g x ω))).1
    have hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂q) ≤ Bd ω := by
      intro ω
      dsimp only [F, Bd]
      rw [integral_add (integrable_const _) (ih _).1, integral_const, probReal_univ, one_smul]
      linarith [(ih (x - precond blk η (g x ω))).2]
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hBd.mono_nonneg hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · apply Filter.Eventually.of_forall
        intro ω
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have heq : (fun z : Ω × (Fin K → Ω) => loss blk η f g (K + 1) x (Fin.cons z.1 z.2)) = F := by
      funext z
      simp only [loss, Fin.cons_zero, Fin.cons_succ, F]
    have hcons := cons_measurePreserving p K
    have hpi : Integrable (loss blk η f g (K + 1) x) (Measure.pi (fun _ : Fin (K + 1) => p)) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
        rw [heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, Bd ω ∂p := integral_mono hFi.integral_prod_left hBd hbound
      _ = weightedGrad blk η f x +
            (2 * ∫ ω, f (x - precond blk η (g x ω)) - lower ∂p +
              K * ∑ j, L j * η j ^ 2 * σ j ^ 2) := by
        have hA1 : Integrable (fun ω => 2 * (f (x - precond blk η (g x ω)) - lower)) p :=
          hstep.1.const_mul _
        have hA2 : Integrable (fun ω => 2 * (f (x - precond blk η (g x ω)) - lower) +
            K * ∑ j, L j * η j ^ 2 * σ j ^ 2) p := hA1.add (integrable_const _)
        dsimp only [Bd]
        rw [integral_add (integrable_const _) hA2,
          integral_add hA1 (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
        have h2 := hstep.2
        have hc : (((K + 1 : ℕ) : ℝ)) * ∑ j, L j * η j ^ 2 * σ j ^ 2 =
            (K : ℝ) * (∑ j, L j * η j ^ 2 * σ j ^ 2) + ∑ j, L j * η j ^ 2 * σ j ^ 2 := by
          push_cast; ring
        rw [hc]
        linarith

end Loss

section Execution

variable {d B : ℕ} {blk : Fin d → Fin B} {Ω : Type}

lemma execute_blockSgd [MeasurableSpace Ω] (η : Fin B → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (K : ℕ)
    (x0 : EuclideanSpace ℝ (Fin d)) (law : ProbabilityMeasure (ℕ → Ω)) (τ : Fin (K + 1))
    (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (sampledPreconditionedSgd (precond blk η) K x0) (fun _ => K + 1) τ ξ =
        iter blk η g x0 ξ τ.val := by
  rw [execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω } :
      Oracle (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (sampledPreconditionedSgd (precond blk η) K x0) (K + 1) τ ξ
    (fun t query => g query.2 (ξ t)) (fun _ query => by cases query; rfl)]
  have hstate : ∀ t, ((fun sc : (sampledPreconditionedSgd (precond blk η) K x0).State × ℕ =>
      ((sampledPreconditionedSgd (precond blk η) K x0).update sc.1
        (g ((sampledPreconditionedSgd (precond blk η) K x0).query sc.1).2 (ξ sc.2)),
        sc.2 + 1))^[t] ((sampledPreconditionedSgd (precond blk η) K x0).initial τ, 0)) =
      ((τ, t, iter blk η g x0 ξ t, if τ.val < t then iter blk η g x0 ξ τ.val else x0), t) := by
    intro t
    induction t with
    | zero => simp [sampledPreconditionedSgd, iter]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [sampledPreconditionedSgd, Prod.mk.injEq, true_and, and_true]
      refine ⟨rfl, ?_⟩
      by_cases h1 : t = τ.val
      · subst h1; simp
      · rw [ite_eq_right h1]
        by_cases h2 : τ.val < t
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  rw [hstate]
  simp [sampledPreconditionedSgd, τ.isLt]

end Execution

end LongTails.Proofs.BlockSgdRate
