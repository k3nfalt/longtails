import LongTails.Algorithms.MinibatchSignSgd
import LongTails.Proofs.AbcSgdUpper
import LongTails.Proofs.FiniteVarianceBatch
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.ProductMeasure

open MeasureTheory Set Finset
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SignSgdRate

open LongTails.Algorithms.MinibatchSignSgd

abbrev Sp (n : ℕ) := EuclideanSpace ℝ (Fin n)

section Descent

variable {d : ℕ}

lemma inner_eq_sum (u v : Sp d) : ⟪u, v⟫ = ∑ i, u i * v i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma linf_upper_bound {f : Sp d → ℝ} {L : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hsm : ∀ x y r, (∀ i, |x i - y i| ≤ r) → ∑ i, |gradient f x i - gradient f y i| ≤ L * r)
    (x y : Sp d) (r : ℝ) (hr0 : 0 ≤ r) (hr : ∀ i, |y i - x i| ≤ r) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * r ^ 2 := by
  let dd := y - x
  let F := fun t : ℝ => f (x + t • dd)
  let F' := fun t : ℝ => ⟪gradient f (x + t • dd), dd⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const dd |>.const_add x)
    simp only [id_eq, one_smul, InnerProductSpace.toDual_apply_apply] at h
    exact h
  let Bf := fun t : ℝ => f x + t * ⟪gradient f x, dd⟫ + t ^ 2 * (L / 2 * r ^ 2)
  have hB : ∀ t, HasDerivAt Bf (⟪gradient f x, dd⟫ + L * r ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪gradient f x, dd⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * r ^ 2)) using 1
    · funext s
      dsimp [Bf]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Set.Ico (0 : ℝ) 1, F' t ≤ ⟪gradient f x, dd⟫ + L * r ^ 2 * t := by
    intro t ht
    have hdiff : F' t - ⟪gradient f x, dd⟫ =
        ∑ i, (gradient f (x + t • dd) i - gradient f x i) * dd i := by
      simp only [F', inner_eq_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hcoord : ∀ i, |(x + t • dd) i - x i| ≤ t * r := by
      intro i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul,
        abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left (hr i) ht.1
    have hsum := hsm (x + t • dd) x (t * r) hcoord
    have hbound : ∑ i, (gradient f (x + t • dd) i - gradient f x i) * dd i ≤
        (∑ i, |gradient f (x + t • dd) i - gradient f x i|) * r := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      calc (gradient f (x + t • dd) i - gradient f x i) * dd i
          ≤ |(gradient f (x + t • dd) i - gradient f x i) * dd i| := le_abs_self _
        _ = |gradient f (x + t • dd) i - gradient f x i| * |dd i| := abs_mul _ _
        _ ≤ |gradient f (x + t • dd) i - gradient f x i| * r :=
            mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _)
    have : F' t - ⟪gradient f x, dd⟫ ≤ L * (t * r) * r := by
      rw [hdiff]
      exact hbound.trans (mul_le_mul_of_nonneg_right hsum hr0)
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ Bf 0 by simp [F, Bf])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa [F, Bf, dd] using h

end Descent

section Step

lemma mul_sign_ge (a m : ℝ) : |a| - 2 * |m - a| ≤ a * Real.sign m := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Real.sign_of_neg hm]
    rcases le_or_gt a 0 with ha | ha
    · rw [abs_of_nonpos ha]; linarith [abs_nonneg (m - a)]
    · rw [abs_of_pos ha, abs_of_neg (by linarith : m - a < 0)]; linarith
  · subst hm
    rw [Real.sign_zero, zero_sub, abs_neg]; linarith [abs_nonneg a]
  · rw [Real.sign_of_pos hm]
    rcases le_or_gt 0 a with ha | ha
    · rw [abs_of_nonneg ha]; linarith [abs_nonneg (m - a)]
    · rw [abs_of_neg ha, abs_of_pos (by linarith : 0 < m - a)]; linarith

lemma integral_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ) :
    Integrable (fun ω => |X ω|) μ ∧ ∫ ω, |X ω| ∂μ ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) := by
  have hint : Integrable (fun ω => |X ω|) μ := by
    refine ((integrable_const (1 : ℝ)).add hX2).mono' hX.norm ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs, abs_abs, Pi.add_apply]
    nlinarith [sq_abs (X ω), sq_nonneg (|X ω| - 1)]
  refine ⟨hint, ?_⟩
  set v := ∫ ω, X ω ^ 2 ∂μ
  have hv : 0 ≤ v := integral_nonneg fun ω => sq_nonneg _
  have key : ∀ c : ℝ, 0 < c → ∫ ω, |X ω| ∂μ ≤ v / (2 * c) + c / 2 := by
    intro c hc
    have hpt : ∀ ω, |X ω| ≤ X ω ^ 2 / (2 * c) + c / 2 := by
      intro ω
      rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|X ω| - c), sq_abs (X ω)]
    calc ∫ ω, |X ω| ∂μ ≤ ∫ ω, (X ω ^ 2 / (2 * c) + c / 2) ∂μ :=
          integral_mono hint ((hX2.div_const _).add (integrable_const _)) hpt
      _ = v / (2 * c) + c / 2 := by
          rw [integral_add (hX2.div_const _) (integrable_const _), integral_div]
          simp [v]
  rcases hv.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero]
    by_contra hneg
    rw [not_le] at hneg
    have := key (∫ ω, |X ω| ∂μ) hneg
    rw [← h0] at this
    simp at this
    linarith
  · have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hpos
    have := key (Real.sqrt v) hs
    have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
    have e : v / (2 * Real.sqrt v) = Real.sqrt v / 2 := by
      rw [div_eq_iff (by positivity)]
      nlinarith [hsq]
    calc ∫ ω, |X ω| ∂μ ≤ v / (2 * Real.sqrt v) + Real.sqrt v / 2 := this
      _ = Real.sqrt v := by rw [e]; ring

variable {d : ℕ}

lemma sign_step_pointwise {f : Sp d → ℝ} {L η : ℝ} (hη : 0 ≤ η)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hsm : ∀ x y r, (∀ i, |x i - y i| ≤ r) → ∑ i, |gradient f x i - gradient f y i| ≤ L * r)
    (x m : Sp d) :
    f (x - η • signVec m) ≤ f x - η * ∑ i, |gradient f x i| +
      2 * η * ∑ i, |m i - gradient f x i| + L / 2 * η ^ 2 := by
  have hr : ∀ i, |(x - η • signVec m) i - x i| ≤ η := by
    intro i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, sub_sub_cancel_left, abs_neg,
      abs_mul, abs_of_nonneg hη, signVec]
    have : |Real.sign (m i)| ≤ 1 := by
      rcases Real.sign_apply_eq (m i) with h | h | h <;> rw [h] <;> norm_num
    nlinarith [abs_nonneg (Real.sign (m i))]
  have h := linf_upper_bound hg hsm x (x - η • signVec m) η hη hr
  have hin : ⟪gradient f x, x - η • signVec m - x⟫ = -η * ∑ i, gradient f x i * Real.sign (m i) := by
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, inner_eq_sum]
    simp [signVec]
  rw [hin] at h
  have hs : ∑ i, |gradient f x i| - 2 * ∑ i, |m i - gradient f x i| ≤
      ∑ i, gradient f x i * Real.sign (m i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => mul_sign_ge _ _
  nlinarith [mul_le_mul_of_nonneg_left hs hη]

end Step

section Expected

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

structure SignModel (f : Sp d → ℝ) (g : Sp d → Ω → Sp d) (p : Measure Ω) (L S fstar : ℝ) : Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  smooth : ∀ x y r, (∀ i, |x i - y i| ≤ r) → ∑ i, |gradient f x i - gradient f y i| ≤ L * r
  lower : ∀ x, fstar ≤ f x
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  varint : ∀ x i, Integrable (fun ω => (g x ω i - gradient f x i) ^ 2) p
  var : ∀ x, ∑ i, Real.sqrt (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p) ≤ S

lemma coord_continuous (i : Fin d) : Continuous (fun z : Sp d => z i) :=
  (EuclideanSpace.proj i).continuous

lemma f_continuous {f : Sp d → ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)

lemma measurable_real_sign : Measurable Real.sign := by
  have h : Real.sign = fun r : ℝ => if r < 0 then -1 else if 0 < r then 1 else 0 := by
    funext r; rfl
  rw [h]
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma measurable_signVec : Measurable (signVec : Sp d → Sp d) := by
  have h : (signVec : Sp d → Sp d) = fun v => (WithLp.equiv 2 (Fin d → ℝ)).symm
      (fun i => Real.sign (v i)) := rfl
  rw [h]
  refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
  exact measurable_pi_iff.mpr fun i => measurable_real_sign.comp (coord_continuous i).measurable

lemma batchMean_apply {B : ℕ} (r : Fin B → Sp d) (i : Fin d) :
    batchMean r i = (1 / (B : ℝ)) * ∑ b, r b i := by
  simp [batchMean, Finset.sum_apply]

lemma measurable_batchMean_comp {g : Sp d → Ω → Sp d} (hg : Measurable (Function.uncurry g))
    (B : ℕ) : Measurable (fun z : Sp d × (Fin B → Ω) => batchMean (fun b => g z.1 (z.2 b))) := by
  unfold batchMean
  have hs : Measurable (fun z : Sp d × (Fin B → Ω) => ∑ b, g z.1 (z.2 b)) :=
    Finset.measurable_sum _ fun b _ =>
      hg.comp (measurable_fst.prodMk ((measurable_pi_apply b).comp measurable_snd))
  exact hs.const_smul (1 / (B : ℝ))

lemma sign_step_expect {f : Sp d → ℝ} {g : Sp d → Ω → Sp d} {p : Measure Ω} [IsProbabilityMeasure p]
    {L S fstar η : ℝ} (hM : SignModel f g p L S fstar) (hη : 0 ≤ η) (B : ℕ) (hB : 0 < B)
    (x : Sp d) :
    Integrable (fun z : Fin B → Ω => f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar)
      (Measure.pi fun _ : Fin B => p) ∧
    ∫ z, f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar
        ∂(Measure.pi fun _ : Fin B => p) ≤
      (f x - fstar) - η * ∑ i, |gradient f x i| + η * (2 * S / Real.sqrt B + L * η / 2) := by
  set μ := Measure.pi fun _ : Fin B => p
  have hmz : Measurable (fun z : Fin B → Ω => batchMean (fun b => g x (z b))) :=
    (measurable_batchMean_comp hM.meas B).comp (measurable_const.prodMk measurable_id)
  have hcoord : ∀ i, Integrable (fun z : Fin B → Ω => |batchMean (fun b => g x (z b)) i -
      gradient f x i|) μ ∧ ∫ z, |batchMean (fun b => g x (z b)) i - gradient f x i| ∂μ ≤
      Real.sqrt (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p) / Real.sqrt B := by
    intro i
    have hXm : Measurable (fun ω => g x ω i) :=
      (coord_continuous i).measurable.comp (hM.meas.comp (measurable_const.prodMk measurable_id))
    have hXi : Integrable (fun ω => g x ω i) p := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp (hM.int x)
    have hXmean : ∫ ω, g x ω i ∂p = gradient f x i := by
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (hM.int x)
      change ∫ ω, (EuclideanSpace.proj (𝕜 := ℝ) i) (g x ω) ∂p = _
      rw [h, hM.mean]
      rfl
    have hX2 : Integrable (fun ω => ‖g x ω i - gradient f x i‖ ^ 2) p := by
      simpa [Real.norm_eq_abs, sq_abs] using hM.varint x i
    have hv := OracleTemplate.RobustGradient.finite_mean_variance hXm hXi (gradient f x i) hX2
      hXmean B hB
    have he : ∀ z : Fin B → Ω, batchMean (fun b => g x (z b)) i - gradient f x i =
        (1 / (B : ℝ)) • ∑ b, g x (z b) i - gradient f x i := by
      intro z; rw [batchMean_apply, smul_eq_mul]
    have hsq : Integrable (fun z : Fin B → Ω => (batchMean (fun b => g x (z b)) i -
        gradient f x i) ^ 2) μ := by
      simpa [he, Real.norm_eq_abs, sq_abs] using hv.1
    have hmeasi : AEStronglyMeasurable (fun z : Fin B → Ω => batchMean (fun b => g x (z b)) i -
        gradient f x i) μ :=
      (((coord_continuous i).measurable.comp hmz).sub_const _).aestronglyMeasurable
    obtain ⟨hai, hab⟩ := integral_abs_le_sqrt μ hmeasi hsq
    refine ⟨hai, hab.trans ?_⟩
    have hval : ∫ z, (batchMean (fun b => g x (z b)) i - gradient f x i) ^ 2 ∂μ =
        (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p) / B := by
      have := hv.2
      simp only [Real.norm_eq_abs, sq_abs] at this
      simpa [he] using this
    rw [hval, Real.sqrt_div' _ (Nat.cast_nonneg B)]
  have hfc := f_continuous hM.grad
  have hmeasF : Measurable (fun z : Fin B → Ω =>
      f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar) :=
    (hfc.measurable.comp (measurable_const.sub ((measurable_signVec.comp hmz).const_smul η))).sub_const _
  let U := fun z : Fin B → Ω => (f x - fstar) - η * ∑ i, |gradient f x i| +
    2 * η * ∑ i, |batchMean (fun b => g x (z b)) i - gradient f x i| + L / 2 * η ^ 2
  have hU : Integrable U μ :=
    ((integrable_const ((f x - fstar) - η * ∑ i, |gradient f x i|)).add
      ((integrable_finsetSum _ fun i _ => (hcoord i).1).const_mul (2 * η))).add
      (integrable_const (L / 2 * η ^ 2))
  have hpt : ∀ z, f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar ≤ U z := by
    intro z
    have := sign_step_pointwise hη hM.grad hM.smooth x (batchMean (fun b => g x (z b)))
    dsimp only [U]; linarith
  have hi : Integrable (fun z : Fin B → Ω =>
      f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar) μ :=
    hU.mono_nonneg hmeasF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sub_nonneg.mpr (hM.lower _))
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  have hA0 : Integrable (fun _ : Fin B → Ω => (f x - fstar) - η * ∑ i, |gradient f x i|) μ :=
    integrable_const _
  have hB0 : Integrable (fun z : Fin B → Ω =>
      2 * η * ∑ i, |batchMean (fun b => g x (z b)) i - gradient f x i|) μ :=
    (integrable_finsetSum _ fun i _ => (hcoord i).1).const_mul _
  have hAB : Integrable (fun z : Fin B → Ω => (f x - fstar) - η * ∑ i, |gradient f x i| +
      2 * η * ∑ i, |batchMean (fun b => g x (z b)) i - gradient f x i|) μ := hA0.add hB0
  have hIU : ∫ z, U z ∂μ = (f x - fstar) - η * ∑ i, |gradient f x i| +
      2 * η * ∑ i, ∫ z, |batchMean (fun b => g x (z b)) i - gradient f x i| ∂μ + L / 2 * η ^ 2 := by
    dsimp only [U]
    rw [integral_add hAB (integrable_const _), integral_add hA0 hB0, integral_const_mul,
      integral_finsetSum _ fun i _ => (hcoord i).1]
    simp
  have hsumb : ∑ i, ∫ z, |batchMean (fun b => g x (z b)) i - gradient f x i| ∂μ ≤
      S / Real.sqrt B := by
    calc ∑ i, ∫ z, |batchMean (fun b => g x (z b)) i - gradient f x i| ∂μ
        ≤ ∑ i, Real.sqrt (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p) / Real.sqrt B :=
          Finset.sum_le_sum fun i _ => (hcoord i).2
      _ = (∑ i, Real.sqrt (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p)) / Real.sqrt B := by
          rw [Finset.sum_div]
      _ ≤ S / Real.sqrt B := by
          gcongr
          exact hM.var x
  calc ∫ z, f (x - η • signVec (batchMean (fun b => g x (z b)))) - fstar ∂μ
      ≤ ∫ z, U z ∂μ := integral_mono hi hU hpt
    _ = _ := hIU
    _ ≤ (f x - fstar) - η * ∑ i, |gradient f x i| + 2 * η * (S / Real.sqrt B) + L / 2 * η ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsumb (by positivity : (0 : ℝ) ≤ 2 * η)]
    _ = _ := by ring

end Expected

section Loss

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

noncomputable def phiLoss (φ : Sp d → ℝ) (G : Sp d → Ω → Sp d) (η : ℝ) :
    (K : ℕ) → Sp d → (Fin K → Ω) → ℝ
  | 0, _, _ => 0
  | K + 1, x, z => φ x + phiLoss φ G η K (x - η • G x (z 0)) (fun i => z i.succ)

lemma measurable_phiLoss {φ : Sp d → ℝ} {G : Sp d → Ω → Sp d} (hφ : Measurable φ)
    (hG : Measurable (Function.uncurry G)) (η : ℝ) (K : ℕ) :
    Measurable (fun z : Sp d × (Fin K → Ω) => phiLoss φ G η K z.1 z.2) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : Sp d × (Fin (K + 1) → Ω) =>
        (z.1 - η • G z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hg : Measurable (fun z : Sp d × (Fin (K + 1) → Ω) => G z.1 (z.2 0)) :=
        hG.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hg.const_smul η)).prodMk (by fun_prop)
    exact (hφ.comp measurable_fst).add (ih.comp ht)

omit [MeasurableSpace Ω] in
lemma phiLoss_nonneg {φ : Sp d → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (G : Sp d → Ω → Sp d) (η : ℝ) (K : ℕ)
    (x : Sp d) (z : Fin K → Ω) : 0 ≤ phiLoss φ G η K x z := by
  induction K generalizing x with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg (hφ0 _) (ih _ _)

lemma phiLoss_bound {f φ : Sp d → ℝ} {G : Sp d → Ω → Sp d} {p : Measure Ω} [IsProbabilityMeasure p]
    {fstar η c : ℝ} (hη : 0 < η) (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hlow : ∀ x, fstar ≤ f x) (hG : Measurable (Function.uncurry G))
    (hstep : ∀ x, Integrable (fun z => f (x - η • G x z) - fstar) p ∧
      ∫ z, f (x - η • G x z) - fstar ∂p ≤ (f x - fstar) - η * φ x + c)
    (K : ℕ) (x : Sp d) :
    Integrable (phiLoss φ G η K x) (Measure.pi fun _ : Fin K => p) ∧
    ∫ z, phiLoss φ G η K x z ∂Measure.pi (fun _ : Fin K => p) ≤
      (f x - fstar) / η + K * c / η := by
  induction K generalizing x with
  | zero =>
    have h0 : phiLoss φ G η 0 x = fun _ => 0 := by funext z; rfl
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero, Nat.cast_zero, zero_mul, zero_div, add_zero]
    exact div_nonneg (sub_nonneg.mpr (hlow x)) hη.le
  | succ K ih =>
    have hmp : Measurable (phiLoss φ G η (K + 1) x) :=
      (measurable_phiLoss hφ hG η (K + 1)).of_uncurry_left
    let q := Measure.pi (fun _ : Fin K => p)
    let F := fun z : Ω × (Fin K → Ω) => φ x + phiLoss φ G η K (x - η • G x z.1) z.2
    let Bd := fun ω => φ x + ((f (x - η • G x ω) - fstar) / η + K * c / η)
    have hstepx := hstep x
    have hBd : Integrable Bd p :=
      (integrable_const _).add ((hstepx.1.div_const _).add (integrable_const _))
    have hF : Measurable F := by
      have hx : Measurable (fun z : Ω × (Fin K → Ω) => x - η • G x z.1) :=
        measurable_const.sub ((hG.comp (measurable_const.prodMk measurable_fst)).const_smul η)
      exact measurable_const.add ((measurable_phiLoss hφ hG η K).comp (hx.prodMk measurable_snd))
    have hnonneg : ∀ z, 0 ≤ F z := fun z => add_nonneg (hφ0 _) (phiLoss_nonneg hφ0 _ _ _ _ _)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q :=
      fun ω => (integrable_const _).add (ih (x - η • G x ω)).1
    have hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂q) ≤ Bd ω := by
      intro ω
      dsimp only [F, Bd]
      rw [integral_add (integrable_const _) (ih _).1, integral_const, probReal_univ, one_smul]
      linarith [(ih (x - η • G x ω)).2]
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hBd.mono_nonneg hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · apply Filter.Eventually.of_forall
        intro ω
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have heq : (fun z : Ω × (Fin K → Ω) => phiLoss φ G η (K + 1) x (Fin.cons z.1 z.2)) = F := by
      funext z
      simp only [phiLoss, Fin.cons_zero, Fin.cons_succ, F]
    have hcons := OracleTemplate.StochasticGradient.cons_measurePreserving p K
    have hpi : Integrable (phiLoss φ G η (K + 1) x) (Measure.pi (fun _ : Fin (K + 1) => p)) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
        rw [heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, Bd ω ∂p := integral_mono hFi.integral_prod_left hBd hbound
      _ = φ x + ((∫ ω, f (x - η • G x ω) - fstar ∂p) / η + K * c / η) := by
        have h1 : Integrable (fun ω => (f (x - η • G x ω) - fstar) / η) p := hstepx.1.div_const _
        have h2 : Integrable (fun ω => (f (x - η • G x ω) - fstar) / η + K * c / η) p :=
          h1.add (integrable_const _)
        dsimp only [Bd]
        rw [integral_add (integrable_const _) h2, integral_add h1 (integrable_const _), integral_div]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
        have h2 := hstepx.2
        have : (∫ ω, f (x - η • G x ω) - fstar ∂p) / η ≤ ((f x - fstar) - η * φ x + c) / η :=
          div_le_div_of_nonneg_right h2 hη.le
        have e : ((f x - fstar) - η * φ x + c) / η = (f x - fstar) / η - φ x + c / η := by
          field_simp
        push_cast
        rw [e] at this
        have e2 : ((K : ℝ) + 1) * c / η = K * c / η + c / η := by ring
        rw [e2]
        linarith

end Loss

section Blocks

variable {Ω : Type} [MeasurableSpace Ω]

lemma block_law {p : Measure Ω} [IsProbabilityMeasure p] {P : Measure (ℕ → Ω)}
    [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (K B : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun t : Fin K => fun i : Fin B => ξ (t * B + i)) P
      (Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin B => p) := by
  have hinj : Function.Injective (fun s : Fin K × Fin B => (s.1 : ℕ) * B + s.2) := by
    intro a b hab
    have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · exact absurd a.2.isLt (by omega)
      · exact h0
    have h1 : ((a.1 : ℕ) * B + a.2) / B = ((b.1 : ℕ) * B + b.2) / B := by simp only at hab; rw [hab]
    have h2 : ((a.1 : ℕ) * B + a.2) % B = ((b.1 : ℕ) * B + b.2) % B := by simp only at hab; rw [hab]
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt a.2.isLt, Nat.mul_comm,
      Nat.mul_add_div hB, Nat.div_eq_of_lt b.2.isLt] at h1
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt a.2.isLt, Nat.mul_comm, Nat.mul_add_mod,
      Nat.mod_eq_of_lt b.2.isLt] at h2
    exact Prod.ext (Fin.ext (by simpa using h1)) (Fin.ext h2)
  have hi := h.independent.precomp hinj
  have hlaw := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun s : Fin K × Fin B => (h.measurable ((s.1 : ℕ) * B + s.2)).aemeasurable)).mp hi
  simp only [h.marginal] at hlaw
  have hcurry := MeasureTheory.Measure.infinitePi_map_curry (fun (_ : Fin K) (_ : Fin B) => p)
  simp only [MeasureTheory.Measure.infinitePi_eq_pi] at hcurry
  have hF : Measurable (fun ξ : ℕ → Ω => fun s : Fin K × Fin B => ξ ((s.1 : ℕ) * B + s.2)) := by
    fun_prop
  refine ⟨by fun_prop, ?_⟩
  have hcomp : (fun ξ : ℕ → Ω => fun t : Fin K => fun i : Fin B => ξ (t * B + i)) =
      (MeasurableEquiv.curry (Fin K) (Fin B) Ω) ∘
        (fun ξ : ℕ → Ω => fun s : Fin K × Fin B => ξ ((s.1 : ℕ) * B + s.2)) := by
    funext ξ t i; rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) hF]
  rw [show P.map (fun ξ : ℕ → Ω => fun s : Fin K × Fin B => ξ ((s.1 : ℕ) * B + s.2)) =
    Measure.pi (fun _ : Fin K × Fin B => p) from hlaw]
  exact hcurry

end Blocks

end LongTails.Proofs.SignSgdRate
