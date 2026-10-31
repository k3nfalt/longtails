import LongTails.Proofs.SingleOracleCounted
import LongTails.Setups.MaleniaIterations
import LongTails.Proofs.RennalaStochastic
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.RennalaConvergence
import LongTails.Proofs.BatchIterations

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OracleTemplate.MaleniaUniform

open Rennala

variable {d : ℕ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem average_gradient {d n : ℕ} (fs : Fin n → Point d → ℝ) (f : Point d → ℝ)
    (hf : ∀ x, f x = (1 / (n : ℝ)) * ∑ i, fs i x)
    (hgi : ∀ i x, HasGradientAt (fs i) (gradient (fs i) x) x) (x : Point d) :
    HasGradientAt f ((1 / (n : ℝ)) • ∑ i, gradient (fs i) x) x := by
  rw [show f = fun y => (1 / (n : ℝ)) * ∑ i, fs i y from funext hf, hasGradientAt_iff_hasFDerivAt]
  have hs : HasFDerivAt (fun y => ∑ i, fs i y)
      (∑ i, InnerProductSpace.toDual ℝ (Point d) (gradient (fs i) x)) x :=
    HasFDerivAt.fun_sum (fun i _ => hasGradientAt_iff_hasFDerivAt.mp (hgi i x))
  convert hs.const_mul (1 / (n : ℝ)) using 1
  rw [map_smul, map_sum]


theorem code_injective (n : ℕ) :
    Function.Injective (fun p : (Σ _ : Fin n, ℕ) => code n p.1 p.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  change j * n + i.val = j' * n + i'.val at h
  have hi : i.val = i'.val := by
    have h1 := congrArg (· % n) h
    simp only [Nat.mul_add_mod_of_lt i.isLt, Nat.mul_add_mod_of_lt i'.isLt] at h1
    simpa [Nat.add_comm, Nat.mul_comm] using h1
  have hii : i = i' := Fin.ext hi
  subst hii
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hj : j * n = j' * n := by omega
  have := Nat.eq_of_mul_eq_mul_right hn hj
  subst this
  rfl


theorem estimator_moments {d n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (fs : Fin n → Point d → ℝ) (f : Point d → ℝ)
    (hf : ∀ x, f x = (1 / (n : ℝ)) * ∑ i, fs i x)
    (hgi : ∀ i x, HasGradientAt (fs i) (gradient (fs i) x) x)
    (μ : ProbabilityMeasure Ω) (g : Fin n → Point d → Ω → Point d) (v : ℝ) (hv : 0 ≤ v)
    (ho : ∀ i, StochasticOracle Ω μ (fs i) (g i) v) (hn : 0 < n) (S : ℕ) (hS : 0 < S)
    (B : Fin n → ℕ) (hB : harmonicReady n S B) :
    StochasticOracle (ℕ → Ω)
      ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩ f (estimator B g) (v / S) := by
  classical
  let P : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω))
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  change LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) (ℕ → Ω) P f (estimator B g)
    (Real.sqrt (v / (S : ℝ)))
  have hgrad (x : Point d) : gradient f x = (1 / (n : ℝ)) • ∑ i, gradient (fs i) x :=
    (average_gradient fs f hf hgi x).gradient
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hBpos (i : Fin n) : (0 : ℝ) < B i := by exact_mod_cast hB.1 i
  have hcan := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  have hlaw (k : ℕ) : HasLaw (fun ω : ℕ → Ω => ω k) (μ : Measure Ω) P :=
    ⟨(measurable_pi_apply k).aemeasurable, hcan.marginal k⟩
  let ι := Σ i : Fin n, Fin (B i)
  let c : ι → ℕ := fun p => code n p.1 p.2.val
  have hc : Function.Injective c := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have := code_injective n (a₁ := ⟨i, j.val⟩) (a₂ := ⟨i', j'.val⟩) h
    simp only [Sigma.mk.injEq] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq] at h2
    exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
  let w : ι → ℝ := fun p => 1 / ((n : ℝ) * B p.1)
  let X (x : Point d) : ι → (ℕ → Ω) → Point d := fun p ω =>
    w p • (g p.1 x (ω (c p)) - gradient (fs p.1) x)
  have hgm (i : Fin n) (x : Point d) : Measurable (g i x) := (ho i).measurable.of_uncurry_left
  have hXm (x : Point d) (p : ι) : Measurable (X x p) :=
    (((hgm p.1 x).comp (measurable_pi_apply (c p))).sub measurable_const).const_smul (w p)
  have hind (x : Point d) : iIndepFun (X x) P := by
    have h1 := hcan.independent.precomp hc
    exact h1.comp (fun p a => w p • (g p.1 x a - gradient (fs p.1) x))
      (fun p => ((hgm p.1 x).sub measurable_const).const_smul (w p))
  have hXi (x : Point d) (p : ι) : Integrable (X x p) P :=
    (((hlaw (c p)).integrable_comp ((ho p.1).integrable x)).sub (integrable_const _)).smul (w p)
  have hX2 (x : Point d) (p : ι) :
      Integrable (fun ω => ‖X x p ω‖ ^ 2) P ∧
      (∫ ω, ‖X x p ω‖ ^ 2 ∂P) ≤ w p ^ 2 * v := by
    have hvi := (hlaw (c p)).integrable_comp ((ho p.1).variance_integrable x)
    have he (ω : ℕ → Ω) : ‖X x p ω‖ ^ 2 = w p ^ 2 * ‖g p.1 x (ω (c p)) - gradient (fs p.1) x‖ ^ 2 := by
      simp only [X, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [he]
    refine ⟨hvi.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hh : (∫ ω, ‖g p.1 x (ω (c p)) - gradient (fs p.1) x‖ ^ 2 ∂P) =
        ∫ a, ‖g p.1 x a - gradient (fs p.1) x‖ ^ 2 ∂(μ : Measure Ω) :=
      (hlaw (c p)).integral_comp ((ho p.1).variance_integrable x).aestronglyMeasurable
    rw [hh]
    have hvar := (ho p.1).variance x
    rw [Real.sq_sqrt hv] at hvar
    exact mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
  have hgI (x : Point d) (p : ι) : Integrable (fun ω : ℕ → Ω => g p.1 x (ω (c p))) P :=
    (hlaw (c p)).integrable_comp ((ho p.1).integrable x)
  have hgE (x : Point d) (p : ι) : (∫ ω, g p.1 x (ω (c p)) ∂P) = gradient (fs p.1) x :=
    ((hlaw (c p)).integral_comp ((ho p.1).integrable x).aestronglyMeasurable).trans ((ho p.1).unbiased x)
  have hX0 (x : Point d) (p : ι) : (∫ ω, X x p ω ∂P) = 0 := by
    simp only [X]
    rw [integral_smul, integral_sub (hgI x p) (integrable_const _), hgE x p]
    simp
  have hdecomp (x : Point d) (ω : ℕ → Ω) : estimator B g x ω = gradient f x + ∑ p, X x p ω := by
    rw [hgrad x, Fintype.sum_sigma]
    change (1 / (n : ℝ)) • ∑ i, (1 / (B i : ℝ)) • ∑ j ∈ Finset.range (B i), g i x (ω (code n i j)) =
      (1 / (n : ℝ)) • ∑ i, gradient (fs i) x +
        ∑ i, ∑ j : Fin (B i), (1 / ((n : ℝ) * B i)) • (g i x (ω (code n i j.val)) - gradient (fs i) x)
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_eq_sum_range (fun j => (1 / ((n : ℝ) * B i)) •
      (g i x (ω (code n i j)) - gradient (fs i) x)) (B i)]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hb := (hBpos i).ne'
    have hn' := hnr.ne'
    match_scalars <;> first | (field_simp; done) | (field_simp; ring)
  have hsum (x : Point d) := RobustGradient.independent_sum_second_moment (P := P) (X x) (hind x)
    (hXi x) (fun p => (hX2 x p).1) (hX0 x)
  have hsumi (x : Point d) : Integrable (fun ω => ∑ p, X x p ω) P :=
    integrable_finsetSum _ (fun p _ => hXi x p)
  have hbound : ∑ p : ι, w p ^ 2 * v ≤ v / S := by
    rw [Fintype.sum_sigma]
    have he (i : Fin n) : (∑ _j : Fin (B i), (1 / ((n : ℝ) * B i)) ^ 2 * v) =
        v / (n : ℝ) ^ 2 * (1 / (B i : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hb := (hBpos i).ne'
      field_simp
    change (∑ i, ∑ _j : Fin (B i), (1 / ((n : ℝ) * B i)) ^ 2 * v) ≤ v / S
    simp_rw [he]
    rw [← Finset.mul_sum]
    set H := ∑ i, 1 / (B i : ℝ) with hHdef
    have hHpos : 0 < H := Finset.sum_pos (fun i _ => one_div_pos.mpr (hBpos i))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hSr : (0 : ℝ) < S := by exact_mod_cast hS
    have h1 : ((1 / (n : ℝ)) * H)⁻¹ = n / H := by field_simp
    have hH := hB.2
    rw [← hHdef, h1, div_le_div_iff₀ hnr hHpos] at hH
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hSr]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun z : Point d × (ℕ → Ω) => (1 / (n : ℝ)) •
      ∑ i, (1 / (B i : ℝ)) • ∑ j ∈ Finset.range (B i), g i z.1 (z.2 (code n i j)))
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      (Finset.measurable_sum (Finset.range (B i)) (fun j _ =>
        (ho i).measurable.comp (measurable_fst.prodMk ((measurable_pi_apply (code n i j)).comp
          measurable_snd)))).const_smul (1 / (B i : ℝ)))).const_smul (1 / (n : ℝ))
  · intro x
    exact ((integrable_const (gradient f x)).add (hsumi x)).congr
      (Filter.Eventually.of_forall (fun ω => (hdecomp x ω).symm))
  · intro x
    simp_rw [hdecomp]
    rw [integral_add (integrable_const _) (hsumi x), integral_finsetSum _ (fun p _ => hXi x p)]
    simp [hX0]
  · intro x
    simpa only [hdecomp, add_sub_cancel_left] using (hsum x).1
  · intro x
    simp_rw [hdecomp, add_sub_cancel_left]
    rw [(hsum x).2, Real.sq_sqrt (div_nonneg hv (Nat.cast_nonneg S))]
    exact (Finset.sum_le_sum (fun p _ => (hX2 x p).2)).trans hbound


theorem arrays_law {Ω : Type} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω))) :
    (P : Measure (ℕ → Ω)).map arrays =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω))) := by
  have hP : (P : Measure (ℕ → Ω)) = Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)) := by
    have h := hiid.stream_law.map_eq
    simpa only [Measure.map_id'] using h
  rw [hP]
  have hcomp : (arrays : (ℕ → Ω) → ℕ → ℕ → Ω) = (MeasurableEquiv.curry ℕ ℕ Ω) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Ω) Nat.pairEquiv).symm := by
    funext ξ r c
    rfl
  have h1 : (Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω))).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Ω) Nat.pairEquiv).symm =
      Measure.infinitePi (fun _ : ℕ × ℕ => (μ : Measure Ω)) := by
    exact ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq _).mp
      (Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => (μ : Measure Ω)) Nat.pairEquiv)).symm
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _), h1]
  exact Measure.infinitePi_map_curry (fun _ _ => (μ : Measure Ω))


theorem sgd_moments (f : Point d → ℝ) (G : ℕ → Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v gamma : ℝ) (x0 : Point d) (hL : 0 < L) (hv : 0 ≤ v)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : ∀ r, StochasticOracle Ω μ f (G r) v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) (k : ℕ) :
    Measurable (fun ω => sgdIterate G gamma x0 (fun j => ξ j ω) k) ∧
    Integrable (fun ω => ‖sgdIterate G gamma x0 (fun j => ξ j ω) k‖ ^ 2) (P : Measure Ξ) ∧
    Integrable (fun ω => f (sgdIterate G gamma x0 (fun j => ξ j ω) k)) (P : Measure Ξ) ∧
    Integrable (fun ω => ‖gradient f (sgdIterate G gamma x0 (fun j => ξ j ω) k)‖ ^ 2)
      (P : Measure Ξ) := by
  classical
  let A : ℕ × Point d → Ω → ℕ × Point d := fun s a => (s.1 + 1, s.2 - gamma • G s.1 s.2 a)
  have hsub (x y : Point d) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hn : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    have hh := pow_le_pow_left₀ (norm_nonneg (x - y)) hn 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hraw (r : ℕ) (x : Point d) : Integrable (fun a => ‖G r x a‖ ^ 2) (μ : Measure Ω) ∧
      (∫ a, ‖G r x a‖ ^ 2 ∂(μ : Measure Ω)) ≤ 2 * v + 2 * ‖gradient f x‖ ^ 2 := by
    have hb (a : Ω) : ‖G r x a‖ ^ 2 ≤ 2 * ‖G r x a - gradient f x‖ ^ 2 +
        2 * ‖gradient f x‖ ^ 2 := by
      simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using
        hsub (G r x a - gradient f x) (-gradient f x)
    have hi : Integrable (fun a => 2 * ‖G r x a - gradient f x‖ ^ 2 +
        2 * ‖gradient f x‖ ^ 2) (μ : Measure Ω) :=
      (((ho r).variance_integrable x).const_mul 2).add (integrable_const _)
    have hgi : Integrable (fun a => ‖G r x a‖ ^ 2) (μ : Measure Ω) := by
      apply hi.mono' (((ho r).measurable.of_uncurry_left (x := x)).norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs, abs_sq] using hb a)
    refine ⟨hgi, ?_⟩
    have hh := integral_mono hgi hi hb
    rw [integral_add (((ho r).variance_integrable x).const_mul 2) (integrable_const _),
      integral_const_mul] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hvx : (∫ a, ‖G r x a - gradient f x‖ ^ 2 ∂(μ : Measure Ω)) ≤ v := by
      simpa only [Real.sq_sqrt hv] using (ho r).variance x
    linarith
  have hGm : Measurable (fun q : ℕ × (Point d × Ω) => G q.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right (fun r => (ho r).measurable)
  have hA : Measurable (fun q : (ℕ × Point d) × Ω => A q.1 q.2) := by
    refine Measurable.prodMk ?_ ?_
    · exact (Measurable.of_discrete (f := fun n : ℕ => n + 1)).comp (measurable_fst.comp measurable_fst)
    · exact (measurable_snd.comp measurable_fst).sub (Measurable.const_smul (hGm.comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))) gamma)
  have hstep (s : ℕ × Point d) : Integrable (fun a => ‖(A s a).2‖ ^ 2) (μ : Measure Ω) ∧
      (∫ a, ‖(A s a).2‖ ^ 2 ∂(μ : Measure Ω)) ≤ (2 + 8 * gamma ^ 2 * L ^ 2) * ‖s.2‖ ^ 2 +
        (4 * gamma ^ 2 * v + 8 * gamma ^ 2 * ‖gradient f 0‖ ^ 2) := by
    have hb (a : Ω) : ‖(A s a).2‖ ^ 2 ≤ 2 * ‖s.2‖ ^ 2 + 2 * gamma ^ 2 * ‖G s.1 s.2 a‖ ^ 2 := by
      simpa only [A, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using
        hsub s.2 (gamma • G s.1 s.2 a)
    have hi : Integrable (fun a => 2 * ‖s.2‖ ^ 2 + 2 * gamma ^ 2 * ‖G s.1 s.2 a‖ ^ 2) (μ : Measure Ω) :=
      (integrable_const _).add ((hraw s.1 s.2).1.const_mul _)
    have hAm : Measurable (fun a => (A s a).2) :=
      ((measurable_snd.comp hA).comp (measurable_const.prodMk measurable_id))
    have hai : Integrable (fun a => ‖(A s a).2‖ ^ 2) (μ : Measure Ω) := by
      apply hi.mono' (hAm.norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs, abs_sq] using hb a)
    refine ⟨hai, ?_⟩
    have hh := integral_mono hai hi hb
    rw [integral_add (integrable_const _) ((hraw s.1 s.2).1.const_mul _)] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hvx := mul_le_mul_of_nonneg_left (hraw s.1 s.2).2 (by positivity : 0 ≤ 2 * gamma ^ 2)
    have hgx := mul_le_mul_of_nonneg_left ((smooth_growth f L hg hlip).2.2 s.2)
      (by positivity : 0 ≤ 4 * gamma ^ 2)
    nlinarith
  have hiter (m : ℕ) (seeds : ℕ → Ω) :
      ContinuizedSimilarQuasar.iterateSamples A m (0, x0) (fun i => seeds i.val) =
        (m, sgdIterate G gamma x0 seeds m) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [GapStrongGrowth.iterateSamples_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      rfl
  let μS : ProbabilityMeasure Ω := μ
  have hpres : MeasurePreserving (fun ω => (fun i : Fin k => ξ i ω)) (P : Measure Ξ)
      (Measure.pi (fun _ : Fin k => (μ : Measure Ω))) :=
    (StochasticGeneralized.prefix_preserving (μ : Measure Ω) k).comp hiid.stream_law
  have hmeas : Measurable (fun b : Fin k → Ω =>
      (ContinuizedSimilarQuasar.iterateSamples A k (0, x0) b).2) :=
    measurable_snd.comp ((GapStrongGrowth.iterateSamples_measurable hA k).comp
      (measurable_const.prodMk measurable_id))
  have hi := (GapStrongGrowth.iterateSamples_measurable_integral hA μS
    (fun s : ℕ × Point d => ‖s.2‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
    (by positivity : 0 ≤ 2 + 8 * gamma ^ 2 * L ^ 2)
    hstep k (0, x0)).1
  have hxe (ω : Ξ) : sgdIterate G gamma x0 (fun j => ξ j ω) k =
      (ContinuizedSimilarQuasar.iterateSamples A k (0, x0) (fun i => ξ i ω)).2 := by
    rw [hiter k (fun j => ξ j ω)]
  have hx : Measurable (fun ω => sgdIterate G gamma x0 (fun j => ξ j ω) k) := by
    simp only [hxe]
    exact hmeas.comp hpres.measurable
  have hx2 : Integrable (fun ω => ‖sgdIterate G gamma x0 (fun j => ξ j ω) k‖ ^ 2) (P : Measure Ξ) := by
    simp only [hxe]
    exact hpres.integrable_comp_of_integrable hi
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hxnorm : Integrable (fun ω => ‖sgdIterate G gamma x0 (fun j => ξ j ω) k‖) (P : Measure Ξ) :=
    (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      ((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mpr hx2)).norm
  refine ⟨hx, hx2, ?_, ?_⟩
  · apply (((integrable_const |f 0|).add (hxnorm.const_mul ‖gradient f 0‖)).add
      (hx2.const_mul (L / 2))).mono' (hfc.measurable.comp hx).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply] using
        (smooth_growth f L hg hlip).2.1 (sgdIterate G gamma x0 (fun j => ξ j ω) k))
  · apply ((integrable_const (2 * ‖gradient f 0‖ ^ 2)).add
      (hx2.const_mul (2 * L ^ 2))).mono' ((hgc.measurable.comp hx).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_sq, Function.comp_def, Pi.add_apply] using
        (smooth_growth f L hg hlip).2.2 (sgdIterate G gamma x0 (fun j => ξ j ω) k))


theorem sgd_descent (f : Point d → ℝ) (G : ℕ → Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v gamma lower : ℝ) (x0 : Point d)
    (hL : 0 < L) (hv : 0 ≤ v) (hgamma : 0 < gamma) (hgammaL : gamma ≤ 1 / L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : ∀ r, StochasticOracle Ω μ f (G r) v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) (k : ℕ) :
    (∫ ω, f (sgdIterate G gamma x0 (fun j => ξ j ω) (k + 1)) - lower ∂(P : Measure Ξ)) ≤
      (∫ ω, f (sgdIterate G gamma x0 (fun j => ξ j ω) k) - lower ∂(P : Measure Ξ)) -
        gamma / 2 * (∫ ω, ‖gradient f (sgdIterate G gamma x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) +
        L * gamma ^ 2 * v / 2 := by
  classical
  let A : ℕ × Point d → Ω → ℕ × Point d := fun s a => (s.1 + 1, s.2 - gamma • G s.1 s.2 a)
  let adv : Point d → Ω → Point d := fun x a => x - gamma • G k x a
  have hGm : Measurable (fun q : ℕ × (Point d × Ω) => G q.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right (fun r => (ho r).measurable)
  have hA : Measurable (fun q : (ℕ × Point d) × Ω => A q.1 q.2) := by
    refine Measurable.prodMk ?_ ?_
    · exact (Measurable.of_discrete (f := fun n : ℕ => n + 1)).comp (measurable_fst.comp measurable_fst)
    · exact (measurable_snd.comp measurable_fst).sub (Measurable.const_smul (hGm.comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))) gamma)
  have ha : Measurable (fun z : Point d × Ω => adv z.1 z.2) :=
    measurable_fst.sub ((ho k).measurable.const_smul gamma)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  let Q : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩
  have hcanon := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  have heval : MeasurePreserving (fun a : ℕ → Ω => a 0) (Q : Measure (ℕ → Ω)) (μ : Measure Ω) :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hfixed (x : Point d) : Integrable (fun a => f (adv x a) - lower) (μ : Measure Ω) := by
    have hmi : Integrable (fun a : ℕ → Ω => f (sgdIterate (fun _ => G k) gamma x a 1))
        (Q : Measure (ℕ → Ω)) :=
      (sgd_moments f (fun _ => G k) μ Q (fun i a => a i) L v gamma x hL hv hg hlip
        (fun _ => ho k) hcanon 1).2.2.1
    have hm : Integrable (fun a : ℕ → Ω => f (sgdIterate (fun _ => G k) gamma x a 1) - lower)
        (Q : Measure (ℕ → Ω)) := hmi.sub (integrable_const lower)
    apply (heval.integrable_comp ((hfc.measurable.comp (ha.of_uncurry_left (x := x))).sub_const
      lower).aestronglyMeasurable).mp
    exact hm
  have hstep (x : Point d) : (∫ a, f (adv x a) - lower ∂(μ : Measure Ω)) ≤
      f x - lower - gamma / 2 * ‖gradient f x‖ ^ 2 + L * gamma ^ 2 * v / 2 := by
    have he (a : Ω) : ‖G k x a‖ ^ 2 = ‖G k x a - gradient f x‖ ^ 2 +
        2 * inner ℝ (gradient f x) (G k x a) - ‖gradient f x‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm (G k x a) (gradient f x)]
      ring
    have hinner : Integrable (fun a => inner ℝ (gradient f x) (G k x a)) (μ : Measure Ω) :=
      ((ho k).integrable x).const_inner _
    have hg2 : Integrable (fun a => ‖G k x a‖ ^ 2) (μ : Measure Ω) := by
      simp_rw [he]
      exact (((ho k).variance_integrable x).add (hinner.const_mul 2)).sub (integrable_const _)
    have heg : (∫ a, ‖G k x a‖ ^ 2 ∂(μ : Measure Ω)) =
        (∫ a, ‖G k x a - gradient f x‖ ^ 2 ∂(μ : Measure Ω)) + ‖gradient f x‖ ^ 2 := by
      simp_rw [he]
      have hsum : Integrable (fun a => ‖G k x a - gradient f x‖ ^ 2 +
          2 * inner ℝ (gradient f x) (G k x a)) (μ : Measure Ω) :=
        ((ho k).variance_integrable x).add (hinner.const_mul 2)
      rw [integral_sub hsum (integrable_const _),
        integral_add ((ho k).variance_integrable x) (hinner.const_mul 2), integral_const_mul,
        integral_inner ((ho k).integrable x), (ho k).unbiased]
      simp only [real_inner_self_eq_norm_sq, integral_const, probReal_univ, one_smul]
      ring
    have hgb : (∫ a, ‖G k x a‖ ^ 2 ∂(μ : Measure Ω)) ≤ v + ‖gradient f x‖ ^ 2 := by
      rw [heg]
      exact add_le_add (by simpa only [Real.sq_sqrt hv] using (ho k).variance x) (le_refl _)
    have hp (a : Ω) : f (adv x a) - lower ≤ f x - lower -
        gamma * inner ℝ (gradient f x) (G k x a) + (L * gamma ^ 2 / 2) * ‖G k x a‖ ^ 2 := by
      have hh := (smooth_growth f L hg hlip).1 x (adv x a)
      have hd : adv x a - x = -(gamma • G k x a) := by dsimp only [adv]; module
      rw [hd, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs] at hh
      nlinarith
    have hbi : Integrable (fun a => f x - lower - gamma * inner ℝ (gradient f x) (G k x a) +
        (L * gamma ^ 2 / 2) * ‖G k x a‖ ^ 2) (μ : Measure Ω) :=
      ((integrable_const _).sub (hinner.const_mul gamma)).add (hg2.const_mul _)
    have hh := integral_mono (hfixed x) hbi hp
    have hlinear : Integrable (fun a => f x - lower - gamma * inner ℝ (gradient f x) (G k x a))
        (μ : Measure Ω) := (integrable_const _).sub (hinner.const_mul gamma)
    rw [integral_add hlinear (hg2.const_mul _),
      integral_sub (integrable_const _) (hinner.const_mul gamma)] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul,
      integral_inner ((ho k).integrable x), (ho k).unbiased, real_inner_self_eq_norm_sq] at hh
    have hvx := mul_le_mul_of_nonneg_left hgb (by positivity : 0 ≤ L * gamma ^ 2 / 2)
    have hgl : gamma * L ≤ 1 := (le_div_iff₀ hL).mp hgammaL
    have hc : L * gamma ^ 2 / 2 ≤ gamma / 2 := by nlinarith
    have hcx := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖gradient f x‖)
    nlinarith
  have hiter (m : ℕ) (seeds : ℕ → Ω) :
      ContinuizedSimilarQuasar.iterateSamples A m (0, x0) (fun i => seeds i.val) =
        (m, sgdIterate G gamma x0 seeds m) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [GapStrongGrowth.iterateSamples_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      rfl
  let X : (Fin k → Ω) → Point d := fun b => (ContinuizedSimilarQuasar.iterateSamples A k (0, x0) b).2
  have hXm : Measurable X := measurable_snd.comp ((GapStrongGrowth.iterateSamples_measurable hA k).comp
    (measurable_const.prodMk measurable_id))
  let ρ : Measure (Fin k → Ω) := Measure.pi (fun _ : Fin k => (μ : Measure Ω))
  have : IsProbabilityMeasure ρ := by dsimp only [ρ]; infer_instance
  have hp : MeasurePreserving (fun ω => (fun i : Fin k => ξ i ω)) (P : Measure Ξ) ρ :=
    (StochasticGeneralized.prefix_preserving (μ : Measure Ω) k).comp hiid.stream_law
  have hpair : MeasurePreserving (fun ω => ((fun i : Fin k => ξ i ω), ξ k ω))
      (P : Measure Ξ) (ρ.prod (μ : Measure Ω)) := by
    have ht := ((MeasurePreserving.id ρ).prod heval).comp (hiid.prefix_tail_law k)
    simpa only [Function.comp_def, Prod.map_apply, id_eq, Nat.add_zero] using ht
  have hx (ω : Ξ) : X (fun i => ξ i ω) = sgdIterate G gamma x0 (fun j => ξ j ω) k := by
    simp only [X]
    rw [hiter k (fun j => ξ j ω)]
  have hnext (ω : Ξ) : adv (X (fun i => ξ i ω)) (ξ k ω) =
      sgdIterate G gamma x0 (fun j => ξ j ω) (k + 1) := by
    rw [hx]
    rfl
  have hmk := sgd_moments f G μ P ξ L v gamma x0 hL hv hg hlip ho hiid k
  have hmk1 := sgd_moments f G μ P ξ L v gamma x0 hL hv hg hlip ho hiid (k + 1)
  have hprei : Integrable (fun b => f (X b) - lower) ρ := by
    apply (hp.integrable_comp ((hfc.measurable.comp hXm).sub_const lower).aestronglyMeasurable).mp
    have hh : Integrable (fun ω => f (sgdIterate G gamma x0 (fun j => ξ j ω) k) - lower)
        (P : Measure Ξ) := Integrable.sub hmk.2.2.1 (integrable_const lower)
    simpa only [Function.comp_def, hx] using hh
  have hgri : Integrable (fun b => ‖gradient f (X b)‖ ^ 2) ρ := by
    apply (hp.integrable_comp ((hgc.measurable.comp hXm).norm.pow_const 2).aestronglyMeasurable).mp
    simpa only [Function.comp_def, hx] using hmk.2.2.2
  let F : (Fin k → Ω) × Ω → ℝ := fun z => f (adv (X z.1) z.2) - lower
  have hFm : Measurable F := (hfc.measurable.comp
    (ha.comp ((hXm.comp measurable_fst).prodMk measurable_snd))).sub_const lower
  have hFi : Integrable F (ρ.prod (μ : Measure Ω)) := by
    apply (hpair.integrable_comp hFm.aestronglyMeasurable).mp
    have hh : Integrable (fun ω => f (sgdIterate G gamma x0 (fun j => ξ j ω) (k + 1)) - lower)
        (P : Measure Ξ) := Integrable.sub hmk1.2.2.1 (integrable_const lower)
    simpa only [Function.comp_def, F, hnext] using hh
  have hprelaw : HasLaw (fun ω => (fun i : Fin k => ξ i ω)) ρ (P : Measure Ξ) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have hpairlaw : HasLaw (fun ω => ((fun i : Fin k => ξ i ω), ξ k ω))
      (ρ.prod (μ : Measure Ω)) (P : Measure Ξ) := ⟨hpair.measurable.aemeasurable, hpair.map_eq⟩
  have heF : (∫ ω, f (sgdIterate G gamma x0 (fun j => ξ j ω) (k + 1)) - lower ∂(P : Measure Ξ)) =
      ∫ z, F z ∂(ρ.prod (μ : Measure Ω)) := by
    simpa only [Function.comp_def, F, hnext] using hpairlaw.integral_comp hFi.aestronglyMeasurable
  have hepre : (∫ ω, f (sgdIterate G gamma x0 (fun j => ξ j ω) k) - lower ∂(P : Measure Ξ)) =
      ∫ b, f (X b) - lower ∂ρ := by
    simpa only [Function.comp_def, hx] using hprelaw.integral_comp hprei.aestronglyMeasurable
  have hegr : (∫ ω, ‖gradient f (sgdIterate G gamma x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) =
      ∫ b, ‖gradient f (X b)‖ ^ 2 ∂ρ := by
    simpa only [Function.comp_def, hx] using hprelaw.integral_comp hgri.aestronglyMeasurable
  rw [heF, hepre, hegr, integral_prod _ hFi]
  have hlinear : Integrable (fun b => f (X b) - lower - gamma / 2 * ‖gradient f (X b)‖ ^ 2) ρ :=
    hprei.sub (hgri.const_mul (gamma / 2))
  have hboundi : Integrable (fun b => f (X b) - lower - gamma / 2 * ‖gradient f (X b)‖ ^ 2 +
      L * gamma ^ 2 * v / 2) ρ := hlinear.add (integrable_const _)
  have hbound := integral_mono hFi.integral_prod_left hboundi (fun b => hstep (X b))
  simpa only [integral_add hlinear (integrable_const _),
    integral_sub hprei (hgri.const_mul (gamma / 2)), integral_const_mul,
    integral_const, probReal_univ, one_smul] using hbound


theorem sgd_average (f : Point d → ℝ) (G : ℕ → Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v gamma Delta lower : ℝ) (x0 : Point d)
    (hL : 0 < L) (hv : 0 ≤ v) (hgamma : 0 < gamma) (hgammaL : gamma ≤ 1 / L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hlower : ∀ x, lower ≤ f x) (hgap : f x0 - lower = Delta)
    (ho : ∀ r, StochasticOracle Ω μ f (G r) v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) (K : ℕ) (hK : 0 < K) :
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
      (∫ ω, ‖gradient f (sgdIterate G gamma x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
        2 * Delta / (gamma * K) + L * gamma * v := by
  classical
  have hDelta : 0 ≤ Delta := by rw [← hgap]; exact sub_nonneg.mpr (hlower x0)
  let F : ℕ → ℝ := fun k => ∫ ω, f (sgdIterate G gamma x0 (fun j => ξ j ω) k) - lower ∂(P : Measure Ξ)
  let H : ℕ → ℝ := fun k =>
    ∫ ω, ‖gradient f (sgdIterate G gamma x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)
  have hstep (k : ℕ) : F (k + 1) ≤ F k - gamma / 2 * H k + L * gamma ^ 2 * v / 2 :=
    sgd_descent f G μ P ξ L v gamma lower x0 hL hv hgamma hgammaL hg hlip ho hiid k
  have hzero : F 0 = Delta := by
    change (∫ ω, f x0 - lower ∂(P : Measure Ξ)) = Delta
    simp only [integral_const, probReal_univ, one_smul, hgap]
  have hnonneg (k : ℕ) : 0 ≤ F k := integral_nonneg (fun ω => sub_nonneg.mpr (hlower _))
  have hsum (m : ℕ) : gamma / 2 * ∑ k ∈ Finset.range m, H k ≤
      F 0 - F m + (m : ℝ) * (L * gamma ^ 2 * v / 2) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      have hs := hstep m
      nlinarith
  have ht := hsum K
  rw [hzero] at ht
  have hd : (∑ k ∈ Finset.range K, H k) ≤ (2 * Delta + L * gamma ^ 2 * v * K) / gamma := by
    apply (le_div_iff₀ hgamma).mpr
    nlinarith [hnonneg K]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hm := div_le_div_of_nonneg_right hd hKr.le
  convert hm using 1
  · change _ = (∑ k ∈ Finset.range K, H k) / K
    ring
  · field_simp


theorem malenia_accuracy {n : ℕ} (fs : Fin n → Point d → ℝ) (f : Point d → ℝ)
    (hf : ∀ x, f x = (1 / (n : ℝ)) * ∑ i, fs i x)
    (hgi : ∀ i x, HasGradientAt (fs i) (gradient (fs i) x) x)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hstream : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Fin n → Point d → Ω → Point d)
    (L v eps Delta lower : ℝ) (x0 : Point d)
    (hn : 0 < n) (hL : 0 < L) (hv : 0 ≤ v) (heps : 0 < eps)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hlower : ∀ x, lower ≤ f x) (hgap : f x0 - lower = Delta)
    (ho : ∀ i, StochasticOracle Ω μ (fs i) (g i) v)
    (B : ℕ → Fin n → ℕ) (hB : ∀ r, harmonicReady n (MaleniaIterations.batchSize n v eps) (B r))
    (K : ℕ) (hK : 0 < K) (hbudget : 24 * L * Delta / eps ≤ (K : ℝ)) :
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
      (∫ ω, ‖gradient f (iterate g (MaleniaIterations.stepSize L v eps (MaleniaIterations.batchSize n v eps)) B x0 ω k)‖ ^ 2
        ∂(Measure.map arrays (P : Measure (ℕ → Ω)))) ≤ eps := by
  classical
  rw [arrays_law μ P hstream]
  let ρR : ProbabilityMeasure (ℕ → ℕ → Ω) :=
    ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω))), inferInstance⟩
  set S := MaleniaIterations.batchSize n v eps with hSdef
  have hS : 0 < S := lt_of_lt_of_le hn (le_max_right _ _)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hSv : v / eps ≤ (S : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
  have hDelta : 0 ≤ Delta := by rw [← hgap]; exact sub_nonneg.mpr (hlower x0)
  let μ' : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩
  have hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun r (ω : ℕ → ℕ → Ω) => ω r) (μ' : Measure (ℕ → Ω))
      (ρR : Measure (ℕ → ℕ → Ω)) := StochasticGeneralized.infinitePi_iid _
  have hoG (r : ℕ) : StochasticOracle (ℕ → Ω) μ' f (estimator (B r) g) (v / S) :=
    estimator_moments fs f hf hgi μ g v hv ho hn S hS (B r) (hB r)
  set gamma := MaleniaIterations.stepSize L v eps S with hgdef
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hb4 : 4 * L * Delta ≤ eps / 6 * K := by
    have := (div_le_iff₀ heps).mp hbudget
    nlinarith
  by_cases hv0 : v = 0
  · have hgam : gamma = 1 / L := by
      rw [hgdef]
      show (if v = 0 then 1 / L else min (1 / L) (eps * S / (2 * L * v))) = 1 / L
      rw [ite_eq_left hv0]
    have hh := sgd_average f (fun r => estimator (B r) g) μ' ρR (fun r ω => ω r) L (v / S)
      gamma Delta lower x0 hL (div_nonneg hv hSr.le) (by rw [hgam]; positivity) (by rw [hgam])
      hg hlip hlower hgap hoG hiid K hK
    refine hh.trans ?_
    rw [hgam, hv0, zero_div, mul_zero, add_zero]
    rw [div_le_iff₀ (by positivity)]
    have he : eps * (1 / L * K) * L = eps * K := by field_simp
    nlinarith [he]
  · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hgam : gamma = min (1 / L) (eps * S / (2 * L * v)) := by
      rw [hgdef]
      show (if v = 0 then 1 / L else min (1 / L) (eps * S / (2 * L * v))) = _
      rw [ite_eq_right hv0]
    have hgpos : 0 < gamma := by rw [hgam]; exact lt_min (one_div_pos.mpr hL) (by positivity)
    have hgL : gamma ≤ 1 / L := by rw [hgam]; exact min_le_left _ _
    have hglow : 1 / (2 * L) ≤ gamma := by
      rw [hgam]
      refine le_min (by rw [div_le_div_iff₀ (by positivity) hL]; linarith) ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := (div_le_iff₀ heps).mp hSv
      nlinarith
    have hh := sgd_average f (fun r => estimator (B r) g) μ' ρR (fun r ω => ω r) L (v / S)
      gamma Delta lower x0 hL (div_nonneg hv hSr.le) hgpos hgL hg hlip hlower hgap hoG hiid K hK
    refine hh.trans ?_
    have hnoise : L * gamma * (v / S) ≤ eps / 2 := by
      have hmin : gamma ≤ eps * S / (2 * L * v) := by rw [hgam]; exact min_le_right _ _
      have h2 := (le_div_iff₀ (by positivity : 0 < 2 * L * v)).mp hmin
      rw [mul_div_assoc', div_le_iff₀ hSr]
      nlinarith
    have hfirst : 2 * Delta / (gamma * K) ≤ eps / 6 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 ≤ 2 * L * gamma := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mp hglow
        linarith
      nlinarith
    linarith


theorem execute_iter (p : BatchIterations.Public) (n : ℕ) (B : ℕ → Fin n → ℕ)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Fin n → Point p.d → Ω → Point p.d)
    (j : Fin (p.N + 1)) (ξ : ℕ → ℕ → Ω) :
    executeCounted (iterOracle p n B P g) (BatchIterations.algorithm p) (p.N + 1) j ξ =
      (iterate g p.gamma B p.x0 ξ j.val, p.N + 1) := by
  classical
  let X := iterate g p.gamma B p.x0 ξ
  let st : ℕ → BatchIterations.State p := fun r =>
    ⟨r, X r, if j.val ≤ r then X j.val else p.x0, j⟩
  let step : ℕ → BatchIterations.State p → BatchIterations.State p := fun r s =>
    (BatchIterations.algorithm p).update s
      ((estimator (B r) g ((BatchIterations.algorithm p).query s).2 (ξ r)))
  have hstep (r : ℕ) : step r (st r) = st (r + 1) := by
    have hx : X (r + 1) = X r - p.gamma • estimator (B r) g (X r) (ξ r) := rfl
    change (⟨r + 1, X r - p.gamma • estimator (B r) g (X r) (ξ r),
      if r + 1 = j.val then X r - p.gamma • estimator (B r) g (X r) (ξ r)
      else (if j.val ≤ r then X j.val else p.x0), j⟩ : BatchIterations.State p) = st (r + 1)
    rw [← hx]
    change _ = (⟨r + 1, X (r + 1), if j.val ≤ r + 1 then X j.val else p.x0, j⟩ : BatchIterations.State p)
    by_cases he : r + 1 = j.val
    · rw [ite_eq_left he, ite_eq_left (by omega), he]
    · rw [ite_eq_right he]
      by_cases hj : j.val ≤ r
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]
  have hinit : (BatchIterations.algorithm p).initial j = st 0 := by
    change (⟨0, p.x0, p.x0, j⟩ : BatchIterations.State p) = ⟨0, X 0, if j.val ≤ 0 then X j.val else p.x0, j⟩
    by_cases hj : j.val ≤ 0
    · have he : j.val = 0 := by omega
      rw [ite_eq_left hj, he]
      rfl
    · rw [ite_eq_right hj]
      rfl
  have hadvance : ∀ K r, StochasticGradient.advance step K r (st r) = st (r + K) := by
    intro K
    induction K with
    | zero => intro r; rfl
    | succ K ih =>
      intro r
      change StochasticGradient.advance step K (r + 1) (step r (st r)) = _
      rw [hstep, ih]
      congr 1
      omega
  erw [executeCounted_advance _ _ _ _ _ (fun k query => estimator (B k) g query.2 (ξ k))
    (fun _ _ => rfl)]
  change ((StochasticGradient.advance step (p.N + 1) 0
    ((BatchIterations.algorithm p).initial j)).selected, p.N + 1) = _
  rw [hinit, hadvance]
  change ((if j.val ≤ 0 + (p.N + 1) then X j.val else p.x0), p.N + 1) = _
  rw [ite_eq_left (by omega)]


end OracleTemplate.MaleniaUniform
