import LongTails.Proofs.AbcHardOracle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardContinuity

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask LongTails.Proofs.AbcChainProperties
open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.AbcHardFunction
open LongTails.Proofs.AbcHardGeometry LongTails.Proofs.AbcHardOracle

variable {d n : ℕ}

lemma trunc_sub (m : ℕ) (u v : Chain n) : trunc m u - trunc m v = trunc m (u - v) := by
  ext i; simp only [PiLp.sub_apply, trunc_apply]; split_ifs <;> simp

lemma trunc_continuous (m : ℕ) : Continuous (trunc (n := n) m) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm, trunc_sub, NNReal.coe_one, one_mul]
  exact trunc_norm_le m _

lemma field_continuous : Continuous (field (n := n)) := by
  apply LipschitzWith.continuous (K := 1000)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  simpa using field_lipschitz u v

lemma knownField_sub_norm (m : ℕ) (u v : Chain n) :
    ‖knownField m u - knownField m v‖ ≤ ‖field u - field v‖ := by
  have h : ‖knownField m u - knownField m v‖ ^ 2 ≤ ‖field u - field v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro k _
    simp only [PiLp.sub_apply, knownField_apply]
    split_ifs
    · exact le_rfl
    · simp [sq_nonneg]
  nlinarith [norm_nonneg (knownField m u - knownField m v), norm_nonneg (field u - field v)]

lemma knownField_continuous (m : ℕ) : Continuous (knownField (n := n) m) := by
  apply LipschitzWith.continuous (K := 1000)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  have := (knownField_sub_norm m u v).trans (field_lipschitz u v)
  simpa using this

lemma chain_continuous : Continuous (chain (n := n)) :=
  continuous_iff_continuousAt.mpr (fun u => (chain_hasGradientAt u).differentiableAt.continuousAt)

lemma weight_continuous (w : ℝ) (f g : Space d → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => weight w (f z) (g z)) := by
  unfold weight rampSlope
  fun_prop

lemma wallFn_continuous (n : ℕ) : Continuous (wallFn (d := d) n) := by
  unfold wallFn; fun_prop

lemma wallGrad_continuous (n : ℕ) : Continuous (wallGrad (d := d) n) := by
  unfold wallGrad; fun_prop

lemma knownGrad_continuous (π : Fin (n + 1) ↪ Fin d) (m : ℕ) :
    Continuous (knownGrad π m) := by
  have hc : Continuous (fun w => chain (trunc m (sel π w))) :=
    chain_continuous.comp ((trunc_continuous m).comp (sel π).continuous)
  have hw := weight_continuous (width n) _ _ hc (wallFn_continuous n)
  have hk : Continuous (fun w => (sel π).adjoint (knownField m (sel π w))) :=
    (sel π).adjoint.continuous.comp ((knownField_continuous m).comp (sel π).continuous)
  unfold knownGrad
  exact (hw.smul hk).add ((continuous_const.sub hw).smul (wallGrad_continuous n))

lemma hardGrad_continuous (π : Fin (n + 1) ↪ Fin d) : Continuous (hardGrad π) := by
  apply LipschitzWith.continuous (K := 1024)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  simpa using hardGrad_lipschitz π x y

lemma toUnit_continuous (S : Scale) (x0 : Space d) : Continuous (toUnit S x0) := by
  unfold toUnit; fun_prop

lemma knownPart_continuous (S : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 : Space d) :
    Continuous (knownPart S π m x0) := by
  unfold knownPart
  exact ((knownGrad_continuous π m).comp (toUnit_continuous S x0)).const_smul (S.a / S.lam)

lemma objGrad_continuous (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Continuous (objGrad S π x0) := by
  unfold objGrad
  exact ((hardGrad_continuous π).comp (toUnit_continuous S x0)).const_smul (S.a / S.lam)

instance : MeasurableSup₂ ℕ := ⟨measurable_of_countable _⟩

lemma stage_measurable (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (fun x => stage (sel π (toUnit S x0 x))) := by
  have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  have he : (fun x => stage (sel π (toUnit S x0 x))) = Finset.univ.sup' hne
      (fun (i : Fin (n + 1)) (x : Space d) =>
        if 1 / 4 < |sel π (toUnit S x0 x) i| then i.val + 1 else 0) := by
    funext x
    rw [Finset.sup'_apply, Finset.sup'_eq_sup]
    rfl
  rw [he]
  apply Finset.measurable_sup'
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_lt measurable_const
  have hc : Continuous (fun x => |sel π (toUnit S x0 x) i|) := by
    have : Continuous (fun x => sel π (toUnit S x0 x)) :=
      (sel π).continuous.comp (toUnit_continuous S x0)
    exact continuous_abs.comp ((PiLp.continuous_apply 2 _ i).comp this)
  exact hc.measurable

lemma reply_measurable (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (Function.uncurry (reply S qf π x0)) := by
  let G : (Space d × ℝ) × ℕ → Space d := fun p =>
    knownPart S π p.2 x0 p.1.1 +
      coin (qf p.2) p.1.2 • (objGrad S π x0 p.1.1 - knownPart S π p.2 x0 p.1.1)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro m
    have hk : Measurable (fun z : Space d × ℝ => knownPart S π m x0 z.1) :=
      (knownPart_continuous S π m x0).measurable.comp measurable_fst
    have ho : Measurable (fun z : Space d × ℝ => objGrad S π x0 z.1) :=
      (objGrad_continuous S π x0).measurable.comp measurable_fst
    have hc : Measurable (fun z : Space d × ℝ => coin (qf m) z.2) :=
      (coin_measurable (qf m)).comp measurable_snd
    exact hk.add (hc.smul (ho.sub hk))
  have he : Function.uncurry (reply S qf π x0) =
      G ∘ (fun z : Space d × ℝ => (z, stage (sel π (toUnit S x0 z.1)))) := by
    funext z
    rfl
  rw [he]
  exact hG.comp (measurable_id.prodMk ((stage_measurable S π x0).comp measurable_fst))

end LongTails.Proofs.AbcHardContinuity
