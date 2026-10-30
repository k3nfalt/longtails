import LongTails.Proofs.NonsmoothHiddenGlobal
import LongTails.Proofs.NonsmoothHiddenExpectation
import LongTails.Proofs.AdaptiveIID

open Set Metric MeasureTheory

namespace OracleTemplate.NonsmoothHidden

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]

lemma localOutput_joint_measurable {oracle : E → Ω → E}
    (hom : Measurable (Function.uncurry oracle)) (r D : ℝ) (N : ℕ) :
    Measurable (Function.uncurry (localOutput oracle r D N)) := by
  exact ((localRun_measurable hom r D N 0).comp
    ((measurable_fst.prodMk (measurable_fst.prodMk measurable_fst)).prodMk measurable_snd)).fst

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma epochRun_mem (oracle : E → Ω → E) (r D : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (N K : ℕ) {b : E} (hb : ‖b‖ ≤ R) (ξ : ℕ → Ω) :
    ‖epochRun oracle r D R N K b ξ‖ ≤ R := by
  induction K generalizing b ξ with
  | zero => exact hb
  | succ K ih => exact ih (restartOutside_mem hR _) _

lemma epochRun_measurable {oracle : E → Ω → E}
    (hom : Measurable (Function.uncurry oracle)) (r D R : ℝ) (N K : ℕ) :
    Measurable (Function.uncurry (epochRun oracle r D R N K)) := by
  induction K with
  | zero => exact measurable_fst
  | succ K ih =>
    have hb : Measurable (fun v : E × (ℕ → Ω) => (v.1, fun i : Fin N => v.2 i)) := by fun_prop
    have hn := (restartOutside_measurable R).comp ((localOutput_joint_measurable hom r D N).comp hb)
    exact ih.comp (hn.prodMk (by fun_prop))

lemma epochRun_integrable {oracle : E → Ω → E}
    (hom : Measurable (Function.uncurry oracle)) (r D : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (N K : ℕ) {F : E → ℝ} (hF : Measurable F) {fstar a C : ℝ}
    (hbound : ∀ x, ‖x‖ ≤ R → |F x - fstar - a| ≤ C)
    {b : E} (hb : ‖b‖ ≤ R) (p : Measure Ω) [IsProbabilityMeasure p] :
    Integrable (fun ξ => F (epochRun oracle r D R N K b ξ) - fstar - a)
      (Measure.infinitePi fun _ : ℕ => p) := by
  have hm := (epochRun_measurable hom r D R N K).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ξ : ℕ → Ω => (b, ξ)))
  apply Integrable.of_bound (((hF.comp hm).sub measurable_const).sub measurable_const).aestronglyMeasurable C
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs]
  exact hbound _ (epochRun_mem oracle r D hR N K hb ξ)

lemma epochRun_contraction {oracle : E → Ω → E}
    (hom : Measurable (Function.uncurry oracle)) (r D : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (N K : ℕ) {F : E → ℝ} (hF : Measurable F) {fstar a C q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ x, ‖x‖ ≤ R → |F x - fstar - a| ≤ C)
    (p : Measure Ω) [IsProbabilityMeasure p]
    (hstep : ∀ b, ‖b‖ ≤ R →
      (∫ ξ, F (restartOutside R (localOutput oracle r D N b ξ)) - fstar - a
        ∂Measure.pi (fun _ : Fin N => p)) ≤ q * (F b - fstar - a))
    {b : E} (hb : ‖b‖ ≤ R) :
    (∫ ξ, F (epochRun oracle r D R N K b ξ) - fstar - a
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ q ^ K * (F b - fstar - a) := by
  induction K generalizing b with
  | zero => simp [epochRun]
  | succ K ih =>
    let Q := Measure.infinitePi (fun _ : ℕ => p)
    let P := Measure.pi (fun _ : Fin N => p)
    let next := fun ξ => restartOutside R (localOutput oracle r D N b ξ)
    let V := fun z : (Fin N → Ω) × (ℕ → Ω) =>
      F (epochRun oracle r D R N K (next z.1) z.2) - fstar - a
    have hn : Measurable next := (restartOutside_measurable R).comp
      ((localOutput_joint_measurable hom r D N).comp measurable_prodMk_left)
    have hm : Measurable V := by
      exact ((hF.comp ((epochRun_measurable hom r D R N K).comp
        ((hn.comp measurable_fst).prodMk measurable_snd))).sub measurable_const).sub measurable_const
    have hi : Integrable V (P.prod Q) := by
      apply Integrable.of_bound hm.aestronglyMeasurable C
      filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact hbound _ (epochRun_mem oracle r D hR N K (restartOutside_mem hR _) _)
    have hni : Integrable (fun ξ => F (next ξ) - fstar - a) P := by
      apply Integrable.of_bound (((hF.comp hn).sub measurable_const).sub measurable_const).aestronglyMeasurable C
      filter_upwards [] with ξ
      rw [Real.norm_eq_abs]
      exact hbound _ (restartOutside_mem hR _)
    have hs := StochasticGeneralized.splitStream_preserving p N
    calc
      _ = ∫ z, V z ∂P.prod Q := hs.integral_comp' V
      _ = ∫ ξ, ∫ η, V (ξ, η) ∂Q ∂P := integral_prod V hi
      _ ≤ ∫ ξ, q ^ K * (F (next ξ) - fstar - a) ∂P := by
        apply integral_mono hi.integral_prod_left (hni.const_mul _)
        intro ξ
        exact ih (restartOutside_mem hR (localOutput oracle r D N b ξ))
      _ = q ^ K * (∫ ξ, F (next ξ) - fstar - a ∂P) := integral_const_mul _ _
      _ ≤ q ^ K * (q * (F b - fstar - a)) :=
        mul_le_mul_of_nonneg_left (hstep b hb) (pow_nonneg hq K)
      _ = _ := by rw [pow_succ]; ring

lemma restart_local_contraction {oracle : E → Ω → E}
    (hom : Measurable (Function.uncurry oracle)) (r D : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (N : ℕ) {F H : E → ℝ} {c : E ≃ₜ E} (hF : Measurable F)
    (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H)
    (hbarrier : ∀ y, ‖y‖ = R → F 0 ≤ F y) {xstar b : E}
    (hstar : IsMinOn F univ xstar) (hxs : ‖xstar‖ ≤ R)
    {a C t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ x, ‖x‖ ≤ R → |F x - F xstar - a| ≤ C)
    (p : Measure Ω) [IsProbabilityMeasure p]
    (hi : Integrable (fun ξ => F (localOutput oracle r D N b ξ) -
      F (hiddenSegment c b xstar t)) (Measure.pi fun _ : Fin N => p))
    (hloc : (∫ ξ, F (localOutput oracle r D N b ξ) - F (hiddenSegment c b xstar t)
      ∂Measure.pi (fun _ : Fin N => p)) ≤ t * a) :
    (∫ ξ, F (restartOutside R (localOutput oracle r D N b ξ)) - F xstar - a
      ∂Measure.pi (fun _ : Fin N => p)) ≤ (1 - t) * (F b - F xstar - a) := by
  have hm : Measurable (fun ξ : Fin N → Ω => restartOutside R (localOutput oracle r D N b ξ)) := (restartOutside_measurable R).comp
    ((localOutput_joint_measurable hom r D N).comp measurable_prodMk_left)
  have hri : Integrable (fun ξ => F (restartOutside R (localOutput oracle r D N b ξ)) -
      F xstar - a) (Measure.pi fun _ : Fin N => p) := by
    apply Integrable.of_bound (((hF.comp hm).sub measurable_const).sub measurable_const).aestronglyMeasurable C
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs]
    exact hbound _ (restartOutside_mem hR _)
  have hv := hiddenSegment_contraction heq hH b xstar ht
  have hp : (∫ ξ, F (restartOutside R (localOutput oracle r D N b ξ)) - F xstar - a
      ∂Measure.pi (fun _ : Fin N => p)) ≤
      (∫ ξ, (F (localOutput oracle r D N b ξ) - F (hiddenSegment c b xstar t)) +
        (F (hiddenSegment c b xstar t) - F xstar - a) ∂Measure.pi (fun _ : Fin N => p)) := by
    apply integral_mono hri (hi.add (integrable_const _))
    intro ξ
    have hh := restartOutside_value heq hH hbarrier hstar hxs (localOutput oracle r D N b ξ)
    dsimp only [Pi.add_apply]
    linarith
  rw [integral_add hi (integrable_const _)] at hp
  simp only [integral_const, probReal_univ, one_smul] at hp
  nlinarith

end OracleTemplate.NonsmoothHidden
