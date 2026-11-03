import LongTails.Proofs.TailObliviousProcess

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

set_option maxHeartbeats 2000000

namespace LongTails.Proofs.TailObliviousAccuracy

open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open TailObliviousAnchoring TailObliviousStage TailObliviousProcess
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {d : Public} {Ω : Type*} [MeasurableSpace Ω]

abbrev Block (k : ℕ) (Ω : Type*) := Fin (innerSteps k) → Fin 2 → Ω

noncomputable def blockLaw (p : ProbabilityMeasure Ω) (k : ℕ) : Measure (Block k Ω) :=
  Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)

instance (p : ProbabilityMeasure Ω) (k : ℕ) : IsProbabilityMeasure (blockLaw p k) := by
  unfold blockLaw; infer_instance

noncomputable def streamLaw (p : ProbabilityMeasure Ω) (k : ℕ) : Measure (ℕ → Block k Ω) :=
  Measure.infinitePi fun _ : ℕ => blockLaw p k

instance (p : ProbabilityMeasure Ω) (k : ℕ) : IsProbabilityMeasure (streamLaw p k) := by
  unfold streamLaw; infer_instance

lemma prefix_next_preserving {B : Type*} [MeasurableSpace B]
    (Q : Measure B) [IsProbabilityMeasure Q] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → B => ((fun i : Fin n => ξ i), ξ n))
      (Measure.infinitePi fun _ : ℕ => Q) ((Measure.pi fun _ : Fin n => Q).prod Q) := by
  have he : MeasurePreserving (fun ξ : ℕ → B => ξ 0) (Measure.infinitePi fun _ : ℕ => Q) Q :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin n => Q)).prod he
  simpa [Function.comp_def, OracleTemplate.StochasticGeneralized.splitStream] using
    hp.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving Q n)

noncomputable def epochError {F : d.E → d.E} (hF : Problem d F) (α : ℝ)
    (g : d.E → Ω → d.E) (k j : ℕ) (ξ : ℕ → Block k Ω) : ℝ :=
  let s := epochState d g k j ξ
  energy hF α k (s.1, s.2.1, (epochAdvance d g k s (ξ j)).2.2)

omit [MeasurableSpace Ω] in
lemma epochError_eq {F : d.E → d.E} (hF : Problem d F) (α : ℝ)
    (g : d.E → Ω → d.E) (k j : ℕ) (ξ : ℕ → Block k Ω) :
    epochError hF α g k j ξ = strength d k j ^ α *
      ‖(epochState d g k (j + 1) ξ).2.2 - root hF k j (epochState d g k j ξ).2.1‖ ^ α := by
  dsimp only [epochError, energy]
  rw [epochState_stage, ← epochState_succ]

lemma epoch_error_bound {F : d.E → d.E} (hF : Problem d F)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α R : ℝ) (hσ : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (xstar : d.E) (hstar : F xstar = 0) (hR : ‖d.x0 - xstar‖ ≤ R) (k j : ℕ) :
    Integrable (epochError hF α g k j) (streamLaw p k) ∧
    (∫ ξ, epochError hF α g k j ξ ∂streamLaw p k) ≤ envelope d R σ α k := by
  let Q : Measure (Block k Ω) := blockLaw p k
  let state := fun ξ : Fin j → Block k Ω => iterateSamples (epochAdvance d g k) j
    (0, strength d k 0 • d.x0, d.x0) ξ
  let Fn : (Fin j → Block k Ω) × Block k Ω → ℝ := fun w =>
    energy hF α k ((state w.1).1, (state w.1).2.1, (epochAdvance d g k (state w.1) w.2).2.2)
  let G : (Fin j → Block k Ω) → ℝ := fun ξ =>
    (1 / 18) * energy hF α k (state ξ) + 18 * floorTerm σ α k
  have hstate : Measurable state :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (epochAdvance_measurable g hg.measurable k) j).comp measurable_prodMk_left
  have hnew := (epochAdvance_measurable g hg.measurable k).comp
    ((hstate.comp measurable_fst).prodMk measurable_snd)
  have hFn : Measurable Fn := (energy_measurable hF α k).comp
    ((hstate.comp measurable_fst).fst.prodMk
      ((hstate.comp measurable_fst).snd.fst.prodMk hnew.snd.snd))
  have hi := epoch_energy_bound hF p g σ α R hσ hg hα1 hα2 xstar hstar hR k j
  have hG : Integrable G (Measure.pi fun _ : Fin j => Q) :=
    (hi.1.const_mul _).add (integrable_const _)
  have hfiber (ξ : Fin j → Block k Ω) := epoch_output_moment hF p g σ α hσ hg hα1 hα2 k (state ξ)
  have hfiber' (ξ : Fin j → Block k Ω) :
      Integrable (fun w => Fn (ξ, w)) Q ∧ (∫ w, Fn (ξ, w) ∂Q) ≤ G ξ := by
    have h := hfiber ξ
    have heq : (fun w => Fn (ξ, w)) = fun w => strength d k (state ξ).1 ^ α *
        ‖(epochAdvance d g k (state ξ) w).2.2 - root hF k (state ξ).1 (state ξ).2.1‖ ^ α := rfl
    rw [heq]
    exact h
  have hp := OracleTemplate.StochasticConvexQuadratic.nonnegative_product_control hFn
    (fun w => energy_nonneg hF α k _) (fun ξ => (hfiber' ξ).1) hG (fun ξ => (hfiber' ξ).2)
  have hpres := prefix_next_preserving Q j
  refine ⟨hpres.integrable_comp_of_integrable hp.1, ?_⟩
  have hchange : (∫ ξ, epochError hF α g k j ξ ∂streamLaw p k) =
      ∫ w, Fn w ∂(Measure.pi fun _ : Fin j => Q).prod Q := by
    have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Q)
      hpres.measurable.aemeasurable hFn.aestronglyMeasurable
    rw [hpres.map_eq] at he
    exact he.symm
  rw [hchange]
  apply hp.2.trans
  dsimp only [G]
  have h1 : Integrable (fun x => 1 / 18 * energy hF α k (state x))
      (Measure.pi fun _ : Fin j => Q) := hi.1.const_mul _
  rw [integral_add h1 (integrable_const _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hf := floorTerm_nonneg σ α hσ k
  have hA : 0 ≤ (2 * strength d k 0 * R) ^ α := by
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
    have := strength_pos d hF.pos k 0
    positivity
  have h2 : (∫ x, energy hF α k (state x) ∂Measure.pi fun _ : Fin j => Q) ≤
      envelope d R σ α k := hi.2
  unfold envelope at h2 ⊢
  linarith

omit [MeasurableSpace Ω] in
lemma terminal_residual {F : d.E → d.E} (hF : Problem d F) (R : ℝ)
    (g : d.E → Ω → d.E) (k : ℕ) (xstar : d.E) (hstar : F xstar = 0)
    (hR : ‖d.x0 - xstar‖ ≤ R) (ξ : ℕ → Block k Ω) :
    ‖F (epochOutput d g k ξ)‖ ≤
      ∑ j ∈ Finset.range (k + 1), 4 * (strength d k j *
        ‖(epochState d g k (j + 1) ξ).2.2 - root hF k j (epochState d g k j ξ).2.1‖) +
      2 * strength d k 0 * R := by
  let b := fun j => (epochState d g k j ξ).2.1
  let z := fun j => (epochState d g k (j + 1) ξ).2.2
  let u := fun j => root hF k j (b j)
  have hb (j : ℕ) : b (j + 1) = b j + strength d k j • z j := epochState_anchor_succ g k j ξ
  have hu (j : ℕ) : F (u j) + strength d k j • u j - b j = 0 := root_equation hF k j (b j)
  have hm (j : ℕ) : ‖u j - u (j + 1)‖ ≤ ‖z j - u j‖ / 2 := by
    have hn := hu (j + 1)
    rw [strength_succ, hb] at hn
    exact doubled_anchor_root_movement F hF.mono (strength d k j) (strength_pos d hF.pos k j)
      (b j) (z j) (u j) (u (j + 1)) (hu j) hn
  have hc := correction_sum_bound (strength d k) b u z (strength_pos d hF.pos k 0).le
    (strength_zero_le d hF.pos k) (strength_succ d k) hb hm k
  have hf := residual_from_correction F d.L hF.lip (strength d k k) (strength d k 0)
    (strength_pos d hF.pos k 0).le (b k) (b 0) (u k) (z k) (hu k)
  have hb0 : b 0 = strength d k 0 • d.x0 := rfl
  rw [hb0] at hf hc
  have hu0 := root_equation hF k 0 (strength d k 0 • d.x0)
  have hd := initial_root_distance F hF.mono (strength d k 0) R (strength_pos d hF.pos k 0)
    d.x0 xstar _ hstar hR hu0
  have hrem := remove_initial_anchor F hF.mono (strength d k 0) R
    (strength_pos d hF.pos k 0).le d.x0 _ (z k) hu0 hd
  have ha0 : strength d k 0 ≤ d.L := strength_le d hF.pos k 0 (Nat.zero_le k)
  have hlast : strength d k k = d.L := strength_last d hF.pos k
  have hs : 0 ≤ ∑ j ∈ Finset.range k, strength d k j * ‖z j - u j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (strength_pos d hF.pos k j).le (norm_nonneg _))
  have hout : epochOutput d g k ξ = z k := rfl
  rw [hout, ← Finset.mul_sum, Finset.sum_range_succ, hlast]
  have hzk := norm_nonneg (z k - u k)
  nlinarith [mul_le_mul_of_nonneg_right ha0 hzk]

noncomputable def accuracyBound (d : Public) (R σ α : ℝ) (k : ℕ) : ℝ :=
  17 * ((k : ℝ) + 2) ^ α * envelope d R σ α k

lemma epoch_accuracy {F : d.E → d.E} (hF : Problem d F)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α R : ℝ) (hσ : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (xstar : d.E) (hstar : F xstar = 0) (hR : ‖d.x0 - xstar‖ ≤ R) (k : ℕ) :
    Measurable (epochOutput d g k (Ω := Ω)) ∧
    Integrable (fun ξ => ‖F (epochOutput d g k ξ)‖ ^ α) (streamLaw p k) ∧
    (∫ ξ, ‖F (epochOutput d g k ξ)‖ ^ α ∂streamLaw p k) ≤ accuracyBound d R σ α k := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hout : Measurable (epochOutput d g k (Ω := Ω)) :=
    (epochState_measurable g hg.measurable k (k + 1)).snd.snd
  refine ⟨hout, ?_⟩
  have hFc : Continuous F := (LipschitzWith.of_dist_le_mul (K := ⟨d.L, hF.pos.le⟩) (by
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact hF.lip x y)).continuous
  let S := k + 2
  let e := fun (ξ : ℕ → Block k Ω) (j : ℕ) => 4 * (strength d k j *
    ‖(epochState d g k (j + 1) ξ).2.2 - root hF k j (epochState d g k j ξ).2.1‖)
  let G := fun ξ : ℕ → Block k Ω => ((k : ℝ) + 2) ^ (α - 1) *
    (4 ^ α * ∑ j ∈ Finset.range (k + 1), epochError hF α g k j ξ +
      (2 * strength d k 0 * R) ^ α)
  have he (j : ℕ) := epoch_error_bound hF p g σ α R hσ hg hα1 hα2 xstar hstar hR k j
  have hsum : Integrable (fun ξ => ∑ j ∈ Finset.range (k + 1), epochError hF α g k j ξ)
      (streamLaw p k) := integrable_finsetSum _ (fun j _ => (he j).1)
  have hGi : Integrable G (streamLaw p k) :=
    ((hsum.const_mul _).add (integrable_const _)).const_mul _
  have hbound (ξ : ℕ → Block k Ω) : ‖F (epochOutput d g k ξ)‖ ^ α ≤ G ξ := by
    have ht := terminal_residual hF R g k xstar hstar hR ξ
    let f : ℕ → ℝ := fun j => if j < k + 1 then e ξ j else 2 * strength d k 0 * R
    have hf0 : ∀ j ∈ Finset.range (k + 2), 0 ≤ f j := by
      intro j _
      dsimp only [f, e]
      split_ifs
      · exact mul_nonneg (by norm_num) (mul_nonneg (strength_pos d hF.pos k j).le (norm_nonneg _))
      · have := strength_pos d hF.pos k 0; positivity
    have hsplit : ∑ j ∈ Finset.range (k + 2), f j =
        ∑ j ∈ Finset.range (k + 1), e ξ j + 2 * strength d k 0 * R := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        dsimp only [f]
        simp only [show j < k + 1 from Finset.mem_range.mp hj, ↓reduceIte]
      · dsimp only [f]
        simp only [show ¬(k + 1 < k + 1) by omega, ↓reduceIte]
    have hsplit2 : ∑ j ∈ Finset.range (k + 2), f j ^ α =
        ∑ j ∈ Finset.range (k + 1), e ξ j ^ α + (2 * strength d k 0 * R) ^ α := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        dsimp only [f]
        simp only [show j < k + 1 from Finset.mem_range.mp hj, ↓reduceIte]
      · dsimp only [f]
        simp only [show ¬(k + 1 < k + 1) by omega, ↓reduceIte]
    have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.range (k + 2))
      (f := f) (p := α) hα1.le hf0
    rw [hsplit, hsplit2, Finset.card_range] at hpm
    have hepow : ∑ j ∈ Finset.range (k + 1), e ξ j ^ α =
        4 ^ α * ∑ j ∈ Finset.range (k + 1), epochError hF α g k j ξ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [epochError_eq]
      dsimp only [e]
      rw [Real.mul_rpow (by norm_num) (mul_nonneg (strength_pos d hF.pos k j).le (norm_nonneg _)),
        Real.mul_rpow (strength_pos d hF.pos k j).le (norm_nonneg _)]
    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast, hepow] at hpm
    have hmono : ‖F (epochOutput d g k ξ)‖ ^ α ≤
        (∑ j ∈ Finset.range (k + 1), e ξ j + 2 * strength d k 0 * R) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) ht (by linarith)
    exact hmono.trans hpm
  have hFm : Measurable (fun ξ => ‖F (epochOutput d g k ξ)‖ ^ α) :=
    (hFc.measurable.comp hout).norm.pow_const α
  have hi : Integrable (fun ξ => ‖F (epochOutput d g k ξ)‖ ^ α) (streamLaw p k) :=
    hGi.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hbound ξ)
  refine ⟨hi, (integral_mono hi hGi hbound).trans ?_⟩
  dsimp only [G]
  rw [integral_const_mul, integral_add (hsum.const_mul _) (integrable_const _),
    integral_const_mul, integral_finsetSum _ (fun j _ => (he j).1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hs : (∑ j ∈ Finset.range (k + 1), ∫ ξ, epochError hF α g k j ξ ∂streamLaw p k) ≤
      ((k : ℝ) + 1) * envelope d R σ α k := by
    have := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun j _ => (he j).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one] using this
  have h4 : (4 : ℝ) ^ α ≤ 16 := by
    calc (4 : ℝ) ^ α ≤ 4 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2
      _ = 16 := by norm_num
  have hf := floorTerm_nonneg σ α hσ k
  have hA : 0 ≤ (2 * strength d k 0 * R) ^ α := by
    have := strength_pos d hF.pos k 0; positivity
  have hEnv : (2 * strength d k 0 * R) ^ α ≤ envelope d R σ α k := by
    unfold envelope; linarith
  have hEnv0 : 0 ≤ envelope d R σ α k := hA.trans hEnv
  have hk2 : (1 : ℝ) ≤ (k : ℝ) + 2 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hpow : ((k : ℝ) + 2) ^ α = ((k : ℝ) + 2) ^ (α - 1) * ((k : ℝ) + 2) := by
    rw [← Real.rpow_add_one (by linarith)]; congr 1; ring
  have hpos : 0 ≤ ((k : ℝ) + 2) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
  have hi4 : 0 ≤ (4 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (k + 1), ∫ ξ, epochError hF α g k j ξ ∂streamLaw p k :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun ξ => by
      rw [epochError_eq]
      exact mul_nonneg (Real.rpow_nonneg (strength_pos d hF.pos k j).le _)
        (Real.rpow_nonneg (norm_nonneg _) _)))
  have hinner : 4 ^ α * ∑ j ∈ Finset.range (k + 1), ∫ ξ, epochError hF α g k j ξ ∂streamLaw p k +
      (2 * strength d k 0 * R) ^ α ≤ 17 * ((k : ℝ) + 2) * envelope d R σ α k := by
    nlinarith [mul_le_mul h4 hs hsum0 (by norm_num)]
  unfold accuracyBound
  rw [hpow]
  calc ((k : ℝ) + 2) ^ (α - 1) * (4 ^ α * ∑ j ∈ Finset.range (k + 1),
        ∫ ξ, epochError hF α g k j ξ ∂streamLaw p k + (2 * strength d k 0 * R) ^ α)
      ≤ ((k : ℝ) + 2) ^ (α - 1) * (17 * ((k : ℝ) + 2) * envelope d R σ α k) :=
        mul_le_mul_of_nonneg_left hinner hpos
    _ = _ := by ring

end LongTails.Proofs.TailObliviousAccuracy
