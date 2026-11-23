import LongTails.Proofs.ContaminatedSeedSelection
import LongTails.Proofs.ContaminatedValidationOutput
import LongTails.Proofs.ContaminatedParallelBudget

namespace LongTails.Proofs.ContaminatedParallelAccuracy

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution height iterations)
open ContaminatedParallelHistory ContaminatedParallelFailures ContaminatedTrainingGeometry ContaminatedParallelSampling
open ContaminatedTrainingHistory ContaminatedValidationCalendar ContaminatedValidationState ContaminatedSeedSelection
open ContaminatedValidationOutput ContaminatedTrainingProbability
open scoped Classical
variable {p : Params}

noncomputable def out (D : Data p) (a : Seed p × Samples p) :=
  output p (run D a.2 a.1 (operations p a.1).length)

lemma measurable_out (D : Data p) : Measurable (out D) := by
  apply measurable_from_prod_countable_right
  intro z
  have h := (measurable_state p D.g (fun i => (D.clean i).measurable) (ops p z) (operations p z).length).best
  exact (h.mono (past_le p _) le_rfl).fst

lemma validated_precision (p : Params) {N : ℕ} (u) (xs : List (Fin N)) {i : ℕ} (hi : i < xs.length) :
    (atOp (validationOps (height (network p)) u xs) i).precision p = 2*confidence p := by
  induction xs generalizing u i with
  | nil => simp at hi
  | cons j xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih _ (Nat.lt_of_succ_lt_succ hi)

noncomputable def badValidation (D : Data p) (z : Seed p) : Set (Samples p) :=
  ⋃ i : Fin (candidateIndices p z).length, bad D (ops p z) (count p+i)

lemma badValidation_measurable (D : Data p) (z : Seed p) : MeasurableSet (badValidation D z) :=
  MeasurableSet.iUnion (fun i => past_le p _ _ (bad_measurable D _ (count p+i)))

lemma validation_probability (D : Data p) (z : Seed p) :
    (D.P : Measure _).real (badValidation D z) ≤ 2*(confidence p:ℝ)*Real.exp (-(2*(confidence p:ℝ))) := by
  apply (measureReal_iUnion_fintype_le _).trans
  have h (i : Fin (candidateIndices p z).length) := unweighted D (ops p z) (count p+i)
  have h₂ (i : Fin (candidateIndices p z).length) :
      (D.P : Measure _).real (bad D (ops p z) (count p+i)) ≤ 2*Real.exp (-(2*(confidence p:ℝ))) := by
    simpa only [suffix p z i i.isLt,validated_precision p _ _ i.isLt,Nat.cast_mul,Nat.cast_ofNat] using h i
  apply (Finset.sum_le_sum (fun i _ => h₂ i)).trans
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hc := (indices_length p z).trans (min_le_right _ _)
  have hc' : ((candidateIndices p z).length:ℝ) ≤ confidence p := by exact_mod_cast hc
  nlinarith only [mul_le_mul_of_nonneg_right hc' (Real.exp_pos (-(2*(confidence p:ℝ)))).le]

lemma success (D : Data p) (s : Samples p) (z : Seed p) (hg : s ∉ badValidation D z)
    (hj : ∃ i, ‖D.G (point D s (z i))‖ ≤ p.ε/2) : ‖D.G (out D (z,s))‖ ≤ p.ε := by
  let xs := candidateIndices p z
  have ht := after_training D s z
  obtain ⟨ha,hb⟩ := untouched D s (count p)
  have he : (operations p z).length = count p+xs.length := by simp [operations,count,xs,validate_length]
  have hh := validate D s z xs none (count p) (congrArg Model.training ht) (suffix p z)
    (fun i hi hm => hg (Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hm⟩)) (indices_sorted p z)
    (by rw [ht]; exact ha) (by rw [ht,hb]; norm_num)
    (by obtain ⟨i,hi⟩ := hj; exact Or.inr ⟨z i,draw_mem p z i,hi⟩)
  simpa only [out,he,output] using hh

lemma slices {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [MeasurableSingletonClass A]
    (E : Set (A × B)) (h : ∀ a, MeasurableSet {b | (a,b) ∈ E}) : MeasurableSet E := by
  have he : E = ⋃ a, ({a} : Set A) ×ˢ {b | (a,b) ∈ E} := by ext w; simp
  rw [he]
  exact MeasurableSet.iUnion (fun a => (measurableSet_singleton a).prod (h a))

lemma prob (D : Data p) :
    ((seeds p).prod (D.P : Measure _)) {w | p.ε < ‖D.G (out D w)‖} ≤ ENNReal.ofReal p.failure := by
  classical
  let P : Measure (Samples p) := D.P
  let Z := seeds p
  let q := (confidence p:ℝ)
  let a := Real.exp (-q)
  let c := 2*q*Real.exp (-(2*q))
  let E : Set (Seed p × Samples p) := Prod.snd ⁻¹' {s | 1 ≤ loss D s}
  let M : Set (Seed p × Samples p) := {w | loss D w.2 < 1 ∧ ∀ i, p.ε/2 < ‖D.G (point D w.2 (w.1 i))‖}
  let V : Set (Seed p × Samples p) := {w | w.2 ∈ badValidation D w.1}
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hc : 0 ≤ c := by dsimp [c,q]; positivity
  have hE : (Z.prod P) E ≤ ENNReal.ofReal a := by
    rw [show E = Set.univ ×ˢ {s | 1 ≤ loss D s} by ext w; simp [E],Measure.prod_prod,measure_univ,one_mul]
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (training_tail D)
  have hM : (Z.prod P) M ≤ ENNReal.ofReal a := by
    have hm : MeasurableSet M := by
      apply slices
      intro z
      change MeasurableSet ({s | loss D s < 1} ∩ {s | ∀ i, p.ε/2 < ‖D.G (point D s (z i))‖})
      apply (measurableSet_lt (loss_measurable D) measurable_const).inter
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const ((D.measurable_G.comp (point_measurable D (z i))).norm))
    rw [Measure.prod_apply_symm hm]
    apply (lintegral_mono (g := fun _ => ENNReal.ofReal a) ?_).trans_eq (by simp)
    intro s
    by_cases hl : loss D s < 1
    · simpa only [M,Set.preimage_ofPred_eq,hl,true_and] using missed D s hl
    · simp [M,hl]
  have hV : (Z.prod P) V ≤ ENNReal.ofReal c := by
    rw [Measure.prod_apply (slices V (fun z => badValidation_measurable D z))]
    apply (lintegral_mono (g := fun _ => ENNReal.ofReal c) ?_).trans_eq (by simp)
    intro z
    change P (badValidation D z) ≤ _
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (validation_probability D z)
  have hsub : {w | p.ε < ‖D.G (out D w)‖} ⊆ (E ∪ M) ∪ V := by
    rintro ⟨z,s⟩ h
    by_cases he : 1 ≤ loss D s
    · exact Or.inl (Or.inl he)
    by_cases hv : s ∈ badValidation D z
    · exact Or.inr hv
    left; right
    refine ⟨lt_of_not_ge he,fun i => lt_of_not_ge (fun hi => ?_)⟩
    exact (not_lt_of_ge (success D s z hv ⟨i,hi⟩)) h
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add (measure_union_le _ _) hV).trans
  apply (add_le_add (add_le_add hE hM) (le_refl (ENNReal.ofReal c))).trans
  rw [← ENNReal.ofReal_add ha ha,← ENNReal.ofReal_add (add_nonneg ha ha) hc]
  exact ENNReal.ofReal_le_ofReal (confidence_budget p D.valid.2.2.2.2.2.1)

end LongTails.Proofs.ContaminatedParallelAccuracy
