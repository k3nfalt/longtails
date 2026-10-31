import LongTails.Template
import LongTails.Algorithms.FreyaRandomness
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.FreyaMoments

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaRandomness
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

theorem choice_row_uniform (j : ℕ) :
    HasLaw (fun row : ChoiceRow => row j) (PMF.uniformOfFintype (Fin (j + 1))).toMeasure
      (rowLaw : Measure ChoiceRow) := by
  refine ⟨(measurable_pi_apply j).aemeasurable, ?_⟩
  exact (measurePreserving_eval_infinitePi
    (fun j : ℕ => (PMF.uniformOfFintype (Fin (j + 1))).toMeasure) j).map_eq

theorem private_rows_iid :
    IID (fun k (tape : ℕ → ℕ → ChoiceRow) => tape (Nat.unpair k).1 (Nat.unpair k).2)
      (rowLaw : Measure ChoiceRow) (choiceTapeLaw : Measure (ℕ → ℕ → ChoiceRow)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (measurable_pi_apply (Nat.unpair k).2).comp
      (measurable_pi_apply (Nat.unpair k).1)
  · have hind := iIndepFun_uncurry_infinitePi'
      (X := fun (_ _ : ℕ) (row : ChoiceRow) => row)
      (fun (_ _ : ℕ) => (rowLaw : Measure ChoiceRow))
      (fun _ _ => measurable_id)
    have hinj : Function.Injective Nat.unpair :=
      (show Function.LeftInverse (fun p : ℕ × ℕ => Nat.pair p.1 p.2) Nat.unpair from
        fun k => Nat.pair_unpair k).injective
    exact hind.precomp hinj
  · intro k
    exact ((measurePreserving_eval_infinitePi
      (fun _ : ℕ => (rowLaw : Measure ChoiceRow)) (Nat.unpair k).2).comp
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (rowLaw : Measure ChoiceRow)))
        (Nat.unpair k).1)).map_eq

theorem fresh_assignments {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (history : ℕ → MeasurableSpace Ω) (remaining : ℕ → Ω → Finset ℕ)
    (rows : ℕ → Ω → ChoiceRow)
    (hhistory : ∀ k, history k ≤ ‹MeasurableSpace Ω›)
    (hremaining : ∀ k, Measurable[history k] (remaining k))
    (hmeasurable : ∀ k, Measurable (rows k))
    (hlaw : ∀ k, HasLaw (rows k) (rowLaw : Measure ChoiceRow) (P : Measure Ω))
    (hind : ∀ k, Indep (history k)
      (MeasurableSpace.comap (rows k) (inferInstance : MeasurableSpace ChoiceRow))
      (P : Measure Ω)) :
    FreshAssignments P history remaining (fun k ω =>
      (chooseRemaining (rows k ω) ((remaining k ω).sort (· ≤ ·))).getD 0) := by
  open scoped ENNReal in
    classical
    let g (s : Finset ℕ) (row : ChoiceRow) : ℕ :=
      (chooseRemaining row (s.sort (· ≤ ·))).getD 0
    have hg (s : Finset ℕ) : Measurable (g s) := by
      by_cases h : (s.sort (· ≤ ·)).length = 0
      · dsimp only [g]
        delta chooseRemaining
        simpa only [h, dite_true, Option.getD_none] using (measurable_const : Measurable (fun _ : ChoiceRow => (0 : ℕ)))
      · let a : Fin ((s.sort (· ≤ ·)).length - 1 + 1) → ℕ := fun i =>
          (s.sort (· ≤ ·)).get ⟨i.val, by have hi := i.isLt; omega⟩
        dsimp only [g]
        delta chooseRemaining
        simp only [h, dite_false, Option.getD_some]
        exact (measurable_of_countable a).comp (measurable_pi_apply _)
    have hprob (s : Finset ℕ) (hs : s.Nonempty) (j : ℕ) :
        (rowLaw : Measure ChoiceRow) {row | g s row = j} =
          if j ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
      let l := s.sort (· ≤ ·)
      have hlen : l.length = s.card := Finset.length_sort _
      have hpos : 0 < l.length := hlen ▸ Finset.card_pos.mpr hs
      have hn : l.length ≠ 0 := hpos.ne'
      have hnodup : l.Nodup := Finset.sort_nodup _ _
      by_cases hj : j ∈ s
      · have hjl : j ∈ l := (Finset.mem_sort (· ≤ ·)).mpr hj
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hjl
        let a : Fin (l.length - 1 + 1) := ⟨i.val, by have := i.isLt; omega⟩
        have he : {row : ChoiceRow | g s row = j} = {row | row (l.length - 1) = a} := by
          ext row
          change (chooseRemaining row l).getD 0 = j ↔ row (l.length - 1) = a
          delta chooseRemaining
          simp only [hn, dite_false, Option.getD_some]
          rw [← hi, hnodup.get_inj_iff]
          constructor <;> intro h <;> apply Fin.ext
          · exact congrArg (fun z : Fin l.length => z.val) h
          · exact congrArg (fun z : Fin (l.length - 1 + 1) => z.val) h
        have heval := (choice_row_uniform (l.length - 1)).measure_eq
          (p := fun z => z = a) (measurableSet_singleton a)
        rw [he, heval]
        simp [hj, PMF.uniformOfFintype_apply,
          show l.length - 1 + 1 = s.card by omega]
      · have he : {row : ChoiceRow | g s row = j} = ∅ := by
          ext row
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          have hmem : g s row ∈ s := by
            apply (Finset.mem_sort (· ≤ ·)).mp
            change (chooseRemaining row l).getD 0 ∈ l
            delta chooseRemaining
            simp only [hn, dite_false, Option.getD_some]
            exact List.get_mem _ _
          exact hj (h ▸ hmem)
        simp [he, hj]
    intro k
    have hr : Measurable (remaining k) := (hremaining k).mono (hhistory k) le_rfl
    have hgm : Measurable (fun a : Finset ℕ × ChoiceRow => g a.1 a.2) :=
      measurable_from_prod_countable_right hg
    refine ⟨hhistory k, hremaining k, hgm.comp (hr.prodMk (hmeasurable k)), ?_⟩
    intro E hE j
    let A (s : Finset ℕ) := E ∩ {ω | remaining k ω = s}
    have hA0 (s : Finset ℕ) : MeasurableSet[history k] (A s) :=
      hE.inter ((hremaining k) (measurableSet_singleton s))
    have hA (s : Finset ℕ) : MeasurableSet (A s) := (hhistory k) _ (hA0 s)
    have hdis : Pairwise (fun s t : Finset ℕ => Disjoint (A s) (A t)) := by
      intro s t hst
      rw [Set.disjoint_left]
      intro ω hs ht
      exact hst (hs.2.symm.trans ht.2)
    have hcover : E = ⋃ s, A s := by
      ext ω
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨remaining k ω, h, rfl⟩
      · rintro ⟨s, h, heq⟩
        exact h
    rw [hcover, lintegral_iUnion hA hdis, lintegral_iUnion hA hdis]
    apply tsum_congr
    intro s
    have hleft := setLIntegral_congr_fun (μ := (P : Measure Ω)) (hA s)
      (f := fun ω => if (remaining k ω).Nonempty ∧ g (remaining k ω) (rows k ω) = j then (1 : ℝ≥0∞) else 0)
      (g := fun ω => if s.Nonempty ∧ g s (rows k ω) = j then (1 : ℝ≥0∞) else 0)
      (fun ω hω => by dsimp only; rw [hω.2])
    have hright := setLIntegral_congr_fun (μ := (P : Measure Ω)) (hA s)
      (f := fun ω => if j ∈ remaining k ω then ((remaining k ω).card : ℝ≥0∞)⁻¹ else 0)
      (g := fun _ => if j ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0)
      (fun ω hω => by dsimp only; rw [hω.2])
    change (∫⁻ ω in A s, if (remaining k ω).Nonempty ∧ g (remaining k ω) (rows k ω) = j then (1 : ℝ≥0∞) else 0 ∂(P : Measure Ω)) = _
    rw [hleft, hright]
    by_cases hs : s.Nonempty
    · let B : Set ChoiceRow := {row | g s row = j}
      have hB : MeasurableSet B := (hg s) (measurableSet_singleton j)
      have hpre : MeasurableSet (rows k ⁻¹' B) := hB.preimage (hmeasurable k)
      have hpre0 : MeasurableSet[MeasurableSpace.comap (rows k) inferInstance] (rows k ⁻¹' B) :=
        ⟨B, hB, rfl⟩
      have hfactor := ((hind k).indepSet_of_measurableSet (hA0 s) hpre0).measure_inter_eq_mul
      have hmass : (P : Measure Ω) (rows k ⁻¹' B) =
          if j ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
        ((hlaw k).measure_eq hB).trans (hprob s hs j)
      simp only [hs, true_and]
      have hindicator : (fun ω => if g s (rows k ω) = j then (1 : ℝ≥0∞) else 0) =
          (rows k ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        simp only [Set.indicator, Set.mem_preimage, B, Set.mem_ofPred_eq]
      rw [hindicator]
      rw [setLIntegral_indicator hpre, setLIntegral_one, Set.inter_comm, hfactor,
        hmass, setLIntegral_const, mul_comm]
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [hempty]


theorem uniform_mean {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} [NeZero m] (v : Fin m → Space d) (X : Ω → Fin m)
    (hmeasurable : Measurable X)
    (hlaw : HasLaw X (PMF.uniformOfFintype (Fin m)).toMeasure (P : Measure Ω)) :
    Integrable (fun ω => v (X ω)) (P : Measure Ω) ∧
      (∫ ω, v (X ω) ∂(P : Measure Ω)) = (m : ℝ)⁻¹ • (∑ i, v i) := by
  open scoped BigOperators in
    have _ := hmeasurable
    have hv : Integrable v (PMF.uniformOfFintype (Fin m)).toMeasure := Integrable.of_finite
    refine ⟨hlaw.integrable_comp hv, ?_⟩
    change (∫ ω, (v ∘ X) ω ∂(P : Measure Ω)) = (m : ℝ)⁻¹ • (∑ i, v i)
    rw [hlaw.integral_comp hv.aestronglyMeasurable]
    rw [integral_fintype hv]
    simp [Measure.real, PMF.uniformOfFintype_apply, ← Finset.smul_sum]

theorem uniform_centered_second_moment {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {d m S : ℕ} [NeZero m] (hS : 0 < S)
    (v : Fin m → Space d) (X : Fin S → Ω → Fin m)
    (hmeasurable : ∀ j, Measurable (X j))
    (hlaw : ∀ j, HasLaw (X j) (PMF.uniformOfFintype (Fin m)).toMeasure (P : Measure Ω))
    (hind : iIndepFun X (P : Measure Ω)) :
    Integrable (fun ω => (S : ℝ)⁻¹ • (∑ j, v (X j ω))) (P : Measure Ω) ∧
      (∫ ω, (S : ℝ)⁻¹ • (∑ j, v (X j ω)) ∂(P : Measure Ω)) =
        (m : ℝ)⁻¹ • (∑ i, v i) ∧
      Integrable (fun ω => ‖(S : ℝ)⁻¹ • (∑ j, v (X j ω)) -
        (m : ℝ)⁻¹ • (∑ i, v i)‖ ^ 2) (P : Measure Ω) ∧
      (∫ ω, ‖(S : ℝ)⁻¹ • (∑ j, v (X j ω)) - (m : ℝ)⁻¹ • (∑ i, v i)‖ ^ 2
        ∂(P : Measure Ω)) =
        (S : ℝ)⁻¹ * ((m : ℝ)⁻¹ * (∑ i, ‖v i‖ ^ 2) -
          ‖(m : ℝ)⁻¹ • (∑ i, v i)‖ ^ 2) := by
  open scoped BigOperators in
    classical
    let μ : Measure (Fin m) := (PMF.uniformOfFintype (Fin m)).toMeasure
    let Q : ProbabilityMeasure (Fin m) := ⟨μ, inferInstance⟩
    let u : Space d := (m : ℝ)⁻¹ • (∑ i, v i)
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    have hS0 : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    have hv : Integrable v μ := Integrable.of_finite
    have hu : (∫ i, v i ∂μ) = u :=
      (uniform_mean Q v id measurable_id ⟨measurable_id.aemeasurable, by rw [Measure.map_id]; rfl⟩).2
    have hvar := OracleTemplate.RobustGradient.finite_mean_variance
      (measurable_of_countable v) hv u
      (show Integrable (fun i => ‖v i - u‖ ^ 2) μ from Integrable.of_finite)
      hu S hS
    have hjoint := iIndepFun.hasLaw_pi hlaw hind
    have havg : Integrable (fun ξ : Fin S → Fin m => (S : ℝ)⁻¹ • (∑ j, v (ξ j)))
        (Measure.pi fun _ : Fin S => μ) := Integrable.of_finite
    have hinner : (m : ℝ)⁻¹ * (∑ i, inner ℝ (v i) u) = ‖u‖ ^ 2 := by
      calc
        (m : ℝ)⁻¹ * (∑ i, inner ℝ (v i) u) =
            inner ℝ ((m : ℝ)⁻¹ • (∑ i, v i)) u := by
          simp [inner_smul_left, sum_inner]
        _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    have hconst : (m : ℝ)⁻¹ * ((m : ℝ) * ‖u‖ ^ 2) = ‖u‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    have hbase : (∫ i, ‖v i - u‖ ^ 2 ∂μ) =
        (m : ℝ)⁻¹ * (∑ i, ‖v i‖ ^ 2) - ‖u‖ ^ 2 := by
      calc
        (∫ i, ‖v i - u‖ ^ 2 ∂μ) = (m : ℝ)⁻¹ * (∑ i, ‖v i - u‖ ^ 2) := by
          rw [integral_fintype (show Integrable (fun i => ‖v i - u‖ ^ 2) μ from
            Integrable.of_finite)]
          simp [μ, Measure.real, PMF.uniformOfFintype_apply, smul_eq_mul, ← Finset.mul_sum]
        _ = (m : ℝ)⁻¹ * (∑ i, ‖v i‖ ^ 2) - ‖u‖ ^ 2 := by
          simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          nlinarith only [hinner, hconst]
    refine ⟨hjoint.integrable_comp havg, ?_, ?_, ?_⟩
    · rw [integral_smul, integral_finsetSum Finset.univ
        (fun j _ => (uniform_mean P v (X j) (hmeasurable j) (hlaw j)).1)]
      have heach (j : Fin S) : (∫ ω, v (X j ω) ∂(P : Measure Ω)) = u :=
        (uniform_mean P v (X j) (hmeasurable j) (hlaw j)).2
      simp_rw [heach]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hS0, one_smul]
      rfl
    · simpa only [Function.comp_def, one_div] using hjoint.integrable_comp hvar.1
    · have htrans := hjoint.integral_comp hvar.1.aestronglyMeasurable
      have hfin := hvar.2
      rw [hbase] at hfin
      simpa only [Function.comp_def, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul, u] using htrans.trans hfin

theorem finite_label_law {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {m S : ℕ} [NeZero m] (X : Fin S → Ω → Fin m)
    (hmeasurable : ∀ j, Measurable (X j))
    (hlaw : ∀ j, HasLaw (X j) (PMF.uniformOfFintype (Fin m)).toMeasure (P : Measure Ω))
    (hind : iIndepFun X (P : Measure Ω)) :
    HasLaw (fun ω j => X j ω)
      (Measure.pi fun _ : Fin S => (PMF.uniformOfFintype (Fin m)).toMeasure)
      (P : Measure Ω) := by
  have _ := hmeasurable
  exact iIndepFun.hasLaw_pi hlaw hind

end LongTails.Proofs.FreyaMoments
