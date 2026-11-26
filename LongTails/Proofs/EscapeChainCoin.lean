import LongTails.Proofs.AbcHardOracle

open MeasureTheory

namespace LongTails.Proofs.EscapeChainCoin

open LongTails.Proofs.AbcHardOracle

noncomputable def icoin (s p U : ℝ) : ℝ := if s ≤ U ∧ U < s + p then 1 / p else 0

lemma icoin_measurable (s p : ℝ) : Measurable (icoin s p) := by
  unfold icoin
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt measurable_id measurable_const)

lemma interval_eq (s p : ℝ) : {U : ℝ | s ≤ U ∧ U < s + p} = Set.Ico s (s + p) := by
  ext U; simp [Set.mem_Ico]

lemma unif_Ico {s p : ℝ} (hs : 0 ≤ s) (h1 : s + p ≤ 1) :
    unif (Set.Ico s (s + p)) = ENNReal.ofReal p := by
  have he : Set.Ico s (s + p) ∩ Set.Icc 0 1 = Set.Ico s (s + p) := by
    ext U; simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h, -⟩; exact h
    · rintro ⟨h1', h2'⟩; exact ⟨⟨h1', h2'⟩, by linarith, by linarith⟩
  rw [unif, Measure.restrict_apply measurableSet_Ico, he, Real.volume_Ico]
  congr 1; ring

lemma unif_real_Ico {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (h1 : s + p ≤ 1) :
    unif.real (Set.Ico s (s + p)) = p := by
  rw [Measure.real, unif_Ico hs h1, ENNReal.toReal_ofReal hp]

lemma icoin_eq (s p : ℝ) : icoin s p = Set.indicator (Set.Ico s (s + p)) (fun _ => 1 / p) := by
  funext U; simp only [icoin, Set.indicator, Set.mem_Ico]

lemma icoin_integrable (s p : ℝ) : Integrable (icoin s p) unif := by
  rw [icoin_eq]
  exact (integrable_const _).indicator measurableSet_Ico

lemma icoin_integral {s p : ℝ} (hs : 0 ≤ s) (hp : 0 < p) (h1 : s + p ≤ 1) :
    ∫ U, icoin s p U ∂unif = 1 := by
  rw [icoin_eq, integral_indicator measurableSet_Ico, setIntegral_const,
    unif_real_Ico hs hp.le h1, smul_eq_mul]
  field_simp

lemma icoin_sq_integral {s p : ℝ} (hs : 0 ≤ s) (hp : 0 < p) (h1 : s + p ≤ 1) :
    ∫ U, (icoin s p U - 1) ^ 2 ∂unif = 1 / p - 1 := by
  have he : (fun U => (icoin s p U - 1) ^ 2) =
      fun U => Set.indicator (Set.Ico s (s + p)) (fun _ => (1 / p - 1) ^ 2 - 1) U + 1 := by
    funext U; simp only [icoin, Set.indicator, Set.mem_Ico]; split_ifs <;> ring
  rw [he, integral_add ((integrable_const _).indicator measurableSet_Ico) (integrable_const _),
    integral_indicator measurableSet_Ico, setIntegral_const, unif_real_Ico hs hp.le h1, smul_eq_mul,
    integral_const, probReal_univ, one_smul]
  field_simp
  ring

lemma icoin_sq_integrable (s p : ℝ) : Integrable (fun U => (icoin s p U - 1) ^ 2) unif := by
  have he : (fun U => (icoin s p U - 1) ^ 2) =
      fun U => Set.indicator (Set.Ico s (s + p)) (fun _ => (1 / p - 1) ^ 2 - 1) U + 1 := by
    funext U; simp only [icoin, Set.indicator, Set.mem_Ico]; split_ifs <;> ring
  rw [he]
  exact ((integrable_const _).indicator measurableSet_Ico).add (integrable_const _)

lemma icoin_zero_of_not {s p U : ℝ} (h : ¬ (s ≤ U ∧ U < s + p)) : icoin s p U = 0 := by
  simp [icoin, h]

end LongTails.Proofs.EscapeChainCoin
