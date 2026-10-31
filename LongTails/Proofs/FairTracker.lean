import LongTails.Proofs.FairBatchMoments

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace Ω]

noncomputable def localBias (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (t : ℕ) (x y : E) : E :=
  observationMean cfg p g t x y - if cfg.isRefresh t then F x else F x - F y

noncomputable def biasDrift (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) : ℕ → E
  | 0 => -F x0
  | t + 1 =>
    localBias cfg p g F t (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 +
      if cfg.isRefresh t then 0 else biasDrift cfg p g F x0 ξ t

noncomputable def centeredBatch (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) : E :=
  (cfg.batch t : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch t), centeredObservation cfg p g t
    (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 (ξ (cfg.blockOffset t + j))

noncomputable def centeredTracker (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) : ℕ → E
  | 0 => 0
  | t + 1 => centeredBatch cfg p g x0 ξ t + if cfg.isRefresh t then 0 else centeredTracker cfg p g x0 ξ t

lemma centeredBatch_eq (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) (hb : 0 < cfg.batch t) :
    centeredBatch cfg p g x0 ξ t =
      batchObservation cfg g t (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 ξ -
        observationMean cfg p g t (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 := by
  unfold centeredBatch centeredObservation batchObservation
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  simp only [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast hb.ne' : (cfg.batch t : ℝ) ≠ 0), one_smul]

lemma tracker_decomposition (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω)
    (hb : ∀ t, 0 < cfg.batch t) :
    ∀ t, (trajectory cfg g x0 ξ t).2.2 - F (trajectory cfg g x0 ξ t).2.1 =
      centeredTracker cfg p g x0 ξ t + biasDrift cfg p g F x0 ξ t
  | 0 => by simp [trajectory, centeredTracker, biasDrift]
  | t + 1 => by
      have hi := tracker_decomposition cfg p g F x0 ξ hb t
      rw [centeredTracker, biasDrift, centeredBatch_eq cfg p g x0 ξ t (hb t)]
      simp only [trajectory, localBias]
      split_ifs
      · module
      · rw [(sub_eq_iff_eq_add).mp hi]
        module

lemma direction_error_decomposition (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω)
    (hb : ∀ t, 0 < cfg.batch t) (t : ℕ) :
    direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1 =
      centeredTracker cfg p g x0 ξ (t + 1) + biasDrift cfg p g F x0 ξ (t + 1) :=
  tracker_decomposition cfg p g F x0 ξ hb (t + 1)

lemma biasDrift_congr (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (x0 : E) {ξ ξ' : ℕ → Fin cfg.m → Ω} :
    ∀ t, (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) →
      biasDrift cfg p g F x0 ξ t = biasDrift cfg p g F x0 ξ' t
  | 0, _ => rfl
  | t + 1, h => by
      have h0 : ∀ i, i < cfg.blockOffset t → ξ i = ξ' i :=
        fun i hi => h i (by rw [blockOffset_succ]; omega)
      rw [biasDrift, biasDrift, trajectory_congr cfg g x0 t h0, biasDrift_congr cfg p g F x0 t h0]

lemma centeredBatch_congr (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (x0 : E) (t : ℕ) (hb : 0 < cfg.batch t)
    {ξ ξ' : ℕ → Fin cfg.m → Ω}
    (h : ∀ i, i < cfg.blockOffset (t + 1) → ξ i = ξ' i) :
    centeredBatch cfg p g x0 ξ t = centeredBatch cfg p g x0 ξ' t := by
  have h0 : ∀ i, i < cfg.blockOffset t → ξ i = ξ' i :=
    fun i hi => h i (by rw [blockOffset_succ]; omega)
  rw [centeredBatch_eq cfg p g x0 ξ t hb, centeredBatch_eq cfg p g x0 ξ' t hb,
    trajectory_congr cfg g x0 t h0, batchObservation_congr cfg g t _ _ h]

lemma centeredTracker_congr (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (x0 : E) (hb : ∀ t, 0 < cfg.batch t)
    {ξ ξ' : ℕ → Fin cfg.m → Ω} :
    ∀ t, (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) →
      centeredTracker cfg p g x0 ξ t = centeredTracker cfg p g x0 ξ' t
  | 0, _ => rfl
  | t + 1, h => by
      have h0 : ∀ i, i < cfg.blockOffset t → ξ i = ξ' i :=
        fun i hi => h i (by rw [blockOffset_succ]; omega)
      rw [centeredTracker, centeredTracker, centeredBatch_congr cfg p g x0 t (hb t) h,
        centeredTracker_congr cfg p g x0 hb t h0]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

lemma measurable_localBias (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E} {F : E → E}
    (hg : Measurable (Function.uncurry g)) (hF : Measurable F) (t : ℕ) :
    Measurable (fun z : E × E => localBias cfg p g F t z.1 z.2) := by
  unfold localBias
  split_ifs
  · exact (measurable_observationMean cfg hm hR p hg t).sub (hF.comp measurable_fst)
  · exact (measurable_observationMean cfg hm hR p hg t).sub
      ((hF.comp measurable_fst).sub (hF.comp measurable_snd))

lemma measurable_biasDrift (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E} {F : E → E}
    (hg : Measurable (Function.uncurry g)) (hF : Measurable F) (x0 : E) :
    ∀ t, Measurable (fun ξ => biasDrift cfg p g F x0 ξ t)
  | 0 => measurable_const
  | t + 1 => by
      have hi := measurable_biasDrift cfg hm hR p hg hF x0 t
      have ht := measurable_trajectory cfg hm hR hg x0 t
      have hm' := (measurable_localBias cfg hm hR p hg hF t).comp (ht.fst.prodMk ht.snd.fst)
      unfold biasDrift
      split_ifs
      · exact hm'.add measurable_const
      · exact hm'.add hi

lemma measurable_centeredBatch (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (x0 : E) (t : ℕ) (hb : 0 < cfg.batch t) :
    Measurable (fun ξ => centeredBatch cfg p g x0 ξ t) := by
  simp_rw [centeredBatch_eq cfg p g x0 _ t hb]
  have ht := measurable_trajectory cfg hm hR hg x0 t
  have hbt : Measurable (fun ξ => batchObservation cfg g t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 ξ) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_batchObservation cfg hm hR hg t).comp
        ((ht.fst.prodMk ht.snd.fst).prodMk measurable_id)
  have hmt : Measurable (fun ξ => observationMean cfg p g t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1) := by
    simpa only [Function.comp_def] using
      (measurable_observationMean cfg hm hR p hg t).comp (ht.fst.prodMk ht.snd.fst)
  exact hbt.sub hmt

lemma measurable_centeredTracker (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (x0 : E) (hb : ∀ t, 0 < cfg.batch t) :
    ∀ t, Measurable (fun ξ => centeredTracker cfg p g x0 ξ t)
  | 0 => measurable_const
  | t + 1 => by
      have hi := measurable_centeredTracker cfg hm hR p hg x0 hb t
      have hm' := measurable_centeredBatch cfg hm hR p hg x0 t (hb t)
      unfold centeredTracker
      split_ifs
      · exact hm'.add measurable_const
      · exact hm'.add hi

end OracleTemplate.FairVarianceReduction
