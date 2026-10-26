import LongTails.Proofs.FairOracleTransfer
import LongTails.Proofs.NormalizedStormTrajectory

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type}

lemma blockOffset_zero (cfg : Config) : cfg.blockOffset 0 = 0 := by simp [Config.blockOffset]

lemma blockOffset_succ (cfg : Config) (t : ℕ) :
    cfg.blockOffset (t + 1) = cfg.blockOffset t + cfg.batch t := by
  simp [Config.blockOffset, Finset.sum_range_succ]

lemma trajectory_step (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) :
    (trajectory cfg g x0 ξ (t + 1)).1 =
      NormalizedStorm.stormStep cfg.η (trajectory cfg g x0 ξ t).1 (direction cfg g x0 ξ t) := rfl

lemma trajectory_previous (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) :
    (trajectory cfg g x0 ξ (t + 1)).2.1 = (trajectory cfg g x0 ξ t).1 := rfl

lemma direction_eq (cfg : Config) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) :
    direction cfg g x0 ξ t =
      batchObservation cfg g t (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 ξ +
        if cfg.isRefresh t then 0 else (trajectory cfg g x0 ξ t).2.2 := rfl

lemma batchObservation_congr (cfg : Config) (g : E → Ω → E) (t : ℕ) (x y : E)
    {ξ ξ' : ℕ → Fin cfg.m → Ω}
    (h : ∀ i, i < cfg.blockOffset (t + 1) → ξ i = ξ' i) :
    batchObservation cfg g t x y ξ = batchObservation cfg g t x y ξ' := by
  unfold batchObservation
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h (cfg.blockOffset t + j) (by
    rw [blockOffset_succ]
    have := Finset.mem_range.mp hj
    omega)]

lemma trajectory_congr (cfg : Config) (g : E → Ω → E) (x0 : E)
    {ξ ξ' : ℕ → Fin cfg.m → Ω} :
    ∀ t, (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) →
      trajectory cfg g x0 ξ t = trajectory cfg g x0 ξ' t
  | 0, _ => rfl
  | t + 1, h => by
      have hi := trajectory_congr cfg g x0 t (fun i hi => h i (by rw [blockOffset_succ]; omega))
      simp only [trajectory, hi]
      rw [batchObservation_congr cfg g t _ _ h]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
variable [MeasurableSpace Ω]

lemma measurable_blockObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : (E × E) × (Fin cfg.m → Ω) => blockObservation cfg g t z.1.1 z.1.2 z.2) := by
  have hleft : Measurable (fun z : (E × E) × (Fin cfg.m → Ω) => fun i => g z.1.1 (z.2 i)) :=
    Measurable.of_eval (fun i => hg.comp
      (measurable_fst.fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hright : Measurable (fun z : (E × E) × (Fin cfg.m → Ω) => fun i => g z.1.2 (z.2 i)) :=
    Measurable.of_eval (fun i => hg.comp
      (measurable_fst.snd.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  unfold blockObservation
  split_ifs
  · simpa only [Function.comp_def] using (measurable_refresh (E := E) hm hR cfg.G).comp hleft
  · simpa only [Function.comp_def] using
      (measurable_increment (E := E) hm hR cfg.B).comp (hleft.prodMk hright)

lemma measurable_batchObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : (E × E) × (ℕ → Fin cfg.m → Ω) => batchObservation cfg g t z.1.1 z.1.2 z.2) := by
  have hs : Measurable (fun z : (E × E) × (ℕ → Fin cfg.m → Ω) =>
      ∑ j ∈ Finset.range (cfg.batch t),
        blockObservation cfg g t z.1.1 z.1.2 (z.2 (cfg.blockOffset t + j))) := by
    apply Finset.measurable_sum
    intro j _
    simpa only [Function.comp_def] using
      (measurable_blockObservation cfg hm hR hg t).comp
        (measurable_fst.prodMk ((measurable_pi_apply (cfg.blockOffset t + j)).comp measurable_snd))
  exact hs.const_smul ((cfg.batch t : ℝ)⁻¹)

lemma measurable_trajectory (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E) :
    ∀ t, Measurable (fun ξ => trajectory cfg g x0 ξ t)
  | 0 => measurable_const
  | t + 1 => by
      have hi := measurable_trajectory cfg hm hR hg x0 t
      have hb := (measurable_batchObservation cfg hm hR hg t).comp
        ((hi.fst.prodMk hi.snd.fst).prodMk measurable_id)
      have hp : Measurable (fun ξ => if cfg.isRefresh t then (0 : E) else (trajectory cfg g x0 ξ t).2.2) := by
        split_ifs
        · exact measurable_const
        · exact hi.snd.snd
      have hv := hb.add hp
      exact ((NormalizedStorm.measurable_stormStep cfg.η).comp (hi.fst.prodMk hv)).prodMk
        (hi.fst.prodMk hv)

lemma measurable_direction (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E) (t : ℕ) :
    Measurable (fun ξ => direction cfg g x0 ξ t) :=
  (measurable_trajectory cfg hm hR hg x0 (t + 1)).snd.snd

end OracleTemplate.FairVarianceReduction
