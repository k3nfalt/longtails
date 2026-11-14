import LongTails.Proofs.StochasticMfcqQuerySafety

open MeasureTheory
namespace LongTails.Proofs.StochasticMfcqGuarantee
open OracleTemplate
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open StochasticMfcqSampling StochasticMfcqExecution StochasticMfcqQuerySafety

lemma iid_pullback {Ω Ξ Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    {p : Measure Ω} {P : Measure Ξ} {Q : Measure Z} [IsProbabilityMeasure Q]
    {ξ : ℕ → Ξ → Ω} (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : Z → Ξ} (hf : MeasurePreserving f Q P) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k z => ξ k (f z)) p Q := by
  have hm : ∀ k, Measurable (fun z => ξ k (f z)) := fun k => (h.measurable k).comp hf.measurable
  have hl : ∀ k, Q.map (fun z => ξ k (f z)) = p := by
    intro k
    change Q.map (ξ k ∘ f) = p
    rw [← Measure.map_map (h.measurable k) hf.measurable, hf.map_eq, h.marginal]
  refine ⟨hm, ?_, hl⟩
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map hm]
  simp only [hl]
  exact (h.stream_law.comp hf).map_eq

lemma execution_guarantee (p : Params) (hp : spec.valid p) (I : Problem p)
    (O : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (hadm : spec.admissible p I O) (K : ℕ) (hK : calls p ≤ K) :
    Measurable (fun seed : (LongTails.Algorithms.StochasticMfcq.algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (LongTails.Algorithms.StochasticMfcq.algorithm p) (fun _ => K) seed.1 seed.2) ∧
    ENNReal.ofReal (1 - p.ρ) ≤
      (((LongTails.Algorithms.StochasticMfcq.algorithm p).law : Measure _).prod (O.law : Measure _))
      {seed | (∀ item ∈ (executeWithTrace O (LongTails.Algorithms.StochasticMfcq.algorithm p)
        (fun _ => K) seed.1 seed.2).2, feasibleQuery p I item.1.2) ∧
        accurate p I (execute O (LongTails.Algorithms.StochasticMfcq.algorithm p)
          (fun _ => K) seed.1 seed.2)} := by
  obtain ⟨g, v, D, μ, P, hIID, rfl, R, H⟩ := hadm
  let O : Oracle (p.E × p.E) (Primitive p × Primitive p) :=
    { Seed := fun _ => p.Ω
      law := P
      answer := fun _ (_, z) ω =>
        ((g z.1 ω, v z.1 ω, D z.1 ω), (g z.2 ω, v z.2 ω, D z.2 ω)) }
  let reply := fun (ξ : ℕ → p.Ω) n (z : p.E × p.E) =>
    ((g z.1 (ξ n), v z.1 (ξ n), D z.1 (ξ n)), (g z.2 (ξ n), v z.2 (ξ n), D z.2 (ξ n)))
  have he : ∀ seed : Unit × (ℕ → p.Ω),
      execute O (LongTails.Algorithms.StochasticMfcq.algorithm p) (fun _ => K) seed.1 seed.2 =
      ((killedStateAt p I g v D seed.2 (outerSteps p)).2.1,
        (killedStateAt p I g v D seed.2 (outerSteps p)).2.2.2.2.2) := by
    intro seed
    rw [killedStateAt_actual]
    exact execute_stateAt p O K seed.1 seed.2 (reply seed.2) (fun _ _ => rfl) hK
  constructor
  · have hm := (measurable_killedStateAt p I R g v D μ H (outerSteps p)).comp
      (measurable_snd : Measurable (Prod.snd : Unit × (ℕ → p.Ω) → (ℕ → p.Ω)))
    have hout : (fun seed : Unit × (ℕ → p.Ω) =>
        execute O (LongTails.Algorithms.StochasticMfcq.algorithm p) (fun _ => K) seed.1 seed.2) =
        (fun seed => ((killedStateAt p I g v D seed.2 (outerSteps p)).2.1,
          (killedStateAt p I g v D seed.2 (outerSteps p)).2.2.2.2.2)) := funext he
    change Measurable (fun seed : Unit × (ℕ → p.Ω) =>
      execute O (LongTails.Algorithms.StochasticMfcq.algorithm p) (fun _ => K) seed.1 seed.2)
    rw [hout]
    exact hm.snd.fst.prodMk hm.snd.snd.snd.snd.snd
  · have hsnd : MeasurePreserving (Prod.snd : Unit × (ℕ → p.Ω) → (ℕ → p.Ω))
        ((Measure.dirac ()).prod (P : Measure _)) (P : Measure _) := measurePreserving_snd
    have hi := iid_pullback hIID hsnd
    have hb := safe_accurate_probability p I hp R g v D μ H
      ((Measure.dirac ()).prod (P : Measure _)) (fun k (w : Unit × (ℕ → p.Ω)) => w.2 k) hi
    apply hb.trans
    apply measure_mono
    intro seed hs
    refine ⟨?_, ?_⟩
    · apply execute_trace_safe p I R O seed.1 seed.2 (reply seed.2) (fun _ _ => rfl)
      intro k hk
      have hh := hs.1 k hk.le
      rw [killedStateAt_actual] at hh
      exact ⟨hh.1, hh.2.1⟩
    · rw [he]
      exact hs.2

lemma execution_success (p : Params) (hp : spec.valid p) (I : Problem p)
    (O : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (hadm : spec.admissible p I O) (K : ℕ) (hK : calls p ≤ K) :
    spec.successful p I
      (fun seed : (LongTails.Algorithms.StochasticMfcq.algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
        output p O K seed.1 seed.2)
      ⟨((LongTails.Algorithms.StochasticMfcq.algorithm p).law : Measure _).prod (O.law : Measure _),
        inferInstance⟩ := by
  have h := execution_guarantee p hp I O hadm K hK
  refine ⟨h.1, h.2.trans (measure_mono ?_)⟩
  intro seed hs
  exact hs.2

lemma execution_calls (p : Params) (O : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (seed : Unit) (ξ : (k : ℕ) → O.Seed k) (K : ℕ) :
    (executeWithTrace O (LongTails.Algorithms.StochasticMfcq.algorithm p)
      (fun _ => K) seed ξ).2.length = K := by
  erw [executeWithTrace_eq_executeIndexedState]
  exact executeIndexedState_length _ _ _ _ _

end LongTails.Proofs.StochasticMfcqGuarantee
