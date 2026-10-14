import LongTails.Proofs.ClippedExtragradientAccuracy

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

lemma measurable_fixed_argument {X Y Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (f : X → Y → Z)
    (hf : Measurable (fun w : X × Y => f w.1 w.2)) (x : X) :
    Measurable (fun y => f x y) :=
  hf.comp (measurable_const.prodMk measurable_id)

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

set_option maxHeartbeats 1200000 in
lemma execution_success (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (hδ : 0 < t.δ)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    {g : E → Ω → E} (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (p : Measure Ω) (P : Measure _))
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure Ω) F g t.σ)
    (x0 xstar : E) (hstar : F xstar = 0) (hd : ‖x0 - xstar‖ ≤ t.R)
    (K : ℕ) (hK : remainingCalls t 0 (stageCount t) ≤ K) :
    Measurable (fun seed : Unit × (ℕ → Ω) =>
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (localizedClippedExtragradient t x0) (fun _ => K) seed.1 seed.2)) ∧
    ((Measure.dirac ()).prod (P : Measure _))
      {seed : Unit × (ℕ → Ω) | t.ε <
        ‖F (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (localizedClippedExtragradient t x0) (fun _ => K) seed.1 seed.2)‖} ≤ ENNReal.ofReal t.δ := by
  let out : (ℕ → Ω) → E := fun ξ =>
    (StochasticGeneralized.blockTrace (stageCost t) (stageNext t g) (0, x0, x0) ξ (stageCount t)).1.2.2
  have ht : Measurable (fun ξ : ℕ → Ω =>
      StochasticGeneralized.blockTrace (stageCost t) (stageNext t g) (0, x0, x0) ξ
        (stageCount t)) :=
    measurable_fixed_argument
      (fun state ξ => StochasticGeneralized.blockTrace (stageCost t) (stageNext t g)
        state ξ (stageCount t))
      (measurable_stageTrace hg.measurable t (stageCount t)) (0, x0, x0)
  have ho : Measurable out := ht.fst.snd.snd
  have he (seed : Unit × (ℕ → Ω)) :
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (localizedClippedExtragradient t x0) (fun _ => K) seed.1 seed.2) = out seed.2 := by
    rw [execute_localized P g t x0 hR K hK seed.1 seed.2]
  simp_rw [he]
  refine ⟨ho.comp measurable_snd, ?_⟩
  have hset : MeasurableSet {ξ | t.ε < ‖F (out ξ)‖} :=
    measurableSet_lt measurable_const (hc.measurable.comp ho).norm
  have hPlaw : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)) := by
    have hh := hIID.stream_law.map_eq
    change Measure.map id (P : Measure (ℕ → Ω)) = _ at hh
    simpa only [Measure.map_id] using hh
  have hbound : (P : Measure _) {ξ | t.ε < ‖F (out ξ)‖} ≤ ENNReal.ofReal t.δ := by
    rw [hPlaw]
    exact stageTrace_high_probability t h0 h1 hR hε hδ F hc hm hlip (p : Measure Ω) hg
      x0 xstar hstar hd
  change ((Measure.dirac ()).prod (P : Measure _))
    (Prod.snd ⁻¹' {ξ | t.ε < ‖F (out ξ)‖}) ≤ _
  rw [measurePreserving_snd.measure_preimage hset.nullMeasurableSet]
  exact hbound

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma execution_success_zero (t : Tuning) (hR : ¬0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (g : E → Ω → E) (P : ProbabilityMeasure (ℕ → Ω))
    (x0 : E) (hroot : F x0 = 0) (K : ℕ) :
    Measurable (fun seed : Unit × (ℕ → Ω) =>
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (localizedClippedExtragradient t x0) (fun _ => K) seed.1 seed.2)) ∧
    ((Measure.dirac ()).prod (P : Measure _))
      {seed : Unit × (ℕ → Ω) | t.ε <
        ‖F (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (localizedClippedExtragradient t x0) (fun _ => K) seed.1 seed.2)‖} ≤ ENNReal.ofReal t.δ := by
  simp_rw [execute_localized_zero P g t x0 hR K]
  refine ⟨measurable_const, ?_⟩
  simp only [hroot, norm_zero, not_lt_of_ge hε.le, Set.ofPred_false, measure_empty]
  exact bot_le

end OracleTemplate.ClippedExtragradient
