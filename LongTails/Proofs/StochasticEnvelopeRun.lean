import LongTails.Proofs.StochasticEnvelopeAccuracy
import LongTails.Proofs.StochasticEnvelopeBudget
open MeasureTheory OracleTemplate
open scoped ENNReal
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeExecution
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma execute_recovery_output (c : Parameters) (d : ℕ) (x0 : E) (g : E → Ω → E)
    (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) (seed : RecoverySeed d) (ξ : ℕ → Ω) :
    execute {Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z}
      (output c d x0) (fun _ => K) seed ξ =
      if recoveryCalls c d seed ≤ K then recoveryValue c g d x0 (seed, ξ) else x0 := by
  exact execute_capped (recoverySeedLaw c.levelProbability d) x0 x0
    (fun seed => ⟨recoveryCalls c d seed, recoverPlan c d seed x0⟩)
    {Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z} K seed ξ
    (fun j x => g x (ξ j)) (fun _ _ => rfl)

lemma measurable_capped_recovery {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (c : Parameters) (d : ℕ) (x0 : E) (K : ℕ) :
    Measurable (fun w : RecoverySeed d × (ℕ → Ω) =>
      if recoveryCalls c d w.1 ≤ K then recoveryValue c g d x0 w else x0) := by
  apply Measurable.ite
  · exact measurableSet_le ((measurable_recoveryCalls c d).comp measurable_fst) measurable_const
  · exact (measurable_recoveryValue hg c d).comp measurable_prodMk_left
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma capped_recovery_failure (c : Parameters) (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (g : E → Ω → E) (f : E → ℝ) (x0 xs : E) (ε δ₁ δ₂ : ℝ) (K : ℕ) (hK : 0 < K)
    (hwork : Integrable (fun s => (recoveryCalls c d s : ℝ)) (recoverySeedLaw c.levelProbability d : Measure _))
    (hmean : (∫ s, (recoveryCalls c d s : ℝ) ∂(recoverySeedLaw c.levelProbability d : Measure _)) ≤ δ₂ * (K : ℝ))
    (hfail : ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P)) {w | ε < f (recoveryValue c g d x0 w) - f xs} ≤ ENNReal.ofReal δ₁) :
    ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | ε < f (if recoveryCalls c d w.1 ≤ K then recoveryValue c g d x0 w else x0) - f xs}
      ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₂ := by
  let Q := (recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d))
  let R := Measure.infinitePi fun _ : ℕ => P
  have hcap : Q {s | K < recoveryCalls c d s} ≤ ENNReal.ofReal δ₂ := by
    have hh := ENNReal.ofReal_le_ofReal (call_cap_probability Q hwork hK hmean)
    rw [ofReal_measureReal] at hh
    exact hh
  have hsubset : {w : RecoverySeed d × (ℕ → Ω) |
      ε < f (if recoveryCalls c d w.1 ≤ K then recoveryValue c g d x0 w else x0) - f xs} ⊆
      {w | ε < f (recoveryValue c g d x0 w) - f xs} ∪
      ({s | K < recoveryCalls c d s} ×ˢ Set.univ) := by
    intro w hw
    by_cases hc : recoveryCalls c d w.1 ≤ K
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, ite_eq_left hc] using hw)
    · exact Or.inr ⟨Nat.lt_of_not_ge hc, Set.mem_univ _⟩
  have hprod : (Q.prod R) ({s | K < recoveryCalls c d s} ×ˢ Set.univ) ≤ ENNReal.ofReal δ₂ := by
    simpa only [Measure.prod_prod, measure_univ, mul_one] using hcap
  exact (measure_mono hsubset).trans ((measure_union_le _ _).trans (add_le_add hfail hprod))


lemma setup_capped_success (q : LongTails.Setups.AffineMomentConvex.Params)
    (hq : LongTails.Setups.AffineMomentConvex.spec.valid q) (hT : 1 ≤ q.L * q.R ^ 2 / q.ε)
    (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _))
    (f : q.E → ℝ) (g : q.E → q.Ω → q.E)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (ho : LongTails.Setups.AffineMomentConvex.IsFiniteMomentOracle (ν : Measure _) f g q.α q.σ q.σ0)
    (xs : q.E) (hmin : IsMinOn f Set.univ xs) (hR : ‖q.x0 - xs‖ ≤ q.R) (K : ℕ) (hK : 0 < K) :
    let d := depth q.L q.R q.ε q.δ q.σ0 q.α
    let c := parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α d (Nat.le_max_left _ _)
    Integrable (fun s => (recoveryCalls c d s : ℝ)) (recoverySeedLaw c.levelProbability d : Measure _) →
    (∫ s, (recoveryCalls c d s : ℝ) ∂(recoverySeedLaw c.levelProbability d : Measure _)) ≤ (q.δ / 4) * (K : ℝ) →
    LongTails.Setups.AffineMomentConvex.spec.successful q f
      (fun w : RecoverySeed d × (ℕ → q.Ω) => execute
        {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
        (output c d q.x0) (fun _ => K) w.1 w.2)
      ⟨(recoverySeedLaw c.levelProbability d : Measure _).prod (P : Measure _), inferInstance⟩ := by
  dsimp only
  intro hwork hmean
  let d := depth q.L q.R q.ε q.δ q.σ0 q.α
  let c := parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α d (Nat.le_max_left _ _)
  let Z := fun w : RecoverySeed d × (ℕ → q.Ω) =>
    if recoveryCalls c d w.1 ≤ K then recoveryValue c g d q.x0 w else q.x0
  have hZ : Measurable Z := measurable_capped_recovery ho.measurable c d q.x0 K
  have he : (fun w : RecoverySeed d × (ℕ → q.Ω) => execute
      {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
      (output c d q.x0) (fun _ => K) w.1 w.2) = Z := by
    funext w
    exact execute_recovery_output c d q.x0 g P K w.1 w.2
  refine Eq.mpr (congrArg (fun out => LongTails.Setups.AffineMomentConvex.spec.successful q f out
    (⟨(recoverySeedLaw c.levelProbability d : Measure _).prod (P : Measure _), inferInstance⟩)) he) ?_
  refine ⟨hZ, xs, hmin, ?_⟩
  have hδ : 0 < q.δ := hq.2.2.2.2.2.2.2.1
  have hPlaw : (P : Measure _) = Measure.infinitePi fun _ : ℕ => (ν : Measure q.Ω) := by
    have hh := hIID.stream_law.map_eq
    change (P : Measure (ℕ → q.Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  have huncap := setup_recovery_failure q hq hT (ν : Measure _) f g hc hf hlip ho xs hmin hR
  have hcap := capped_recovery_failure c d (ν : Measure _) g f q.x0 xs q.ε (q.δ / 4) (q.δ / 4)
    K hK hwork hmean huncap
  have hbad : ((recoverySeedLaw c.levelProbability d : Measure _).prod (P : Measure _))
      {w | q.ε < f (Z w) - f xs} ≤ ENNReal.ofReal q.δ := by
    rw [hPlaw]
    refine hcap.trans ?_
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 4) (by positivity : 0 ≤ q.δ / 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hset : MeasurableSet {w | q.ε < f (Z w) - f xs} :=
    measurableSet_lt measurable_const ((hfc.measurable.comp hZ).sub_const _)
  change (∫ w, {w : RecoverySeed d × (ℕ → q.Ω) | q.ε < f (Z w) - f xs}.indicator (1 : RecoverySeed d × (ℕ → q.Ω) → ℝ) w
    ∂(recoverySeedLaw c.levelProbability d : Measure _).prod (P : Measure _)) ≤ q.δ
  rw [integral_indicator_one hset]
  exact ((ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbad).trans_eq
    (ENNReal.toReal_ofReal hδ.le)


lemma setup_trivial_success (q : LongTails.Setups.AffineMomentConvex.Params)
    (hq : LongTails.Setups.AffineMomentConvex.spec.valid q) (hT : q.L * q.R ^ 2 / q.ε ≤ 1)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (f : q.E → ℝ) (g : q.E → q.Ω → q.E)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (xs : q.E) (hmin : IsMinOn f Set.univ xs) (hR : ‖q.x0 - xs‖ ≤ q.R) (K : ℕ) :
    LongTails.Setups.AffineMomentConvex.spec.successful q f
      (fun w : Unit × (ℕ → q.Ω) => execute
        {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
        (LongTails.Algorithms.StochasticEnvelopeProgram.algorithm
          (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit) q.x0 q.x0
          (fun _ => ⟨0, QueryPlan.done q.x0⟩)) (fun _ => K) w.1 w.2)
      ⟨(Measure.dirac ()).prod (P : Measure _), inferInstance⟩ := by
  have hgrad : gradient f xs = 0 := by
    apply (InnerProductSpace.toDual ℝ q.E).injective
    rw [toDual_gradient, map_zero]
    exact (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
  have hgap := OracleTemplate.Gradient.smooth_upper_bound hf hlip xs q.x0
  rw [hgrad, inner_zero_left, add_zero] at hgap
  have hε : 0 < q.ε := hq.2.2.2.2.2.2.1
  have hL : 0 < q.L := hq.1
  have hδ : 0 < q.δ := hq.2.2.2.2.2.2.2.1
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hLR : q.L * q.R ^ 2 ≤ q.ε := (div_le_one hε).1 hT
  have hgood : f q.x0 - f xs ≤ q.ε := by nlinarith
  have hexec : (fun w : Unit × (ℕ → q.Ω) => execute
      {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
      (LongTails.Algorithms.StochasticEnvelopeProgram.algorithm
        (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit) q.x0 q.x0
        (fun _ => ⟨0, QueryPlan.done q.x0⟩)) (fun _ => K) w.1 w.2) = fun _ => q.x0 := by
    funext w
    have hh := execute_capped (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit) q.x0 q.x0
      (fun _ => ⟨0, QueryPlan.done q.x0⟩)
      {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
      K w.1 w.2 (fun j x => g x (w.2 j)) (fun _ _ => rfl)
    simpa only [Nat.zero_le, ite_true, RecursiveEnvelopeExecution.evalAt] using hh
  refine Eq.mpr (congrArg (fun out => LongTails.Setups.AffineMomentConvex.spec.successful q f out
    (⟨(Measure.dirac ()).prod (P : Measure _), inferInstance⟩)) hexec) ?_
  refine ⟨measurable_const, xs, hmin, ?_⟩
  simp only [not_lt_of_ge hgood, ite_false, integral_zero]
  exact hδ.le

lemma successful_execution (q : LongTails.Setups.AffineMomentConvex.Params)
    (hq : LongTails.Setups.AffineMomentConvex.spec.valid q)
    (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _))
    (f : q.E → ℝ) (g : q.E → q.Ω → q.E)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (xs : q.E) (hmin : IsMinOn f Set.univ xs) (hR : ‖q.x0 - xs‖ ≤ q.R)
    (ho : LongTails.Setups.AffineMomentConvex.IsFiniteMomentOracle (ν : Measure _) f g q.α q.σ q.σ0)
    (K : ℕ) (hK : 0 < K)
    (hbudget :
      let a := q.α / (q.α - 1)
      let T := q.L * q.R ^ 2 / q.ε
      let V := (q.σ0 * q.R / q.ε) ^ a
      let M := 4 + T + V + 1 / q.δ
      Real.exp ((2 : ℝ) ^ (32 : ℕ) * a ^ 4 * (1 + Real.sqrt (Real.log M)) * Real.log (2 + a + Real.log M)) *
        ((1 + q.σ) ^ a * Real.sqrt T + 1 + V) / q.δ ≤ (K : ℝ)) :
    LongTails.Setups.AffineMomentConvex.spec.successful q f
      (fun w => execute
        {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
        (algorithm q) (fun _ => K) w.1 w.2)
      ⟨((algorithm q).law : Measure _).prod (P : Measure _), inferInstance⟩ := by
  let success := fun A : Algorithm q.E q.E q.E =>
    LongTails.Setups.AffineMomentConvex.spec.successful q f
      (fun w : A.Seed × (ℕ → q.Ω) => execute
        {Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) z => g x z}
        A (fun _ => K) w.1 w.2)
      (⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩)
  change success (algorithm q)
  by_cases hT : q.L * q.R ^ 2 / q.ε ≤ 1
  · have hA : algorithm q = LongTails.Algorithms.StochasticEnvelopeProgram.algorithm
        (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit) q.x0 q.x0
        (fun _ => ⟨0, QueryPlan.done q.x0⟩) := by simp only [LongTails.Algorithms.StochasticEnvelope.algorithm, hT, ite_true]
    rw [hA]
    exact setup_trivial_success q hq hT P f g hf hlip xs hmin hR K
  · have hT' : 1 ≤ q.L * q.R ^ 2 / q.ε := le_of_lt (lt_of_not_ge hT)
    obtain ⟨hL, hRad, ha, hs, hp, hp2, he, hd, hd1⟩ := hq
    have hw := StochasticEnvelopeBudget.parameters_public_work hL hRad he hd hd1.le hs ha hp hp2 hT'
    have hcap := setup_capped_success q ⟨hL, hRad, ha, hs, hp, hp2, he, hd, hd1⟩ hT'
      ν P hIID f g hc hf hlip ho xs hmin hR K hK hw.1
    have hb := (div_le_iff₀ hd).1 hbudget
    have hmean := hw.2
    have hcost : (∫ s, (recoveryCalls
        (parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α (depth q.L q.R q.ε q.δ q.σ0 q.α) (Nat.le_max_left _ _))
        (depth q.L q.R q.ε q.δ q.σ0 q.α) s : ℝ)
        ∂(recoverySeedLaw
          (parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α (depth q.L q.R q.ε q.δ q.σ0 q.α) (Nat.le_max_left _ _)).levelProbability
          (depth q.L q.R q.ε q.δ q.σ0 q.α) : Measure _)) ≤ (q.δ / 4) * (K : ℝ) := by
      nlinarith only [hmean, hb]
    have hA : algorithm q = output
        (parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α (depth q.L q.R q.ε q.δ q.σ0 q.α) (Nat.le_max_left _ _))
        (depth q.L q.R q.ε q.δ q.σ0 q.α) q.x0 := by simp only [LongTails.Algorithms.StochasticEnvelope.algorithm, hT, ite_false]
    rw [hA]
    exact hcap hcost

end LongTails.Proofs.StochasticEnvelopeRecursion
