import LongTails.Algorithms.AffineResidualProx
import LongTails.Proofs.AffineResidualLocal
import LongTails.Proofs.AffineSoftmaxMultilevel

namespace LongTails.Proofs.AffineResidualMultilevel

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot countLaw)
open LongTails.Proofs.AffineSoftmaxMultilevel
open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)
open LongTails.Algorithms.AffineSoftmaxEstimator (smoothValue)

lemma first_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : LocalSeed → X) :
    (∫ seed : MultilevelSeed, f seed.2.1 ∂(multilevelLaw : Measure MultilevelSeed)) =
      ∫ seeds, f seeds ∂(localLaw : Measure LocalSeed) := by
  change (∫ z : ℕ × (LocalSeed × LocalSeed × LocalSeed), f z.2.1
    ∂((LongTails.Algorithms.AffineSoftmaxEstimator.countLaw : Measure ℕ).prod
      ((localLaw : Measure LocalSeed).prod
      ((localLaw : Measure LocalSeed).prod (localLaw : Measure LocalSeed))))) = _
  rw [integral_fun_snd (fun z : LocalSeed × LocalSeed × LocalSeed => f z.1), probReal_univ, one_smul]
  exact (triple_integrals localLaw f).1

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (C : Set E) (s : Snapshot ι E) (τ μ L r δ : ℝ)
  (reply : ι × E → ℝ × E)

lemma levelPlan_integrable (j : ℕ) :
    Integrable (fun seeds => Program.eval reply (levelPlan C s τ μ L r δ j seeds))
      (localLaw : Measure LocalSeed) :=
  AffineResidualLocal.localPlan_observable_integrable C s τ μ L r (δ / 2 ^ j) reply id _

lemma levelPlan_squared_integrable (j : ℕ) (u : E) :
    Integrable (fun seeds => ‖Program.eval reply (levelPlan C s τ μ L r δ j seeds) - u‖ ^ 2)
      (localLaw : Measure LocalSeed) :=
  AffineResidualLocal.localPlan_observable_integrable C s τ μ L r (δ / 2 ^ j) reply
    (fun x => ‖x - u‖ ^ 2) _

lemma multilevelPlan_eval (J : ℕ) (seed : MultilevelSeed) :
    Program.eval reply (multilevelPlan C s τ μ L r δ J seed) =
      Program.eval reply (levelPlan C s τ μ L r δ 0 seed.2.1) +
      if seed.1 + 1 ≤ J then (2 : ℝ) ^ (seed.1 + 1) •
        (Program.eval reply (levelPlan C s τ μ L r δ (seed.1 + 1) seed.2.2.1) -
          Program.eval reply (levelPlan C s τ μ L r δ seed.1 seed.2.2.2)) else 0 := by
  by_cases h : seed.1 + 1 ≤ J
  · simp only [multilevelPlan, Program.eval_bind, ite_eq_left h, Program.eval_map]
  · simp only [multilevelPlan, Program.eval_bind, ite_eq_right h, Program.eval, add_zero]

lemma multilevelPlan_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (J : ℕ) : Measurable (fun seed => Program.eval reply (multilevelPlan C s τ μ L r δ J seed)) := by
  have hm (j : ℕ) : Measurable (fun seeds => Program.eval reply (levelPlan C s τ μ L r δ j seeds)) :=
    AffineResidualLocal.localPlan_observable_measurable C s τ μ L r (δ / 2 ^ j) reply id
  simp_rw [multilevelPlan_eval]
  apply measurable_from_prod_countable_right
  intro k
  by_cases hk : k + 1 ≤ J
  · simp only [hk, ite_true]
    exact ((hm 0).comp measurable_fst).add
      ((((hm (k + 1)).comp measurable_snd.fst).sub
        ((hm k).comp measurable_snd.snd)).const_smul ((2 : ℝ) ^ (k + 1)))
  · simpa only [hk, ite_false, add_zero, Function.comp_def] using (hm 0).comp measurable_fst

lemma multilevelPlan_queriesWithin (hC : IsCompact C) (hne : C.Nonempty)
    (J : ℕ) (seed : MultilevelSeed) :
    AffineSoftmaxQuerySafety.QueriesWithin reply (fun q => q.2 ∈ C)
      (multilevelPlan C s τ μ L r δ J seed) := by
  apply AffineSoftmaxQuerySafety.queriesWithin_bind
  · exact AffineResidualExecution.localPlan_queriesWithin hC hne _ _ _ _ _ _ _ _
  · split_ifs
    · apply AffineSoftmaxQuerySafety.queriesWithin_bind
      · exact AffineResidualExecution.localPlan_queriesWithin hC hne _ _ _ _ _ _ _ _
      · apply AffineSoftmaxQuerySafety.queriesWithin_map
        exact AffineResidualExecution.localPlan_queriesWithin hC hne _ _ _ _ _ _ _ _
    · trivial

lemma multilevelPlan_finite_range (J : ℕ) :
    (Set.range (fun seed => Program.eval reply (multilevelPlan C s τ μ L r δ J seed))).Finite := by
  let level := fun j seeds => Program.eval reply (levelPlan C s τ μ L r δ j seeds)
  have hl j : (Set.range (level j)).Finite :=
    AffineResidualLocal.localPlan_observable_finite_range C s τ μ L r (δ / 2 ^ j) reply id
  let value := fun j (seeds : LocalSeed × LocalSeed × LocalSeed) =>
    level 0 seeds.1 + (2 : ℝ) ^ (j + 1) • (level (j + 1) seeds.2.1 - level j seeds.2.2)
  have hv j : (Set.range (value j)).Finite := by
    apply (((hl 0).prod ((hl (j + 1)).prod (hl j))).image
      (fun z : E × E × E => z.1 + (2 : ℝ) ^ (j + 1) • (z.2.1 - z.2.2))).subset
    rintro _ ⟨seeds, rfl⟩
    exact ⟨(level 0 seeds.1, level (j + 1) seeds.2.1, level j seeds.2.2),
      ⟨⟨seeds.1, rfl⟩, ⟨seeds.2.1, rfl⟩, ⟨seeds.2.2, rfl⟩⟩, rfl⟩
  have hU : (⋃ j ∈ (↑(Finset.range J) : Set ℕ), Set.range (value j)).Finite :=
    (Finset.finite_toSet _).biUnion (fun j _ => hv j)
  apply ((hl 0).union hU).subset
  rintro _ ⟨seed, rfl⟩
  dsimp only
  rw [multilevelPlan_eval]
  by_cases hk : seed.1 + 1 ≤ J
  · apply Or.inr
    simp only [hk, ite_true]
    exact Set.mem_iUnion.mpr ⟨seed.1, Set.mem_iUnion.mpr
      ⟨by simpa only [Finset.mem_coe, Finset.mem_range] using (Nat.lt_of_succ_le hk), ⟨seed.2, rfl⟩⟩⟩
  · apply Or.inl
    simp only [hk, ite_false, add_zero]
    exact ⟨seed.2.1, rfl⟩

lemma cachedProxGradientPlan_finite_range (σ β : ℝ) :
    (Set.range (fun seed => Program.eval reply (cachedProxGradientPlan C s τ μ L r σ β seed))).Finite := by
  simp only [cachedProxGradientPlan, Program.eval_map]
  exact ((multilevelPlan_finite_range C s τ μ L r _ reply _).image (fun x => μ • (s.anchor - x))).subset
    (by rintro _ ⟨seed, rfl⟩; exact ⟨_, ⟨seed, rfl⟩, rfl⟩)

lemma multilevelPlan_integrable (J : ℕ) :
    Integrable (fun seed => Program.eval reply (multilevelPlan C s τ μ L r δ J seed))
      (multilevelLaw : Measure MultilevelSeed) := by
  have hh := independent_level_integrable localLaw
    (fun j seeds => Program.eval reply (levelPlan C s τ μ L r δ j seeds))
    (levelPlan_integrable C s τ μ L r δ reply) J
  simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk] using hh

lemma multilevelPlan_moments [FiniteDimensional ℝ E] (J : ℕ) (u : E) {v : ℝ}
    (hb : ∀ j, (∫ seeds, ‖Program.eval reply (levelPlan C s τ μ L r δ j seeds) - u‖ ^ 2
      ∂(localLaw : Measure LocalSeed)) ≤ v / 2 ^ j) :
    (∫ seed, Program.eval reply (multilevelPlan C s τ μ L r δ J seed)
      ∂(multilevelLaw : Measure MultilevelSeed)) =
      (∫ seeds, Program.eval reply (levelPlan C s τ μ L r δ J seeds) ∂(localLaw : Measure LocalSeed)) ∧
    Integrable (fun seed => ‖Program.eval reply (multilevelPlan C s τ μ L r δ J seed) - u‖ ^ 2)
      (multilevelLaw : Measure MultilevelSeed) ∧
    (∫ seed, ‖Program.eval reply (multilevelPlan C s τ μ L r δ J seed) - u‖ ^ 2
      ∂(multilevelLaw : Measure MultilevelSeed)) ≤ (2 + 12 * (J : ℝ)) * v := by
  have hi := levelPlan_integrable C s τ μ L r δ reply
  have hi2 := fun j => levelPlan_squared_integrable C s τ μ L r δ reply j u
  have hm := independent_level_mean localLaw _ hi J
  have hsq := independent_level_second_moment localLaw _ u hi hi2 hb J
  constructor
  · simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk] using hm
  · simpa only [multilevelPlan_eval, multilevelLaw, ProbabilityMeasure.coe_mk] using hsq

lemma multilevelPlan_cost (J : ℕ) (seed : MultilevelSeed) :
    Program.cost reply (multilevelPlan C s τ μ L r δ J seed) =
      2 * LongTails.Algorithms.AffineResidualSaddle.localSteps (Fintype.card ι) τ μ L r δ +
      if seed.1 + 1 ≤ J then
        2 * LongTails.Algorithms.AffineResidualSaddle.localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ (seed.1 + 1)) +
          2 * LongTails.Algorithms.AffineResidualSaddle.localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ seed.1) else 0 := by
  by_cases h : seed.1 + 1 ≤ J
  · simp only [multilevelPlan, Program.cost_bind, ite_eq_left h, Program.cost_map,
      levelPlan, AffineResidualExecution.localPlan_cost, pow_zero, div_one]
  · simp only [multilevelPlan, Program.cost_bind, ite_eq_right h, Program.cost,
      levelPlan, AffineResidualExecution.localPlan_cost, pow_zero, div_one]

lemma cachedProxGradientPlan_queriesWithin (hC : IsCompact C) (hne : C.Nonempty)
    (σ β : ℝ) (seed : MultilevelSeed) :
    AffineSoftmaxQuerySafety.QueriesWithin reply (fun q => q.2 ∈ C)
      (cachedProxGradientPlan C s τ μ L r σ β seed) := by
  apply AffineSoftmaxQuerySafety.queriesWithin_map
  exact multilevelPlan_queriesWithin C s τ μ L r _ reply hC hne _ seed

lemma cachedProxGradientPlan_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (σ β : ℝ) : Measurable (fun seed => Program.eval reply
      (cachedProxGradientPlan C s τ μ L r σ β seed)) := by
  simp only [cachedProxGradientPlan, Program.eval_map]
  exact (measurable_const.sub (multilevelPlan_measurable C s τ μ L r _ reply _)).const_smul μ

lemma cachedProxGradientPlan_moments [FiniteDimensional ℝ E]
    (C : Set E) (s : Snapshot ι E) (τ L r : ℝ) {μ σ β : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ) (hβ : 0 < β)
    (reply : ι × E → ℝ × E) (u : E) :
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
    (∀ j, (∫ seeds, ‖Program.eval reply (levelPlan C s τ μ L r δ j seeds) - u‖ ^ 2
      ∂(localLaw : Measure LocalSeed)) ≤ (2 * δ / μ) / 2 ^ j) →
    let g := fun seed => Program.eval reply (cachedProxGradientPlan C s τ μ L r σ β seed)
    Integrable g (multilevelLaw : Measure MultilevelSeed) ∧
      ‖(∫ seed, g seed ∂(multilevelLaw : Measure MultilevelSeed)) - μ • (s.anchor - u)‖ ≤ β ∧
      Integrable (fun seed => ‖g seed - μ • (s.anchor - u)‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) ∧
      (∫ seed, ‖g seed - μ • (s.anchor - u)‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  dsimp only
  intro hb
  have hi := levelPlan_integrable C s τ μ L r δ reply
  have hi2 := fun j => levelPlan_squared_integrable C s τ μ L r δ reply j u
  let level := fun j seeds => Program.eval reply (levelPlan C s τ μ L r δ j seeds)
  let Y := fun seed => Program.eval reply (multilevelPlan C s τ μ L r δ J seed)
  let Z := fun seed : MultilevelSeed => level J seed.2.1
  have hYi : Integrable Y (multilevelLaw : Measure MultilevelSeed) :=
    multilevelPlan_integrable C s τ μ L r δ reply J
  have hZi : Integrable Z (multilevelLaw : Measure MultilevelSeed) :=
    ((hi J).comp_fst ((localLaw : Measure LocalSeed).prod (localLaw : Measure LocalSeed))).comp_snd
      (countLaw : Measure ℕ)
  have hZ2 : Integrable (fun seed => ‖Z seed - u‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) :=
    ((hi2 J).comp_fst ((localLaw : Measure LocalSeed).prod (localLaw : Measure LocalSeed))).comp_snd
      (countLaw : Measure ℕ)
  have hYmom := multilevelPlan_moments C s τ μ L r δ reply J u hb
  have hmean : (∫ seed, Y seed ∂(multilevelLaw : Measure MultilevelSeed)) =
      ∫ seed, Z seed ∂(multilevelLaw : Measure MultilevelSeed) :=
    hYmom.1.trans (first_integral (level J)).symm
  have ht := multilevel_tuning hμ hσ hβ
  have hYbound : μ ^ 2 * (∫ seed, ‖Y seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hYmom.2.2 (sq_nonneg μ)
    have he : μ ^ 2 * ((2 + 12 * (J : ℝ)) * (2 * δ / μ)) = σ ^ 2 := by
      rw [← mul_assoc]
      exact ht.2.1
    exact hh.trans_eq he
  have hZbound : μ ^ 2 * (∫ seed, ‖Z seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ β ^ 2 := by
    rw [show (∫ seed, ‖Z seed - u‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) =
      (∫ seeds, ‖level J seeds - u‖ ^ 2 ∂(localLaw : Measure LocalSeed)) from
      first_integral (fun seeds => ‖level J seeds - u‖ ^ 2)]
    exact (mul_le_mul_of_nonneg_left (hb J) (sq_nonneg μ)).trans ht.2.2
  have hh := prox_gradient_moments multilevelLaw Y Z s.anchor u hμ.le hβ.le hYi hZi hYmom.2.1 hZ2
    hmean hYbound hZbound
  simpa only [cachedProxGradientPlan, Program.eval_map, J, δ, Y] using hh

lemma levelPlan_distance [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : ι → E → ℝ)
    (hC : IsCompact C) (hconv : Convex ℝ C)
    {G : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor) C z) (j : ℕ) :
    (∫ ω, ‖Program.eval (fun q => (f q.1 q.2, gradient (f q.1) q.2))
      (levelPlan C s τ μ L r δ j ω) - z‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval).prod volume)) ≤ (2 * δ / μ) / 2 ^ j := by
  have hh := AffineResidualLocal.localPlan_distance C s τ μ f hC hconv hμ hτ hL
    (by positivity : 0 < δ / 2 ^ j) hf hg hlip hbound ha hvalue hfield hradius z hz hmin
  have he : 2 * (δ / 2 ^ j) / μ = (2 * δ / μ) / 2 ^ j := by ring
  rw [he] at hh
  exact hh

lemma smooth_prox_gradient_moments [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : ι → E → ℝ)
    (hC : IsCompact C) (hconv : Convex ℝ C)
    {G σ β : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hσ : 0 < σ) (hβ : 0 < β)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor) C z) :
    let g := fun seed => Program.eval (fun q => (f q.1 q.2, gradient (f q.1) q.2))
      (cachedProxGradientPlan C s τ μ L r σ β seed)
    Integrable g (multilevelLaw : Measure MultilevelSeed) ∧
      ‖(∫ seed, g seed ∂(multilevelLaw : Measure MultilevelSeed)) - μ • (s.anchor - z)‖ ≤ β ∧
      Integrable (fun seed => ‖g seed - μ • (s.anchor - z)‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) ∧
      (∫ seed, ‖g seed - μ • (s.anchor - z)‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
  apply cachedProxGradientPlan_moments C s τ L r hμ hσ hβ _ z
  intro j
  apply levelPlan_distance C s τ μ L r _ f hC hconv hμ hτ hL
    (by positivity) hf hg hlip hbound ha hvalue hfield hradius z hz hmin j

lemma oracle_prox_gradient_moments [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : ι → E → ℝ)
    (hC : IsCompact C) (hconv : Convex ℝ C)
    {G σ β : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hL : 0 ≤ L) (hσ : 0 < σ) (hβ : 0 < β)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    (ha : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hradius : ∀ x ∈ C, ‖x - s.anchor‖ ≤ r) (z : E) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (fun y => smoothValue τ (fun i => f i y)) μ s.anchor) C z)
    (hreply : ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x)) :
    let g := fun seed => Program.eval reply
      (cachedProxGradientPlan C s τ μ L r σ β seed)
    Integrable g (multilevelLaw : Measure MultilevelSeed) ∧
      ‖(∫ seed, g seed ∂(multilevelLaw : Measure MultilevelSeed)) - μ • (s.anchor - z)‖ ≤ β ∧
      Integrable (fun seed => ‖g seed - μ • (s.anchor - z)‖ ^ 2) (multilevelLaw : Measure MultilevelSeed) ∧
      (∫ seed, ‖g seed - μ • (s.anchor - z)‖ ^ 2 ∂(multilevelLaw : Measure MultilevelSeed)) ≤ σ ^ 2 := by
  have he (seed : MultilevelSeed) := AffineResidualExecution.eval_eq_of_queriesWithin reply
    (fun q => (f q.1 q.2, gradient (f q.1) q.2)) (fun q => q.2 ∈ C)
    (cachedProxGradientPlan C s τ μ L r σ β seed)
    (cachedProxGradientPlan_queriesWithin C s τ μ L r reply hC ⟨s.anchor, ha⟩ σ β seed)
    (fun q hq => hreply q.1 q.2 hq)
  dsimp only
  simp_rw [he]
  exact smooth_prox_gradient_moments C s τ μ L r f hC hconv hμ hτ hL hσ hβ
    hf hg hlip hbound ha hvalue hfield hradius z hz hmin

end LongTails.Proofs.AffineResidualMultilevel
