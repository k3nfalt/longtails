import LongTails.Proofs.EscapeChainAverage
import LongTails.Proofs.EscapeChainBadCount
import LongTails.Proofs.EscapeChainFreeze

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainProbability

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open scoped RealInnerProductSpace BigOperators ENNReal
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainFamily EscapeChainSmooth
open EscapeChainCounting EscapeChainRun EscapeChainInvariance EscapeChainPast EscapeChainCertificate
open EscapeChainMeasurable EscapeChainAverage EscapeChainBadCount EscapeChainFreeze
open LongTails.Proofs.AbcLowerMeasure

variable {d : ℕ} (c : Ctx d) (alg : Algorithm (Sp d) (Sp d) (Sp d))

section measurability

variable [MeasurableSpace alg.State] (hinit : Measurable alg.initial) (hq : Measurable alg.query)
  (hu : Measurable alg.update.uncurry) (hout : Measurable alg.output)

include hinit hq hu in
lemma runJ_measurable (θ : Hid c.n c.b) (j t : ℕ) :
    Measurable (fun z : alg.Seed × (ℕ → ℝ) => runJ c alg θ j z t) :=
  run_measurable alg hinit hq hu (ans c θ j) (ans_measurable c θ j) t

include hinit hq hu in
lemma yq_measurable (θ : Hid c.n c.b) (j t : ℕ) :
    Measurable (fun z : alg.Seed × (ℕ → ℝ) => yq c alg θ j z t) :=
  (measurable_snd.comp (hq.comp (runJ_measurable c alg hinit hq hu θ j t))).const_smul c.r0⁻¹

include hinit hq hu hout in
lemma yo_measurable (θ : Hid c.n c.b) (j : ℕ) :
    Measurable (fun z : alg.Seed × (ℕ → ℝ) => yo c alg θ j z) :=
  (hout.comp (runJ_measurable c alg hinit hq hu θ j c.N)).const_smul c.r0⁻¹

include hinit hq hu in
lemma rev_measurable (θ : Hid c.n c.b) (j l t : ℕ) :
    MeasurableSet {z : alg.Seed × (ℕ → ℝ) | rev c alg θ j l z t} := by
  have h := reveals_measurableSet c.K c.A (U c θ) (V c θ) l
  exact ((yq_measurable c alg hinit hq hu θ j t).prodMk
    ((measurable_pi_apply t).comp measurable_snd)) h

include hinit hq hu in
lemma win_measurable (θ : Hid c.n c.b) (j t : ℕ) :
    MeasurableSet {z : alg.Seed × (ℕ → ℝ) | Win c alg θ j z t} := by
  classical
  have hrev := rev_measurable c alg hinit hq hu θ
  have hset : {z : alg.Seed × (ℕ → ℝ) | Win c alg θ j z t} =
      {z | j = 0 ∧ t ≤ c.m} ∪ ({z | j ≠ 0} ∩ ⋃ s ∈ Finset.range t,
        ({z | t ≤ s + c.m} ∩ {z | rev c alg θ j (j - 1) z s} ∩
          ⋂ s' ∈ Finset.range s, {z | rev c alg θ j (j - 1) z s'}ᶜ)) := by
    ext z
    simp only [Win, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range, exists_prop]
    constructor
    · rintro (h | ⟨h0, s, hs, hst, hr, hmin⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h0, s, hs, ⟨hst, hr⟩, fun s' hs' => hmin s' hs'⟩
    · rintro (h | ⟨h0, s, hs, ⟨hst, hr⟩, hmin⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h0, s, hs, hst, hr, fun s' hs' => hmin s' hs'⟩
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.const _) ((MeasurableSet.const _).inter ?_)
  refine Finset.measurableSet_biUnion _ fun s _ => ?_
  refine ((MeasurableSet.const _).inter (hrev j (j - 1) s)).inter ?_
  exact Finset.measurableSet_biInter _ fun s' _ => (hrev j (j - 1) s').compl

include hinit hq hu in
lemma fast_measurable (θ : Hid c.n c.b) (j : ℕ) :
    MeasurableSet {z : alg.Seed × (ℕ → ℝ) | Fast c alg θ j z} := by
  have hset : {z : alg.Seed × (ℕ → ℝ) | Fast c alg θ j z} =
      ⋃ t ∈ Finset.range c.N, ({z | rev c alg θ j j z t} ∩ {z | Win c alg θ j z t}) := by
    ext z
    simp only [Fast, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range,
      exists_prop]
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun t _ =>
    (rev_measurable c alg hinit hq hu θ j j t).inter (win_measurable c alg hinit hq hu θ j t)

lemma clean_measurable (K : ℕ) (u v : ℕ → Sp d) (j : ℕ) :
    MeasurableSet {y : Sp d | Clean K u v j y} := by
  have hset : {y : Sp d | Clean K u v j y} = ⋂ l ∈ Finset.range K,
      ({y | j ≤ l} ᶜ ∪ ({y | |⟪u l, y⟫| ≤ 1 / 128} ∩ {y | |⟪v l, y⟫| ≤ 1 / 128})) := by
    ext y
    simp only [Clean, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_union,
      Set.mem_compl_iff, Set.mem_inter_iff, not_le]
    constructor
    · intro h l hl
      by_cases hjl : j ≤ l
      · exact Or.inr (h l hjl hl)
      · exact Or.inl (by omega)
    · intro h l hjl hl
      rcases h l hl with h | h
      · omega
      · exact h
  rw [hset]
  refine Finset.measurableSet_biInter _ fun l _ => (MeasurableSet.const _).compl.union ?_
  exact (measurableSet_le ((continuous_const.inner continuous_id).abs.measurable) measurable_const).inter
    (measurableSet_le ((continuous_const.inner continuous_id).abs.measurable) measurable_const)

include hinit hq hu hout in
lemma bad_measurable (θ : Hid c.n c.b) :
    MeasurableSet {z : alg.Seed × (ℕ → ℝ) | Bad c alg θ z} := by
  have hset : {z : alg.Seed × (ℕ → ℝ) | Bad c alg θ z} = ⋃ j ∈ Finset.range (c.K + 1),
      ((⋃ t ∈ Finset.range c.N, ({z | ‖yq c alg θ j z t‖ ≤ 2 * radius c.K} ∩
        (fun z => yq c alg θ j z t) ⁻¹' {y | Clean c.K (U c θ) (V c θ) j y}ᶜ)) ∪
      ({z | ‖yo c alg θ j z‖ ≤ radius c.K} ∩
        (fun z => yo c alg θ j z) ⁻¹' {y | Clean c.K (U c θ) (V c θ) j y}ᶜ)) := by
    ext z
    simp only [Bad, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_compl_iff, Finset.mem_range, exists_prop, Nat.lt_succ_iff]
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun j _ => MeasurableSet.union ?_ ?_
  · refine Finset.measurableSet_biUnion _ fun t _ => ?_
    have hy := yq_measurable c alg hinit hq hu θ j t
    exact (measurableSet_le hy.norm measurable_const).inter
      (hy (clean_measurable c.K (U c θ) (V c θ) j).compl)
  · have hy := yo_measurable c alg hinit hq hu hout θ j
    exact (measurableSet_le hy.norm measurable_const).inter
      (hy (clean_measurable c.K (U c θ) (V c θ) j).compl)

end measurability

section bounds

noncomputable abbrev μ : Measure (alg.Seed × (ℕ → ℝ)) := (alg.law : Measure alg.Seed).prod stream

lemma yq_prefix (θ : Hid c.n c.b) (j t : ℕ) (z : alg.Seed × (ℕ → ℝ)) (ω' : ℕ → ℝ)
    (h : ∀ s < t, z.2 s = ω' s) : yq c alg θ j (z.1, ω') t = yq c alg θ j z t := by
  unfold yq runJ
  rw [run_prefix alg (ans c θ j) z.1 t (fun s hs => (h s hs).symm)]

lemma rev_prefix (θ : Hid c.n c.b) (j l s t : ℕ) (hs : s < t) (z : alg.Seed × (ℕ → ℝ)) (ω' : ℕ → ℝ)
    (h : ∀ s < t, z.2 s = ω' s) : rev c alg θ j l (z.1, ω') s ↔ rev c alg θ j l z s := by
  unfold rev
  simp only [yq_prefix c alg θ j s z ω' (fun s' hs' => h s' (by omega)), (h s hs).symm]

lemma win_prefix (θ : Hid c.n c.b) (j t : ℕ) (z : alg.Seed × (ℕ → ℝ)) (ω' : ℕ → ℝ)
    (h : ∀ s < t, z.2 s = ω' s) : Win c alg θ j (z.1, ω') t ↔ Win c alg θ j z t := by
  unfold Win
  constructor
  · rintro (h0 | ⟨h0, s, hs, hst, hr, hmin⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨h0, s, hs, hst, (rev_prefix c alg θ j _ s t hs z ω' h).1 hr, fun s' hs' => ?_⟩
      rw [← rev_prefix c alg θ j _ s' t (by omega) z ω' h]; exact hmin s' hs'
  · rintro (h0 | ⟨h0, s, hs, hst, hr, hmin⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨h0, s, hs, hst, (rev_prefix c alg θ j _ s t hs z ω' h).2 hr, fun s' hs' => ?_⟩
      rw [rev_prefix c alg θ j _ s' t (by omega) z ω' h]; exact hmin s' hs'

variable [MeasurableSpace alg.State] (hinit : Measurable alg.initial) (hq : Measurable alg.query)
  (hu : Measurable alg.update.uncurry) (hout : Measurable alg.output)

include hinit hq hu in
lemma fast_step (θ : Hid c.n c.b) {j : ℕ} (hj : j < c.K) (t : ℕ) :
    μ alg {z | rev c alg θ j j z t ∧ Win c alg θ j z t} =
      ∫⁻ z, ENNReal.ofReal (winInd c alg θ j z t *
        prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)) ∂(μ alg) := by
  classical
  have hA0 : 0 < c.A := lt_of_lt_of_le (by norm_num) c.hA
  have hy := yq_measurable c alg hinit hq hu θ j t
  have hW := win_measurable c alg hinit hq hu θ j t
  let φ : alg.Seed × (ℕ → ℝ) → ℝ≥0∞ := fun z => if Win c alg θ j z t then 1 else 0
  let a : alg.Seed × (ℕ → ℝ) → ℝ := fun z => start c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)
  let p : alg.Seed × (ℕ → ℝ) → ℝ := fun z => prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)
  have hφ : Measurable φ := Measurable.ite hW measurable_const measurable_const
  have ha : Measurable a := (start_continuous _ _ _ _ _).measurable.comp hy
  have hp : Measurable p := (prob_continuous _ _ _ _ _).measurable.comp hy
  have hfr := freeze (alg.law : Measure alg.Seed) t φ a p hφ ha hp
    (fun z ω' h => by simp only [φ, win_prefix c alg θ j t z ω' h])
    (fun z ω' h => by simp only [a, yq_prefix c alg θ j t z ω' h])
    (fun z ω' h => by simp only [p, yq_prefix c alg θ j t z ω' h])
    (fun _ => start_nonneg hA0 j _)
    (fun _ => interval_fits (frameθ c θ) c.hA hj _)
  have hL : μ alg {z | rev c alg θ j j z t ∧ Win c alg θ j z t} =
      ∫⁻ z, φ z * (if a z ≤ z.2 t ∧ z.2 t < a z + p z then 1 else 0) ∂(μ alg) := by
    have hset : {z | rev c alg θ j j z t ∧ Win c alg θ j z t} =
        {z | rev c alg θ j j z t} ∩ {z | Win c alg θ j z t} := rfl
    rw [hset, ← lintegral_indicator_one ((rev_measurable c alg hinit hq hu θ j j t).inter hW)]
    refine lintegral_congr fun z => ?_
    simp only [Set.indicator, φ, a, p, rev, reveals, Pi.one_apply]
    split_ifs <;> simp_all
  rw [hL, hfr]
  refine lintegral_congr fun z => ?_
  simp only [φ, p, winInd]
  split_ifs <;> simp

include hinit hq hu in
theorem fast_sum (j : ℕ) (hj : j < c.K) :
    ∑ θ : Hid c.n c.b, μ alg {z | Fast c alg θ j z} ≤
      ENNReal.ofReal (2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * ((c.m + 1) *
        Fintype.card (Hid c.n c.b))) := by
  classical
  set q := 2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) with hqd
  have hA0 : 0 < c.A := lt_of_lt_of_le (by norm_num) c.hA
  have hgap : (0 : ℝ) < c.n - (2 * c.K + 1) := by
    have := c.hK
    have : ((2 * c.K + 2 : ℕ) : ℝ) ≤ c.n := by exact_mod_cast this
    push_cast at this; linarith
  have hb0 : (0 : ℝ) < c.b := by exact_mod_cast c.hb
  have hq0 : 0 ≤ q := by positivity
  have hunion : ∀ θ : Hid c.n c.b, μ alg {z | Fast c alg θ j z} ≤
      ∑ t ∈ Finset.range c.N, μ alg {z | rev c alg θ j j z t ∧ Win c alg θ j z t} := by
    intro θ
    have hset : {z | Fast c alg θ j z} = ⋃ t ∈ Finset.range c.N,
        {z | rev c alg θ j j z t ∧ Win c alg θ j z t} := by
      ext z
      simp only [Fast, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [hset]
    exact measure_biUnion_finset_le _ _
  refine (Finset.sum_le_sum fun θ _ => hunion θ).trans ?_
  rw [Finset.sum_comm]
  simp_rw [fast_step c alg hinit hq hu _ hj]
  have hmeasW : ∀ θ t, Measurable fun z : alg.Seed × (ℕ → ℝ) =>
      ENNReal.ofReal (winInd c alg θ j z t * prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)) := by
    intro θ t
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Measurable.ite (win_measurable c alg hinit hq hu θ j t) measurable_const measurable_const
    · exact (prob_continuous _ _ _ _ _).measurable.comp (yq_measurable c alg hinit hq hu θ j t)
  have hstep : ∀ t ∈ Finset.range c.N, ∑ θ : Hid c.n c.b, ∫⁻ z, ENNReal.ofReal (winInd c alg θ j z t *
      prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)) ∂(μ alg) ≤
      ∫⁻ z, ENNReal.ofReal (q * ∑ θ : Hid c.n c.b, winInd c alg θ j z t) ∂(μ alg) := by
    intro t _
    rw [← lintegral_finsetSum _ fun θ _ => hmeasW θ t]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ => mul_nonneg (winInd_nonneg c alg θ j z t)
      (prob_nonneg hA0 j _)]
    exact ENNReal.ofReal_le_ofReal (reveal_average c alg hj z t)
  refine (Finset.sum_le_sum hstep).trans ?_
  have hmeas2 : ∀ t, Measurable fun z : alg.Seed × (ℕ → ℝ) =>
      ENNReal.ofReal (q * ∑ θ : Hid c.n c.b, winInd c alg θ j z t) := by
    intro t
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Finset.measurable_sum _ fun θ _ => ?_))
    exact Measurable.ite (win_measurable c alg hinit hq hu θ j t) measurable_const measurable_const
  rw [← lintegral_finsetSum _ fun t _ => hmeas2 t]
  calc ∫⁻ z, ∑ t ∈ Finset.range c.N, ENNReal.ofReal (q * ∑ θ : Hid c.n c.b, winInd c alg θ j z t)
        ∂(μ alg)
      ≤ ∫⁻ _z, ENNReal.ofReal (q * ((c.m + 1) * Fintype.card (Hid c.n c.b))) ∂(μ alg) := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg hq0
          (Finset.sum_nonneg fun θ _ => winInd_nonneg c alg θ j z t)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left ?_ hq0
        calc ∑ θ : Hid c.n c.b, ∑ t ∈ Finset.range c.N, winInd c alg θ j z t
            ≤ ∑ _θ : Hid c.n c.b, ((c.m : ℝ) + 1) :=
              Finset.sum_le_sum fun θ _ => window_count c alg θ j z
          _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end bounds

section total

variable [MeasurableSpace alg.State] (hinit : Measurable alg.initial) (hq : Measurable alg.query)
  (hu : Measurable alg.update.uncurry) (hout : Measurable alg.output)

include hinit hq hu hout in
theorem total (S : Hid c.n c.b → Set (alg.Seed × (ℕ → ℝ))) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30)
    (hS : ∀ θ z, z ∈ S θ → Calm' c θ (yo c alg θ c.K z) g) (hK : 0 < c.K)
    (hm : 2 * c.N ≤ (c.m + 1) * c.K) :
    ∑ θ : Hid c.n c.b, μ alg (S θ) ≤
      ENNReal.ofReal (Fintype.card (Hid c.n c.b) * ((c.K + 1) * (c.N + 1) * c.K * 2 *
        (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2)))))) +
      2 * ENNReal.ofReal (2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * ((c.m + 1) *
        Fintype.card (Hid c.n c.b))) := by
  classical
  set Many : Hid c.n c.b → Set (alg.Seed × (ℕ → ℝ)) := fun θ =>
    {z | c.K < 2 * ((Finset.range c.K).filter (fun j => Fast c alg θ j z)).card}
  have hsub : ∀ θ, S θ ⊆ {z | Bad c alg θ z} ∪ Many θ := by
    intro θ z hz
    by_cases hb : Bad c alg θ z
    · exact Or.inl hb
    · exact Or.inr (many_fast c alg θ z hb hg0 hg (hS θ z hz) hK hm)
  have hle : ∀ θ, μ alg (S θ) ≤ μ alg {z | Bad c alg θ z} + μ alg (Many θ) :=
    fun θ => (measure_mono (hsub θ)).trans (measure_union_le _ _)
  refine (Finset.sum_le_sum fun θ _ => hle θ).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · have hind : ∀ θ, μ alg {z | Bad c alg θ z} =
        ∫⁻ z, ENNReal.ofReal (if Bad c alg θ z then 1 else 0) ∂(μ alg) := by
      intro θ
      rw [← lintegral_indicator_one (bad_measurable c alg hinit hq hu hout θ)]
      refine lintegral_congr fun z => ?_
      simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      split_ifs <;> simp
    simp_rw [hind]
    rw [← lintegral_finsetSum _ fun θ _ =>
      (show Measurable fun z => ENNReal.ofReal (if Bad c alg θ z then (1 : ℝ) else 0) from
        ENNReal.measurable_ofReal.comp
          (Measurable.ite (bad_measurable c alg hinit hq hu hout θ) measurable_const measurable_const))]
    calc ∫⁻ z, ∑ θ : Hid c.n c.b, ENNReal.ofReal (if Bad c alg θ z then 1 else 0) ∂(μ alg)
        ≤ ∫⁻ _z, ENNReal.ofReal (Fintype.card (Hid c.n c.b) * ((c.K + 1) * (c.N + 1) * c.K * 2 *
            (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2)))))) ∂(μ alg) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ => by split_ifs <;> norm_num]
          exact ENNReal.ofReal_le_ofReal (bad_count c alg z)
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  · have hmarkov : ∀ θ, μ alg (Many θ) ≤ (2 / c.K : ℝ≥0∞) *
        ∑ j ∈ Finset.range c.K, μ alg {z | Fast c alg θ j z} := by
      intro θ
      set f : alg.Seed × (ℕ → ℝ) → ℝ≥0∞ := fun z =>
        ∑ j ∈ Finset.range c.K, Set.indicator {z | Fast c alg θ j z} 1 z
      have hf : Measurable f := Finset.measurable_sum _ fun j _ =>
        (measurable_one.indicator (fast_measurable c alg hinit hq hu θ j))
      have hmany : Many θ ⊆ {z | ((c.K : ℝ≥0∞) / 2) ≤ f z} := by
        intro z hz
        simp only [Set.mem_ofPred_eq, Many] at hz ⊢
        have hfz : f z = (((Finset.range c.K).filter (fun j => Fast c alg θ j z)).card : ℝ≥0∞) := by
          simp only [f, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
        rw [hfz, ENNReal.div_le_iff (by norm_num) (by norm_num)]
        have : (c.K : ℝ≥0∞) ≤ (((Finset.range c.K).filter (fun j => Fast c alg θ j z)).card) * 2 := by
          rw [mul_comm]; exact_mod_cast (by omega)
        exact this
      have hint : ∫⁻ z, f z ∂(μ alg) = ∑ j ∈ Finset.range c.K, μ alg {z | Fast c alg θ j z} := by
        rw [lintegral_finsetSum _ fun j _ =>
          (measurable_one.indicator (fast_measurable c alg hinit hq hu θ j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_indicator_one (fast_measurable c alg hinit hq hu θ j)]
      have hm := mul_meas_ge_le_lintegral hf ((c.K : ℝ≥0∞) / 2) (μ := μ alg)
      rw [hint] at hm
      calc μ alg (Many θ) ≤ μ alg {z | ((c.K : ℝ≥0∞) / 2) ≤ f z} := measure_mono hmany
        _ ≤ (2 / c.K : ℝ≥0∞) * ∑ j ∈ Finset.range c.K, μ alg {z | Fast c alg θ j z} := by
          have hK0 : (c.K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
          have hKt : (c.K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          have hone : (2 / c.K : ℝ≥0∞) * (c.K / 2) = 1 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc ((c.K : ℝ≥0∞)⁻¹),
              ENNReal.inv_mul_cancel hK0 hKt, one_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          calc μ alg {z | ((c.K : ℝ≥0∞) / 2) ≤ f z}
              = (2 / c.K : ℝ≥0∞) * ((c.K / 2 : ℝ≥0∞) * μ alg {z | ((c.K : ℝ≥0∞) / 2) ≤ f z}) := by
                rw [← mul_assoc, hone, one_mul]
            _ ≤ _ := by gcongr
    refine (Finset.sum_le_sum fun θ _ => hmarkov θ).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hj : ∀ j ∈ Finset.range c.K, ∑ θ : Hid c.n c.b, μ alg {z | Fast c alg θ j z} ≤
        ENNReal.ofReal (2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * ((c.m + 1) *
          Fintype.card (Hid c.n c.b))) :=
      fun j hj => fast_sum c alg hinit hq hu j (Finset.mem_range.1 hj)
    calc (2 / c.K : ℝ≥0∞) * ∑ j ∈ Finset.range c.K, ∑ θ : Hid c.n c.b, μ alg {z | Fast c alg θ j z}
        ≤ (2 / c.K : ℝ≥0∞) * ∑ _j ∈ Finset.range c.K, ENNReal.ofReal (2 ^ 30 /
            (c.A * c.b * (c.n - (2 * c.K + 1))) * ((c.m + 1) * Fintype.card (Hid c.n c.b))) := by
          gcongr with j hj'; exact hj j hj'
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
          congr 1
          have hK0 : (c.K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
          have hKt : (c.K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          rw [ENNReal.div_mul_cancel hK0 hKt]

end total

end LongTails.Proofs.EscapeChainProbability
