import LongTails.Proofs.AffineSoftmaxMultilevel

open MeasureTheory

namespace LongTails.Proofs.AffineSoftmaxMultilevelCost

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Proofs.AffineSoftmaxMultilevel

lemma half_power_sum (J : ℕ) :
    (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1)) = 1 - (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma weighted_half_power_sum (J : ℕ) :
    (∑ k ∈ Finset.range J, ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1)) =
      2 - ((J : ℝ) + 2) * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma truncated_unweighted_moments {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (d : ℕ → Ω → ℝ)
    (hd : ∀ k, Integrable (d k) (Q : Measure Ω)) (J : ℕ) :
    Integrable (fun z : ℕ × Ω => if z.1 < J then d z.1 z.2 else 0)
      ((countLaw : Measure ℕ).prod (Q : Measure Ω)) ∧
    (∫ z : ℕ × Ω, (if z.1 < J then d z.1 z.2 else 0)
      ∂((countLaw : Measure ℕ).prod (Q : Measure Ω))) =
      ∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1) * (∫ ω, d k ω ∂(Q : Measure Ω)) := by
  let e := fun k ω => (1 / 2 : ℝ) ^ (k + 1) * d k ω
  have hei k : Integrable (e k) (Q : Measure Ω) := (hd k).const_mul _
  have hi := truncated_integrable Q e hei J
  have hm := truncated_random_mean Q e hei J
  have he (k : ℕ) (ω : Ω) : (2 : ℝ) ^ (k + 1) • e k ω = d k ω := by
    dsimp [e]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  simp_rw [he] at hi hm
  refine ⟨hi, ?_⟩
  simpa only [e, integral_const_mul] using hm

lemma independent_level_cost {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (level : ℕ → Ω → ℝ)
    (hi : ∀ j, Integrable (level j) (Q : Measure Ω)) (J : ℕ) :
    let P := (countLaw : Measure ℕ).prod
      ((Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)))
    let cost := fun z : ℕ × (Ω × Ω × Ω) => level 0 z.2.1 +
      (if z.1 + 1 ≤ J then level (z.1 + 1) z.2.2.1 + level z.1 z.2.2.2 else 0)
    Integrable cost P ∧
      (∫ z, cost z ∂P) = (∫ ω, level 0 ω ∂(Q : Measure Ω)) +
        ∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1) *
          ((∫ ω, level (k + 1) ω ∂(Q : Measure Ω)) + (∫ ω, level k ω ∂(Q : Measure Ω))) := by
  let T : ProbabilityMeasure (Ω × Ω × Ω) :=
    ⟨(Q : Measure Ω).prod ((Q : Measure Ω).prod (Q : Measure Ω)), inferInstance⟩
  let B := fun z : Ω × Ω × Ω => level 0 z.1
  let d := fun j (z : Ω × Ω × Ω) => level (j + 1) z.2.1 + level j z.2.2
  have hB : Integrable B (T : Measure _) := (hi 0).comp_fst _
  have hF j : Integrable (fun z : Ω × Ω × Ω => level j z.2.1) (T : Measure _) :=
    ((hi j).comp_fst (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hC j : Integrable (fun z : Ω × Ω × Ω => level j z.2.2) (T : Measure _) :=
    ((hi j).comp_snd (Q : Measure Ω)).comp_snd (Q : Measure Ω)
  have hd j : Integrable (d j) (T : Measure _) := (hF (j + 1)).add (hC j)
  have hh := truncated_unweighted_moments T d hd J
  have hsum := (hB.comp_snd (countLaw : Measure ℕ)).add hh.1
  change Integrable (fun z : ℕ × (Ω × Ω × Ω) => B z.2 +
    (if z.1 < J then d z.1 z.2 else 0)) ((countLaw : Measure ℕ).prod (T : Measure _)) at hsum
  have hm : (∫ z : ℕ × (Ω × Ω × Ω), B z.2 + (if z.1 < J then d z.1 z.2 else 0)
      ∂((countLaw : Measure ℕ).prod (T : Measure _))) =
      (∫ ω, level 0 ω ∂(Q : Measure Ω)) + ∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1) *
        ((∫ ω, level (k + 1) ω ∂(Q : Measure Ω)) + (∫ ω, level k ω ∂(Q : Measure Ω))) := by
    rw [integral_add (hB.comp_snd _) hh.1, integral_fun_snd B, probReal_univ, one_smul, hh.2]
    rw [show (∫ z, B z ∂(T : Measure _)) = (∫ ω, level 0 ω ∂(Q : Measure Ω)) from
      (triple_integrals Q (level 0)).1]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    change (∫ z : Ω × Ω × Ω, level (k + 1) z.2.1 + level k z.2.2
      ∂(T : Measure (Ω × Ω × Ω))) = _
    rw [integral_add (hF _) (hC _)]
    rw [show (∫ z : Ω × Ω × Ω, level (k + 1) z.2.1 ∂(T : Measure _)) =
      (∫ ω, level (k + 1) ω ∂(Q : Measure Ω)) from (triple_integrals Q (level (k + 1))).2.1]
    exact congrArg (_ + ·) (triple_integrals Q (level k)).2.2
  constructor
  · simpa only [T, B, d, ProbabilityMeasure.coe_mk, Nat.lt_iff_add_one_le] using hsum
  · simpa only [T, B, d, ProbabilityMeasure.coe_mk, Nat.lt_iff_add_one_le] using hm

lemma multilevel_cost_sum_le (c : ℕ → ℝ) {A B M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hc : ∀ j, c j ≤ A * (M + j) + B * 2 ^ j) (J : ℕ) :
    c 0 + (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1) * (c (k + 1) + c k)) ≤
      A * (3 * M + 4) + B * (1 + 3 * (J : ℝ) / 2) := by
  have hterm k : (1 / 2 : ℝ) ^ (k + 1) * (c (k + 1) + c k) ≤
      (2 * A * M) * (1 / 2 : ℝ) ^ (k + 1) +
        (2 * A) * (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1)) + 3 * B / 2 := by
    have hp : (1 / 2 : ℝ) ^ (k + 1) * 2 ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
    have hq : (1 / 2 : ℝ) ^ (k + 1) * 2 ^ k = 1 / 2 := by
      rw [pow_succ (2 : ℝ) k] at hp
      linarith
    have hh := mul_le_mul_of_nonneg_left (add_le_add (hc (k + 1)) (hc k))
      (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (k + 1))
    push_cast at hh
    calc
      _ ≤ (1 / 2 : ℝ) ^ (k + 1) *
          (A * (M + ((k : ℝ) + 1)) + B * 2 ^ (k + 1) + (A * (M + k) + B * 2 ^ k)) := hh
      _ = A * (2 * M + 2 * (k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1) +
          B * ((1 / 2 : ℝ) ^ (k + 1) * 2 ^ (k + 1) + (1 / 2 : ℝ) ^ (k + 1) * 2 ^ k) := by ring
      _ ≤ _ := by
        rw [hp, hq]
        nlinarith [mul_nonneg hA (show 0 ≤ (1 / 2 : ℝ) ^ (k + 1) by positivity)]
  have hsum := Finset.sum_le_sum (s := Finset.range J) (fun k _ => hterm k)
  have hpsum : (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1)) ≤ 1 := by
    rw [half_power_sum]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J]
  have hwsum : (∑ k ∈ Finset.range J, ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1)) ≤ 2 := by
    rw [weighted_half_power_sum]
    have hh : 0 ≤ ((J : ℝ) + 2) * (1 / 2 : ℝ) ^ J := by positivity
    linarith
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hp := mul_le_mul_of_nonneg_left hpsum (show 0 ≤ 2 * A * M by positivity)
  have hw := mul_le_mul_of_nonneg_left hwsum (show 0 ≤ 2 * A by positivity)
  have hzero := hc 0
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at hzero
  nlinarith

lemma levelPlan_cost_bound {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ L : ℝ) {G r μ δ : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hμ : 0 < μ) (hδ : 0 < δ)
    (project : E → E) (reply : ι × E → ℝ × E) (j : ℕ) :
    let S := L + 2 * G ^ 2 / τ + μ
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    Integrable (fun seeds => (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ project j seeds) : ℝ))
      (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _) ∧
    (∫ seeds, (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ project j seeds) : ℝ)
      ∂(LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)) ≤
      (16 * Real.sqrt (S / μ) + 4) *
        ((LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (G * r) δ : ℝ) + j) +
      (1024 * V / (μ * δ)) * 2 ^ j := by
  let S := L + 2 * G ^ 2 / τ + μ
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have heps : 0 < δ / (2 : ℝ) ^ j := by positivity
  constructor
  · unfold LongTails.Algorithms.AffineSoftmaxProx.levelPlan
      LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
    exact (AffineSoftmaxRestarts.restartPlan_cost_moments s τ μ _ _ project s.anchor reply _).1
  · have hc := AffineSoftmaxRestarts.restartPlan_expected_cost_le s τ (S := S) hV hμ
      (mul_pos hG hr) heps project s.anchor reply
    have hj := AffineSoftmaxRestarts.restartRounds_scaled (d := G * r) hδ j
    have hjr : (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds
        (G * r) (δ / 2 ^ j) : ℝ) ≤
        (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (G * r) δ : ℝ) + j := by
      exact_mod_cast hj
    have ha := mul_le_mul_of_nonneg_right hjr
      (show 0 ≤ 16 * Real.sqrt (S / μ) + 4 by positivity)
    have hn : 1024 * V / (μ * (δ / 2 ^ j)) = (1024 * V / (μ * δ)) * 2 ^ j := by
      field_simp
    have hh := hc.trans (add_le_add ha (le_refl (1024 * V / (μ * (δ / 2 ^ j)))))
    rw [hn] at hh
    simpa only [LongTails.Algorithms.AffineSoftmaxProx.levelPlan,
      LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan,
      LongTails.Algorithms.AffineSoftmaxProx.proxLaw, ProbabilityMeasure.coe_mk, S, V, mul_comm] using hh

lemma multilevelPlan_cost_moments {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ L G r μ δ : ℝ) (project : E → E) (J : ℕ)
    (reply : ι × E → ℝ × E)
    (hi : ∀ j, Integrable (fun seeds => (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ project j seeds) : ℝ))
      (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)) :
    let c := fun j => ∫ seeds, (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ project j seeds) : ℝ)
      ∂(LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)
    Integrable (fun seed => (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelPlan s τ L G r μ δ project J seed) : ℝ))
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _) ∧
    (∫ seed, (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelPlan s τ L G r μ δ project J seed) : ℝ)
      ∂(LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _)) =
      c 0 + ∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ (k + 1) * (c (k + 1) + c k) := by
  let level := fun j seeds => (OracleTemplate.ComponentEnvelope.Program.cost reply
    (LongTails.Algorithms.AffineSoftmaxProx.levelPlan s τ L G r μ δ project j seeds) : ℝ)
  have hh := independent_level_cost LongTails.Algorithms.AffineSoftmaxProx.proxLaw level hi J
  have he (seed : LongTails.Algorithms.AffineSoftmaxProx.MultilevelSeed) :
      (OracleTemplate.ComponentEnvelope.Program.cost reply
        (LongTails.Algorithms.AffineSoftmaxProx.multilevelPlan s τ L G r μ δ project J seed) : ℝ) =
      level 0 seed.2.1 + (if seed.1 + 1 ≤ J then level (seed.1 + 1) seed.2.2.1 + level seed.1 seed.2.2.2 else 0) := by
    rw [AffineSoftmaxMultilevel.multilevelPlan_cost]
    by_cases h : seed.1 + 1 ≤ J <;> simp only [h, ite_true, ite_false, Nat.cast_add, Nat.cast_zero, level]
  constructor
  · exact hh.1.congr (Filter.Eventually.of_forall (fun seed => (he seed).symm))
  · calc
      _ = ∫ seed : LongTails.Algorithms.AffineSoftmaxProx.MultilevelSeed, level 0 seed.2.1 +
          (if seed.1 + 1 ≤ J then level (seed.1 + 1) seed.2.2.1 + level seed.1 seed.2.2.2 else 0)
          ∂(LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _) :=
        integral_congr_ae (Filter.Eventually.of_forall he)
      _ = _ := hh.2

lemma multilevelPlan_cost_le {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ L : ℝ) {G r μ δ : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hμ : 0 < μ) (hδ : 0 < δ)
    (project : E → E) (reply : ι × E → ℝ × E) (J : ℕ) :
    let S := L + 2 * G ^ 2 / τ + μ
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    (∫ seed, (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelPlan s τ L G r μ δ project J seed) : ℝ)
      ∂(LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _)) ≤
      (16 * Real.sqrt (S / μ) + 4) *
        (3 * (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (G * r) δ : ℝ) + 4) +
      (1024 * V / (μ * δ)) * (1 + 3 * (J : ℝ) / 2) := by
  have hi j := (levelPlan_cost_bound s τ L hG hr hμ hδ project reply j).1
  have hh := multilevelPlan_cost_moments s τ L G r μ δ project J reply hi
  dsimp only at hh ⊢
  rw [hh.2]
  exact multilevel_cost_sum_le _ (by positivity) (Nat.cast_nonneg _)
    (fun j => (levelPlan_cost_bound s τ L hG hr hμ hδ project reply j).2) J

lemma cachedProxGradientPlan_cost_moments {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Snapshot ι E) (τ L β : ℝ) {G r μ σ : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hμ : 0 < μ) (hσ : 0 < σ)
    (project : E → E) (reply : ι × E → ℝ × E) :
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let C := 2 + 12 * (J : ℝ)
    let δ := σ ^ 2 / (2 * μ * C)
    let S := L + 2 * G ^ 2 / τ + μ
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    Integrable (fun seed => (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxGradientPlan s τ L G r μ σ β project seed) : ℝ))
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _) ∧
    (∫ seed, (OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxGradientPlan s τ L G r μ σ β project seed) : ℝ)
      ∂(LongTails.Algorithms.AffineSoftmaxProx.multilevelLaw : Measure _)) ≤
      (16 * Real.sqrt (S / μ) + 4) *
        (3 * (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (G * r) δ : ℝ) + 4) +
      1024 * V * C * (2 + 3 * (J : ℝ)) / σ ^ 2 := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let C := 2 + 12 * (J : ℝ)
  let δ := σ ^ 2 / (2 * μ * C)
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hi j := (levelPlan_cost_bound s τ L hG hr hμ hδ project reply j).1
  have hmi := (multilevelPlan_cost_moments s τ L G r μ δ project J reply hi).1
  have hc := multilevelPlan_cost_le s τ L hG hr hμ hδ project reply J
  have he : (1024 * V / (μ * δ)) * (1 + 3 * (J : ℝ) / 2) =
      1024 * V * C * (2 + 3 * (J : ℝ)) / σ ^ 2 := by
    dsimp [δ]
    field_simp
  dsimp only at hc
  change _ ≤ _ + (1024 * V / (μ * δ)) * (1 + 3 * (J : ℝ) / 2) at hc
  rw [he] at hc
  constructor
  · simpa only [LongTails.Algorithms.AffineSoftmaxProx.cachedProxGradientPlan,
      OracleTemplate.ComponentEnvelope.Program.cost_map, J, δ, C] using hmi
  · simpa only [LongTails.Algorithms.AffineSoftmaxProx.cachedProxGradientPlan,
      OracleTemplate.ComponentEnvelope.Program.cost_map, J, δ, C, V] using hc

lemma multilevelProxPlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L G r μ δ : ℝ) (project : E → E) (J : ℕ)
    (seed : LongTails.Algorithms.AffineSoftmaxProx.MultilevelSeed) (reply : Fin m × E → ℝ × E) :
    OracleTemplate.ComponentEnvelope.Program.cost reply
      (LongTails.Algorithms.AffineSoftmaxProx.multilevelProxPlan m center τ L G r μ δ project J seed) =
      m + OracleTemplate.ComponentEnvelope.Program.cost reply
        (LongTails.Algorithms.AffineSoftmaxProx.multilevelPlan
          (OracleTemplate.ComponentEnvelope.Program.eval reply
            (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m center)) τ L G r μ δ project J seed) := by
  simp only [LongTails.Algorithms.AffineSoftmaxProx.multilevelProxPlan,
    OracleTemplate.ComponentEnvelope.Program.cost_bind, AffineSoftmaxExecution.cachePlan_cost]

lemma measurable_restart_cost_sum {Z : Type*} [MeasurableSpace Z]
    (seeds : Z → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed)
    (hs : ∀ j k, Measurable (fun z => seeds z j k))
    (steps : Z → ℕ → ℕ) (ht : ∀ j, Measurable (fun z => steps z j))
    (rounds : Z → ℕ) (hr : Measurable rounds) :
    Measurable (fun z => ∑ j ∈ Finset.range (rounds z),
      ∑ k ∈ Finset.range (steps z j), ((seeds z j k).1 + 1)) := by
  have hm (j : ℕ) : Measurable (fun z =>
      ∑ k ∈ Finset.range (steps z j), ((seeds z j k).1 + 1)) :=
    AffineSoftmaxMeasurability.measurable_select _
      (fun n => Finset.measurable_sum _ (fun k _ => (hs j k).fst.add_const 1)) _ (ht j)
  exact AffineSoftmaxMeasurability.measurable_select _
    (fun n => Finset.measurable_sum _ (fun j _ => hm j)) _ hr

open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxAcceleration
open OracleTemplate.ComponentEnvelope

lemma cachedProxPlan_cost_measurable {ι E Z : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Z]
    (s : Z → Snapshot ι E) (τ L G r : ℝ) (μ ε : Z → ℝ)
    (hμ : Measurable μ) (hε : Measurable ε) (project : Z → E → E)
    (reply : ι × E → ℝ × E) (seeds : Z → ProxSeed)
    (hs : ∀ j k, Measurable (fun z => seeds z j k)) :
    Measurable (fun z => Program.cost reply
      (cachedProxPlan (s z) τ L G r (μ z) (ε z) (project z) (seeds z))) := by
  simp only [cachedProxPlan, AffineSoftmaxRestarts.restartPlan_cost]
  exact measurable_restart_cost_sum seeds hs _
    (fun _ => AffineSoftmaxRestarts.restartSteps_measurable _ _ _ _
      (measurable_const.add hμ) measurable_const hμ measurable_const) _
    (AffineSoftmaxRestarts.restartRounds_measurable _ _ measurable_const hε)

lemma multilevelPlan_cost_measurable {ι E Z : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Z]
    (s : Z → Snapshot ι E) (τ L G r : ℝ) (μ δ : Z → ℝ)
    (hμ : Measurable μ) (hδ : Measurable δ) (project : Z → E → E)
    (J : Z → ℕ) (hJ : Measurable J) (reply : ι × E → ℝ × E)
    (seed : Z → MultilevelSeed) (hseed : Measurable seed) :
    Measurable (fun z => Program.cost reply
      (multilevelPlan (s z) τ L G r (μ z) (δ z) (project z) (J z) (seed z))) := by
  have hm (j : ℕ) (seeds : Z → ProxSeed) (hs : Measurable seeds) :
      Measurable (fun z => Program.cost reply
        (levelPlan (s z) τ L G r (μ z) (δ z) (project z) j (seeds z))) :=
    cachedProxPlan_cost_measurable s τ L G r μ (fun z => δ z / 2 ^ j)
      hμ (hδ.div_const _) project reply seeds
      (fun j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hs))
  simp_rw [multilevelPlan_cost]
  have hb := hm 0 (fun z => (seed z).2.1) hseed.snd.fst
  have hf := AffineSoftmaxMeasurability.measurable_select _
    (fun k => hm (k + 1) (fun z => (seed z).2.2.1) hseed.snd.snd.fst)
    (fun z => (seed z).1) hseed.fst
  have hc := AffineSoftmaxMeasurability.measurable_select _
    (fun k => hm k (fun z => (seed z).2.2.2) hseed.snd.snd.snd)
    (fun z => (seed z).1) hseed.fst
  exact hb.add ((hf.add hc).ite (measurableSet_le (hseed.fst.add_const 1) hJ) measurable_const)

lemma restartRounds_tolerance_antitone {d δ ε : ℝ} (hd : 0 ≤ d)
    (hδ : 0 < δ) (hδε : δ ≤ ε) : restartRounds d ε ≤ restartRounds d δ := by
  apply Nat.clog_mono_right
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left hd hδ hδε

lemma restartSteps_regularization_antitone {S V floor μ d : ℝ}
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hf : 0 < floor) (hfm : floor ≤ μ) (hd : 0 < d) :
    restartSteps (S + μ) V μ d ≤ restartSteps (S + floor) V floor d := by
  have hμ : 0 < μ := hf.trans_le hfm
  have hratio : (S + μ) / μ ≤ (S + floor) / floor := by
    rw [add_div, add_div, div_self hμ.ne', div_self hf.ne']
    exact add_le_add (div_le_div_of_nonneg_left hS hf hfm) (le_refl 1)
  have hroot := Real.sqrt_le_sqrt hratio
  have hnoise := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hV)
    (mul_pos hf hd) (mul_le_mul_of_nonneg_right hfm hd.le)
  unfold restartSteps
  apply Nat.ceil_mono
  linarith

lemma cachedProxPlan_cost_domination {ι E : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s t : Snapshot ι E) {τ L G r floor μ δ ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfm : floor ≤ μ) (hδ : 0 < δ) (hδε : δ ≤ ε)
    (project otherProject : E → E) (reply otherReply : ι × E → ℝ × E) (seeds : ProxSeed) :
    Program.cost reply (cachedProxPlan s τ L G r μ ε project seeds) ≤
      Program.cost otherReply (cachedProxPlan t τ L G r floor δ otherProject seeds) := by
  simp only [cachedProxPlan, AffineSoftmaxRestarts.restartPlan_cost]
  have hround := restartRounds_tolerance_antitone (mul_pos hG hr).le hδ hδε
  have hsteps (j : ℕ) :
      restartSteps (L + 2 * G ^ 2 / τ + μ)
          (8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)) μ (restartGap (G * r) j) ≤
        restartSteps (L + 2 * G ^ 2 / τ + floor)
          (8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)) floor (restartGap (G * r) j) :=
    restartSteps_regularization_antitone (by positivity) (by positivity) hf hfm
      (by unfold restartGap; positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range (restartRounds (G * r) ε),
        ∑ k ∈ Finset.range (restartSteps (L + 2 * G ^ 2 / τ + floor)
          (8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)) floor (restartGap (G * r) j)),
          ((seeds j k).1 + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hsteps j)) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hround) (fun _ _ _ => Nat.zero_le _)

lemma multilevelPlan_cost_domination {ι E : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s t : Snapshot ι E) {τ L G r floor μ δ ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfm : floor ≤ μ) (hδ : 0 < δ) (hδε : δ ≤ ε)
    (project otherProject : E → E) (reply otherReply : ι × E → ℝ × E)
    {J cap : ℕ} (hJ : J ≤ cap) (seed : MultilevelSeed) :
    Program.cost reply (multilevelPlan s τ L G r μ ε project J seed) ≤
      Program.cost otherReply (multilevelPlan t τ L G r floor δ otherProject cap seed) := by
  have hlevel (j : ℕ) (seeds : ProxSeed) :
      Program.cost reply (levelPlan s τ L G r μ ε project j seeds) ≤
        Program.cost otherReply (levelPlan t τ L G r floor δ otherProject j seeds) :=
    cachedProxPlan_cost_domination s t hτ hL hG hr hf hfm
      (div_pos hδ (by positivity))
      (div_le_div_of_nonneg_right hδε (by positivity)) project otherProject reply otherReply seeds
  simp only [multilevelPlan_cost]
  by_cases ha : seed.1 + 1 ≤ J
  · have hc := ha.trans hJ
    simp only [ha, hc, ite_true]
    exact add_le_add (hlevel 0 seed.2.1)
      (add_le_add (hlevel (seed.1 + 1) seed.2.2.1) (hlevel seed.1 seed.2.2.2))
  · simp only [ha, ite_false, add_zero]
    by_cases hc : seed.1 + 1 ≤ cap
    · simp only [hc, ite_true]
      exact (hlevel 0 seed.2.1).trans (Nat.le_add_right _ _)
    · simpa only [hc, ite_false, add_zero] using hlevel 0 seed.2.1

lemma adaptive_multilevel_cost_moments {ι E Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (s : Ω → Snapshot ι E) (t : Snapshot ι E)
    {τ L G r floor δ : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hδ : 0 < δ) (μ ε : Ω → ℝ) (hm : Measurable μ) (he : Measurable ε)
    (hfm : ∀ ω, floor ≤ μ ω) (hde : ∀ ω, δ ≤ ε ω)
    (project : Ω → E → E) (otherProject : E → E) (reply otherReply : ι × E → ℝ × E)
    (J : Ω → ℕ) (hJm : Measurable J) (cap : ℕ) (hJ : ∀ ω, J ω ≤ cap)
    (seed : Ω → MultilevelSeed)
    (hlaw : MeasurePreserving seed (P : Measure Ω) (multilevelLaw : Measure MultilevelSeed)) :
    Integrable (fun ω => (Program.cost reply
      (multilevelPlan (s ω) τ L G r (μ ω) (ε ω) (project ω) (J ω) (seed ω)) : ℝ)) (P : Measure Ω) ∧
    (∫ ω, (Program.cost reply
      (multilevelPlan (s ω) τ L G r (μ ω) (ε ω) (project ω) (J ω) (seed ω)) : ℝ) ∂(P : Measure Ω)) ≤
      ∫ ξ, (Program.cost otherReply
        (multilevelPlan t τ L G r floor δ otherProject cap ξ) : ℝ) ∂(multilevelLaw : Measure MultilevelSeed) := by
  let reference := fun ξ => (Program.cost otherReply
    (multilevelPlan t τ L G r floor δ otherProject cap ξ) : ℝ)
  have hri : Integrable reference (multilevelLaw : Measure MultilevelSeed) :=
    (multilevelPlan_cost_moments t τ L G r floor δ otherProject cap otherReply
      (fun j => (levelPlan_cost_bound t τ L hG hr hf hδ otherProject otherReply j).1)).1
  have hrm : Measurable reference :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (multilevelPlan_cost_measurable (fun _ => t) τ L G r (fun _ => floor) (fun _ => δ)
        measurable_const measurable_const (fun _ => otherProject) (fun _ => cap) measurable_const
        otherReply id measurable_id)
  have hai : Measurable (fun ω => (Program.cost reply
      (multilevelPlan (s ω) τ L G r (μ ω) (ε ω) (project ω) (J ω) (seed ω)) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (multilevelPlan_cost_measurable s τ L G r μ ε hm he project J hJm reply seed hlaw.measurable)
  have hd (ω : Ω) : (Program.cost reply
      (multilevelPlan (s ω) τ L G r (μ ω) (ε ω) (project ω) (J ω) (seed ω)) : ℝ) ≤ reference (seed ω) := by
    dsimp only [reference]
    exact_mod_cast multilevelPlan_cost_domination (s ω) t hτ hL hG hr hf (hfm ω) hδ (hde ω)
      (project ω) otherProject reply otherReply (hJ ω) (seed ω)
  have henv : Integrable (fun ω => reference (seed ω)) (P : Measure Ω) :=
    hlaw.integrable_comp_of_integrable hri
  have hint := henv.mono' hai.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hd ω)
  refine ⟨hint, ?_⟩
  have hb := integral_mono hint henv hd
  rw [← integral_map_of_stronglyMeasurable hlaw.measurable hrm.stronglyMeasurable,
    hlaw.map_eq] at hb
  exact hb

end LongTails.Proofs.AffineSoftmaxMultilevelCost
