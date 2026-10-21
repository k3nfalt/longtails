import outputs.Proofs.SingleOracleCounted
import outputs.Proofs.RennalaStochastic
import outputs.Proofs.RennalaExecution
import outputs.Setups.RennalaTime
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OracleTemplate.Rennala

lemma uniform_prefix_accuracy {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (f : Point d → ℝ) (N : ℕ)
    (x : Fin (N + 1) → Ω → Point d) (eps : ℝ)
    (hm : ∀ j, Measurable (x j))
    (hi : ∀ j, Integrable (fun ω => ‖gradient f (x j ω)‖ ^ 2) (P : Measure Ω))
    (ha : (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
      (∫ ω, ‖gradient f (x j ω)‖ ^ 2 ∂(P : Measure Ω)) ≤ eps) :
    let U := (PMF.uniformOfFintype (Fin (N + 1))).toMeasure
    let Q := U.prod (P : Measure Ω)
    Measurable (fun z : Fin (N + 1) × Ω => x z.1 z.2) ∧
    Integrable (fun z : Fin (N + 1) × Ω => ‖gradient f (x z.1 z.2)‖ ^ 2) Q ∧
    (∫ z, ‖gradient f (x z.1 z.2)‖ ^ 2 ∂Q) =
      (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
        (∫ ω, ‖gradient f (x j ω)‖ ^ 2 ∂(P : Measure Ω)) ∧
    (∫ z, ‖gradient f (x z.1 z.2)‖ ^ 2 ∂Q) ≤ eps := by
  classical
  let U := (PMF.uniformOfFintype (Fin (N + 1))).toMeasure
  let Q := U.prod (P : Measure Ω)
  have hmjoint : Measurable (fun z : Fin (N + 1) × Ω => x z.1 z.2) :=
    measurable_from_prod_countable_right hm
  have hpart (j : Fin (N + 1)) : Integrable
      (fun z : Fin (N + 1) × Ω => if z.1 = j then ‖gradient f (x j z.2)‖ ^ 2 else 0) Q := by
    have hh := (hi j).comp_snd U
    have hs : MeasurableSet {z : Fin (N + 1) × Ω | z.1 = j} :=
      measurable_fst (measurableSet_singleton j)
    convert! hh.indicator hs using 1
    funext z
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have he (z : Fin (N + 1) × Ω) : (∑ j : Fin (N + 1),
      if z.1 = j then ‖gradient f (x j z.2)‖ ^ 2 else 0) = ‖gradient f (x z.1 z.2)‖ ^ 2 := by
    simp
  have hjoint : Integrable (fun z : Fin (N + 1) × Ω => ‖gradient f (x z.1 z.2)‖ ^ 2) Q := by
    simpa only [he] using integrable_finsetSum Finset.univ (fun j _ => hpart j)
  have heq : (∫ z : Fin (N + 1) × Ω, ‖gradient f (x z.1 z.2)‖ ^ 2 ∂Q) =
      (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
        (∫ ω, ‖gradient f (x j ω)‖ ^ 2 ∂(P : Measure Ω)) := by
    rw [integral_prod _ hjoint]
    change (∫ j, (∫ ω, ‖gradient f (x j ω)‖ ^ 2 ∂(P : Measure Ω))
      ∂(PMF.uniformOfFintype (Fin (N+1))).toMeasure) = _
    rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_fin, smul_eq_mul, one_div, Finset.mul_sum]
  exact ⟨hmjoint, hjoint, heq, heq.le.trans ha⟩


lemma completion_time_bound (p : Params) (hp : outputs.Setups.RennalaTime.spec.valid p) :
    completionClock (publicInput p) p.tau (publicInput p).horizon ≤ deadline p := by
  classical
  rcases hp with ⟨hn, hL, hv, heps, hDelta, htau, horder⟩
  let q := publicInput p
  have hmono : Monotone (fun r => (skeleton q p.tau r).clock) := by
    apply monotone_nat_of_le_succ
    intro r
    exact (schedule_invariants q hn p.tau htau (fun _ (_ : Unit) => 0)
      ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r).2.2.2.1
  have hex (k : ℕ) : ∃ r, (skeleton q p.tau r).iteration = k ∧
      ∀ m : Fin p.n, (skeleton q p.tau r).clock ≤ 2 * (k : ℝ) * allocationTime p.tau (batchSize p.v p.eps) m := by
    induction k with
    | zero =>
      refine ⟨0, rfl, ?_⟩
      intro m
      dsimp only [skeleton, workerState, initialState]
      simp
    | succ k ih =>
      obtain ⟨r, hr, hb⟩ := ih
      obtain ⟨s, hrs, hs, hit, hpre, htime⟩ := batch_time_bound q hn p.tau htau horder
        (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r
      change (skeleton q p.tau s).iteration = (skeleton q p.tau r).iteration + 1 at hit
      refine ⟨s, by simpa only [hr] using hit, ?_⟩
      intro m
      have hh := htime m
      change (skeleton q p.tau s).clock ≤ (skeleton q p.tau r).clock + 2 * allocationTime p.tau (batchSize p.v p.eps) m at hh
      rw [Nat.cast_add, Nat.cast_one]
      linarith [hb m]
  have hclock (m : Fin p.n) : completionClock q p.tau q.horizon ≤
      2 * (q.horizon : ℝ) * allocationTime p.tau (batchSize p.v p.eps) m := by
    obtain ⟨r, hr, hb⟩ := hex q.horizon
    have he : ∃ r, (skeleton q p.tau r).iteration = q.horizon := ⟨r, hr⟩
    have hidx : completionIndex q p.tau q.horizon ≤ r := by
      dsimp only [completionIndex]
      simp only [dite_eq_left he]
      exact Nat.find_min' he hr
    exact (hmono hidx).trans (hb m)
  have ha : 0 ≤ p.L * p.Delta / p.eps := by positivity
  have hN : (q.horizon : ℝ) ≤ 24 * (p.L * p.Delta / p.eps) := by
    change (⌊24 * p.L * p.Delta / p.eps⌋₊ : ℝ) ≤ _
    convert Nat.floor_le (by positivity : 0 ≤ 24 * p.L * p.Delta / p.eps) using 1 <;> ring
  have hS : (batchSize p.v p.eps : ℝ) ≤ p.v / p.eps + 1 := by
    change ((max ⌈p.v / p.eps⌉₊ 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Nat.ceil_lt_add_one (div_nonneg hv heps.le)).le (by linarith [div_nonneg hv heps.le])
  have hrate (m : Fin p.n) : 0 < prefixRate p.tau m := by
    apply Finset.sum_pos'
    · intro i hi
      split_ifs
      · exact (one_div_pos.mpr (htau i)).le
      · exact le_rfl
    · refine ⟨m, Finset.mem_univ _, ?_⟩
      simp only [le_refl, ↓reduceIte]
      exact one_div_pos.mpr (htau m)
  have hbound (m : Fin p.n) : completionClock q p.tau q.horizon ≤
      96 * ((prefixRate p.tau m / (m.val + 1 : ℕ))⁻¹ *
        (p.L * p.Delta / p.eps + p.v * p.L * p.Delta / ((m.val + 1 : ℕ) * p.eps ^ 2))) := by
    have hm : (1 : ℝ) ≤ ((m.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m.val)
    have hmn : (((m.val + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hh : (batchSize p.v p.eps : ℝ) + ((m.val+1 : ℕ) : ℝ) ≤
        2 * (((m.val+1 : ℕ) : ℝ) + p.v / p.eps) := by
      have hvb : 0 ≤ p.v / p.eps := div_nonneg hv heps.le
      linarith
    have hT : 0 ≤ allocationTime p.tau (batchSize p.v p.eps) m := by
      dsimp only [allocationTime]
      exact div_nonneg (by positivity) (hrate m).le
    have hfirst := mul_le_mul_of_nonneg_right hN hT
    have hsecond := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hh (hrate m).le) (by positivity : 0 ≤ 48 * (p.L * p.Delta / p.eps))
    have he : 96 * ((prefixRate p.tau m / (m.val+1 : ℕ))⁻¹ *
        (p.L * p.Delta / p.eps + p.v * p.L * p.Delta / ((m.val+1 : ℕ) * p.eps ^ 2))) =
        48 * (p.L * p.Delta / p.eps) *
          ((2 * (((m.val+1 : ℕ) : ℝ) + p.v / p.eps)) / prefixRate p.tau m) := by
      field_simp
      <;> ring
    rw [he]
    have h1 := hclock m
    dsimp [allocationTime] at h1 hfirst
    nlinarith
  change completionClock q p.tau q.horizon ≤ deadline p
  dsimp only [deadline]
  rw [dif_pos hn]
  rw [mul_comm (96 : ℝ)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 96)).mp
  apply Finset.le_inf'
  intro m hm
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 96)).mpr (by nlinarith [hbound m])


lemma execution_success (p : Params) (hp : outputs.Setups.RennalaTime.spec.valid p) (I : Instance p.d)
    (O : Oracle (Query (publicInput p)) (Reply (publicInput p)))
    (hO : outputs.Setups.RennalaTime.spec.admissible p I O) (B : ℕ)
    (hB : (publicInput p).horizon * (batchSize p.v p.eps + p.n) ≤ B) :
    let A := algorithm (publicInput p)
    let P : ProbabilityMeasure (A.Seed × ((k : ℕ) → O.Seed k)) :=
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩
    outputs.Setups.RennalaTime.spec.successful p I (fun z => (executeCounted O A B z.1 z.2).1) P := by
  classical
  rcases hO with ⟨hf, Ω, m, μ, P, g, hiid, hg, rfl⟩
  letI := m
  let q := publicInput p
  have hn := hp.1
  have hL := hp.2.1
  have hv := hp.2.2.1
  have heps := hp.2.2.2.1
  have hDelta := hp.2.2.2.2.1
  have htau := hp.2.2.2.2.2.1
  have horder := hp.2.2.2.2.2.2
  let ζ : ℕ → (ℕ → Ω) → Ω := fun k seeds => seeds (sampleIndex q p.tau k)
  have hfresh := fresh_batch_law q hn p.tau htau μ P hiid g
  let x : Fin (q.horizon + 1) → (ℕ → Ω) → Point p.d := fun j seeds =>
    iterate g (stepSize p.L p.v p.eps) (batchSize p.v p.eps) p.x0 (fun i => ζ i seeds) j.val
  have hS : 0 < batchSize p.v p.eps := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hm (j : Fin (q.horizon + 1)) : Measurable (x j) :=
    (finite_moments I.f g μ P ζ p.L p.v (stepSize p.L p.v p.eps) p.x0 (batchSize p.v p.eps)
      hS hL hv hf.hasGradient hf.lipschitz hg hfresh.2.1 j.val).1
  have hi (j : Fin (q.horizon + 1)) : Integrable (fun seeds => ‖gradient I.f (x j seeds)‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    (finite_moments I.f g μ P ζ p.L p.v (stepSize p.L p.v p.eps) p.x0 (batchSize p.v p.eps)
      hS hL hv hf.hasGradient hf.lipschitz hg hfresh.2.1 j.val).2.2.2
  have hbudget : 24 * p.Delta * p.L / p.eps ≤ ((q.horizon+1 : ℕ) : ℝ) := by
    have hh := Nat.lt_floor_add_one (24 * p.L * p.Delta / p.eps)
    change 24 * p.Delta * p.L / p.eps ≤ ((⌊24 * p.L * p.Delta / p.eps⌋₊ + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    convert hh.le using 1 <;> ring
  have ha : (1 / ((q.horizon+1 : ℕ) : ℝ)) * ∑ j : Fin (q.horizon+1),
      (∫ seeds, ‖gradient I.f (x j seeds)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.eps := by
    have hh := iteration_accuracy I.f g μ P ζ p.L p.v p.eps p.Delta I.lower p.x0
      hL hv heps hf.hasGradient hf.lipschitz hf.lower hf.gap hg hfresh.2.1
      (q.horizon+1) (Nat.succ_pos _) hbudget
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      ∫ seeds, ‖gradient I.f (iterate g (stepSize p.L p.v p.eps) (batchSize p.v p.eps) p.x0
        (fun i => ζ i seeds) k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (q.horizon+1)] at hh
    exact hh
  have hu := uniform_prefix_accuracy P I.f q.horizon x p.eps hm hi ha
  have hex (z : Fin (q.horizon+1) × (ℕ → Ω)) :
      (executeCounted (eventOracle (publicInput p) p.tau P g) (algorithm (publicInput p)) B z.1 z.2).1 =
        (x z.1 z.2, completionClock q p.tau q.horizon) := by
    rw [execute_prefix q hn p.tau htau P g B hB z.1 z.2]
    rfl
  have hexFun : (fun z : Fin (q.horizon+1) × (ℕ → Ω) =>
      (executeCounted (eventOracle (publicInput p) p.tau P g) (algorithm (publicInput p)) B z.1 z.2).1) =
      (fun z => (x z.1 z.2, completionClock q p.tau q.horizon)) := funext hex
  let Q : ProbabilityMeasure (Fin (q.horizon+1) × (ℕ → Ω)) :=
    ⟨(PMF.uniformOfFintype (Fin (q.horizon+1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩
  change outputs.Setups.RennalaTime.spec.successful p I (fun z : Fin (q.horizon+1) × (ℕ → Ω) =>
      (executeCounted (eventOracle (publicInput p) p.tau P g) (algorithm (publicInput p)) B z.1 z.2).1) Q
  rw [hexFun]
  exact ⟨hu.1.prodMk measurable_const, hu.2.1, hu.2.2.2,
    Filter.Eventually.of_forall (fun _ => completion_time_bound p hp)⟩


end OracleTemplate.Rennala
