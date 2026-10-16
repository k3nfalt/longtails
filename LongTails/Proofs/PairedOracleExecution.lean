import LongTails.Proofs.ClippedTwoPointExecution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.WeightedOracleBlocks
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PairedOracleExecution

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma product_iid {A B X Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p : Measure A} {q : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    {u : ℕ → X → A} {v : ℕ → Y → B} (hu : IID u p μ) (hv : IID v q ν) :
    IID (fun i (z : X × Y) => (u i z.1, v i z.2)) (p.prod q) (μ.prod ν) := by
  have hm (i : ℕ) : Measurable (fun z : X × Y => (u i z.1, v i z.2)) :=
    (hu.measurable i).prodMap (hv.measurable i)
  have hmar (i : ℕ) : (μ.prod ν).map (fun z : X × Y => (u i z.1, v i z.2)) = p.prod q := by
    change (μ.prod ν).map (Prod.map (u i) (v i)) = _
    rw [← Measure.map_prod_map μ ν (hu.measurable i) (hv.measurable i), hu.marginal, hv.marginal]
  refine ⟨hm, ?_, hmar⟩
  rw [iIndepFun_iff_finset]
  intro s
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i : s => (hm i).aemeasurable)).mpr
  have hmu : μ.map (fun x (i : s) => u i x) = Measure.pi (fun _ : s => p) := by
    simpa only [hu.marginal] using (hu.independent.restrict s).map_fun_eq_pi_map
      (fun i : s => (hu.measurable i).aemeasurable)
  have hnu : ν.map (fun y (i : s) => v i y) = Measure.pi (fun _ : s => q) := by
    simpa only [hv.marginal] using (hv.independent.restrict s).map_fun_eq_pi_map
      (fun i : s => (hv.measurable i).aemeasurable)
  have he := MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow A B s)
    (measurePreserving_arrowProdEquivProdArrow A B s (fun _ => p) (fun _ => q))
  have hprod : (μ.prod ν).map (fun z : X × Y => ((fun i : s => u i z.1), (fun i : s => v i z.2))) =
      (Measure.pi fun _ : s => p).prod (Measure.pi fun _ : s => q) := by
    change (μ.prod ν).map (Prod.map (fun x (i : s) => u i x) (fun y (i : s) => v i y)) = _
    rw [← Measure.map_prod_map μ ν (Measurable.of_eval (fun i : s => hu.measurable i))
      (Measurable.of_eval (fun i : s => hv.measurable i)), hmu, hnu]
  have hmap : Measurable (fun z : X × Y => ((fun i : s => u i z.1), (fun i : s => v i z.2))) :=
    (Measurable.of_eval (fun i : s => hu.measurable i)).prodMap
      (Measurable.of_eval (fun i : s => hv.measurable i))
  have heq := he.map_eq
  rw [← hprod, Measure.map_map he.measurable hmap] at heq
  change (μ.prod ν).map (fun z : X × Y => fun i : s => (u i z.1, v i z.2)) =
    Measure.pi (fun _ : s => p.prod q) at heq
  simpa only [Finset.restrict, hmar] using heq

lemma accelerated_weights_sum (N : ℕ) :
    (∑ t ∈ Finset.range N, (t + 1 : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => norm_num
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma accelerated_solver_cost {N T : ℕ} (hN : 0 < N) (hT : 0 < T) :
    LongTails.Algorithms.ClippedTwoPoint.solverCalls
      (fun t => LongTails.Algorithms.ClippedTwoPoint.batchSize T ((N : ℝ) * (N + 1) / 2) (t + 1)) N ≤
        2 * T + 2 * N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * (N + 1) / 2 := by positivity
  have hsum : (∑ i : Fin N, ((i : ℕ) + 1 : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ))]
    exact accelerated_weights_sum N
  have hh := WeightedOracleBlocks.batch_total_size_nat hT hA
    (α := fun i : Fin N => ((i : ℕ) + 1 : ℝ)) (fun i => by positivity) hsum
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    LongTails.Algorithms.ClippedTwoPoint.batchSize T ((N : ℝ) * (N + 1) / 2) (t + 1))] at hh
  rw [ClippedTwoPointExecution.solver_calls_eq]
  omega

lemma dual_solver_calls_eq (B : ℕ → ℕ) (N : ℕ) :
    LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls B N =
      2 * LongTails.Algorithms.ClippedTwoPoint.solverCalls B N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls,
      LongTails.Algorithms.ClippedTwoPoint.solverCalls, ih]
    omega

lemma adaptive_selection_cost {N T : ℕ} (hN : 0 < N) (hT : 0 < T) :
    2 * T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls
      (fun t => LongTails.Algorithms.ClippedTwoPoint.batchSize T ((N : ℝ) * (N + 1) / 2) (t + 1)) N ≤
        6 * T + 4 * N := by
  rw [dual_solver_calls_eq]
  have hh := accelerated_solver_cost hN hT
  omega

lemma paired_stream_marginal {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {P : Measure Z} {p : Measure W} (ξ : ℕ → Z → W)
    (hξ : ∀ k, Measurable (ξ k)) (hlaw : ∀ k, P.map (ξ k) = p) (k : ℕ) :
    (P.map (fun z n => ξ (n / 2) z)).map (fun r : ℕ → W => (r (2 * k), r (2 * k + 1))) =
      p.map (fun w => (w, w)) := by
  have hm : Measurable (fun z n => ξ (n / 2) z) := Measurable.of_eval (fun n => hξ (n / 2))
  rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) hm]
  have hdiag : Measurable (fun w : W => (w, w)) := measurable_id.prodMk measurable_id
  rw [← hlaw k, Measure.map_map hdiag (hξ k)]
  congr 1
  funext z
  simp only [Function.comp_apply, show 2 * k / 2 = k by omega,
    show (2 * k + 1) / 2 = k by omega]

lemma paired_stream_output_law {S Z W E : Type*} [MeasurableSpace S] [MeasurableSpace Z]
    [MeasurableSpace W] [MeasurableSpace E] {μ : Measure S} {P : Measure Z}
    [SFinite μ] [SFinite P] (ξ : ℕ → Z → W) (hξ : ∀ k, Measurable (ξ k))
    {F : S × (ℕ → W) → E} (hF : Measurable F) {V : S × Z → E}
    (he : ∀ s z, F (s, fun n => ξ (n / 2) z) = V (s, z)) :
    (μ.prod (P.map (fun z n => ξ (n / 2) z))).map F = (μ.prod P).map V := by
  let dup := fun z n => ξ (n / 2) z
  have hd : Measurable dup := Measurable.of_eval (fun n => hξ (n / 2))
  have hp : (μ.prod P).map (Prod.map id dup) = μ.prod (P.map dup) := by
    rw [← Measure.map_prod_map μ P measurable_id hd, Measure.map_id]
  rw [← hp, Measure.map_map hF (measurable_id.prodMap hd)]
  congr 1
  funext z
  exact he z.1 z.2

open LongTails.Algorithms.ClippedTwoPoint OracleTemplate.QueryPlan

lemma adaptive_execution_output_law {S Z W E : Type} [MeasurableSpace S] [MeasurableSpace Z]
    [MeasurableSpace W] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (law : ProbabilityMeasure S) (P : ProbabilityMeasure Z)
    (ξ : ℕ → Z → W) (hξ : ∀ k, Measurable (ξ k))
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u v : S → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (hv : ∀ t i, Measurable (fun z => v z t i))
    (g : E → W → ℝ) (hg : Measurable (fun p : E × W => g p.1 p.2))
    (N T K : ℕ) (hK : 2 * T + dualSolverCalls B N ≤ K) :
    let paired := P.map (fun z n => ξ (n / 2) z)
    let oracle : OracleTemplate.Oracle E ℝ :=
      { Seed := fun _ => W, law := paired, answer := fun _ (_, q) w => g q w }
    ((law : Measure S).prod (paired : Measure (ℕ → W))).map
      (fun z => OracleTemplate.execute oracle
        (adaptiveAlgorithm law d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T)
        (fun _ => K) z.1 z.2) =
      ((law : Measure S).prod (P : Measure Z)).map
        (fun z => adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial B (u z.1) (v z.1)
          g (fun j => ξ j z.2) 0 N T) := by
  dsimp only
  apply paired_stream_output_law ξ hξ
  · have hm := ClippedTwoPointExecution.adaptive_plan_measurable d τ₁ τ₂ γ₁ γ₂ h s hp
      initial B (fun z : S × (ℕ → W) => u z.1) (fun z => v z.1)
      (fun t i => (hu t i).comp measurable_fst) (fun t i => (hv t i).comp measurable_fst)
      g hg (fun j z => z.2 j) (fun j => (measurable_pi_apply j).comp measurable_snd) 0 N T
    convert hm using 1
    funext z
    exact execute_sampledPlan_of_le law (P.map (fun z n => ξ (n / 2) z)) initial.1 initial.1
      (2 * T + dualSolverCalls B N) K
      (fun seed => adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B (u seed) (v seed) N T)
      g z.1 z.2 hK
  · intro seed z
    exact ClippedTwoPointExecution.adaptive_execute law (P.map (fun z n => ξ (n / 2) z))
      d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T K g seed (fun j => ξ j z) hK

lemma interleaved_record_index {N : ℕ} (B : ℕ → ℕ) (j : Fin (∑ i : Fin N, 2 * B i)) :
    let r := batchRecord (fun i : Fin N => 2 * B i) j
    (j : ℕ) = 2 * (∑ i ∈ Finset.range (r.1 : ℕ), B i) + r.2 := by
  have hh := WeightedOracleBlocks.batch_record_index (fun i : Fin N => 2 * B i) j
  dsimp only
  simpa only [Fin.val_castLE, Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 * B i),
    Finset.mul_sum] using hh

lemma doubled_batch_sum {M : Type*} [AddCommMonoid M] (B : ℕ) (f g : ℕ → M) :
    (∑ i : Fin (2 * B), if (i : ℕ) < B then f i else g i) =
      (∑ i : Fin B, f i) + ∑ i : Fin B, g (B + i) := by
  rw [two_mul, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    change (if (i : ℕ) < B then f i else g i) = f i
    simp only [ite_eq_left i.isLt]
  · apply Finset.sum_congr rfl
    intro i hi
    change (if B + (i : ℕ) < B then f (B + i) else g (B + i)) = g (B + i)
    rw [ite_eq_right (by omega)]

lemma interleaved_half_weight_square (B : ℕ) (w : ℝ) (branch : Bool) :
    (∑ i : Fin (2 * B),
      (if (i : ℕ) < B then (if branch then w else 0) else (if branch then 0 else w)) ^ 2) =
        (B : ℝ) * w ^ 2 := by
  have he (i : Fin (2 * B)) :
      (if (i : ℕ) < B then (if branch then w else 0) else (if branch then 0 else w)) ^ 2 =
      if (i : ℕ) < B then (if branch then w ^ 2 else 0) else (if branch then 0 else w ^ 2) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [doubled_batch_sum B (fun _ => if branch then w ^ 2 else 0)
    (fun _ => if branch then 0 else w ^ 2)]
  cases branch <;> simp

lemma interleaved_weight_square {N : ℕ} (B : Fin N → ℕ) (w : Fin N → ℝ) (branch : Bool) :
    (∑ j : Fin (∑ i : Fin N, 2 * B i),
      let r := batchRecord (fun i : Fin N => 2 * B i) j
      (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
        else (if branch then 0 else w r.1)) ^ 2) = ∑ i, (B i : ℝ) * w i ^ 2 := by
  rw [WeightedOracleBlocks.batch_record_sum (fun i : Fin N => 2 * B i)
    (fun r => (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
      else (if branch then 0 else w r.1)) ^ 2)]
  apply Finset.sum_congr rfl
  intro i hi
  exact interleaved_half_weight_square (B i) (w i) branch

lemma interleaved_block_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (B : Fin N → ℕ) (w : Fin N → ℝ) (Y : Fin N → ℕ → E) (branch : Bool) :
    ‖∑ j : Fin (∑ i : Fin N, 2 * B i),
      let r := batchRecord (fun i : Fin N => 2 * B i) j
      (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
        else (if branch then 0 else w r.1)) •
          (PiLp.single 2 r.1 (Y r.1 r.2) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 =
      ∑ t : Fin N, w t ^ 2 * ‖∑ i : Fin (B t), Y t ((if branch then 0 else B t) + i)‖ ^ 2 := by
  let Z := fun r : (t : Fin N) × Fin (2 * B t) =>
    if (r.2 : ℕ) < B r.1 then (if branch then Y r.1 r.2 else 0)
      else (if branch then 0 else Y r.1 r.2)
  have hz (t : Fin N) : (PiLp.single 2 t (0 : E) : PiLp 2 (fun _ : Fin N => E)) = 0 :=
    (PiLp.single_eq_zero_iff 2 t).mpr rfl
  have he (r : (t : Fin N) × Fin (2 * B t)) :
      (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
        else (if branch then 0 else w r.1)) •
          (PiLp.single 2 r.1 (Y r.1 r.2) : PiLp 2 (fun _ : Fin N => E)) =
      w r.1 • (PiLp.single 2 r.1 (Z r) : PiLp 2 (fun _ : Fin N => E)) := by
    dsimp only [Z]
    split_ifs <;> simp only [zero_smul, hz, smul_zero]
  have hs (t : Fin N) : (∑ i : Fin (2 * B t), Z ⟨t, i⟩) =
      ∑ i : Fin (B t), Y t ((if branch then 0 else B t) + i) := by
    change (∑ i : Fin (2 * B t), if (i : ℕ) < B t then (if branch then Y t i else 0)
      else (if branch then 0 else Y t i)) = _
    rw [doubled_batch_sum (B t) (fun i => if branch then Y t i else 0)
      (fun i => if branch then 0 else Y t i)]
    cases branch <;> simp
  dsimp only
  simp_rw [he]
  rw [WeightedOracleBlocks.batch_record_block_energy (fun i : Fin N => 2 * B i) w Z]
  simp_rw [hs]

lemma interleaved_predictable_states {R W E : Type*} [MeasurableSpace R] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : Continuous project) (hproject : ∀ x, project x ∈ Q) {initial : E × E}
    (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (B : ℕ → ℕ) (N : ℕ)
    (direction : R → E) (sample : R → W) (hd : Measurable direction) (hs : Measurable sample)
    (fallback : R) (g : E → W → ℝ) (hg : Measurable (fun p : E × W => g p.1 p.2)) :
    ∃ state : (i : ℕ) → (Fin i → R) → (E × E) × (E × E),
      (∀ i, Measurable (state i)) ∧
      (∀ i a, ((state i a).1.1 ∈ Q ∧ (state i a).1.2 ∈ Q) ∧
        ((state i a).2.1 ∈ Q ∧ (state i a).2.2 ∈ Q)) ∧
      ∀ i (hi : i < ∑ t : Fin N, 2 * B t) (records : ℕ → R),
        let r := batchRecord (fun t : Fin N => 2 * B t) ⟨i, hi⟩
        state i (fun j => records j) = dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t j => direction (records (2 * (∑ k ∈ Finset.range t, B k) + j)))
          (fun t j => direction (records (2 * (∑ k ∈ Finset.range t, B k) + B t + j)))
          g (fun j => sample (records j)) 0 r.1 := by
  classical
  have hex (i : ℕ) : ∃ state : (Fin i → R) → (E × E) × (E × E),
      Measurable state ∧
      (∀ a, ((state a).1.1 ∈ Q ∧ (state a).1.2 ∈ Q) ∧
        ((state a).2.1 ∈ Q ∧ (state a).2.2 ∈ Q)) ∧
      ∀ (hi : i < ∑ t : Fin N, 2 * B t) (records : ℕ → R),
        let r := batchRecord (fun t : Fin N => 2 * B t) ⟨i, hi⟩
        state (fun j => records j) = dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t j => direction (records (2 * (∑ k ∈ Finset.range t, B k) + j)))
          (fun t j => direction (records (2 * (∑ k ∈ Finset.range t, B k) + B t + j)))
          g (fun j => sample (records j)) 0 r.1 := by
    by_cases hi : i < ∑ t : Fin N, 2 * B t
    · let r := batchRecord (fun t : Fin N => 2 * B t) ⟨i, hi⟩
      have hprefix : 2 * (∑ t ∈ Finset.range (r.1 : ℕ), B t) ≤ i := by
        have he := interleaved_record_index B (⟨i, hi⟩ : Fin (∑ t : Fin N, 2 * B t))
        change i = 2 * (∑ t ∈ Finset.range (r.1 : ℕ), B t) + (r.2 : ℕ) at he
        omega
      obtain ⟨st, hm, hmem, he⟩ := ClippedTwoPointExecution.dual_solver_extended_history
        hQ hp hproject hx hz d τ₁ τ₂ γ₁ γ₂ h B direction sample hd hs fallback g hg r.1 i hprefix
      exact ⟨st, hm, hmem, fun _ records => he records⟩
    · refine ⟨fun _ => (initial, initial), measurable_const, ?_, ?_⟩
      · exact fun _ => ⟨⟨hx, hz⟩, ⟨hx, hz⟩⟩
      · intro hi'
        exact False.elim (hi hi')
  choose state hm hmem he using hex
  exact ⟨state, hm, hmem, he⟩

lemma interleaved_predictable_centers {R W E : Type*} [MeasurableSpace R] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : Continuous project) (hproject : ∀ x, project x ∈ Q) {initial : E × E}
    (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (B : ℕ → ℕ) (N : ℕ) (branch : Bool)
    (direction : R → E) (sample : R → W) (hd : Measurable direction) (hs : Measurable sample)
    (fallback : R) (g : E → W → ℝ) (hg : Measurable (fun p : E × W => g p.1 p.2)) :
    ∃ x z : (i : ℕ) → (Fin i → R) → E,
      (∀ i, Measurable (x i)) ∧ (∀ i, Measurable (z i)) ∧
      (∀ i a, x i a ∈ Q ∧ z i a ∈ Q) ∧
      ∀ (j : Fin (∑ t : Fin N, 2 * B t)) (records : ℕ → R),
        let r := batchRecord (fun t : Fin N => 2 * B t) j
        let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t i => direction (records (2 * (∑ k ∈ Finset.range t, B k) + i)))
          (fun t i => direction (records (2 * (∑ k ∈ Finset.range t, B k) + B t + i)))
          g (fun i => sample (records i)) 0 r.1
        let state := if branch then states.1 else states.2
        x j (fun i => records i) = acceleratedMix r.1 state.1 state.2 ∧
          z j (fun i => records i) = state.2 := by
  classical
  obtain ⟨state, hm, hmem, he⟩ := interleaved_predictable_states hQ hp hproject hx hz
    d τ₁ τ₂ γ₁ γ₂ h B N direction sample hd hs fallback g hg
  let round := fun i => if hi : i < ∑ t : Fin N, 2 * B t then
    ((batchRecord (fun t : Fin N => 2 * B t) ⟨i, hi⟩).1 : ℕ) else 0
  let pair := fun i a => if branch then (state i a).1 else (state i a).2
  have hpair (i : ℕ) : Measurable (pair i) := by
    cases branch
    · exact (hm i).snd
    · exact (hm i).fst
  have hpQ (i : ℕ) (a : Fin i → R) : (pair i a).1 ∈ Q ∧ (pair i a).2 ∈ Q := by
    cases branch
    · exact (hmem i a).2
    · exact (hmem i a).1
  let x := fun i a => acceleratedMix (round i) (pair i a).1 (pair i a).2
  let z := fun i a => (pair i a).2
  refine ⟨x, z, ?_, ?_, ?_, ?_⟩
  · exact fun i => (ClippedTwoPointExecution.accelerated_mix_continuous (round i)).measurable.comp (hpair i)
  · exact fun i => (hpair i).snd
  · exact fun i a => ⟨ClippedTwoPointExecution.accelerated_mix_mem hQ (hpQ i a).1
      (hpQ i a).2 (round i), (hpQ i a).2⟩
  · intro j records
    dsimp only
    simp only [x, z, pair, round, dite_eq_left j.isLt, he j j.isLt records, and_self]

lemma interleaved_comparator_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (B : Fin N → ℕ) (w : Fin N → ℝ) (Y : Fin N → ℕ → E)
    (v : Fin N → E) (branch : Bool) :
    (∑ j : Fin (∑ i : Fin N, 2 * B i),
      let r := batchRecord (fun i : Fin N => 2 * B i) j
      (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
        else (if branch then 0 else w r.1)) * ⟪v r.1, Y r.1 r.2⟫) =
      ∑ t : Fin N, w t * ⟪v t, ∑ i : Fin (B t), Y t ((if branch then 0 else B t) + i)⟫ := by
  rw [WeightedOracleBlocks.batch_record_sum (fun i : Fin N => 2 * B i)
    (fun r => (if (r.2 : ℕ) < B r.1 then (if branch then w r.1 else 0)
      else (if branch then 0 else w r.1)) * ⟪v r.1, Y r.1 r.2⟫)]
  apply Finset.sum_congr rfl
  intro t ht
  have he (i : Fin (2 * B t)) :
      (if (i : ℕ) < B t then (if branch then w t else 0) else (if branch then 0 else w t)) *
        ⟪v t, Y t i⟫ =
      if (i : ℕ) < B t then (if branch then w t * ⟪v t, Y t i⟫ else 0)
        else (if branch then 0 else w t * ⟪v t, Y t i⟫) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [doubled_batch_sum (B t) (fun i => if branch then w t * ⟪v t, Y t i⟫ else 0)
    (fun i => if branch then 0 else w t * ⟪v t, Y t i⟫)]
  cases branch <;> simp [inner_sum, Finset.mul_sum]

lemma interleaved_schedule_bounds {N : ℕ} (hN : 0 < N) (B : Fin N → ℕ)
    (weights : Fin N → ℝ) (branch : Bool) {cap energy : ℝ} (hcap : 0 ≤ cap)
    (hw : ∀ t, |weights t| ≤ cap) (hs : (∑ t, (B t : ℝ) * weights t ^ 2) ≤ energy) :
    ∃ (block : ℕ → Fin N) (w : ℕ → ℝ),
      (∀ i, |w i| ≤ cap) ∧
      (∑ i ∈ Finset.range (∑ t, 2 * B t), w i ^ 2) ≤ energy ∧
      ∀ j : Fin (∑ t, 2 * B t),
        let r := batchRecord (fun t => 2 * B t) j
        block j = r.1 ∧ w j =
          (if (r.2 : ℕ) < B r.1 then (if branch then weights r.1 else 0)
            else (if branch then 0 else weights r.1)) := by
  classical
  let W := fun j : Fin (∑ t, 2 * B t) =>
    let r := batchRecord (fun t => 2 * B t) j
    if (r.2 : ℕ) < B r.1 then (if branch then weights r.1 else 0)
      else (if branch then 0 else weights r.1)
  let w := fun i => if hi : i < ∑ t, 2 * B t then W ⟨i, hi⟩ else 0
  let block := fun i => if hi : i < ∑ t, 2 * B t then
    (batchRecord (fun t => 2 * B t) ⟨i, hi⟩).1 else ⟨0, hN⟩
  have hwW (j : Fin (∑ t, 2 * B t)) : |W j| ≤ cap := by
    dsimp only [W]
    split_ifs <;> first | exact hw _ | simpa only [abs_zero] using hcap
  refine ⟨block, w, ?_, ?_, ?_⟩
  · intro i
    dsimp only [w]
    split_ifs with hi
    · exact hwW ⟨i, hi⟩
    · simpa only [abs_zero] using hcap
  · rw [← Fin.sum_univ_eq_sum_range (fun i => w i ^ 2)]
    have he : (∑ j : Fin (∑ t, 2 * B t), w j ^ 2) = ∑ j, W j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [w, dite_eq_left j.isLt]
    rw [he]
    exact (interleaved_weight_square B weights branch).le.trans hs
  · intro j
    simp only [block, w, W, dite_eq_left j.isLt, and_self]

lemma interleaved_centered_energy {R E : Type*} [MeasurableSpace R]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : Measure R)
    {N : ℕ} (B : ℕ → ℕ) (weights : Fin N → ℝ) (branch : Bool)
    (records : ℕ → R) (kernel : E → R → E)
    (x : (j : ℕ) → (Fin j → R) → E) (center : Fin N → E)
    (hx : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      x j (fun i => records i) = center (batchRecord (fun t : Fin N => 2 * B t) j).1) :
    ‖∑ j : Fin (∑ t : Fin N, 2 * B t),
      let r := batchRecord (fun t : Fin N => 2 * B t) j
      (if (r.2 : ℕ) < B r.1 then (if branch then weights r.1 else 0)
        else (if branch then 0 else weights r.1)) •
          (PiLp.single 2 r.1
            (kernel (x j (fun i => records i)) (records j) -
              ∫ fresh, kernel (x j (fun i => records i)) fresh ∂p) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 =
      ∑ t : Fin N, weights t ^ 2 *
        ‖∑ i : Fin (B t), (kernel (center t)
          (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))) -
            ∫ fresh, kernel (center t) fresh ∂p)‖ ^ 2 := by
  let Y := fun (t : Fin N) (i : ℕ) =>
    kernel (center t) (records (2 * (∑ k ∈ Finset.range t, B k) + i)) -
      ∫ fresh, kernel (center t) fresh ∂p
  have he (j : Fin (∑ t : Fin N, 2 * B t)) :
      kernel (x j (fun i => records i)) (records j) -
        (∫ fresh, kernel (x j (fun i => records i)) fresh ∂p) =
      Y (batchRecord (fun t : Fin N => 2 * B t) j).1
        (batchRecord (fun t : Fin N => 2 * B t) j).2 := by
    dsimp only [Y]
    rw [hx j, ← interleaved_record_index B j]
  dsimp only
  simp_rw [he]
  exact interleaved_block_energy (fun t : Fin N => B t) weights Y branch

lemma interleaved_centered_comparator {R E : Type*} [MeasurableSpace R]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : Measure R)
    {N : ℕ} (B : ℕ → ℕ) (weights : Fin N → ℝ) (branch : Bool)
    (records : ℕ → R) (kernel : E → R → E)
    (x v : (j : ℕ) → (Fin j → R) → E) (center direction : Fin N → E)
    (hx : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      x j (fun i => records i) = center (batchRecord (fun t : Fin N => 2 * B t) j).1)
    (hv : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      v j (fun i => records i) = direction (batchRecord (fun t : Fin N => 2 * B t) j).1) :
    (∑ j : Fin (∑ t : Fin N, 2 * B t),
      let r := batchRecord (fun t : Fin N => 2 * B t) j
      (if (r.2 : ℕ) < B r.1 then (if branch then weights r.1 else 0)
        else (if branch then 0 else weights r.1)) *
          ⟪v j (fun i => records i), kernel (x j (fun i => records i)) (records j) -
            ∫ fresh, kernel (x j (fun i => records i)) fresh ∂p⟫) =
      ∑ t : Fin N, weights t * ⟪direction t,
        ∑ i : Fin (B t), (kernel (center t)
          (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))) -
            ∫ fresh, kernel (center t) fresh ∂p)⟫ := by
  let Y := fun (t : Fin N) (i : ℕ) =>
    kernel (center t) (records (2 * (∑ k ∈ Finset.range t, B k) + i)) -
      ∫ fresh, kernel (center t) fresh ∂p
  have he (j : Fin (∑ t : Fin N, 2 * B t)) :
      kernel (x j (fun i => records i)) (records j) -
        (∫ fresh, kernel (x j (fun i => records i)) fresh ∂p) =
      Y (batchRecord (fun t : Fin N => 2 * B t) j).1
        (batchRecord (fun t : Fin N => 2 * B t) j).2 := by
    dsimp only [Y]
    rw [hx j, ← interleaved_record_index B j]
  dsimp only
  simp_rw [he, hv]
  exact interleaved_comparator_sum (fun t : Fin N => B t) weights Y direction branch

lemma interleaved_batch_error_identities {R E : Type*} [MeasurableSpace R]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : Measure R)
    {N : ℕ} (B : ℕ → ℕ) (a : Fin N → ℝ) (branch : Bool)
    (records : ℕ → R) (kernel : E → R → E)
    (x v : (j : ℕ) → (Fin j → R) → E) (center direction : Fin N → E)
    (block : ℕ → Fin N) (w : ℕ → ℝ)
    (hx : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      x j (fun i => records i) = center (batchRecord (fun t : Fin N => 2 * B t) j).1)
    (hv : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      v j (fun i => records i) = direction (batchRecord (fun t : Fin N => 2 * B t) j).1)
    (hw : ∀ j : Fin (∑ t : Fin N, 2 * B t),
      let r := batchRecord (fun t : Fin N => 2 * B t) j
      block j = r.1 ∧ w j =
        (if (r.2 : ℕ) < B r.1 then (if branch then a r.1 / B r.1 else 0)
          else (if branch then 0 else a r.1 / B r.1))) :
    let Y := fun j => kernel (x j (fun i => records i)) (records j) -
      ∫ fresh, kernel (x j (fun i => records i)) fresh ∂p
    let noise := fun t : Fin N => (B t : ℝ)⁻¹ •
      (∑ i : Fin (B t), (kernel (center t)
        (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))) -
          ∫ fresh, kernel (center t) fresh ∂p))
    (‖∑ j ∈ Finset.range (∑ t : Fin N, 2 * B t), w j •
        (PiLp.single 2 (block j) (Y j) : PiLp 2 (fun _ : Fin N => E))‖ =
      ‖∑ t : Fin N, a t • (PiLp.single 2 t (noise t) : PiLp 2 (fun _ : Fin N => E))‖) ∧
    (∑ j ∈ Finset.range (∑ t : Fin N, 2 * B t),
      w j * ⟪v j (fun i => records i), Y j⟫) =
        ∑ t : Fin N, a t * ⟪noise t, direction t⟫ := by
  classical
  dsimp only
  let S := fun t : Fin N => ∑ i : Fin (B t), (kernel (center t)
    (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))) -
      ∫ fresh, kernel (center t) fresh ∂p)
  have he := interleaved_centered_energy p B (fun t => a t / B t) branch
    records kernel x center hx
  have hc := interleaved_centered_comparator p B (fun t => a t / B t) branch
    records kernel x v center direction hx hv
  have he' : ‖∑ j ∈ Finset.range (∑ t : Fin N, 2 * B t), w j •
      (PiLp.single 2 (block j)
        (kernel (x j (fun i => records i)) (records j) -
          ∫ fresh, kernel (x j (fun i => records i)) fresh ∂p) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 =
      ∑ t : Fin N, (a t / B t) ^ 2 * ‖S t‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    convert he using 1
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hw j).1, (hw j).2]
  constructor
  · have hr : ‖∑ t : Fin N, a t •
        (PiLp.single 2 t ((B t : ℝ)⁻¹ • S t) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 =
        ∑ t : Fin N, (a t / B t) ^ 2 * ‖S t‖ ^ 2 := by
      rw [WeightedOracleBlocks.block_energy]
      apply Finset.sum_congr rfl
      intro t ht
      have hcoord : (∑ j : Fin N, a j •
          (PiLp.single 2 j ((B j : ℝ)⁻¹ • S j) : PiLp 2 (fun _ : Fin N => E))) t =
          a t • ((B t : ℝ)⁻¹ • S t) := by
        change (WithLp.ofLp (∑ j : Fin N, a j •
          (PiLp.single 2 j ((B j : ℝ)⁻¹ • S j) : PiLp 2 (fun _ : Fin N => E)))) t = _
        simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply, smul_ite]
      rw [hcoord, smul_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_eq_mul_inv]
    nlinarith only [he', hr, norm_nonneg (∑ j ∈ Finset.range (∑ t : Fin N, 2 * B t), w j •
      (PiLp.single 2 (block j) (kernel (x j (fun i => records i)) (records j) -
        ∫ fresh, kernel (x j (fun i => records i)) fresh ∂p) : PiLp 2 (fun _ : Fin N => E))),
      norm_nonneg (∑ t : Fin N, a t •
        (PiLp.single 2 t ((B t : ℝ)⁻¹ • S t) : PiLp 2 (fun _ : Fin N => E)))]
  · rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ t : Fin N, (a t / B t) * ⟪direction t, S t⟫ := by
        convert hc using 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [(hw j).2]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [real_inner_smul_left, real_inner_comm]
        dsimp only [S]
        ring

end LongTails.Proofs.PairedOracleExecution
