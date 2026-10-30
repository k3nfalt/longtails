import LongTails.Algorithms.ScheduledMomentum
import LongTails.Proofs.BatchedMuonRate

namespace LongTails.Proofs.ScheduledMomentumExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ScheduledMomentum
open LongTails.Setups.ScheduledMomentumComparison
open LongTails.Proofs.BatchedDirectionExecution

variable {m n : ℕ}

noncomputable def savedAt (direction : Space m n → Space m n) (β : ℝ) (η : ℕ → ℝ) (B : ℕ)
    (x0 : Space m n) (reply : ℕ → Space m n) (k t : ℕ) : Space m n :=
  if k ≤ t then (momentumIterate direction β η B x0 reply k).1 else x0

lemma method_state (direction : Space m n → Space m n) (β : ℝ) (η : ℕ → ℝ) {B : ℕ}
    (hB : 0 < B) (T : ℕ) (x0 : Space m n) (k : Fin (T + 1)) (reply : ℕ → Space m n) (t : ℕ) :
    ∀ j < B, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
        (method direction β η B T x0) k reply (B * t + j) =
      (k, ⟨t, j, (momentumIterate direction β η B x0 reply t).1,
        (momentumIterate direction β η B x0 reply t).2,
        ∑ i ∈ Finset.range j, reply (B * t + i), savedAt direction β η B x0 reply k.val t⟩) := by
  induction t with
  | zero =>
      intro j hj
      induction j with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, Finset.range_zero, Finset.sum_empty]
          change (k, (⟨0, 0, x0, 0, 0, x0⟩ : Progress m n)) = _
          congr 2
          unfold savedAt
          split_ifs with h
          · rw [Nat.le_zero.mp h]
            rfl
          · rfl
      | succ j ih =>
          have hprev := ih (by omega)
          rw [show B * 0 + (j + 1) = (B * 0 + j) + 1 by omega]
          change (method direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction β η B T x0) k reply (B * 0 + j)) (reply (B * 0 + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [method, advanceProgress, hs, ↓reduceIte, Finset.sum_range_succ]
  | succ t ih =>
      intro j hj
      induction j with
      | zero =>
          have hprev := ih (B - 1) (by omega)
          rw [show B * (t + 1) + 0 = (B * t + (B - 1)) + 1 by
            rw [Nat.mul_succ]; omega]
          change (method direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction β η B T x0) k reply (B * t + (B - 1)))
              (reply (B * t + (B - 1))) = _
          rw [hprev]
          have hs : ¬ (B - 1 + 1 < B) := by omega
          have hsum : (∑ i ∈ Finset.range (B - 1), reply (B * t + i)) + reply (B * t + (B - 1)) =
              ∑ i ∈ Finset.range B, reply (B * t + i) := by
            have hB1 : B - 1 + 1 = B := Nat.sub_add_cancel hB
            rw [← Finset.sum_range_succ (fun i => reply (B * t + i)) (B - 1), hB1]
          simp only [method, advanceProgress, hs, ↓reduceIte, hsum, Finset.range_zero,
            Finset.sum_empty]
          congr 2
          unfold savedAt
          by_cases hk : k.val = t + 1
          · rw [ite_eq_left hk.symm, ite_eq_left (by omega), hk]
            rfl
          · rw [ite_eq_right (Ne.symm hk)]
            by_cases hkt : k.val ≤ t
            · rw [ite_eq_left hkt, ite_eq_left (by omega)]
            · rw [ite_eq_right hkt, ite_eq_right (by omega)]
      | succ j ih' =>
          have hprev := ih' (by omega)
          rw [show B * (t + 1) + (j + 1) = (B * (t + 1) + j) + 1 by omega]
          change (method direction β η B T x0).update
            (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState
              (method direction β η B T x0) k reply (B * (t + 1) + j))
              (reply (B * (t + 1) + j)) = _
          rw [hprev]
          have hs : j + 1 < B := hj
          simp only [method, advanceProgress, hs, ↓reduceIte, Finset.sum_range_succ]

lemma method_follows (direction : Space m n → Space m n) (β : ℝ) (η : ℕ → ℝ) {B : ℕ}
    (hB : 0 < B) (T : ℕ) (x0 : Space m n) :
    FollowsScheduledMomentum direction β η B T x0 (method direction β η B T x0) := by
  refine ⟨id, measurable_id, ?_, ?_⟩
  · exact Measure.map_id
  · intro seed reply
    refine ⟨?_, ?_⟩
    · intro t j _ hj
      rw [method_state direction β η hB T x0 seed reply t j hj]
      rfl
    · intro extra
      have hdiv : B * (T + 1) + extra = B * (T + 1 + extra / B) + extra % B := by
        rw [Nat.mul_add B (T + 1), add_assoc, Nat.div_add_mod]
      have h := method_state direction β η hB T x0 seed reply (T + 1 + extra / B) (extra % B)
        (Nat.mod_lt _ hB)
      rw [hdiv, h]
      have hle : (seed : Fin (T + 1)).val ≤ T + 1 + extra / B :=
        le_trans (Nat.le_succ_of_le (Nat.lt_succ_iff.mp (seed : Fin (T + 1)).isLt))
          (Nat.le_add_right _ _)
      show savedAt direction β η B x0 reply _ (T + 1 + extra / B) = _
      unfold savedAt
      split_ifs
      rfl

lemma sgdMomentum_follows (β : ℝ) (η : ℕ → ℝ) {B : ℕ} (hB : 0 < B) (T : ℕ) (x0 : Space m n) :
    FollowsScheduledMomentum sgdDirection β η B T x0 (sgdMomentum β η B T x0) :=
  method_follows sgdDirection β η hB T x0

lemma nsgdMomentum_follows (β : ℝ) (η : ℕ → ℝ) {B : ℕ} (hB : 0 < B) (T : ℕ) (x0 : Space m n) :
    FollowsScheduledMomentum nsgdDirection β η B T x0 (nsgdMomentum β η B T x0) :=
  method_follows nsgdDirection β η hB T x0

noncomputable def sampledMomentum {Ω : Type*} (direction : Space m n → Space m n) (β : ℝ)
    (η : ℕ → ℝ) (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) :
    ℕ → Space m n × Space m n
  | 0 => (x0, 0)
  | t + 1 =>
      let M := β • (sampledMomentum direction β η B x0 g ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
        ∑ j ∈ Finset.range B, g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j)))
      ((sampledMomentum direction β η B x0 g ξ t).1 - η t • direction M, M)

lemma measurable_sampledMomentum {Ω : Type*} [MeasurableSpace Ω]
    {direction : Space m n → Space m n} (hdir : Measurable direction) (β : ℝ) (η : ℕ → ℝ)
    (B : ℕ) (x0 : Space m n) {g : Space m n → Ω → Space m n}
    (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledMomentum direction β η B x0 g ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hsum : Measurable (fun ξ : ℕ → Ω => ∑ j ∈ Finset.range B,
          g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j))) := by
        apply Finset.measurable_sum
        intro j _
        exact hg.comp (ih.fst.prodMk (measurable_pi_apply _))
      have hM : Measurable (fun ξ : ℕ → Ω => β • (sampledMomentum direction β η B x0 g ξ t).2 +
          (1 - β) • ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
            g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j)))) :=
        (Measurable.const_smul ih.snd β).add
          ((hsum.const_smul (1 / (B : ℝ))).const_smul (1 - β) :)
      have hD : Measurable (fun ξ : ℕ → Ω => direction (β • (sampledMomentum direction β η B x0 g ξ t).2 +
          (1 - β) • ((1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
            g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j))))) := hdir.comp hM
      exact (ih.fst.sub (hD.const_smul (η t) :)).prodMk hM

lemma execute_eq_sampledMomentum {Ω : Type} [MeasurableSpace Ω]
    (law : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    {direction : Space m n → Space m n} {β : ℝ} {η : ℕ → ℝ} {B T : ℕ} {x0 : Space m n}
    {A : Algorithm (Space m n) (Space m n) (Space m n)} (draw : A.Seed → Fin (T + 1))
    (hA : ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = (momentumIterate direction β η B x0 reply t).1) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        (momentumIterate direction β η B x0 reply (draw seed)).1)
    (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
        A (fun _ => B * (T + 1)) seed ξ =
      (sampledMomentum direction β η B x0 g ξ (draw seed)).1 := by
  rw [StochasticGradient.execute_advance]
  have hadv := advance_stateSeq A seed g ξ (B * (T + 1)) 0
  rw [Nat.zero_add] at hadv
  change A.output (StochasticGradient.advance _ _ 0 (stateSeq A seed g ξ 0)) = _
  rw [hadv]
  let reply := fun i => g (A.query (stateSeq A seed g ξ i)).2 (ξ i)
  have hrep : ∀ k, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply k =
      stateSeq A seed g ξ k := replyState_stateSeq A seed g ξ
  obtain ⟨hq, hout⟩ := hA seed reply
  simp only [hrep] at hq hout
  have hout0 := hout 0
  rw [Nat.add_zero] at hout0
  rw [hout0]
  have hiter : ∀ t ≤ T + 1, momentumIterate direction β η B x0 reply t =
      sampledMomentum direction β η B x0 g ξ t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        have ih' := ih (by omega)
        have hb : LongTails.Setups.BatchedSpectralSmooth.batchMean B reply t =
            (1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
              g (sampledMomentum direction β η B x0 g ξ t).1 (ξ (B * t + j)) := by
          unfold LongTails.Setups.BatchedSpectralSmooth.batchMean
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          change g (A.query (stateSeq A seed g ξ (B * t + j))).2 (ξ (B * t + j)) = _
          rw [hq t j (by omega) (Finset.mem_range.mp hj), ih']
        simp only [momentumIterate, sampledMomentum, ih', hb]
  rw [hiter _ (by omega)]

lemma uniform_output {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g))
    {direction : Space m n → Space m n} (hdir : Measurable direction) {β : ℝ} {η : ℕ → ℝ}
    {B T : ℕ} {x0 : Space m n} {A : Algorithm (Space m n) (Space m n) (Space m n)}
    (hA : FollowsScheduledMomentum direction β η B T x0 A)
    (F : Space m n → ℝ) (hF : Measurable F)
    (hi : ∀ t, Integrable (fun ξ => F (sampledMomentum direction β η B x0 g ξ t).1)
      (P : Measure _)) :
    let O : Oracle (Space m n) (Space m n) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let out := fun z : A.Seed × (ℕ → Ω) => execute O A (fun _ => B * (T + 1)) z.1 z.2
    Measurable out ∧ Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) ∧
      (∫ z, F (out z) ∂((A.law : Measure _).prod (P : Measure _))) =
        (∑ t ∈ Finset.range (T + 1),
          ∫ ξ, F (sampledMomentum direction β η B x0 g ξ t).1 ∂(P : Measure _)) / (T + 1) := by
  obtain ⟨draw, hdraw, hlaw, hA⟩ := hA
  intro O out
  have hout : out = fun z => (sampledMomentum direction β η B x0 g z.2 (draw z.1)).1 := by
    funext z
    exact execute_eq_sampledMomentum P g draw hA z.1 z.2
  have hX (t : ℕ) : Measurable (fun ξ : ℕ → Ω => (sampledMomentum direction β η B x0 g ξ t).1) :=
    (measurable_sampledMomentum hdir β η B x0 hg t).fst
  have hjoint : Measurable (fun z : Fin (T + 1) × (ℕ → Ω) =>
      (sampledMomentum direction β η B x0 g z.2 z.1).1) :=
    measurable_from_prod_countable_right fun k => hX k
  have hm : Measurable out := by
    rw [hout]
    exact hjoint.comp ((hdraw.comp measurable_fst).prodMk measurable_snd)
  let G := fun k : Fin (T + 1) =>
    ∫ ξ, F (sampledMomentum direction β η B x0 g ξ k).1 ∂(P : Measure _)
  have hFm : Measurable (fun z : A.Seed × (ℕ → Ω) => F (out z)) := hF.comp hm
  have hbound : ∀ k : Fin (T + 1),
      ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ k).1‖ ∂(P : Measure _) ≤
      ∑ t : Fin (T + 1), ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖
        ∂(P : Measure _) := by
    intro k
    exact Finset.single_le_sum (f := fun t : Fin (T + 1) =>
      ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖ ∂(P : Measure _))
      (fun t _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ k)
  have hint : Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall fun seed => by
        simpa only [hout] using hi (draw seed)
    · apply Integrable.of_bound (C := ∑ t : Fin (T + 1),
        ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖ ∂(P : Measure _))
      · exact (hFm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun seed => by
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          simpa only [hout] using hbound (draw seed)
  refine ⟨hm, hint, ?_⟩
  rw [integral_prod _ hint]
  have hinner : (fun seed => ∫ ξ, F (out (seed, ξ)) ∂(P : Measure _)) =
      fun seed => G (draw seed) := by
    funext seed
    simp only [hout, G]
  rw [hinner, ← integral_map hdraw.aemeasurable (measurable_of_countable G).aestronglyMeasurable,
    hlaw, OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, F (sampledMomentum direction β η B x0 g ξ t).1
    ∂(P : Measure _)) (T + 1)]
  push_cast
  ring

end LongTails.Proofs.ScheduledMomentumExecution
