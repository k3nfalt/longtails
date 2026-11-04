import LongTails.Proofs.TaylorCorrectedStep
import LongTails.Proofs.VarianceReducedWeakMintySampling
import LongTails.Proofs.RecursiveGradientConvergence
import Mathlib.Data.List.GetD

namespace LongTails.Proofs.TaylorCorrectedEpoch

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms
open LongTails.Algorithms.TaylorCorrectedNewton
open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma epochs_length (oracle : Fin n × E → Reply E) (η ρ : ℝ) (c : E)
    (m : ℕ) (z w : E) (seeds : Fin m → EpochSeed n) :
    (eval oracle (epochs η ρ c m z w seeds)).2.2.length = n * m := by
  induction m generalizing z w with
  | zero => rfl
  | succ m ih =>
    simp only [epochs, eval_bind, eval_map, List.length_append, List.length_ofFn, ih,
      Nat.mul_succ]
    omega

omit [NeZero n] in
lemma restart_mean (oracle : Fin n × E → Reply E) (η ρ : ℝ) (c y : E)
    (m : ℕ) (seeds : Fin m → EpochSeed n) (F : E → ℝ) :
    (𝔼 selection : Fin (n * m), F (eval oracle (restart η ρ c y m seeds selection))) =
      ((eval oracle (epochs η ρ c m y y seeds)).2.2.map F).sum / (n * m : ℕ) := by
  simp only [restart, eval_map]
  exact OracleTemplate.NonconvexFiniteSum.expect_list_getD _ y F (n * m)
    (epochs_length oracle η ρ c m y y seeds)

omit [NeZero n] in
lemma restart_selected (oracle : Fin n × E → Reply E) (η ρ : ℝ) (c y : E)
    (m : ℕ) (seeds : Fin m → EpochSeed n) (selection : Fin (n * m)) :
    eval oracle (restart η ρ c y m seeds selection) ∈
      (eval oracle (epochs η ρ c m y y seeds)).2.2 := by
  have hlt : selection.val < (eval oracle (epochs η ρ c m y y seeds)).2.2.length := by
    rw [epochs_length]
    exact selection.isLt
  simp only [restart, eval_map]
  rw [List.getD_eq_getElem _ y hlt]
  exact List.getElem_mem hlt

omit [NeZero n] in
lemma epoch_points_mem [FiniteDimensional ℝ E] (oracle : Fin n × E → Reply E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (c z w : E) (seed : EpochSeed n) (j : Fin n) :
    (eval oracle (epoch η ρ c z w seed.1 seed.2)).2.2 j ∈ Metric.closedBall c ρ := by
  simp only [epoch, eval_bind, eval_map]
  exact TaylorCorrectedStep.inner_points_mem oracle hρ η c w _ n z seed.1 j

omit [NeZero n] in
lemma epochs_points_mem [FiniteDimensional ℝ E] (oracle : Fin n × E → Reply E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (c : E) (m : ℕ) (z w : E)
    (seeds : Fin m → EpochSeed n) (x : E)
    (hx : x ∈ (eval oracle (epochs η ρ c m z w seeds)).2.2) :
    x ∈ Metric.closedBall c ρ := by
  induction m generalizing z w with
  | zero => simp [epochs, eval] at hx
  | succ m ih =>
    simp only [epochs, eval_bind, eval_map, List.mem_append, List.mem_ofFn] at hx
    rcases hx with ⟨j, rfl⟩ | hx
    · exact epoch_points_mem oracle hρ η c z w (seeds 0) j
    · exact ih _ _ _ hx

omit [NeZero n] in
lemma restart_mem [FiniteDimensional ℝ E] (oracle : Fin n × E → Reply E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (c y : E) (m : ℕ)
    (seeds : Fin m → EpochSeed n) (selection : Fin (n * m)) :
    eval oracle (restart η ρ c y m seeds selection) ∈ Metric.closedBall c ρ :=
  epochs_points_mem oracle hρ η c m y y seeds _
    (restart_selected oracle η ρ c y m seeds selection)

lemma inner_potential (oracle : Fin n × E → Reply E) (η ρ : ℝ) (c w : E)
    (cache : Fin n → Reply E) (V D : E → ℝ) (b : ℝ)
    (hstep : ∀ z, (𝔼 i : Fin n,
      (V (eval oracle (step η ρ c z w cache i)).1 +
        D (eval oracle (step η ρ c z w cache i)).2)) ≤ V z + b)
    (k : ℕ) (z : E) :
    (𝔼 indices : Fin k → Fin n,
      let result := eval oracle (TaylorCorrectedNewton.inner η ρ c w cache k z indices)
      V result.1 + ∑ j : Fin k, D (result.2 j)) ≤
      V z + (k : ℝ) * b := by
  induction k generalizing z with
  | zero => simp [TaylorCorrectedNewton.inner, eval]
  | succ k ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    let S := fun i : Fin n => eval oracle (step η ρ c z w cache i)
    have he (i : Fin n) (indices : Fin k → Fin n) :
        eval oracle (TaylorCorrectedNewton.inner η ρ c w cache (k + 1) z (Fin.cons i indices)) =
          let rest := eval oracle (TaylorCorrectedNewton.inner η ρ c w cache k (S i).1 indices)
          (rest.1, Fin.cons (S i).2 rest.2) := by
      simp only [TaylorCorrectedNewton.inner, eval_bind, eval_map, Fin.cons_zero, Fin.cons_succ]
      rfl
    simp only [he, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      add_le_add_right (ih (S i).1) (D (S i).2))
    have hs := hstep z
    change (𝔼 i, (V (S i).1 + D (S i).2)) ≤ _ at hs
    simp only [Finset.expect_add_distrib, Fintype.expect_const, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul] at hh hs ⊢
    linarith

lemma epoch_potential (oracle : Fin n × E → Reply E) (η ρ : ℝ) (c w : E)
    (V A B : E → ℝ)
    (hstep : ∀ z, (𝔼 i : Fin n,
      let result := eval oracle (step η ρ c z w (fun j => oracle (j, w)) i)
      V result.1 + A result.2 + 2 * B result.2) ≤ V z + B w)
    (z : E) :
    (𝔼 seed : EpochSeed n,
      let result := eval oracle (epoch η ρ c z w seed.1 seed.2)
      V result.1 + (n : ℝ) * B result.2.1 + ∑ j, (A (result.2.2 j) + B (result.2.2 j))) ≤
        V z + (n : ℝ) * B w := by
  let cache := fun j => oracle (j, w)
  let S := fun indices : Fin n → Fin n =>
    eval oracle (TaylorCorrectedNewton.inner η ρ c w cache n z indices)
  have he (seed : EpochSeed n) : eval oracle (epoch η ρ c z w seed.1 seed.2) =
      ((S seed.1).1, (S seed.1).2 seed.2, (S seed.1).2) := by
    simp only [epoch, eval_bind, eval_map, snapshot, TaylorCorrectedStep.eval_collect]
    rfl
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hsel (indices : Fin n → Fin n) :
      (𝔼 j : Fin n, (n : ℝ) * B ((S indices).2 j)) = ∑ j, B ((S indices).2 j) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ← Finset.mul_sum]
    field_simp
  have hi := inner_potential oracle η ρ c w cache V (fun v => A v + 2 * B v) (B w)
    (fun v => by simpa [cache, add_assoc] using hstep v) n z
  change (𝔼 indices, (V (S indices).1 + ∑ j, (A ((S indices).2 j) + 2 * B ((S indices).2 j)))) ≤ _ at hi
  simp only [he, ← Finset.univ_product_univ, Finset.expect_product]
  simp only [Finset.expect_add_distrib, Fintype.expect_const, hsel,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_expect] at hi ⊢
  linarith

lemma epochs_potential [FiniteDimensional ℝ E] (oracle : Fin n × E → Reply E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (c : E) (V : E × E → ℝ) (D : E → ℝ)
    (hepoch : ∀ z w, w ∈ Metric.closedBall c ρ →
      (𝔼 seed : EpochSeed n,
        let result := eval oracle (epoch η ρ c z w seed.1 seed.2)
        V (result.1, result.2.1) + ∑ j, D (result.2.2 j)) ≤ V (z, w))
    (m : ℕ) (z w : E) (hw : w ∈ Metric.closedBall c ρ) :
    (𝔼 seeds : Fin m → EpochSeed n,
      let result := eval oracle (epochs η ρ c m z w seeds)
      V (result.1, result.2.1) + (result.2.2.map D).sum) ≤ V (z, w) := by
  induction m generalizing z w with
  | zero => simp [epochs, eval]
  | succ m ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    let S := fun seed : EpochSeed n => eval oracle (epoch η ρ c z w seed.1 seed.2)
    have hmem (seed : EpochSeed n) : (S seed).2.1 ∈ Metric.closedBall c ρ := by
      simpa only [S, epoch, eval_bind, eval_map] using
        epoch_points_mem oracle hρ η c z w seed seed.2
    have he (seed : EpochSeed n) (seeds : Fin m → EpochSeed n) :
        eval oracle (epochs η ρ c (m + 1) z w (Fin.cons seed seeds)) =
          let rest := eval oracle (epochs η ρ c m (S seed).1 (S seed).2.1 seeds)
          (rest.1, rest.2.1, List.ofFn (S seed).2.2 ++ rest.2.2) := by
      simp only [epochs, eval_bind, eval_map, Fin.cons_zero, Fin.cons_succ]
      rfl
    simp only [he, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun seed _ =>
      add_le_add_right (ih (S seed).1 (S seed).2.1 (hmem seed))
        (∑ j, D ((S seed).2.2 j)))
    have hs := hepoch z w hw
    change (𝔼 seed, (V ((S seed).1, (S seed).2.1) + ∑ j, D ((S seed).2.2 j))) ≤ _ at hs
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at hh hs ⊢
    linarith

lemma restart_average_bound [FiniteDimensional ℝ E] (oracle : Fin n × E → Reply E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (c : E) (V : E × E → ℝ) (D : E → ℝ)
    (hV : ∀ st, 0 ≤ V st)
    (hepoch : ∀ z w, w ∈ Metric.closedBall c ρ →
      (𝔼 seed : EpochSeed n,
        let result := eval oracle (epoch η ρ c z w seed.1 seed.2)
        V (result.1, result.2.1) + ∑ j, D (result.2.2 j)) ≤ V (z, w))
    (m : ℕ) (y : E) (hy : y ∈ Metric.closedBall c ρ) :
    (𝔼 seeds : Fin m → EpochSeed n, 𝔼 selection : Fin (n * m),
      D (eval oracle (restart η ρ c y m seeds selection))) ≤ V (y, y) / (n * m : ℕ) := by
  have hh := epochs_potential oracle hρ η c V D hepoch m y y hy
  have hcost : (𝔼 seeds : Fin m → EpochSeed n,
      ((eval oracle (epochs η ρ c m y y seeds)).2.2.map D).sum) ≤ V (y, y) := by
    apply le_trans _ hh
    apply Finset.expect_le_expect
    intro seeds _
    exact le_add_of_nonneg_left (hV _)
  simp only [restart_mean]
  rw [← Finset.expect_div]
  exact div_le_div_of_nonneg_right hcost (by positivity)

end LongTails.Proofs.TaylorCorrectedEpoch
