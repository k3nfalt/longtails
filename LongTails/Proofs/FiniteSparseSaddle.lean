import LongTails.Proofs.SparseGroupChoices
import LongTails.Proofs.SparseConvexCertificate
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped BigOperators

namespace LongTails.Proofs.FiniteSparseSaddle

open LongTails.Algorithms.SparseGroupSampling LongTails.Proofs.SparseGroupChoices

variable {E ι H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [Nonempty ι]
  [Fintype H] [Nonempty H] [Fintype W] [Nonempty W]

omit [Nonempty ι] in
lemma weighted_perturbation (u w v : ι → ℝ) (η B : ℝ)
    (hd : ∀ i, |w i - v i| ≤ η) (hu : ∀ i, |u i| ≤ B) :
    |(∑ i, w i * u i) - ∑ i, v i * u i| ≤ Fintype.card ι * η * B := by
  calc
    _ = |∑ i, (w i - v i) * u i| := by rw [← Finset.sum_sub_distrib]; congr 1; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i, |(w i - v i) * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, η * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hd i) (hu i) (abs_nonneg _) ((abs_nonneg _).trans (hd i))
    _ = _ := by simp [mul_assoc]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nonempty ι] in
lemma weighted_lipschitz (Q : Set E) (u : ι → E → ℝ) (w : ι → ℝ)
    (G : ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, ∀ x ∈ Q, ∀ y ∈ Q, |u i x - u i y| ≤ G * dist x y)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    |(∑ i, w i * u i x) - ∑ i, w i * u i y| ≤ G * dist x y := by
  calc
    _ = |∑ i, w i * (u i x - u i y)| := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |w i * (u i x - u i y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * (G * dist x y) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (hu i x hx y hy) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

noncomputable def primalValue (u : ι → E → ℝ) (points : H → E) : ℝ :=
  let h := finiteMinimizer (fun h => u (finiteMaximizer (fun i => u i (points h))) (points h))
  u (finiteMaximizer (fun i => u i (points h))) (points h)

noncomputable def dualValue (u : ι → E → ℝ) (points : H → E) (w : ι → ℝ) : ℝ :=
  let h := finiteMinimizer (fun h => ∑ i, w i * u i (points h))
  ∑ i, w i * u i (points h)

lemma finite_sparse_saddle (Q : Set E) (u : ι → E → ℝ) (points : H → E)
    (weights : W → ι → ℝ) (G ρ η τ : ℝ)
    (hQ : Convex ℝ Q) (hu : ∀ i, ConvexOn ℝ Q (u i))
    (hpoints : ∀ h, points h ∈ Q)
    (hcover : ∀ x ∈ Q, ∃ h, dist x (points h) ≤ ρ)
    (hG : 0 ≤ G) (hτ : 0 < τ)
    (hlip : ∀ i, ∀ x ∈ Q, ∀ y ∈ Q, |u i x - u i y| ≤ G * dist x y)
    (hbound : ∀ i h, |u i (points h)| ≤ 2)
    (hweights : ∀ w, (∀ i, 0 ≤ weights w i) ∧ ∑ i, weights w i = 1)
    (hnet : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      (∃ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 ∧ ∀ i, i ∉ S → w i = 0) →
      ∃ v, ∀ i, |w i - weights v i| ≤ η) :
    ∀ x ∈ Q, primalValue u points ≤
      (∑ i, weights (finiteMaximizer (fun w => dualValue u points (weights w))) i * u i x) +
        (2 * G * ρ + τ + 2 * Fintype.card ι * η) := by
  classical
  let V := primalValue u points
  let t := V - G * ρ - τ
  have hbad : ¬ (⋂ i, {x ∈ Q | u i x ≤ t}).Nonempty := by
    rintro ⟨x, hx⟩
    have hxQ : x ∈ Q := (Set.mem_iInter.mp hx (Classical.arbitrary ι)).1
    obtain ⟨h, hh⟩ := hcover x hxQ
    have hmin : V ≤ u (finiteMaximizer (fun i => u i (points h))) (points h) :=
      finiteMinimizer_le (fun h => u (finiteMaximizer (fun i => u i (points h))) (points h)) h
    let i := finiteMaximizer (fun i => u i (points h))
    have hxi : u i x ≤ t := (Set.mem_iInter.mp hx i).2
    have hli := hlip i (points h) (hpoints h) x hxQ
    rw [dist_comm] at hli
    have hmul := mul_le_mul_of_nonneg_left hh hG
    have hside := le_abs_self (u i (points h) - u i x)
    change V ≤ u i (points h) at hmin
    dsimp [t] at hxi
    linarith
  obtain ⟨S, w, _, hS, hw, hsum, hsupp, hlower⟩ :=
    SparseConvexCertificate.sparse_weighted_lower_certificate Q u t
      ⟨points (Classical.arbitrary H), hpoints _⟩ hQ hu hbad
  obtain ⟨v, hv⟩ := hnet w hw hsum ⟨S, hS, hsupp⟩
  have hdual : t - 2 * Fintype.card ι * η ≤ dualValue u points (weights v) := by
    let h := finiteMinimizer (fun h => ∑ i, weights v i * u i (points h))
    have hlo := hlower (points h) (hpoints h)
    have hpert := weighted_perturbation (fun i => u i (points h)) w (weights v) η 2 hv (fun i => hbound i h)
    have habs := le_abs_self ((∑ i, w i * u i (points h)) - ∑ i, weights v i * u i (points h))
    change t - 2 * Fintype.card ι * η ≤ ∑ i, weights v i * u i (points h)
    linarith
  let j := finiteMaximizer (fun v => dualValue u points (weights v))
  have hbest : dualValue u points (weights v) ≤ dualValue u points (weights j) :=
    le_finiteMaximizer (fun v => dualValue u points (weights v)) v
  intro x hx
  obtain ⟨h, hh⟩ := hcover x hx
  have hmin : dualValue u points (weights j) ≤ ∑ i, weights j i * u i (points h) :=
    finiteMinimizer_le (fun h => ∑ i, weights j i * u i (points h)) h
  have hli := weighted_lipschitz Q u (weights j) G (hweights j).1 (hweights j).2
    hlip (hpoints h) hx
  rw [dist_comm] at hli
  have hmul := mul_le_mul_of_nonneg_left hh hG
  have hside := le_abs_self ((∑ i, weights j i * u i (points h)) - ∑ i, weights j i * u i x)
  change V ≤ (∑ i, weights j i * u i x) + _
  dsimp [t] at hdual
  linarith

end LongTails.Proofs.FiniteSparseSaddle
