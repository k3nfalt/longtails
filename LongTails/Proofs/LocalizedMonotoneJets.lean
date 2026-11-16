import LongTails.Proofs.LocalizedMonotoneInstance

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalizedMonotoneJets

open LocalizedMonotoneConstruction LocalizedMonotoneProfile LocalizedMonotoneRadial

noncomputable def partialChain {d n : ℕ} (a c : ℝ) (k : ℕ)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  c • axis (π 0) + ∑ j : Fin n,
    if j.val < k then gate a (axis (π j.succ)) (axis (π j.castSucc)) x else 0

noncomputable def partialJacobian {d n : ℕ} (a : ℝ) (k : ℕ)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ∑ j : Fin n, if j.val < k then slope a (x (π j.castSucc)) •
    InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.castSucc)) else 0

lemma chain_eq_partial {d n k : ℕ} (a c : ℝ) (ha : 0 < a) (hk : k ≤ n)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i : Fin (n + 1), k ≤ i.val → |x (π i)| ≤ a) :
    chain a c π x = partialChain a c k π x := by
  have hl := (profile_flat a _ ha (hx (Fin.last n) hk)).1
  simp only [chain, partialChain, gate, axis_inner, hl, zero_smul, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
  · have hf := (profile_flat a _ ha (hx j.castSucc (by simpa using Nat.le_of_not_gt hj))).1
    simp only [hj, ite_false, hf, zero_smul]

lemma jacobian_eq_partial {d n k : ℕ} (a : ℝ) (ha : 0 < a) (hk : k ≤ n)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i : Fin (n + 1), k ≤ i.val → |x (π i)| ≤ a) :
    chainJacobian a π x = partialJacobian a k π x := by
  have hl := (profile_flat a _ ha (hx (Fin.last n) hk)).2
  simp only [chainJacobian, partialJacobian, hl, zero_smul, neg_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
  · have hf := (profile_flat a _ ha (hx j.castSucc (by simpa using Nat.le_of_not_gt hj))).2
    simp only [hj, ite_false, hf, zero_smul]

lemma partialChain_prefix {d n k : ℕ} (a c : ℝ)
    (π τ : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialChain a c k π x = partialChain a c k τ x := by
  have h0 : π 0 = τ 0 := h 0 (by simp)
  simp only [partialChain, h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · rw [ite_eq_left hj, ite_eq_left hj, h j.succ (by simpa using Nat.succ_lt_succ hj),
      h j.castSucc (by simp only [Fin.val_castSucc]; omega)]
  · simp only [hj, ite_false]

lemma partialJacobian_prefix {d n k : ℕ} (a : ℝ)
    (π τ : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialJacobian a k π x = partialJacobian a k τ x := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · rw [ite_eq_left hj, ite_eq_left hj, h j.succ (by simpa using Nat.succ_lt_succ hj),
      h j.castSucc (by simp only [Fin.val_castSucc]; omega)]
  · simp only [hj, ite_false]

noncomputable def partialReply {d n : ℕ} (a b c γ : ℝ) (k : ℕ)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :=
  (γ • (x - partialChain a c k π (radial b x)),
    γ • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) -
      (partialJacobian a k π (radial b x)).comp (radialJacobian b x)))

lemma partialReply_prefix {d n k : ℕ} (a b c γ : ℝ)
    (π τ : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialReply a b c γ k π x = partialReply a b c γ k τ x := by
  simp only [partialReply, partialChain_prefix a c π τ _ h,
    partialJacobian_prefix a π τ _ h]

lemma fullReply_eq_partial {d n k : ℕ} (a b c γ : ℝ) (ha : 0 < a) (hk : k ≤ n)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i : Fin (n + 1), k ≤ i.val → |radial b x (π i)| ≤ a) :
    (LocalizedMonotoneInstance.field a b c γ π x,
      LocalizedMonotoneInstance.jacobian a b γ π x) = partialReply a b c γ k π x := by
  simp only [LocalizedMonotoneInstance.field, LocalizedMonotoneInstance.jacobian,
    partialReply, chain_eq_partial a c ha hk π _ hx, jacobian_eq_partial a ha hk π _ hx]

end LongTails.Proofs.LocalizedMonotoneJets
