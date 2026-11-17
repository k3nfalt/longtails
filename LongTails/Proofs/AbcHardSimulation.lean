import LongTails.Proofs.AbcHardOracle

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardSimulation

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.AbcChain
open LongTails.Proofs.AbcChainProperties LongTails.Proofs.AbcChainMask
open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.AbcHardFunction
open LongTails.Proofs.AbcHardGeometry LongTails.Proofs.AbcHardOracle

variable {d n : ℕ}

noncomputable def visibleField (r : ℕ) (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => if k.val < r then field (trunc r u) k else 0)

noncomputable def visibleGrad (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d) : Space d :=
  weight (width n) (chain (trunc r (sel π w))) (wallFn n w) •
      (sel π).adjoint (visibleField r (sel π w)) +
    (1 - weight (width n) (chain (trunc r (sel π w))) (wallFn n w)) • wallGrad n w

lemma visibleField_congr (r : ℕ) (u v : Chain n) (h : ∀ i : Fin (n + 1), i.val < r → u i = v i) :
    visibleField r u = visibleField r v := by
  simp only [visibleField, trunc_congr r u v h]

lemma visibleGrad_prefix (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ∀ k : Fin (n + 1), k.val < r → π k = ρ k) :
    visibleGrad π r w = visibleGrad ρ r w := by
  have hs : ∀ i : Fin (n + 1), i.val < r → sel π w i = sel ρ w i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  have hv := visibleField_congr r _ _ hs
  have hsupp : ∀ k : Fin (n + 1), r ≤ k.val → visibleField r (sel ρ w) k = 0 := by
    intro k hk
    simp only [visibleField]
    rw [ite_eq_right (by omega)]
  rw [visibleGrad, visibleGrad, trunc_congr r _ _ hs, hv, adjoint_congr π ρ _ r hsupp h]

lemma chain_trunc_succ (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    chain (trunc (m + 1) u) = chain u := by
  unfold chain
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [trunc_apply, trunc_apply]
  by_cases h1 : i.val + 1 < m + 1
  · rw [ite_eq_left (by simp; omega), ite_eq_left (by simp; omega)]
  · rw [link_of_small _ (hs i.castSucc (by simp; omega))]
    by_cases h2 : i.val < m + 1
    · rw [ite_eq_left (by simp; omega), link_of_small _ (hs i.castSucc (by simp; omega))]
    · rw [ite_eq_right (by simp; omega), link_of_small _ (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]

lemma field_zero_beyond (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) (k : Fin (n + 1)) (hk : m + 1 ≤ k.val) :
    field u k = 0 := by
  have hkm := hs k (by omega)
  have hA : fieldA u k = 0 := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_of_small _ hkm
  have hF : fieldFirst u k = 0 := by
    induction k using Fin.cases with
    | zero => simp at hk
    | succ i => simp [fieldFirst]
  have hB : fieldB u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ]
      exact linkB_of_small _ (hs i.castSucc (by simp at hk ⊢; omega))
  rw [field_apply, hF, hA, hB]
  ring

lemma fieldA_of_small (u : Chain n) (k : Fin (n + 1)) (h : |u k| ≤ 1 / 4) : fieldA u k = 0 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_of_small _ h

lemma fieldB_congr (u v : Chain n) (k : Fin (n + 1))
    (h : ∀ j : Fin (n + 1), j.val + 1 = k.val ∨ j = k → u j = v j) : fieldB u k = fieldB v k := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i =>
    simp only [fieldB, Fin.cases_succ]
    rw [h i.castSucc (Or.inl (by simp)), h i.succ (Or.inr rfl)]

lemma visibleField_eq (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    visibleField (m + 1) u = field u := by
  ext k
  simp only [visibleField]
  by_cases hk : k.val < m
  · rw [ite_eq_left (by omega)]
    apply field_congr
    intro j hj
    rw [trunc_apply, ite_eq_left (by omega)]
  · by_cases hkm : k.val = m
    · rw [ite_eq_left (by omega), field_apply, field_apply]
      have hsm := hs k (by omega)
      have htk : trunc (m + 1) u k = u k := by rw [trunc_apply, ite_eq_left (by omega)]
      have hF : fieldFirst (trunc (m + 1) u) k = fieldFirst u k := by
        simp only [fieldFirst]
        rw [trunc_apply, ite_eq_left (by simp)]
      have hA : fieldA (trunc (m + 1) u) k = fieldA u k := by
        rw [fieldA_of_small _ k (by rw [htk]; exact hsm), fieldA_of_small _ k hsm]
      have hB : fieldB (trunc (m + 1) u) k = fieldB u k := by
        apply fieldB_congr
        intro j hj
        rw [trunc_apply, ite_eq_left]
        rcases hj with hj | hj
        · omega
        · rw [hj]; omega
      rw [hF, hA, hB]
    · rw [ite_eq_right (by omega), field_zero_beyond m u hs k (by omega)]

lemma visibleGrad_eq (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |sel π w i| ≤ 1 / 4) :
    visibleGrad π (m + 1) w = hardGrad π w := by
  rw [visibleGrad, hardGrad, chain_trunc_succ m _ hs, visibleField_eq m _ hs]

lemma visibleGrad_outside (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : visibleGrad π r w = wallGrad n w := by
  rw [visibleGrad, (weight_zero_outside π r w hw).1]
  simp

end LongTails.Proofs.AbcHardSimulation
