import LongTails.Proofs.SampleLossChain

open scoped RealInnerProductSpace BigOperators Topology
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossMixture
open LongTails.Proofs.SampleLossChain

namespace LongTails.Proofs.SampleLossFrontier

variable {E B : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

noncomputable def frontier (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (row : B)
    (M : ℝ) (n k : ℕ) (x : E) : ℝ :=
  2 * n + M + base P u k x +
    M * (1 - incoming P u k x) * perturbation P u w k x -
    incoming P u k x * (1 + alignment row (P k x))

omit [CompleteSpace B] in
lemma frontier_eq (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (row : B)
    (M : ℝ) (n k : ℕ) (hk : k < n) (x : E)
    (hw : M * signal P w k x = signal P u k x - alignment row (P k x))
    (hflat : ∀ j, k ≤ j → j < n → signal P u j x ≤ 1/128) :
    sampleLoss P u w M n x = frontier P u w row M n k x := by
  have htail (j : ℕ) (hj : k ≤ j) (hj' : j < n) : incoming P u (j+1) x = 0 :=
    (gate_flat_below (hflat j hj hj')).1
  have hconstant (t : ℕ) (hkt : k+1 ≤ t) (htn : t ≤ n) :
      base P u t x = base P u (k+1) x ∧
      perturbation P u w t x = perturbation P u w (k+1) x := by
    induction t, hkt using Nat.le_induction with
    | base => exact ⟨rfl,rfl⟩
    | succ t ht ih =>
      obtain ⟨hb, hp⟩ := ih (by omega)
      have h0 : incoming P u t x = 0 := by
        obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
        exact htail s (by omega) (by omega)
      constructor
      · simpa [base, Finset.sum_range_succ, link, h0] using hb
      · simpa [perturbation, mixture, blend, h0] using hp
  obtain ⟨hb, hp⟩ := hconstant n (by omega) le_rfl
  unfold sampleLoss frontier
  rw [hb, hp]
  simp only [base, Finset.sum_range_succ, perturbation, mixture, blend, link]
  linear_combination (incoming P u k x) * hw

lemma frontier_gradient [CompleteSpace E] (P : ℕ → E →L[ℝ] B) (u w : ℕ → B) (row : B)
    (M : ℝ) (n k : ℕ) (hk : k < n) (x : E)
    (hw : ∀ z, M * signal P w k z = signal P u k z - alignment row (P k z))
    (hflat : ∀ j, k ≤ j → j < n → signal P u j x < 1/128) :
    gradient (sampleLoss P u w M n) x = gradient (frontier P u w row M n k) x := by
  apply Filter.EventuallyEq.gradient_eq
  have h : ∀ᶠ z in 𝓝 x, ∀ j ∈ Finset.range n, k ≤ j → signal P u j z < 1/128 := by
    rw [Finset.eventually_all]
    intro j hj
    by_cases hkj : k ≤ j
    · exact ((signal_differentiable P u j).continuous.continuousAt.eventually_lt continuousAt_const
        (hflat j hkj (Finset.mem_range.mp hj))).mono fun z hz _ => hz
    · exact Filter.Eventually.of_forall fun _ h' => (hkj h').elim
  filter_upwards [h] with z hz
  exact frontier_eq P u w row M n k hk z (hw z) fun j hj hj' => (hz j (Finset.mem_range.mpr hj') hj).le

end LongTails.Proofs.SampleLossFrontier
