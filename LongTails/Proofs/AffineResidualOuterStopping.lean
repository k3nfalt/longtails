import LongTails.Proofs.AffineResidualOuterDrift
import LongTails.Proofs.AffineSoftmaxOuterStopping

namespace LongTails.Proofs.AffineResidualOuterStopping

open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualSearch
open AffineResidualOuterProcess
open AffineResidualOuterDrift
open AffineSoftmaxOuterProcess (StateSpace state lift displacement)

lemma transition_weight_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    (state s).weight ≤ (state (transition m hX hcompact D ε hτ hL hr select hs H hH reply s seed)).weight := by
  classical
  rw [state_transition]
  split_ifs
  · exact le_rfl
  · rw [finalStepPlan_weight]
    have ha : 0 < nextWeight (select s seed.1) (state s).weight :=
      (CappedProximalGeometry.accelerated_weight_properties (hs s seed.1) s.property.1).1
    linarith

lemma transition_weight_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hM : 0 < 100 * D ^ 2 / ε)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    0 < (state (transition m hX hcompact D ε hτ hL hr select hs H hH reply s seed)).weight := by
  classical
  rw [state_transition]
  split_ifs with hstop
  · exact hM.trans_le hstop
  · rw [finalStepPlan_weight]
    have ha : 0 < nextWeight (select s seed.1) (state s).weight :=
      (CappedProximalGeometry.accelerated_weight_properties (hs s seed.1) s.property.1).1
    have hA : 0 ≤ (state s).weight := s.property.1
    linarith

lemma path_weight_monotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (D ε : ℝ) {τ L r : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (hH : 0 < H) (reply : Fin m × E → ℝ × E) (initial : StateSpace X) (seeds : ℕ → OuterSeed) :
    Monotone (fun n => (state (AffineSoftmaxSearchCoupling.path
      (transition m hX hcompact D ε hτ hL hr select hs H hH reply) initial seeds n)).weight) := by
  apply monotone_nat_of_le_succ
  intro n
  exact transition_weight_mono m hX hcompact D ε hτ hL hr select hs H hH reply _ _

lemma stopping_of_movement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (F : E → ℝ) {τ L r D ε floor cap t : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L)
    (hr : 0 < r) (hD : 0 < D) (hε : 0 < ε) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H : ℕ) (hH : 3 ≤ H) (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hfloor : floor * (100 * D ^ 2 / ε) ≤ 100 * (H : ℝ) ^ 2 * t ^ 2)
    (hMscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (hlog : 1 + Real.log (3 * (100 * D ^ 2 / ε) * cap) ≤ 6 * H)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (select s seeds))
    (reply : Fin m × E → ℝ × E) (initial : E) (hi : initial ∈ X)
    (seeds : ℕ → OuterSeed) (N : ℕ) (hN : 200 * H * t ≤ (N : ℝ)) :
    let step := transition m hX hcompact D ε hτ hL hr select hs H (by omega) reply
    let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
    let states := fun k => AffineSoftmaxSearchCoupling.path step initialState seeds k
    (∑ k ∈ Finset.range N, movement F floor D ε select (states k) (seeds k).1 ≤ 60 * D ^ 2) →
      100 * D ^ 2 / ε ≤ (state (states N)).weight := by
  let step := transition m hX hcompact D ε hτ hL hr select hs H (by omega) reply
  let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
  let states := fun k => AffineSoftmaxSearchCoupling.path step initialState seeds k
  let A := fun k => (state (states k)).weight
  let μ := fun k => select (states k) (seeds k).1
  let a := fun k => nextWeight (μ k) (A k)
  let d := fun k => displacement F floor (states k) (μ k)
  have hM : 0 < 100 * D ^ 2 / ε := by positivity
  have hHt : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have htpos : 0 < t := by linarith
  have hNpos : 0 < N := by
    have hreal : (0 : ℝ) < N := (show 0 < 200 * H * t by positivity).trans_le hN
    exact_mod_cast hreal
  have hAzero : A 0 = 0 := rfl
  have hAmono : Monotone A := path_weight_monotone m hX hcompact D ε hτ hL hr select hs H (by omega) reply initialState seeds
  have hApos k : 0 < A (k + 1) :=
    transition_weight_pos m hX hcompact D ε hτ hL hr hM select hs H (by omega) reply (states k) (seeds k)
  have hA_nonneg k : 0 ≤ A k := (states k).property.1
  have hμ k : 0 < μ k := hs _ _
  have ha k : 0 < a k := (CappedProximalGeometry.accelerated_weight_properties (hμ k) (hA_nonneg k)).1
  have hlower s seed : floor ≤ select s seed := (hcert s seed).1.1
  have hAend : A N ≤ 3 * (100 * D ^ 2 / ε) := path_weight_bound m hX hcompact D ε hτ hL hr
    select hs hlower hM hMscale H (by omega) reply initialState (by change 0 ≤ _; positivity) seeds N
  change (∑ k ∈ Finset.range N, movement F floor D ε select (states k) (seeds k).1 ≤ 60 * D ^ 2) →
    100 * D ^ 2 / ε ≤ A N
  intro henergy
  by_contra hnot
  have hstop k (hk : k < N) : ¬ 100 * D ^ 2 / ε ≤ A k :=
    not_le_of_gt ((hAmono (Nat.le_of_lt hk)).trans_lt (lt_of_not_ge hnot))
  have hstep k (hk : k < N) : A k + a k = A (k + 1) := by
    change _ = (state (step (states k) (seeds k))).weight
    rw [state_transition, ite_eq_right (hstop k hk), finalStepPlan_weight]
  have hweight k (hk : k < N) : μ k * a k ^ 2 = A (k + 1) :=
    (CappedProximalGeometry.accelerated_weight_properties (hμ k) (hA_nonneg k)).2.trans (hstep k hk)
  have hfirst : 1 / cap ≤ A 1 := by
    have hw := hweight 0 hNpos
    have he : A 1 = a 0 := by simpa only [hAzero, zero_add] using (hstep 0 hNpos).symm
    rw [he] at hw ⊢
    have hp : (μ 0 * a 0 - 1) * a 0 = 0 := by nlinarith only [hw]
    have heq := (mul_eq_zero.mp hp).resolve_right (ha 0).ne'
    have hbound := mul_le_mul_of_nonneg_right (hcert (states 0) (seeds 0).1).1.2 (ha 0).le
    apply (div_le_iff₀ (hf.trans_le hfc)).2
    change μ 0 * a 0 ≤ cap * a 0 at hbound
    nlinarith only [heq, hbound]
  have hratio0 := AffineSoftmaxOuterStopping.weight_ratio_bound A hAzero hAmono hApos N hM (hf.trans_le hfc)
    (show (0 : ℝ) ≤ H by positivity) hAend hfirst hlog
  have hratio : ∑ k ∈ Finset.range N, a k / A (k + 1) ≤ 6 * H := by
    have he : (∑ k ∈ Finset.range N, a k / A (k + 1)) =
        ∑ k ∈ Finset.range N, (A (k + 1) - A k) / A (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hstep k (Finset.mem_range.mp hk)]
      congr 1
      ring
    rw [he]
    exact hratio0
  have hraw : ∑ k ∈ Finset.range N, μ k * A (k + 1) * d k ^ 2 ≤ 960 * D ^ 2 := by
    have he : (∑ k ∈ Finset.range N, μ k * A (k + 1) * d k ^ 2) =
        16 * ∑ k ∈ Finset.range N, movement F floor D ε select (states k) (seeds k).1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hn := Finset.mem_range.mp hk
      rw [← hstep k hn]
      dsimp only [movement]
      rw [ite_eq_right (hstop k hn)]
      dsimp only [a, μ, d, A]
      ring
    rw [he]
    nlinarith only [henergy]
  have hc := AffineSoftmaxOuterStopping.active_step_count A a μ d N hr htpos hHt hf hM hscale hfloor hAzero hAmono hAend
    (fun k _ => ha k) (fun k _ => hμ k) hstep hweight
    (fun k _ => (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert (states k) (seeds k).1)).2)
    hraw hratio
  nlinarith [mul_pos (show (0 : ℝ) < H by positivity) htpos]

end LongTails.Proofs.AffineResidualOuterStopping
