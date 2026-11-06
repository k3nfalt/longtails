import LongTails.Proofs.AffineSoftmaxOuterDrift

namespace LongTails.Proofs.AffineSoftmaxOuterStopping

open LongTails.Proofs.AffineSoftmaxOuterProcess
open LongTails.Proofs.AffineSoftmaxOuterDrift
open LongTails.Algorithms.CappedProximal
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxSearch

lemma transition_weight_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    (state s).weight ≤ (state (transition m hX hcompact τ L G r D ε hr select hs H reply s seed)).weight := by
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
    (τ L G r D ε : ℝ) (hr : 0 ≤ r) (hM : 0 < 100 * D ^ 2 / ε)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (s : StateSpace X) (seed : OuterSeed) :
    0 < (state (transition m hX hcompact τ L G r D ε hr select hs H reply s seed)).weight := by
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
    (τ L G r D ε : ℝ) (hr : 0 ≤ r)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (H : ℕ) (reply : Fin m × E → ℝ × E) (initial : StateSpace X) (seeds : ℕ → OuterSeed) :
    Monotone (fun n => (state (AffineSoftmaxSearchCoupling.path
      (transition m hX hcompact τ L G r D ε hr select hs H reply) initial seeds n)).weight) := by
  apply monotone_nat_of_le_succ
  intro n
  exact transition_weight_mono m hX hcompact τ L G r D ε hr select hs H reply _ _

lemma inverse_square_weight {A a μ : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hweight : μ * a ^ 2 = A + a) :
    (μ * (A + a)) * (a / (A + a)) ^ 2 = 1 := by
  have hT : 0 < A + a := by positivity
  field_simp
  nlinarith only [hweight]

lemma big_movement_sum {ι : Type*} (s u : Finset ι) (hsub : s ⊆ u) (b d : ι → ℝ)
    {r D t : ℝ} (hr : 0 < r) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hb : ∀ i ∈ u, 0 ≤ b i) (hd : ∀ i ∈ s, 3 * r / 4 ≤ d i)
    (henergy : ∑ i ∈ u, b i * d i ^ 2 ≤ 960 * D ^ 2) :
    ∑ i ∈ s, b i ≤ (5120 / 3) * t ^ 3 := by
  have hi (i : ι) (h : i ∈ s) : (9 * r ^ 2 / 16) * b i ≤ b i * d i ^ 2 := by
    have hh := hd i h
    have hsq : 9 * r ^ 2 / 16 ≤ d i ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq (hb i (hsub h))
    nlinarith only [hm]
  have hsum := Finset.sum_le_sum hi
  rw [← Finset.mul_sum] at hsum
  have hsubset : ∑ i ∈ s, b i * d i ^ 2 ≤ ∑ i ∈ u, b i * d i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => mul_nonneg (hb i hi) (sq_nonneg _))
  have htot := hsum.trans (hsubset.trans henergy)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).1
  nlinarith only [htot, hscale]

lemma sqrt_increment_sum (A : ℕ → ℝ) (hzero : A 0 = 0) (hmono : Monotone A)
    (n : ℕ) (s : Finset ℕ) (hsub : s ⊆ Finset.range n) :
    ∑ i ∈ s, (Real.sqrt (A (i + 1)) - Real.sqrt (A i)) ≤ Real.sqrt (A n) := by
  have hsum : ∑ i ∈ s, (Real.sqrt (A (i + 1)) - Real.sqrt (A i)) ≤
      ∑ i ∈ Finset.range n, (Real.sqrt (A (i + 1)) - Real.sqrt (A i)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      sub_nonneg.mpr (Real.sqrt_le_sqrt (hmono (Nat.le_succ i))))
  rw [Finset.sum_range_sub (fun i => Real.sqrt (A i)) n] at hsum
  simpa only [hzero, Real.sqrt_zero, sub_zero] using hsum

lemma active_step_count (A a μ d : ℕ → ℝ) (n : ℕ) {r D t H floor M : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hH : 3 ≤ H) (hf : 0 < floor) (hM : 0 < M)
    (hscale : t ^ 3 * r ^ 2 = D ^ 2) (hfloor : floor * M ≤ 100 * H ^ 2 * t ^ 2)
    (hzero : A 0 = 0) (hmono : Monotone A) (hend : A n ≤ 3 * M)
    (ha : ∀ i < n, 0 < a i) (hμ : ∀ i < n, 0 < μ i)
    (hstep : ∀ i < n, A i + a i = A (i + 1))
    (hweight : ∀ i < n, μ i * a i ^ 2 = A (i + 1))
    (hvalid : ∀ i < n, μ i ≤ 2 * floor ∨ 3 * r / 4 ≤ d i)
    (henergy : ∑ i ∈ Finset.range n, μ i * A (i + 1) * d i ^ 2 ≤ 960 * D ^ 2)
    (hratio : ∑ i ∈ Finset.range n, a i / A (i + 1) ≤ 6 * H) : (n : ℝ) < 79 * H * t := by
  classical
  let big := (Finset.range n).filter (fun i => 2 * floor < μ i)
  let small := (Finset.range n).filter (fun i => ¬ 2 * floor < μ i)
  have hAi i : 0 ≤ A i := by rw [← hzero]; exact hmono (Nat.zero_le i)
  have hnext i (hi : i < n) : 0 < A (i + 1) := by rw [← hstep i hi]; exact add_pos_of_nonneg_of_pos (hAi i) (ha i hi)
  have hq i (hi : i ∈ Finset.range n) : 0 < a i / A (i + 1) := div_pos (ha i (Finset.mem_range.mp hi)) (hnext i (Finset.mem_range.mp hi))
  have hb i (hi : i ∈ Finset.range n) : 0 ≤ μ i * A (i + 1) :=
    mul_nonneg (hμ i (Finset.mem_range.mp hi)).le (hnext i (Finset.mem_range.mp hi)).le
  have hbigsub : big ⊆ Finset.range n := Finset.filter_subset _ _
  have hsmallsub : small ⊆ Finset.range n := Finset.filter_subset _ _
  have hbigsum := big_movement_sum big (Finset.range n) hbigsub
    (fun i => μ i * A (i + 1)) d hr hscale hb (fun i hi => by
      have hn := Finset.mem_range.mp (hbigsub hi)
      rcases hvalid i hn with h | h
      · exact False.elim ((not_le_of_gt (Finset.mem_filter.mp hi).2) h)
      · exact h) henergy
  have hqsum : ∑ i ∈ big, a i / A (i + 1) ≤ 6 * H :=
    (Finset.sum_le_sum_of_subset_of_nonneg hbigsub (fun i hi _ => (hq i hi).le)).trans hratio
  have hbigcount := AffineSoftmaxOuterBounds.inverse_square_count big
    (fun i => a i / A (i + 1)) (fun i => μ i * A (i + 1)) ht hH
    (fun i hi => hq i (hbigsub hi)) (fun i hi => by
      have hn := Finset.mem_range.mp (hbigsub hi)
      have hw : μ i * a i ^ 2 = A i + a i := (hweight i hn).trans (hstep i hn).symm
      simpa only [hstep i hn] using inverse_square_weight (hAi i) (ha i hn) hw) hbigsum hqsum
  have hsmallcount := AffineSoftmaxOuterBounds.sqrt_progress_count small
    (fun i => Real.sqrt (A (i + 1)) - Real.sqrt (A i)) hf hM (by linarith : 0 < H) ht
    (fun i hi => by
      have hn := Finset.mem_range.mp (hsmallsub hi)
      have hw : μ i * a i ^ 2 = A i + a i := (hweight i hn).trans (hstep i hn).symm
      have h := AffineSoftmaxOuterBounds.small_sqrt_progress (hμ i hn) (hAi i) (ha i hn) hw
        (le_of_not_gt (Finset.mem_filter.mp hi).2)
      simpa only [hstep i hn] using h)
    ((sqrt_increment_sum A hzero hmono n small hsmallsub).trans (Real.sqrt_le_sqrt hend)) hfloor
  have hcard : big.card + small.card = n := by
    simpa only [big, small, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun i => 2 * floor < μ i))
  have hcardreal : (big.card : ℝ) + (small.card : ℝ) = n := by exact_mod_cast hcard
  linarith

lemma weight_ratio_bound (A : ℕ → ℝ) (hzero : A 0 = 0) (hmono : Monotone A)
    (hpos : ∀ i, 0 < A (i + 1)) (n : ℕ) {M cap H : ℝ}
    (hM : 0 < M) (hcap : 0 < cap) (hH : 0 ≤ H) (hend : A n ≤ 3 * M)
    (hfirst : 1 / cap ≤ A 1) (hlog : 1 + Real.log (3 * M * cap) ≤ 6 * H) :
    ∑ i ∈ Finset.range n, (A (i + 1) - A i) / A (i + 1) ≤ 6 * H := by
  cases n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hH)
  | succ n =>
    have hs := AffineSoftmaxOuterBounds.weight_ratio_sum A hzero hpos (fun i => hmono (Nat.le_succ i)) n
    have hc : 1 ≤ A 1 * cap := (div_le_iff₀ hcap).1 hfirst
    have hratio : A (n + 1) / A 1 ≤ 3 * M * cap := by
      apply (div_le_iff₀ (hpos 0)).2
      have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3 * M by positivity)
      nlinarith only [hm, hend]
    have hl := Real.log_le_log (div_pos (hpos n) (hpos 0)) hratio
    rw [Real.log_div (hpos n).ne' (hpos 0).ne'] at hl
    linarith

lemma stopping_of_movement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] {X : Set E} (hX : Convex ℝ X) (hcompact : IsCompact X)
    (F : E → ℝ) (τ L G : ℝ) {r D ε floor cap t : ℝ}
    (hr : 0 < r) (hD : 0 < D) (hε : 0 < ε) (hf : 0 < floor) (hfc : floor ≤ cap)
    (H : ℕ) (hH : 3 ≤ H) (ht : 1 ≤ t) (hscale : t ^ 3 * r ^ 2 = D ^ 2)
    (hfloor : floor * (100 * D ^ 2 / ε) ≤ 100 * (H : ℝ) ^ 2 * t ^ 2)
    (hMscale : 1 ≤ floor * (100 * D ^ 2 / ε))
    (hlog : 1 + Real.log (3 * (100 * D ^ 2 / ε) * cap) ≤ 6 * H)
    (select : StateSpace X → (ℕ → ProbeSeed) → ℝ) (hs : ∀ s seeds, 0 < select s seeds)
    (hcert : ∀ s seeds, AffineSoftmaxSearchCoupling.Certificate (displacement F floor s) r floor cap (select s seeds))
    (reply : Fin m × E → ℝ × E) (initial : E) (hi : initial ∈ X)
    (seeds : ℕ → OuterSeed) (N : ℕ) (hN : 200 * H * t ≤ (N : ℝ)) :
    let step := transition m hX hcompact τ L G r D ε hr.le select hs H reply
    let initialState := lift (⟨0, initial, initial⟩ : State E) ⟨le_rfl, hi, hi⟩
    let states := fun k => AffineSoftmaxSearchCoupling.path step initialState seeds k
    (∑ k ∈ Finset.range N, movement F floor D ε select (states k) (seeds k).1 ≤ 60 * D ^ 2) →
      100 * D ^ 2 / ε ≤ (state (states N)).weight := by
  let step := transition m hX hcompact τ L G r D ε hr.le select hs H reply
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
  have hAmono : Monotone A := path_weight_monotone m hX hcompact τ L G r D ε hr.le select hs H reply initialState seeds
  have hApos k : 0 < A (k + 1) :=
    transition_weight_pos m hX hcompact τ L G r D ε hr.le hM select hs H reply (states k) (seeds k)
  have hA_nonneg k : 0 ≤ A k := (states k).property.1
  have hμ k : 0 < μ k := hs _ _
  have ha k : 0 < a k := (CappedProximalGeometry.accelerated_weight_properties (hμ k) (hA_nonneg k)).1
  have hlower s seed : floor ≤ select s seed := (hcert s seed).1.1
  have hAend : A N ≤ 3 * (100 * D ^ 2 / ε) := path_weight_bound m hX hcompact τ L G r D ε hr.le
    select hs hlower hM hMscale H reply initialState (by change 0 ≤ _; positivity) seeds N
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
  have hratio0 := weight_ratio_bound A hAzero hAmono hApos N hM (hf.trans_le hfc)
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
  have hc := active_step_count A a μ d N hr htpos hHt hf hM hscale hfloor hAzero hAmono hAend
    (fun k _ => ha k) (fun k _ => hμ k) hstep hweight
    (fun k _ => (AffineSoftmaxSearchCoupling.certificate_outer_validity _ hr hf.le (hcert (states k) (seeds k).1)).2)
    hraw hratio
  nlinarith [mul_pos (show (0 : ℝ) < H by positivity) htpos]

end LongTails.Proofs.AffineSoftmaxOuterStopping
