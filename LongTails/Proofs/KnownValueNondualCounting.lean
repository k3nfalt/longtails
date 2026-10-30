import LongTails.Proofs.KnownValueNondualTrajectory
import LongTails.Proofs.NondualSelectorMovement

open Set

namespace LongTails.Proofs.KnownValueNondualCounting

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualControl KnownValueNondualExecution KnownValueNondualTrajectory

lemma selectorRadius_properties (p : Public) (hd : 0 < p.d) (hR : 0 < p.R) :
    0 < selectorRadius p ∧
      selectorRadius p ^ 2 * ((1 + Nat.log 2 p.d : ℕ) : ℝ) = p.R ^ 2 * p.d := by
  have hd' : 0 < (p.d : ℝ) := by exact_mod_cast hd
  have hk : 0 < (1 : ℝ) + Nat.log 2 p.d := by positivity
  constructor
  · unfold selectorRadius
    positivity
  · simp only [selectorRadius, mul_pow, Nat.cast_add, Nat.cast_one]
    rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma trajectory_movement (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      ‖selector p ((advance p f g)^[k] (initialControl p)).body -
        selector p ((advance p f g)^[k + 1] (initialControl p)).body‖) ≤
      12 * p.R * Real.sqrt (((1 + Nat.log 2 p.d : ℕ) : ℝ) * (1 + Nat.log 2 n : ℕ)) := by
  let : NeZero p.d := ⟨Nat.ne_of_gt hd⟩
  let c := fun k => (advance p f g)^[k] (initialControl p)
  have hi : ∀ k, Invariant p f xstar (c k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hnest : ∀ t < n, (c (t + 1)).body ⊆ (c t).body := by
    intro t _
    simpa only [c, Function.iterate_succ_apply'] using advance_body_subset p f g (c t)
  have hpow : ∀ t : ℕ, t ≤ 2 ^ (1 + Nat.log 2 t) := by
    intro t
    simpa only [Nat.add_comm 1, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t).le
  have h := NondualSelectorMovement.nested_movement_bound (fun k => (c k).body) n
    (fun k _ => ⟨_, (hi k).minimizer_mem⟩) (fun k _ => (hi k).compact)
    (fun k _ => (hi k).convex) hnest hR.le (selectorRadius_properties p hd hR).1
    (fun k _ u hu => (hi k).subset hu) (1 + Nat.log 2 p.d) (1 + Nat.log 2 n)
    (by omega) (by omega) (hpow p.d) (hpow n) (selectorRadius_properties p hd hR).2
  have he : ∀ t, ‖selector p (c t).body - selector p (c (t + 1)).body‖ =
      ‖LongTails.Algorithms.NondualSelector.center (c (t + 1)).body (selectorRadius p) -
        LongTails.Algorithms.NondualSelector.center (c t).body (selectorRadius p)‖ := by
    intro t
    rw [norm_sub_rev]
    simp [selector, Nat.ne_of_gt hd]
  change (∑ k ∈ Finset.range n, ‖selector p (c k).body - selector p (c (k + 1)).body‖) ≤ _
  simpa only [he] using h

lemma weighted_low_count {ι : Type*} (s : Finset ι) (G M Γ : ι → ℝ) {C : ℝ}
    (hΓ : ∀ i ∈ s, 0 < Γ i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hstep : ∀ i ∈ s, Γ i ≤ G i * M i)
    (henergy : (∑ i ∈ s, G i ^ 2 / Γ i ^ 2) ≤ C) :
    (s.card : ℝ) ^ 3 ≤ C * (∑ i ∈ s, M i) ^ 2 := by
  have h := NondualMovement.weighted_cube_of_nonneg s (fun i => G i ^ 2 / Γ i ^ 2) M (fun _ => 1)
    (fun i _ => by positivity) hM (fun _ _ => by norm_num) (by
      intro i hi
      have hs := pow_le_pow_left₀ (hΓ i hi).le (hstep i hi) 2
      rw [mul_pow] at hs
      rw [div_mul_eq_mul_div]
      simpa using (le_div_iff₀ (sq_pos_of_pos (hΓ i hi))).mpr (by simpa using hs))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right henergy (sq_nonneg _))

lemma weighted_high_count {ι : Type*} (s : Finset ι) (G M Γ : ι → ℝ) {C : ℝ}
    (hΓ : ∀ i ∈ s, 0 < Γ i) (hG : ∀ i ∈ s, 0 ≤ G i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hstep : ∀ i ∈ s, Γ i ≤ G i * M i)
    (henergy : (∑ i ∈ s, G i / Γ i) ≤ C) :
    (s.card : ℝ) ^ 2 ≤ C * (∑ i ∈ s, M i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => G i / Γ i) (g := M) (r := fun _ => 1)
    (fun i hi => div_nonneg (hG i hi) (hΓ i hi).le) hM (by
      intro i hi
      rw [div_mul_eq_mul_div]
      simpa using (le_div_iff₀ (hΓ i hi)).mpr (by simpa using hstep i hi))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right henergy (Finset.sum_nonneg hM))

noncomputable def trajectory (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) : Control p :=
  (advance p f g)^[k] (initialControl p)

noncomputable def movement (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) : ℝ :=
  ‖selector p (trajectory p f g k).body - selector p (trajectory p f g (k + 1)).body‖

noncomputable def gradientSize (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) : ℝ :=
  ‖(lineOutput p f g (trajectory p f g k)).2.1.2‖

def FailureAt (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) : Prop :=
  (trajectory p f g k).finished = false ∧ (trajectory p f g (k + 1)).finished = false ∧
    (trajectory p f g (k + 1)).phase = (trajectory p f g k).phase

noncomputable def warmFailures (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => FailureAt p f g k ∧ (trajectory p f g k).warm = true)

noncomputable def lowFailures (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => FailureAt p f g k ∧ (trajectory p f g k).warm = false ∧
    p.L1 * gradientSize p f g k ≤ p.L0)

noncomputable def highFailures (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => FailureAt p f g k ∧ (trajectory p f g k).warm = false ∧
    p.L0 < p.L1 * gradientSize p f g k)

noncomputable def phaseSteps (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => (trajectory p f g (k + 1)).phase = (trajectory p f g k).phase + 1)

lemma trajectory_succ (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) :
    trajectory p f g (k + 1) = advance p f g (trajectory p f g k) := Function.iterate_succ_apply' _ _ _

lemma active_before (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (n k : ℕ) (hk : k ≤ n) (hn : (trajectory p f g n).finished = false) :
    (trajectory p f g k).finished = false := by
  cases hf : (trajectory p f g k).finished with
  | false => rfl
  | true =>
    have he : trajectory p f g n = trajectory p f g k := by
      change (advance p f g)^[n] (initialControl p) = _
      rw [show n = (n - k) + k by omega, Function.iterate_add_apply]
      exact Function.iterate_fixed (advance_finished p f g _ hf) _
    rw [he, hf] at hn
    contradiction

lemma phaseSteps_card (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) :
    ((phaseSteps p f g n).card : ℝ) ≤ ((trajectory p f g n).phase : ℝ) := by
  classical
  let a := fun k => if (trajectory p f g (k + 1)).phase = (trajectory p f g k).phase + 1 then (1 : ℝ) else 0
  have hs : ∀ k, a k ≤ (0 : ℝ) - 0 + 1 *
      (((trajectory p f g (k + 1)).phase : ℝ) - ((trajectory p f g k).phase : ℝ)) := by
    intro k
    rcases advance_phase_target p f g (trajectory p f g k) with h | h
    · simp [a, trajectory_succ, h.1]
    · simp [a, trajectory_succ, h.1, Nat.cast_add, Nat.cast_one]
  have ht := KnownValueNondualPotential.telescope_energy a (fun _ => 0)
    (fun k => ((trajectory p f g k).phase : ℝ)) 1 hs n
  have hsum : (∑ k ∈ Finset.range n, a k) = ((phaseSteps p f g n).card : ℝ) := by
    simp [a, phaseSteps, Finset.sum_boole]
  rw [hsum] at ht
  simpa [trajectory, initialControl] using ht

lemma round_partition (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ)
    (hn : (trajectory p f g n).finished = false) :
    (n : ℝ) ≤ (warmFailures p f g n).card + (lowFailures p f g n).card +
      (highFailures p f g n).card + ((trajectory p f g n).phase : ℝ) := by
  classical
  have hcover : Finset.range n ⊆ ((warmFailures p f g n ∪ lowFailures p f g n) ∪
      highFailures p f g n) ∪ phaseSteps p f g n := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases advance_phase_target p f g (trajectory p f g k) with h | h
    · have hfail : FailureAt p f g k := ⟨active_before p f g n k (by omega) hn,
        active_before p f g n (k + 1) (by omega) hn, by simpa only [trajectory_succ] using h.1⟩
      cases hw : (trajectory p f g k).warm with
      | true => simp [warmFailures, hk, hfail, hw]
      | false =>
        rcases le_or_gt (p.L1 * gradientSize p f g k) p.L0 with hsmall | hlarge
        · simp [lowFailures, hk, hfail, hw, hsmall]
        · simp [highFailures, hk, hfail, hw, hlarge]
    · have hp : k ∈ phaseSteps p f g n := by
        simp only [phaseSteps, Finset.mem_filter, hk, true_and]
        simpa only [trajectory_succ] using h.1
      exact Finset.mem_union_right _ hp
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hcard' := Finset.card_union_le (warmFailures p f g n ∪ lowFailures p f g n) (highFailures p f g n)
  have hcard'' := Finset.card_union_le (warmFailures p f g n) (lowFailures p f g n)
  have hnat : n ≤ (warmFailures p f g n).card + (lowFailures p f g n).card +
      (highFailures p f g n).card + (phaseSteps p f g n).card := by
    simp only [Finset.card_range] at hcard
    omega
  have hreal : (n : ℝ) ≤ (warmFailures p f g n).card + (lowFailures p f g n).card +
      (highFailures p f g n).card + ((phaseSteps p f g n).card : ℝ) := by exact_mod_cast hnat
  linarith [phaseSteps_card p f g n]

lemma trajectory_charge_nonneg (p : Public) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (f : Point p → ℝ) (g : Point p → Point p) (k : ℕ) :
    0 ≤ KnownValueNondualPotential.charge p f g (trajectory p f g k) := by
  unfold KnownValueNondualPotential.charge
  split_ifs
  · rfl
  · exact KnownValueNondualPotential.cutEnergy_nonneg p hL0 hL1 _ _

lemma warm_failure_count (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    ((warmFailures p f g n).card : ℝ) * (7 * warmScale p) ≤
      16 * p.L1 * (∑ k ∈ Finset.range n, movement p f g k) := by
  classical
  have hi : ∀ k, Invariant p f xstar (trajectory p f g k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hstep : ∀ k ∈ warmFailures p f g n, 7 * warmScale p / (16 * p.L1) ≤ movement p f g k := by
    intro k hk
    obtain ⟨_, hfail, hw⟩ := Finset.mem_filter.mp hk
    have h := failure_movement p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
      (KnownValueNondualGeometry.initialBody_norm p hprior) (trajectory p f g k) (hi k) hfail.1
      (by simpa only [trajectory_succ] using hfail.2.1) (by simpa only [trajectory_succ] using hfail.2.2)
    simpa only [movement, trajectory_succ] using h.2 hw
  have hsum := Finset.sum_le_sum hstep
  have hsub : (∑ k ∈ warmFailures p f g n, movement p f g k) ≤
      ∑ k ∈ Finset.range n, movement p f g k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have hh : ((warmFailures p f g n).card : ℝ) * (7 * warmScale p) / (16 * p.L1) ≤
      ∑ k ∈ Finset.range n, movement p f g k := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_div_assoc] using hsum.trans hsub
  have h := (div_le_iff₀ (show 0 < 16 * p.L1 by positivity)).mp hh
  simpa only [mul_comm (16 * p.L1)] using h

lemma low_failure_count (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    ((lowFailures p f g n).card : ℝ) ^ 3 ≤
      30 * p.L0 / p.ε * (∑ k ∈ Finset.range n, movement p f g k) ^ 2 := by
  classical
  let c := trajectory p f g
  let Γ := fun k => (c k).target
  let G := gradientSize p f g
  let M := movement p f g
  have hi : ∀ k, Invariant p f xstar (c k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hΓ : ∀ k, 0 < Γ k := fun k => hε.trans_le (hi k).target_floor
  have hsub : lowFailures p f g n ⊆ Finset.range n := Finset.filter_subset _ _
  have hstep : ∀ k ∈ lowFailures p f g n, Γ k ≤ G k * M k := by
    intro k hk
    obtain ⟨_, hfail, hw, _⟩ := Finset.mem_filter.mp hk
    have h := failure_movement p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
      (KnownValueNondualGeometry.initialBody_norm p hprior) (c k) (hi k) hfail.1
      (by simpa only [trajectory_succ] using hfail.2.1) (by simpa only [trajectory_succ] using hfail.2.2)
    simpa only [Γ, G, M, c, gradientSize, movement, trajectory_succ] using (h.1 hw).le
  have hpoint : ∀ k ∈ lowFailures p f g n, G k ^ 2 / Γ k ^ 2 ≤
      (48 / 5 : ℝ) * p.L0 * (KnownValueNondualPotential.charge p f g (c k) / Γ k ^ 2) := by
    intro k hk
    obtain ⟨_, hfail, hw, hsmall⟩ := Finset.mem_filter.mp hk
    have hc := charge_failure p f g (c k) hfail.1 hw
      (by simpa only [trajectory_succ] using hfail.2.1) (by simpa only [trajectory_succ] using hfail.2.2)
    have h := KnownValueNondualProgress.low_descent_energy hL0 hL1 (show 0 ≤ G k from norm_nonneg _) hsmall
    rw [hc]
    simpa only [mul_div_assoc, G, gradientSize, c] using div_le_div_of_nonneg_right h (sq_nonneg (Γ k))
  have henergy : (∑ k ∈ lowFailures p f g n, G k ^ 2 / Γ k ^ 2) ≤ 30 * p.L0 / p.ε := by
    have he := KnownValueNondualPotential.square_energy_sum p hd hconv hgrad hg hL0 hL1 hR hε hgs
      xstar hmin hval hprior n
    have hsum := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum] at hsum
    have hs : (∑ k ∈ lowFailures p f g n, KnownValueNondualPotential.charge p f g (c k) / Γ k ^ 2) ≤
        ∑ k ∈ Finset.range n, KnownValueNondualPotential.charge p f g (c k) / Γ k ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
        div_nonneg (trajectory_charge_nonneg p hL0 hL1 f g k) (sq_nonneg _))
    have hh := hsum.trans (mul_le_mul_of_nonneg_left (hs.trans he) (by positivity))
    calc
      _ ≤ (48 / 5 : ℝ) * p.L0 * (3 / p.ε) := hh
      _ = (144 / 5 : ℝ) * (p.L0 / p.ε) := by ring
      _ ≤ 30 * (p.L0 / p.ε) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 30 * p.L0 / p.ε := by ring
  have hcount := weighted_low_count (lowFailures p f g n) G M Γ (fun k _ => hΓ k)
    (fun _ _ => norm_nonneg _) hstep henergy
  have hm : (∑ k ∈ lowFailures p f g n, M k) ≤ ∑ k ∈ Finset.range n, M k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
  exact hcount.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2) (by positivity))

lemma high_failure_count (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    ((highFailures p f g n).card : ℝ) ^ 2 ≤
      20 * p.L1 * (1 + ((trajectory p f g n).phase : ℝ)) *
        (∑ k ∈ Finset.range n, movement p f g k) := by
  classical
  let c := trajectory p f g
  let Γ := fun k => (c k).target
  let G := gradientSize p f g
  let M := movement p f g
  have hi : ∀ k, Invariant p f xstar (c k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hΓ : ∀ k, 0 < Γ k := fun k => hε.trans_le (hi k).target_floor
  have hsub : highFailures p f g n ⊆ Finset.range n := Finset.filter_subset _ _
  have hstep : ∀ k ∈ highFailures p f g n, Γ k ≤ G k * M k := by
    intro k hk
    obtain ⟨_, hfail, hw, _⟩ := Finset.mem_filter.mp hk
    have h := failure_movement p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
      (KnownValueNondualGeometry.initialBody_norm p hprior) (c k) (hi k) hfail.1
      (by simpa only [trajectory_succ] using hfail.2.1) (by simpa only [trajectory_succ] using hfail.2.2)
    simpa only [Γ, G, M, c, gradientSize, movement, trajectory_succ] using (h.1 hw).le
  have hpoint : ∀ k ∈ highFailures p f g n, G k / Γ k ≤
      (48 / 5 : ℝ) * p.L1 * (KnownValueNondualPotential.charge p f g (c k) / Γ k) := by
    intro k hk
    obtain ⟨_, hfail, hw, hlarge⟩ := Finset.mem_filter.mp hk
    have hc := charge_failure p f g (c k) hfail.1 hw
      (by simpa only [trajectory_succ] using hfail.2.1) (by simpa only [trajectory_succ] using hfail.2.2)
    have h := KnownValueNondualProgress.high_descent_energy hL0 hL1 hlarge.le
    rw [hc]
    simpa only [mul_div_assoc, G, gradientSize, c] using div_le_div_of_nonneg_right h (hΓ k).le
  have henergy : (∑ k ∈ highFailures p f g n, G k / Γ k) ≤ 20 * p.L1 * (1 + ((trajectory p f g n).phase : ℝ)) := by
    have he := KnownValueNondualPotential.linear_energy_sum p hd hconv hgrad hg hL0 hL1 hR hε hgs
      xstar hmin hval hprior n
    have hsum := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum] at hsum
    have hs : (∑ k ∈ highFailures p f g n, KnownValueNondualPotential.charge p f g (c k) / Γ k) ≤
        ∑ k ∈ Finset.range n, KnownValueNondualPotential.charge p f g (c k) / Γ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
        div_nonneg (trajectory_charge_nonneg p hL0 hL1 f g k) (hΓ k).le)
    have hh := hsum.trans (mul_le_mul_of_nonneg_left (hs.trans he) (by positivity))
    calc
      _ ≤ (48 / 5 : ℝ) * p.L1 * (2 + 2 * ((trajectory p f g n).phase : ℝ)) := hh
      _ = (96 / 5 : ℝ) * (p.L1 * (1 + ((trajectory p f g n).phase : ℝ))) := by ring
      _ ≤ 20 * (p.L1 * (1 + ((trajectory p f g n).phase : ℝ))) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 20 * p.L1 * (1 + ((trajectory p f g n).phase : ℝ)) := by ring
  have hcount := weighted_high_count (highFailures p f g n) G M Γ (fun k _ => hΓ k)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hstep henergy
  have hm : (∑ k ∈ highFailures p f g n, M k) ≤ ∑ k ∈ Finset.range n, M k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
  exact hcount.trans (mul_le_mul_of_nonneg_left hm (by positivity))

end LongTails.Proofs.KnownValueNondualCounting
