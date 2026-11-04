import LongTails.Proofs.UscgSharpScalarPath
import LongTails.Proofs.UscgSharpMixing
import LongTails.Proofs.UscgSharpInstances

namespace LongTails.Proofs.UscgSharpMixingPath

open scoped RealInnerProductSpace
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open LongTails.Algorithms.UscgSharpConfidence
open UscgSharpScalar UscgSharpScalarPath UscgSharpSchedule UscgSharpMixing

noncomputable def arrivals (α : ℝ) (I : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (1 - α) ^ (n - 1 - j) * (I j : ℝ)

lemma arrivals_succ (α : ℝ) (I : ℕ → ℕ) (n : ℕ) :
    arrivals α I (n + 1) = (1 - α) * arrivals α I n + I n := by
  unfold arrivals
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : n - j = (n - 1 - j) + 1 := by have := Finset.mem_range.mp hj; omega
  rw [he, pow_succ]
  ring

lemma arrivals_padded (α C : ℝ) (I : ℕ → ℕ) {t T : ℕ} (ht : t < T) :
    (∑ j ∈ Finset.range T, (I j : ℝ) * (if j ≤ t then C * (1 - α) ^ (t - j) else 0)) =
      C * arrivals α I (t + 1) := by
  calc
    _ = ∑ j ∈ Finset.range (t + 1), (I j : ℝ) * (if j ≤ t then C * (1 - α) ^ (t - j) else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : t + 1 ≤ T))
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [show ¬j ≤ t by omega]
    _ = _ := by
      unfold arrivals
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_sub_cancel, ite_eq_left (show j ≤ t by have := Finset.mem_range.mp hj; omega)]
      ring

lemma constant_momentum {Ω : Type} {α η g p : ℝ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (I : ℕ → ℕ)
    (ha : 0 < α) (ha1 : α < 1)
    (hnoise : ∀ t, noise (ξ t) = -2 * g + (2 * g / p) * I t) (n : ℕ) :
    momentum α η (fun _ => g) noise lmo ξ n =
      g * (-mass α n + (2 * α / p) * arrivals α I n) := by
  induction n with
  | zero => simp [momentum, mass, arrivals]
  | succ n ih =>
    rw [momentum_succ _ _ _ _ ha ha1, ih, hnoise n, arrivals_succ]
    simp only [mass, pow_succ]
    ring

lemma positive_constant_path {Ω : Type} {α η g p : ℝ} {T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (I : ℕ → ℕ)
    (ha : 0 < α) (ha1 : α < 1) (he : 0 < η) (hg : 0 < g) (hp : 0 < p)
    (hC : 1 ≤ 4 * α / p) (hI : ∀ j, I j ≤ 1)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hnoise : ∀ t, noise (ξ t) = -2 * g + (2 * g / p) * I t)
    (hsparse : ∀ n, 0 < n → n ≤ T →
      2 * ((Real.log (4 * α / p) + 2) / α) *
        ((∑ j ∈ Finset.range n, I j : ℕ) : ℝ) < n) :
    ∀ n, 0 < n → n ≤ T → 0 < position α η (fun _ => g) noise lmo ξ n := by
  let x := position α η (fun _ => g) noise lmo ξ
  let m := fun t => momentum α η (fun _ => g) noise lmo ξ (t + 1) / g
  let v := fun t => ⟪axis, lmo (trajectory α η (fun _ => g) noise lmo ξ (t + 1)).2⟫
  have hsignal : ∀ n ≤ T, ∀ t < n, m t = -mass α (t + 1) +
      (∑ j ∈ Finset.range n, (I j : ℝ) *
        (if j ≤ t then (4 * α / p) * (1 - α) ^ (t - j) else 0)) / 2 := by
    intro n hn t ht
    dsimp [m]
    rw [constant_momentum noise lmo ξ I ha ha1 hnoise, arrivals_padded _ _ _ ht]
    field_simp
    ring
  have ho : ∀ n ≤ T, (∑ t ∈ Finset.range n, if 0 ≤ m t then (1 : ℝ) else 0) ≤
      ((Real.log (4 * α / p) + 2) / α) * ((∑ j ∈ Finset.range n, I j : ℕ) : ℝ) := by
    intro n hn
    have hz := early_zero_of_sparse (burn_le_radius ha ha1.le hC)
      (fun k hk hkn => hsparse k hk (hkn.trans hn))
    have hh := occupation_from_signal (mass := fun t => mass α (t + 1)) ha ha1.le hC hI hz
      (fun t _ => mass_pos ha ha1 (by omega))
      (fun t _ ht => late_mass ha ha1.le ht) (hsignal n hn)
    simpa using hh
  apply positive_displacement (x := x) (m := m) (v := v) he (initial _ _ _ _).1
    (fun t _ => position_succ _ _ _ _ t)
    (fun t _ => lmo_coordinate_lower hlmo _) ?_ ho hsparse
  intro t ht hmt
  have hm : momentum α η (fun _ => g) noise lmo ξ (t + 1) < 0 := by
    have hh := (div_lt_iff₀ hg).mp hmt
    simpa using hh
  have hh := position_succ_negative (fun _ => g) noise lmo ξ ha ha1 hlmo t hm
  have hu := position_succ (α := α) (η := η) (fun _ => g) noise lmo ξ t
  change v t = 1
  change x (t + 1) = x t + η * v t at hu
  change x (t + 1) = x t + η at hh
  nlinarith

lemma ramp_stationarity {Ω : Type} {α η L g : ℝ} {T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (hg : 0 ≤ g)
    (hx : ∀ t < T, 0 ≤ position α η (fun _ => g) noise lmo ξ t) :
    ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
      (gradient (lift (UscgSharpInstances.ramp L g 0))
        (trajectory α η (UscgSharpInstances.rampSlope L g 0) noise lmo ξ t).1) = T * g := by
  have hgrad : ∀ t < T, (fun _ => g) (position α η (fun _ => g) noise lmo ξ t) =
      UscgSharpInstances.rampSlope L g 0 (position α η (fun _ => g) noise lmo ξ t) := by
    intro t ht
    symm
    exact UscgSharpInstances.ramp_plateau (by simpa using hx t ht)
  have hpath := trajectory_coupling (α := α) (η := η) (fun _ => g) noise lmo ξ
    (UscgSharpInstances.rampSlope L g 0) T hgrad
  calc
    _ = ∑ t ∈ Finset.range T, g := by
      apply Finset.sum_congr rfl
      intro t ht
      have htr := Finset.mem_range.mp ht
      rw [← hpath t htr.le, lift_gradient_eq (UscgSharpInstances.ramp_derivative L g 0), dual_axis]
      change |UscgSharpInstances.rampSlope L g 0 (position α η (fun _ => g) noise lmo ξ t)| = g
      rw [← hgrad t htr]
      exact abs_of_nonneg hg
    _ = _ := by simp

end LongTails.Proofs.UscgSharpMixingPath
