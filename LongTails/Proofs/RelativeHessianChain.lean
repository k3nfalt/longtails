import LongTails.Proofs.RelativeHessianArctan
import LongTails.Proofs.RelativeHessianGate

namespace LongTails.Proofs.RelativeHessianChain

open RelativeHessianArctan RelativeHessianGate
open scoped BigOperators

noncomputable def link (s t : ℝ) : ℝ := gate (-s) * profile (-t) - gate s * profile t
noncomputable def outgoing (s t : ℝ) : ℝ := -gateSlope (-s) * profile (-t) - gateSlope s * profile t
noncomputable def incoming (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then -density (y i) else -(gate (y (i - 1)) + gate (-y (i - 1))) * density (y i)
noncomputable def field (y : ℕ → ℝ) (m i : ℕ) : ℝ :=
  incoming y i + if i + 1 < m then outgoing (y i) (y (i + 1)) else 0
noncomputable def value (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  -profile (y 0) + ∑ i ∈ Finset.range (m - 1), link (y i) (y (i + 1))

lemma outgoing_nonpos (s t : ℝ) : outgoing s t ≤ 0 := by
  have h1 := mul_nonneg (gateSlope_nonneg (-s)) (profile_bounds (-t)).1.le
  have h2 := mul_nonneg (gateSlope_nonneg s) (profile_bounds t).1.le
  unfold outgoing
  nlinarith

lemma incoming_nonpos (y : ℕ → ℝ) (i : ℕ) : incoming y i ≤ 0 := by
  unfold incoming
  split_ifs
  · exact neg_nonpos.mpr (density_bounds _).1.le
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg
      (gate_bounds _).1 (gate_bounds _).1)) (density_bounds _).1.le

lemma field_nonpos (y : ℕ → ℝ) (m i : ℕ) : field y m i ≤ 0 := by
  have hi := incoming_nonpos y i
  have ho := outgoing_nonpos (y i) (y (i + 1))
  unfold field
  split_ifs <;> linarith

lemma saturated_pair {t : ℝ} (ht : 1 / 5 ≤ |t|) : gate t + gate (-t) = 1 := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    rw [(gate_saturated ht).1, (gate_flat (show -t ≤ 1 / 10 by linarith)).1]
    ring
  · rw [abs_of_neg h] at ht
    rw [(gate_saturated ht).1, (gate_flat (show t ≤ 1 / 10 by linarith)).1]
    ring

lemma incoming_active (y : ℕ → ℝ) (i : ℕ)
    (hi : i = 0 ∨ 1 / 5 ≤ |y (i - 1)|) : incoming y i = -density (y i) := by
  unfold incoming
  split_ifs with hz
  · rfl
  · rw [saturated_pair (hi.resolve_left hz)]
    ring

lemma first_small_gradient (y : ℕ → ℝ) (m i : ℕ) (hi : |y i| ≤ 1 / 5)
    (hprev : ∀ j < i, 1 / 5 < |y j|) : coefficient * y i + field y m i ≤ -7 / 10 := by
  have ha : i = 0 ∨ 1 / 5 ≤ |y (i - 1)| := by
    by_cases hz : i = 0
    · exact Or.inl hz
    · exact Or.inr (hprev (i - 1) (by omega)).le
  have hsmall := small_gradient hi
  have ho := outgoing_nonpos (y i) (y (i + 1))
  unfold field
  rw [incoming_active y i ha]
  split_ifs <;> linarith

lemma exists_large_gradient (y : ℕ → ℝ) (m : ℕ) (h : ∃ i < m, |y i| ≤ 1 / 5) :
    ∃ i < m, coefficient * y i + field y m i ≤ -7 / 10 := by
  classical
  let P := fun i : ℕ => i < m ∧ |y i| ≤ 1 / 5
  have he : ∃ i, P i := h
  let i := Nat.find he
  have hi := Nat.find_spec he
  refine ⟨i, hi.1, first_small_gradient y m i hi.2 ?_⟩
  intro j hj
  by_contra hc
  have hjc : |y j| ≤ 1 / 5 := le_of_not_gt hc
  have hn := Nat.find_min' he (show P j from ⟨by omega, hjc⟩)
  change i ≤ j at hn
  omega

lemma link_bounds (s t : ℝ) : -Real.pi ≤ link s t ∧ link s t ≤ Real.pi := by
  have h1 := mul_nonneg (gate_bounds (-s)).1 (profile_bounds (-t)).1.le
  have h2 := mul_nonneg (gate_bounds s).1 (profile_bounds t).1.le
  have h3 := mul_le_mul (gate_bounds (-s)).2 (profile_bounds (-t)).2.le
    (profile_bounds (-t)).1.le (by norm_num : (0 : ℝ) ≤ 1)
  have h4 := mul_le_mul (gate_bounds s).2 (profile_bounds t).2.le
    (profile_bounds t).1.le (by norm_num : (0 : ℝ) ≤ 1)
  unfold link
  constructor <;> nlinarith

lemma value_lower (y : ℕ → ℝ) (m : ℕ) : -Real.pi * (m + 1 : ℕ) ≤ value y m := by
  have hs : -(m - 1 : ℕ) * Real.pi ≤ ∑ i ∈ Finset.range (m - 1), link (y i) (y (i + 1)) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (m - 1)) => (link_bounds (y i) (y (i + 1))).1)
    simpa using h
  have hp := (profile_bounds (y 0)).2
  have hm : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hpi := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_right hm hpi.le
  unfold value
  push_cast
  linarith

lemma value_zero (m : ℕ) : value (fun _ => 0) m = -Real.pi / 2 := by
  have hg := (gate_flat (by norm_num : (0 : ℝ) ≤ 1 / 10)).1
  simp [value, link, hg, profile]
  ring

lemma field_zero (m : ℕ) (i : ℕ) : field (fun _ => 0) m i = if i = 0 then -1 else 0 := by
  obtain ⟨hg, hgs, _, _⟩ := gate_flat (by norm_num : (0 : ℝ) ≤ 1 / 10)
  simp [field, incoming, outgoing, hg, hgs, density]

end LongTails.Proofs.RelativeHessianChain
