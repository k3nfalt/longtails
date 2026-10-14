import LongTails.Proofs.FixedBatchConfidenceTrajectory
import LongTails.Proofs.FixedBatchConfidenceProbability

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma one_hot_entries {m : ℕ} (v : Fin m → Bool)
    (hv : v ∈ ⋃ j : Fin m, {Function.update (fun _ => false) j true}) :
    ∃ j : Fin m, ∀ i : Fin m, v i = decide (i.val = j.val) := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
  have he : v = Function.update (fun _ => false) j true := Set.mem_singleton_iff.mp hj
  refine ⟨j, ?_⟩
  intro i
  rw [he]
  by_cases hij : i = j
  · subst i
    simp
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Function.update_of_ne hij, hne]

lemma boolean_count_one_hot {b : ℕ} (j : Fin b) :
    (∑ i : Fin b, if decide (i.val = j.val) then (1 : ℝ) else 0) = 1 := by
  have he (i : Fin b) : (if decide (i.val = j.val) then (1 : ℝ) else 0) =
      if i = j then 1 else 0 := by simp [Fin.ext_iff]
  simp_rw [he]
  simp

lemma count_extension_zero (f : ℕ → ℝ) (n m : ℕ)
    (hz : ∀ j < m, f (n + j) = 0) :
    (∑ j ∈ Finset.range (n + m), f j) = ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_range_add]
  have hsum : (∑ j ∈ Finset.range m, f (n + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (Finset.mem_range.mp hj)
  rw [hsum, add_zero]

lemma window_rare_batch {b m hit start : ℕ} (hb : 0 < b) (hhit : hit < m * b)
    (ξ : ℕ → Bool)
    (hwindow : ∀ r < m * b, ξ (start + r) = decide (r = hit)) :
    (∑ i : Fin b, if ξ (start + hit / b * b + i.val) then (1 : ℝ) else 0) = 1 := by
  let j : Fin b := ⟨hit % b, Nat.mod_lt hit hb⟩
  have hdiv : hit / b < m := (Nat.div_lt_iff_lt_mul hb).mpr hhit
  have hsum : hit / b * b + hit % b = hit := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod hit b
  have he (i : Fin b) : ξ (start + hit / b * b + i.val) = decide (i.val = j.val) := by
    have hr : hit / b * b + i.val < m * b := by
      have hm := Nat.mul_le_mul_right b (show hit / b + 1 ≤ m by omega)
      have hi := i.isLt
      nlinarith
    rw [Nat.add_assoc, hwindow _ hr]
    have heq : (hit / b * b + i.val = hit) ↔ (i.val = j.val) := by
      dsimp [j]
      omega
    exact Bool.decide_congr heq
  simp_rw [he]
  exact boolean_count_one_hot j

lemma window_common_batch {b m hit start k : ℕ} (hb : 0 < b) (hk : k < m)
    (hneq : k ≠ hit / b) (ξ : ℕ → Bool)
    (hwindow : ∀ r < m * b, ξ (start + r) = decide (r = hit)) :
    ∀ i : Fin b, ξ (start + k * b + i.val) = false := by
  intro i
  have hr : k * b + i.val < m * b := by
    have hm := Nat.mul_le_mul_right b (show k + 1 ≤ m by omega)
    have hi := i.isLt
    nlinarith
  have hne : k * b + i.val ≠ hit := by
    intro he
    have hd := congrArg (fun r => r / b) he
    rw [Nat.mul_comm k, Nat.mul_add_div hb, Nat.div_eq_of_lt i.isLt, Nat.add_zero] at hd
    exact hneq hd
  rw [Nat.add_assoc, hwindow _ hr]
  simp [hne]

lemma window_prefix_count {b m hit start : ℕ} (hhit : hit < m * b)
    (ξ : ℕ → Bool)
    (hwindow : ∀ r < m * b, ξ (start + r) = decide (r = hit)) :
    (∑ j ∈ Finset.range (start + hit / b * b), if ξ j then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.range start, if ξ j then (1 : ℝ) else 0 := by
  apply count_extension_zero
  intro j hj
  have hmul : hit / b * b ≤ hit := Nat.div_mul_le_self hit b
  have hjhit : j < hit := lt_of_lt_of_le hj hmul
  rw [hwindow j (hjhit.trans hhit)]
  simp [ne_of_lt hjhit]

lemma window_batch_fractions {b m hit offset : ℕ} (hb : 0 < b) (hhit : hit < m * b)
    (ξ : ℕ → Bool)
    (hwindow : ∀ r < m * b, ξ (offset * b + r) = decide (r = hit)) :
    let θ := fun k => (b : ℝ)⁻¹ * ∑ i : Fin b, if ξ (k * b + i.val) then (1 : ℝ) else 0
    θ (offset + hit / b) = 1 / b ∧
      (∑ j ∈ Finset.range (offset + hit / b), θ j) =
        (b : ℝ)⁻¹ * (∑ j ∈ Finset.range (offset * b), if ξ j then (1 : ℝ) else 0) ∧
      ∀ j < m, j ≠ hit / b → θ (offset + j) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul, window_rare_batch hb hhit ξ hwindow]
    simp
  · rw [rare_fraction_sum ξ (offset + hit / b), Nat.add_mul, window_prefix_count hhit ξ hwindow]
  · intro j hj hne
    have hz := window_common_batch hb hj hne ξ hwindow
    rw [Nat.add_mul]
    simp_rw [hz]
    simp

lemma normalized_window_risk {b m hit offset : ℕ} (hb : 0 < b) (hhit : hit < m * b)
    (ξ : ℕ → Bool) {a c η p : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a ^ 2 + c ^ 2 = 1) (hc2 : 1 / 2 ≤ c ^ 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 8)
    (hwindow : ∀ r < m * b, ξ (offset * b + r) = decide (r = hit))
    (hcount : η * a ^ 2 / b * (∑ j ∈ Finset.range (offset * b), if ξ j then (1 : ℝ) else 0) ≤ 1 / 4)
    (hpersist : 1 / 4 ≤ (1 - η) ^ (m - 1)) :
    let G := fun (x : Space) (v : Fin b → Bool) => (b : ℝ)⁻¹ • ∑ i,
      ⟪(if v i then pair a c else pair 0 1), x⟫ •
        (if v i then pair a c else pair 0 1)
    let X := MarkovQuadratic.iterate G η (pair 1 0) (fun k i => ξ (k * b + i.val))
    (η / b) ^ 2 * a ^ 2 / 256 ≤
      ((1 - p) * (X (offset + m) 1) ^ 2 +
        p * (a * X (offset + m) 0 + c * X (offset + m) 1) ^ 2) / 2 := by
  intro G X
  let θ := fun k => (b : ℝ)⁻¹ * ∑ i : Fin b, if ξ (k * b + i.val) then (1 : ℝ) else 0
  let k := offset + hit / b
  let n := m - (hit / b + 1)
  have hj : hit / b < m := (Nat.div_lt_iff_lt_mul hb).mpr hhit
  have hend : k + 1 + n = offset + m := by dsimp [k, n]; omega
  have hn : n ≤ m - 1 := by
    exact Nat.sub_le_sub_left (Nat.le_add_left 1 (hit / b)) m
  have hfractions := window_batch_fractions hb hhit ξ hwindow
  have hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ 1 := fun j => boolean_fraction_bounds hb (fun i => ξ (j * b + i.val))
  have hsteps := normalized_iterate_step hb (fun k i => ξ (k * b + i.val)) a c η
  have hprefix : η * a ^ 2 * ∑ j ∈ Finset.range k, θ j ≤ 1 / 4 := by
    change η * a ^ 2 * (∑ j ∈ Finset.range (offset + hit / b), θ j) ≤ _
    rw [hfractions.2.1]
    convert hcount using 1; ring
  have hzero : ∀ j < n, θ (k + 1 + j) = 0 := by
    intro j hjn
    have hlt : hit / b + 1 + j < m := by dsimp [n] at hjn; omega
    have hne : hit / b + 1 + j ≠ hit / b := by omega
    have he : k + 1 + j = offset + (hit / b + 1 + j) := by dsimp [k]; omega
    rw [he]
    exact hfractions.2.2 _ hlt hne
  have hpow : 1 / 4 ≤ (1 - η) ^ n :=
    hpersist.trans (pow_le_pow_of_le_one (by linarith) (by linarith) hn)
  have hr := rare_window_path_risk (fun j => X j 0) (fun j => X j 1) θ
    hη0 hη1 ha hc hac hc2 (by exact_mod_cast hb) hp0 hp1 hθ (by rfl) (by rfl)
    (fun j => (hsteps j).1) (fun j => (hsteps j).2) k n hfractions.1 hprefix hzero hpow
  simpa only [hend] using hr

end OracleTemplate.FixedBatchConfidence
