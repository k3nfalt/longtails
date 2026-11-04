import Mathlib

namespace LongTails.Proofs.UscgSharpShock

open MeasureTheory ProbabilityTheory

noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

noncomputable def law (p : unitInterval) : Measure (Bool × Bool) :=
  (bernoulliMeasure true false p).prod (bernoulliMeasure true false half)

instance (p : unitInterval) : IsProbabilityMeasure (law p) := by unfold law; infer_instance

def noise (B : ℝ) (b : Bool × Bool) : ℝ := if b.1 then (if b.2 then B else -B) else 0

lemma mean (p : unitInterval) (B : ℝ) : ∫ b, noise B b ∂law p = 0 := by
  rw [law, integral_prod _ Integrable.of_finite]
  simp_rw [integral_bernoulliMeasure]
  simp [noise, half]
  ring_nf
  simp

lemma variance (p : unitInterval) (B : ℝ) : ∫ b, noise B b ^ 2 ∂law p = (p : ℝ) * B ^ 2 := by
  rw [law, integral_prod _ Integrable.of_finite]
  simp_rw [integral_bernoulliMeasure]
  simp [noise, half]
  ring_nf
  simp

lemma negative_probability (p : unitInterval) : (law p).real {(true, false)} = (p : ℝ) / 2 := by
  have heq : ({(true, false)} : Set (Bool × Bool)) = {true} ×ˢ {false} := by ext ⟨a,b⟩; simp
  rw [heq, measureReal_def, law, Measure.prod_prod, ENNReal.toReal_mul]
  change (bernoulliMeasure true false p).real {true} * (bernoulliMeasure true false half).real {false} = _
  simp [bernoulliMeasure_real_apply _ (measurableSet_singleton _), half]
  ring

lemma zero_probability (p : unitInterval) : (law p).real {b | b.1 = false} = 1 - (p : ℝ) := by
  have heq : ({b : Bool × Bool | b.1 = false} : Set (Bool × Bool)) = {false} ×ˢ Set.univ := by ext ⟨a,b⟩; simp
  rw [heq, measureReal_def, law, Measure.prod_prod, ENNReal.toReal_mul]
  change (bernoulliMeasure true false p).real {false} * (bernoulliMeasure true false half).real Set.univ = _
  simp [bernoulliMeasure_real_apply _ (measurableSet_singleton _)]

lemma power_lower {p : ℝ} (hp1 : p ≤ 1) (n : ℕ) : 1 - (n : ℝ) * p ≤ (1 - p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p, Nat.cast_nonneg (α := ℝ) n]

def event {n : ℕ} (j : Fin n) : Set (Fin n → Bool × Bool) :=
  Set.pi Set.univ (fun i => if i = j then {(true, false)} else {b | b.1 = false})

lemma event_probability {n : ℕ} (p : unitInterval) (j : Fin n) :
    (Measure.pi fun _ : Fin n => law p).real (event j) =
      (p : ℝ) / 2 * (1 - (p : ℝ)) ^ (n - 1) := by
  have hval (i : Fin n) : (law p).real
      (if i = j then {(true, false)} else {b | b.1 = false}) =
      if i = j then (p : ℝ) / 2 else 1 - (p : ℝ) := by
    split_ifs <;> simp [negative_probability, zero_probability]
  rw [measureReal_def, event, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ i : Fin n, (law p).real (if i = j then {(true, false)} else {b | b.1 = false})) = _
  simp_rw [hval]
  rw [Finset.prod_ite]
  simp [Finset.filter_eq', Finset.filter_ne']

lemma event_noise {n : ℕ} {j : Fin n} {ξ : Fin n → Bool × Bool}
    (hξ : ξ ∈ event j) (B : ℝ) (i : Fin n) : noise B (ξ i) = if i = j then -B else 0 := by
  have hi := hξ i (Set.mem_univ i)
  by_cases hij : i = j
  · simp only [hij, ite_true, Set.mem_singleton_iff] at hi
    simp [hi, noise, hij]
  · simp only [hij, ite_false, Set.mem_ofPred_eq] at hi
    simp [noise, hi, hij]

def streamEvent (T : ℕ) : Set (ℕ → Bool × Bool) :=
  Set.pi (Finset.range T) (fun i => if i = 0 then {(true, false)} else {b | b.1 = false})

lemma stream_probability (p : unitInterval) {T : ℕ} (hT : 0 < T) :
    (Measure.infinitePi fun _ : ℕ => law p).real (streamEvent T) =
      (p : ℝ) / 2 * (1 - (p : ℝ)) ^ (T - 1) := by
  have hval (i : ℕ) : (law p).real
      (if i = 0 then {(true, false)} else {b | b.1 = false}) =
      if i = 0 then (p : ℝ) / 2 else 1 - (p : ℝ) := by
    split_ifs <;> simp [negative_probability, zero_probability]
  rw [measureReal_def, streamEvent, Measure.infinitePi_pi _ (fun _ _ => (Set.to_countable _).measurableSet), ENNReal.toReal_prod]
  change (∏ i ∈ Finset.range T, (law p).real (if i = 0 then {(true, false)} else {b | b.1 = false})) = _
  simp_rw [hval]
  rw [Finset.prod_ite]
  simp [Finset.filter_eq', Finset.filter_ne', hT]

lemma stream_noise {T : ℕ} {ξ : ℕ → Bool × Bool}
    (hξ : ξ ∈ streamEvent T) (B : ℝ) {t : ℕ} (ht : t < T) :
    noise B (ξ t) = if t = 0 then -B else 0 := by
  have hi := hξ t (Finset.mem_range.mpr ht)
  by_cases ht0 : t = 0
  · simp only [ht0, ite_true, Set.mem_singleton_iff] at hi
    simp [ht0, hi, noise]
  · simp only [ht0, ite_false, Set.mem_ofPred_eq] at hi
    simp [noise, hi, ht0]

lemma probability_lower {δ : ℝ} {T : ℕ} (hδ : 0 ≤ δ) (hp : 4 * δ ≤ 1)
    (hT : (T : ℝ) * δ ≤ 1 / 16) :
    3 / 2 * δ ≤ (4 * δ) / 2 * (1 - 4 * δ) ^ (T - 1) := by
  have hn : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.sub_le T 1
  have hm := mul_le_mul_of_nonneg_right hn hδ
  have hh := power_lower hp (T - 1)
  have hl : (3 / 4 : ℝ) ≤ (1 - 4 * δ) ^ (T - 1) := by linarith
  nlinarith

end LongTails.Proofs.UscgSharpShock
