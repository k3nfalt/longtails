import LongTails.Proofs.UscgSharpLowerWitness
import LongTails.Proofs.UscgSharpDeterministicLower

namespace LongTails.Proofs.UscgSharpDeterministicWitness

open MeasureTheory
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open UscgSharpScalar UscgSharpScalarPath UscgSharpInstances UscgSharpLowerWitness

lemma ramp_witness {L σ Δ ε δ α η g a : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (hg : 0 ≤ g) (ha : 0 ≤ a) (hδ : δ < 1)
    (hgap : g * a + g ^ 2 / (2 * L) ≤ Δ)
    (hbad : ∀ ξ : ℕ → Unit, ε * T < ∑ t ∈ Finset.range T,
      dualNorm (normSeminorm ℝ (Space 1)) (gradient (lift (ramp L g a))
        (trajectory α η (rampSlope L g a) (fun _ : Unit => 0) lmo ξ t).1)) :
    Nonempty (Witness L σ Δ ε δ α η T lmo) := by
  refine ⟨{
    Ω := Unit
    measurableΩ := inferInstance
    law := Measure.dirac ()
    probability := inferInstance
    f := ramp L g a
    f' := rampSlope L g a
    noise := fun _ => 0
    derivative := ramp_derivative L g a
    problem := ramp_problem hL hg ha hgap measurable_const Integrable.of_finite
      (by simp) Integrable.of_finite (by simpa using sq_nonneg σ)
    failure := ?_ }⟩
  have heq : {ξ : ℕ → Unit | ε * T < ∑ t ∈ Finset.range T,
      dualNorm (normSeminorm ℝ (Space 1)) (gradient (lift (ramp L g a))
        (trajectory α η (rampSlope L g a) (fun _ : Unit => 0) lmo ξ t).1)} = Set.univ := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hbad ξ
  rw [heq, probReal_univ]
  exact hδ

lemma small_horizon_witness {L σ Δ ε δ α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (hδ : δ < 1) (hT : 0 < T) (hT3 : T ≤ 3)
    (hD : 256 ≤ L * Δ / ε ^ 2) :
    Nonempty (Witness L σ Δ ε δ α η T lmo) := by
  have hd := (le_div_iff₀ (sq_pos_of_pos he)).mp hD
  apply ramp_witness (g := 4 * ε) (a := 0) lmo hL (by positivity) (by norm_num) hδ
  · have hh : (4 * ε) ^ 2 / (2 * L) ≤ Δ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    simpa using hh
  · intro ξ
    have hh := UscgSharpDeterministicLower.initial_stationarity (α := α) (η := η) (L := L)
      (fun _ : Unit => (0 : ℝ)) lmo ξ (show 0 ≤ 4 * ε by positivity) hT
    have ht : (T : ℝ) ≤ 3 := by exact_mod_cast hT3
    nlinarith

lemma slow_step_witness {L σ Δ ε δ α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (hδ : δ < 1) (hη : 0 ≤ η) (hT : 0 < T)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hD : 256 ≤ L * Δ / ε ^ 2) (hprogress : 4 * ε * η * T < Δ) :
    Nonempty (Witness L σ Δ ε δ α η T lmo) := by
  have hd := (le_div_iff₀ (sq_pos_of_pos he)).mp hD
  have hhalf : (2 * ε) ^ 2 / (2 * L) ≤ Δ / 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hΔ : 0 < Δ := by nlinarith [sq_pos_of_pos he]
  let a := (Δ - (2 * ε) ^ 2 / (2 * L)) / (2 * ε)
  have ha : 0 ≤ a := by unfold a; apply div_nonneg _ (by positivity); linarith
  have hgap : (2 * ε) * a + (2 * ε) ^ 2 / (2 * L) ≤ Δ := by dsimp [a]; field_simp; ring_nf; rfl
  have hslow : η * T ≤ a := by
    apply (le_div_iff₀ (show 0 < 2 * ε by positivity)).mpr
    nlinarith
  apply ramp_witness (g := 2 * ε) (a := a) lmo hL (by positivity) ha hδ hgap
  intro ξ
  rw [UscgSharpDeterministicLower.slow_stationarity (fun _ : Unit => (0 : ℝ)) lmo ξ hη (by positivity) hlmo hslow]
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  nlinarith

end LongTails.Proofs.UscgSharpDeterministicWitness
