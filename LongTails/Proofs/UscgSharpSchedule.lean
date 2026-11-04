import LongTails.Algorithms.UscgSharpConfidence
import LongTails.Proofs.CappedMomentumProcess
import LongTails.Proofs.LmoTrajectory

namespace LongTails.Proofs.UscgSharpSchedule

open LongTails.Algorithms.UscgSharpConfidence
open LongTails.Setups.UscgConstant
open OracleTemplate.NormBallLMO

lemma mass_pos {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {t : ℕ} (ht : 1 ≤ t) :
    0 < mass α t := by
  have hh := pow_lt_one₀ (show 0 ≤ 1 - α by linarith)
    (show 1 - α < 1 by linarith) (show t ≠ 0 by omega)
  dsimp [mass]
  linarith

lemma corrected_one {α : ℝ} (hα : 0 < α) : correctedWeight α 1 = 1 := by
  simp [correctedWeight, mass, hα.ne']

lemma corrected_bounds {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {t : ℕ} (ht : 1 ≤ t) : 0 < correctedWeight α t ∧ correctedWeight α t ≤ 1 := by
  have hm := mass_pos hα hα1 ht
  refine ⟨div_pos hα hm, ?_⟩
  change α / mass α t ≤ 1
  apply (div_le_one hm).mpr
  by_cases heq : t = 1
  · subst t
    simp [mass]
  · have hp := pow_lt_self_of_lt_one₀ (show 0 < 1 - α by linarith)
      (show 1 - α < 1 by linarith) (show 1 < t by omega)
    dsimp [mass]
    linarith

lemma corrected_lt_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {t : ℕ} (ht : 2 ≤ t) : correctedWeight α t < 1 := by
  apply (div_lt_one (mass_pos hα hα1 (by omega))).mpr
  have hp := pow_lt_self_of_lt_one₀ (show 0 < 1 - α by linarith)
    (show 1 - α < 1 by linarith) (show 1 < t by omega)
  dsimp [mass]
  linarith

lemma mass_weight {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (t : ℕ) :
    mass α (t + 1) * correctedWeight α (t + 1) = α := by
  unfold correctedWeight
  have hm := (mass_pos hα hα1 (show 1 ≤ t + 1 by omega)).ne'
  field_simp

lemma mass_old_weight {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (t : ℕ) :
    mass α (t + 1) * (1 - correctedWeight α (t + 1)) = (1 - α) * mass α t := by
  rw [mul_sub, mul_one, mass_weight hα hα1]
  simp only [mass, pow_succ]
  ring

lemma raw_momentum {d : ℕ} {Ω : Type} (step : Space d → Space d → Space d)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (t : ℕ) :
    mass α t • (path step (correctedWeight α) x₁ g ξ t).2 =
      CappedMomentumProcess.ema α
        (fun k (_ : Unit) => g (path step (correctedWeight α) x₁ g ξ k).1 (ξ k)) t () := by
  induction t with
  | zero => simp [mass, path_zero, CappedMomentumProcess.ema]
  | succ t ih =>
    rw [path_succ]
    simp only [smul_add, smul_smul, mass_weight hα hα1, mass_old_weight hα hα1]
    rw [mul_smul, ih]
    simp only [CappedMomentumProcess.ema]
    abel

lemma algorithm_allowed (p : LongTails.Setups.UscgHighProbability.Public)
    {α η : ℝ} (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    LongTails.Setups.UscgHighProbability.spec.allowedAlgorithm p (algorithm p α η) := by
  refine ⟨correctedWeight α, fun _ => η, corrected_one hα, ?_, ?_, rfl⟩
  · intro t ht
    exact ⟨(corrected_bounds hα hα1 ht).1, (corrected_bounds hα hα1 ht).2, hη⟩
  · intro t ht
    exact corrected_lt_one hα hα1 ht

end LongTails.Proofs.UscgSharpSchedule
