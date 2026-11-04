import LongTails.Proofs.UscgSharpScalar
import LongTails.Proofs.UscgSharpSchedule

namespace LongTails.Proofs.UscgSharpScalarPath

open scoped RealInnerProductSpace
open LongTails.Setups.UscgConstant (Space IsBallLMO)
open LongTails.Algorithms.UscgSharpConfidence
open OracleTemplate.NormBallLMO
open UscgSharpScalar UscgSharpSchedule

noncomputable def trajectory {Ω : Type} (α η : ℝ) (f' : ℝ → ℝ) (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) :=
  path (fun x m => x + η • lmo m) (correctedWeight α) 0 (oracle f' noise) ξ

noncomputable def position {Ω : Type} (α η : ℝ) (f' : ℝ → ℝ) (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (t : ℕ) : ℝ :=
  ⟪axis, (trajectory α η f' noise lmo ξ t).1⟫

noncomputable def momentum {Ω : Type} (α η : ℝ) (f' : ℝ → ℝ) (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (t : ℕ) : ℝ :=
  mass α t * ⟪axis, (trajectory α η f' noise lmo ξ t).2⟫

variable {Ω : Type} {α η : ℝ} (f' : ℝ → ℝ) (noise : Ω → ℝ)
  (lmo : Space 1 → Space 1) (ξ : ℕ → Ω)

lemma initial : position α η f' noise lmo ξ 0 = 0 ∧ momentum α η f' noise lmo ξ 0 = 0 := by
  simp [position, momentum, trajectory, path_zero, mass]

lemma momentum_succ (ha : 0 < α) (ha1 : α < 1) (t : ℕ) :
    momentum α η f' noise lmo ξ (t + 1) =
      (1 - α) * momentum α η f' noise lmo ξ t +
        α * (f' (position α η f' noise lmo ξ t) + noise (ξ t)) := by
  simp only [momentum, trajectory, path_succ, inner_add_right, inner_smul_right]
  rw [mul_add, ← mul_assoc, mass_weight ha ha1]
  rw [← mul_assoc, mass_old_weight ha ha1]
  simp only [oracle, inner_smul_right, axis_inner, mul_one]
  unfold position trajectory
  ring

lemma position_succ (t : ℕ) : position α η f' noise lmo ξ (t + 1) =
    position α η f' noise lmo ξ t + η * ⟪axis, lmo (trajectory α η f' noise lmo ξ (t + 1)).2⟫ := by
  simp [position, trajectory, path_succ, inner_add_right, inner_smul_right]

lemma position_succ_negative (ha : 0 < α) (ha1 : α < 1)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) (t : ℕ)
    (hm : momentum α η f' noise lmo ξ (t + 1) < 0) :
    position α η f' noise lmo ξ (t + 1) = position α η f' noise lmo ξ t + η := by
  have hp := mass_pos ha ha1 (show 1 ≤ t + 1 by omega)
  have hn : ⟪axis, (trajectory α η f' noise lmo ξ (t + 1)).2⟫ < 0 := by
    unfold momentum at hm
    nlinarith
  have he : lmo (trajectory α η f' noise lmo ξ (t + 1)).2 = axis := by
    rw [axis_repr (trajectory α η f' noise lmo ξ (t + 1)).2]
    exact lmo_negative hlmo hn
  rw [position_succ, he, axis_inner, mul_one]

lemma position_succ_lower (he : 0 ≤ η)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) (t : ℕ) :
    position α η f' noise lmo ξ t - η ≤ position α η f' noise lmo ξ (t + 1) := by
  rw [position_succ]
  have hh := mul_le_mul_of_nonneg_left (lmo_coordinate_lower hlmo (trajectory α η f' noise lmo ξ (t + 1)).2) he
  linarith

lemma trajectory_coupling (f₂ : ℝ → ℝ) (T : ℕ)
    (hf : ∀ t < T, f' (position α η f' noise lmo ξ t) = f₂ (position α η f' noise lmo ξ t)) :
    ∀ t ≤ T, trajectory α η f' noise lmo ξ t = trajectory α η f₂ noise lmo ξ t := by
  intro t
  induction t with
  | zero => simp [trajectory, path_zero]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hg := hf t (by omega)
    have ho : oracle f' noise (trajectory α η f' noise lmo ξ t).1 (ξ t) =
        oracle f₂ noise (trajectory α η f₂ noise lmo ξ t).1 (ξ t) := by
      unfold oracle
      change (f' (position α η f' noise lmo ξ t) + noise (ξ t)) • axis = _
      rw [hg]
      unfold position
      rw [hprev]
    change path _ _ _ _ _ (t + 1) = path _ _ _ _ _ (t + 1)
    rw [path_succ, path_succ]
    change (fun z : Space 1 × Space 1 =>
      (z.1 + η • lmo (correctedWeight α (t + 1) • oracle f' noise z.1 (ξ t) +
        (1 - correctedWeight α (t + 1)) • z.2),
       correctedWeight α (t + 1) • oracle f' noise z.1 (ξ t) +
        (1 - correctedWeight α (t + 1)) • z.2)) (trajectory α η f' noise lmo ξ t) = _
    dsimp only
    rw [ho, hprev]
    rfl

end LongTails.Proofs.UscgSharpScalarPath
