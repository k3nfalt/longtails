import LongTails.Proofs.FixedBatchConfidenceTrajectory
import LongTails.Proofs.FixedBatchConfidenceDynamics
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma constant_batch_gradient {b : ℕ} (hb : 0 < b) (a x : Space) :
    (b : ℝ)⁻¹ • (∑ _i : Fin b, ⟪a, x⟫ • a) = ⟪a, x⟫ • a := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]

lemma scalar_batch_iterate {b : ℕ} (hb : 0 < b) (a η : ℝ)
    (ξ : ℕ → Fin b → Bool) (K : ℕ) :
    MarkovQuadratic.iterate
      (fun (x : Space) (_ : Fin b → Bool) => (b : ℝ)⁻¹ •
        ∑ _i : Fin b, ⟪pair a 0, x⟫ • pair a 0) η (pair 1 0) ξ K =
      pair ((1 - η * a ^ 2) ^ K) 0 := by
  induction K with
  | zero => simp [MarkovQuadratic.iterate]
  | succ K ih =>
    rw [MarkovQuadratic.iterate, ih, constant_batch_gradient hb]
    ext i
    fin_cases i <;> simp [pair_inner, PiLp.sub_apply, PiLp.smul_apply, pow_succ]; ring

lemma scalar_tuning {η : ℝ} {K : ℕ} (hη : 0 < η) (hK : 0 < K) :
    let ell := min 1 (1 / (2 * η * (K : ℝ)))
    0 < ell ∧ ell ≤ 1 ∧
      ell / 8 ≤ ell * (1 - η * ell) ^ (2 * K) / 2 := by
  intro ell
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : 0 < 2 * η * (K : ℝ) := by positivity
  have hell0 : 0 < ell := lt_min zero_lt_one (by positivity)
  have hell1 : ell ≤ 1 := min_le_left _ _
  have he : ell * (2 * η * (K : ℝ)) ≤ 1 :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have hb : (K : ℝ) * η * ell ≤ 1 / 2 := by nlinarith
  exact ⟨hell0, hell1, scalar_bias_lower hK hη.le hell0.le hb⟩

lemma deterministic_failure_probability (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P]
    {b : ℕ} (hb : 0 < b) (a η e δ : ℝ) (K : ℕ) (p : unitInterval)
    (hδ : δ < 1) (herror : e < a ^ 2 * (1 - η * a ^ 2) ^ (2 * K) / 2) :
    let G := fun (x : Space) (z : Fin b → Bool) => (b : ℝ)⁻¹ • ∑ i,
      ⟪(if z i then pair a 0 else pair a 0), x⟫ •
        (if z i then pair a 0 else pair a 0)
    let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
      (fun k i => ξ (k * b + i.val)) K
    δ < P.real {ξ | e < (p : ℝ) * (⟪pair a 0, X ξ⟫ ^ 2 / 2) +
      (1 - p) * (⟪pair a 0, X ξ⟫ ^ 2 / 2)} := by
  intro G X
  have hx (ξ : ℕ → Bool) : X ξ = pair ((1 - η * a ^ 2) ^ K) 0 := by
    dsimp [X, G]
    simpa only [ite_self] using scalar_batch_iterate hb a η
      (fun k i => ξ (k * b + i.val)) K
  have he (ξ : ℕ → Bool) : (p : ℝ) * (⟪pair a 0, X ξ⟫ ^ 2 / 2) +
      (1 - p) * (⟪pair a 0, X ξ⟫ ^ 2 / 2) =
        a ^ 2 * (1 - η * a ^ 2) ^ (2 * K) / 2 := by
    rw [hx, pair_inner, Nat.mul_comm 2 K, pow_mul]
    ring
  have hs : {ξ | e < (p : ℝ) * (⟪pair a 0, X ξ⟫ ^ 2 / 2) +
      (1 - p) * (⟪pair a 0, X ξ⟫ ^ 2 / 2)} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ξ
    change e < _
    rw [he]
    exact herror
  simpa only [hs, probReal_univ] using hδ

end OracleTemplate.FixedBatchConfidence
