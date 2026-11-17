import LongTails.Proofs.FrontierChainWall
import LongTails.Proofs.FrontierChainPrefix
import LongTails.Proofs.HolderNoiseHardOracle

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FrontierChainOracle

open FrontierChainWall FrontierChainNoise FrontierChainPrefix SoftRadialProjection HolderNoiseHardOracle

variable {d k : ℕ}

noncomputable def projectedNoise (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  derivative (radius k) x (noiseField π (project (radius k) x))

noncomputable def canonicalOracle (π : Fin (k + 1) ↪ Fin d) (p : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (b : Bool) : EuclideanSpace ℝ (Fin d) :=
  oracleValue p (wallField π (radius k) (1 / 5)) (projectedNoise π) x b

lemma projectedNoise_norm (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖projectedNoise π x‖ ≤ 66 := by
  exact (derivative_norm_le (radius_pos k) x _).trans (by linarith [noiseField_norm π (project (radius k) x)])

lemma projectedNoise_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖projectedNoise π x - projectedNoise π y‖ ≤ 10242 * ‖x - y‖ := by
  have h := composition_field_lipschitz (radius_pos k) (by norm_num : (0 : ℝ) ≤ 2560)
    (noiseField π) (noiseField_norm π) (noiseField_lipschitz π) x y
  have hr : 6 * 33 / radius k ≤ 2 := by
    rw [div_le_iff₀ (radius_pos k)]
    linarith [radius_lower k]
  change ‖projectedNoise π x - projectedNoise π y‖ ≤ _ at h
  nlinarith [norm_nonneg (x - y)]

lemma canonicalOracle_false (π : Fin (k + 1) ↪ Fin d) (p : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    canonicalOracle π p x false =
      derivative (radius k) x (FrontierChain.field π (project (radius k) x) -
        noiseField π (project (radius k) x)) + (1 / 5 : ℝ) • x := by
  simp only [canonicalOracle, oracleValue, coinError, Bool.false_eq_true, ite_false,
    neg_one_smul, wallField, projectedNoise, map_sub]
  abel

lemma canonicalOracle_false_prefix (π π' : Fin (k + 1) ↪ Fin d) (p : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val < r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |project (radius k) x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |project (radius k) x (π' j)| ≤ 1 / 4) :
    canonicalOracle π p x false = canonicalOracle π' p x false := by
  rw [canonicalOracle_false, canonicalOracle_false, residual_prefix π π' _ r hπ hx hx']

lemma canonicalOracle_prefix (π π' : Fin (k + 1) ↪ Fin d) (p : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (r : ℕ) (b : Bool)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |project (radius k) x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |project (radius k) x (π' j)| ≤ 1 / 4) :
    canonicalOracle π p x b = canonicalOracle π' p x b := by
  unfold canonicalOracle oracleValue wallField projectedNoise
  rw [field_prefix π π' _ r hπ hx hx', noise_prefix π π' _ r hπ hx hx']

end LongTails.Proofs.FrontierChainOracle
