import LongTails.Proofs.AdaptiveReplicaProcess
import LongTails.Proofs.RobustPilotConfidence

open MeasureTheory

namespace LongTails.Proofs.AdaptiveReplicaProbability

lemma majority_product_lower {r : ℕ} (X : Fin r → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hbad : r ≤ 2 * (Finset.univ.filter (fun i => 64 ≤ X i)).card) :
    (8 : ℝ) ^ r ≤ ∏ i, (1 + X i) := by
  classical
  have hprod : (∏ i : Fin r, if 64 ≤ X i then (64 : ℝ) else 1) ≤
      ∏ i, (1 + X i) := by
    apply Finset.prod_le_prod₀
    · intro i _
      split <;> norm_num
    · intro i _
      split_ifs with hi <;> linarith [hX i]
  have heq : (∏ i : Fin r, if 64 ≤ X i then (64 : ℝ) else 1) =
      (8 : ℝ) ^ (2 * (Finset.univ.filter (fun i => 64 ≤ X i)).card) := by
    rw [← Finset.prod_filter, Finset.prod_const, pow_mul]
    norm_num
  rw [heq] at hprod
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hbad).trans hprod

lemma killed_majority_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {r : ℕ}
    (alive : Set Ω) (X : Fin r → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω)
    (hi : Integrable (alive.indicator (fun ω => ∏ i, (1 + X i ω))) P)
    (hb : (∫ ω, alive.indicator (fun ω => ∏ i, (1 + X i ω)) ω ∂P) ≤ (2 : ℝ) ^ r) :
    P {ω | ω ∈ alive ∧ r ≤ 2 * (Finset.univ.filter (fun i => 64 ≤ X i ω)).card} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ r) := by
  classical
  let W := alive.indicator (fun ω => ∏ i, (1 + X i ω))
  have hW : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact Set.indicator_nonneg (fun x _ => Finset.prod_nonneg (fun i _ => by linarith [hX i x])) ω
  have h := (hi.div_const ((8 : ℝ) ^ r)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hW ω) (by positivity)))
    (s := {ω | ω ∈ alive ∧ r ≤ 2 * (Finset.univ.filter (fun i => 64 ≤ X i ω)).card}) (by
      intro ω hω
      apply (one_le_div (by positivity : (0 : ℝ) < 8 ^ r)).2
      rw [Set.indicator_of_mem hω.1]
      exact majority_product_lower (fun i => X i ω) (fun i => hX i ω) hω.2)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  calc
    _ ≤ (2 : ℝ) ^ r / 8 ^ r := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by rw [← div_pow]; norm_num

lemma scaled_majority_product_lower {r : ℕ} (X : Fin r → ℝ) (hX : ∀ i, 0 ≤ X i)
    (V a : ℝ) (hV : 0 < V) (ha : 0 ≤ a)
    (hbad : r ≤ 2 * (Finset.univ.filter (fun i => 64 * V ≤ X i)).card) :
    (8 * V) ^ r ≤ ∏ i, (X i + V + a) := by
  classical
  have hb : r ≤ 2 * (Finset.univ.filter (fun i => 64 ≤ X i / V)).card := by
    simpa only [le_div_iff₀ hV] using hbad
  have h := majority_product_lower (fun i => X i / V)
    (fun i => div_nonneg (hX i) hV.le) hb
  calc
    (8 * V) ^ r = V ^ r * (8 : ℝ) ^ r := by rw [mul_pow]; ring
    _ ≤ V ^ r * ∏ i, (1 + X i / V) := mul_le_mul_of_nonneg_left h (pow_nonneg hV.le r)
    _ = ∏ i, (V * (1 + X i / V)) := by simp only [Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, (X i + V + a) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have := hX i
        positivity
      · intro i _
        have he : V * (1 + X i / V) = X i + V := by field_simp; ring
        rw [he]
        linarith

lemma scaled_reward_probability {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → ℝ) (hF : Integrable F P) (hF0 : ∀ ω, 0 ≤ F ω)
    (V : ℝ) (hV : 0 < V) (r : ℕ)
    (hb : (∫ ω, F ω ∂P) ≤ (2 * V) ^ r) :
    P {ω | (8 * V) ^ r ≤ F ω} ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ r) := by
  have ht : 0 < (8 * V) ^ r := pow_pos (by positivity) r
  have h := (hF.div_const ((8 * V) ^ r)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hF0 ω) ht.le))
    (s := {ω | (8 * V) ^ r ≤ F ω}) (by
      intro ω hω
      exact (one_le_div ht).mpr hω)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  calc
    _ ≤ (2 * V) ^ r / (8 * V) ^ r := div_le_div_of_nonneg_right hb ht.le
    _ = (1 / 4 : ℝ) ^ r := by
      rw [← div_pow]
      congr 1
      field_simp
      ring

end LongTails.Proofs.AdaptiveReplicaProbability
