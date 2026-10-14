import LongTails.Proofs.FixedBatchConfidenceWindow
import LongTails.Proofs.FixedBatchConfidenceParameters

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma general_window_probability (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P]
    (p : unitInterval)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Bool) => ξ k)
      (bernoulliMeasure true false p) P)
    {b K m : ℕ} (hb : 0 < b) (hmK : m ≤ K) {η a c δ : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (ha : 0 < a) (hc : 0 ≤ c)
    (hac : a ^ 2 + c ^ 2 = 1) (hc2 : 1 / 2 ≤ c ^ 2)
    (hp1 : (p : ℝ) ≤ 1 / 8) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hmean : (((K - m) * b : ℕ) : ℝ) * p ≤ (1 / (4 * (η / b) * a ^ 2)) / 2)
    (hlo : 4 * δ ≤ ((m * b : ℕ) : ℝ) * p)
    (hhi : ((m * b : ℕ) : ℝ) * p ≤ 8 * δ)
    (hpersist : 1 / 4 ≤ (1 - η) ^ (m - 1)) :
    let G := fun (x : Space) (v : Fin b → Bool) => (b : ℝ)⁻¹ • ∑ i,
      ⟪(if v i then pair a c else pair 0 1), x⟫ •
        (if v i then pair a c else pair 0 1)
    let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
      (fun k i => ξ (k * b + i.val)) K
    δ < P.real {ξ | (η / b) ^ 2 * a ^ 2 / 256 ≤
      ((1 - p) * (X ξ 1) ^ 2 + p * (a * X ξ 0 + c * X ξ 1) ^ 2) / 2} := by
  intro G X
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : 0 < η / b := div_pos hη0 hb0
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hgood := iid_good_window_probability p hIID ((K - m) * b) (m * b)
    (by positivity : 0 < 1 / (4 * (η / b) * a ^ 2)) hmean hδ0 hδ1 hlo hhi
  apply hgood.trans_le
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ξ hξ
  obtain ⟨hcount, hhot⟩ := hξ
  obtain ⟨hit, hhit⟩ := one_hot_entries (fun i : Fin (m * b) => ξ ((K - m) * b + i.val)) hhot
  have hwindow : ∀ r < m * b, ξ ((K - m) * b + r) = decide (r = hit.val) := by
    intro r hr
    exact hhit ⟨r, hr⟩
  have hcount' : (η / b) * a ^ 2 *
      (∑ j ∈ Finset.range ((K - m) * b), if ξ j then (1 : ℝ) else 0) ≤ 1 / 4 := by
    apply below_prefix_threshold ht ha2
    rw [Fin.sum_univ_eq_sum_range (fun j => if ξ j then (1 : ℝ) else 0)] at hcount
    exact hcount
  have hpref : η * a ^ 2 / b *
      (∑ j ∈ Finset.range ((K - m) * b), if ξ j then (1 : ℝ) else 0) ≤ 1 / 4 := by
    convert hcount' using 1; ring
  have hrisk := normalized_window_risk hb hit.isLt ξ hη0.le hη1 ha.le hc hac hc2
    p.2.1 hp1 hwindow hpref hpersist
  have hend : K - m + m = K := Nat.sub_add_cancel hmK
  simpa only [Set.mem_ofPred_eq, hend, X, G] using hrisk

lemma calibrated_rare_probability {η δ : ℝ} {b K : ℕ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hb : 0 < b) (hK : 2 ≤ η * (K : ℝ)) :
    ∃ (p : unitInterval) (a c : ℝ), 0 < a ∧ 0 ≤ c ∧
      a ^ 2 + c ^ 2 = 1 ∧
      let P := Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p
      let G := fun (x : Space) (v : Fin b → Bool) => (b : ℝ)⁻¹ • ∑ i,
        ⟪(if v i then pair a c else pair 0 1), x⟫ •
          (if v i then pair a c else pair 0 1)
      let X := fun ξ : ℕ → Bool => MarkovQuadratic.iterate G η (pair 1 0)
        (fun k i => ξ (k * b + i.val)) K
      δ < P.real {ξ | min ((η / b) ^ 2 / 512)
        (1 / (16384 * δ * ((K * b : ℕ) : ℝ))) ≤
          ((1 - p) * (X ξ 1) ^ 2 + p * (a * X ξ 0 + c * X ξ 1) ^ 2) / 2} := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hK0 : 0 < (K : ℝ) := by nlinarith
  have hn0 : 0 < ((K * b : ℕ) : ℝ) := by push_cast; positivity
  let t := η / b
  let A := min (1 / 2) (1 / (64 * t ^ 2 * δ * ((K * b : ℕ) : ℝ)))
  have ht : 0 < t := div_pos hη0 hb0
  obtain ⟨hA0, hA1, hbudget, hrisk⟩ := amplitude_calibration ht hδ0 hn0
  change 0 < A at hA0
  change A ≤ 1 / 2 at hA1
  let a := Real.sqrt A
  let c := Real.sqrt (1 - A)
  have ha : 0 < a := Real.sqrt_pos.mpr hA0
  have ha2 : a ^ 2 = A := Real.sq_sqrt hA0.le
  obtain ⟨_, hc, hac, hc2⟩ := amplitude_square_roots hA0.le hA1
  let m := ⌈1 / (2 * η)⌉₊
  obtain ⟨hm0, hmK, hp0, hp1, hlo, hhi, hpersist⟩ :=
    window_calibration hη0 hη1 hδ0 hδ1 hb hK
  let p : unitInterval := ⟨8 * η * δ / b, hp0.le, by linarith⟩
  have hpt : (p : ℝ) = 8 * t * δ := by dsimp [p, t]; ring
  have hmean0 : (p : ℝ) * ((K * b : ℕ) : ℝ) ≤ (1 / (4 * t * A)) / 2 := by
    rw [hpt]
    exact (prefix_threshold_calibration ht hA0 hbudget).2
  have hmean : (((K - m) * b : ℕ) : ℝ) * p ≤
      (1 / (4 * (η / b) * a ^ 2)) / 2 := by
    rw [ha2]
    calc
      _ ≤ ((K * b : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ p.2.1
        exact_mod_cast Nat.mul_le_mul_right b (Nat.sub_le K m)
      _ = (p : ℝ) * ((K * b : ℕ) : ℝ) := mul_comm _ _
      _ ≤ _ := hmean0
  refine ⟨p, a, c, ha, hc, hac, ?_⟩
  have h := general_window_probability
    (Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p) p
    (StochasticGeneralized.infinitePi_iid _) hb hmK hη0 hη1 ha hc hac hc2
    hp1 hδ0 hδ1 hmean hlo hhi hpersist
  dsimp only at h ⊢
  have he : (η / b) ^ 2 * a ^ 2 / 256 =
      min ((η / b) ^ 2 / 512) (1 / (16384 * δ * ((K * b : ℕ) : ℝ))) := by
    rw [ha2]
    exact hrisk
  simpa only [he] using h

end OracleTemplate.FixedBatchConfidence
