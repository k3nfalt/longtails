import LongTails.Algorithms.HeavyTailedEnergyProbe
import LongTails.Proofs.MatrixGeneralizedRademacher

namespace LongTails.Proofs.HeavyTailedProbeGeometry

open LongTails.Algorithms.HeavyTailedEnergyProbe

lemma initialVector_norm {d : ℕ} (hd : 0 < d) (s : Fin d → Bool) :
    ‖initialVector s‖ = 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hn : ‖OracleTemplate.MatrixGeneralizedZO.signVec s‖ = Real.sqrt (d : ℝ) := by
    rw [← OracleTemplate.MatrixGeneralizedZO.norm_vec_sq s, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  rw [initialVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), hn,
    inv_mul_cancel₀ hs.ne']

lemma normalize_norm {d : ℕ} {fallback : EuclideanSpace ℝ (Fin d)}
    (hf : ‖fallback‖ = 1) (w : EuclideanSpace ℝ (Fin d)) :
    ‖normalize fallback w‖ = 1 := by
  classical
  by_cases hw : w = 0
  · simp [LongTails.Algorithms.HeavyTailedEnergyProbe.normalize, hw, hf]
  · have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp only [LongTails.Algorithms.HeavyTailedEnergyProbe.normalize, ite_eq_right hw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']

lemma step_vector_norm {d : ℕ} (L η : ℝ) (s : State d)
    (hf : ‖s.fallback‖ = 1) (reply : EuclideanSpace ℝ (Fin d)) :
    ‖(step L η s reply).vector‖ = 1 :=
  normalize_norm hf _

lemma step_selected_norm {d : ℕ} (L η : ℝ) (s : State d)
    (hv : ‖s.vector‖ = 1) (hs : ‖s.selected‖ = 1) (reply : EuclideanSpace ℝ (Fin d)) :
    ‖(step L η s reply).selected‖ = 1 := by
  classical
  simp only [step]
  split_ifs <;> assumption

lemma normalize_of_ne_zero {d : ℕ} (fallback : EuclideanSpace ℝ (Fin d))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) :
    LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback w = ‖w‖⁻¹ • w := by
  simp only [LongTails.Algorithms.HeavyTailedEnergyProbe.normalize, ite_eq_right hw]

lemma normalize_unit {d : ℕ} (fallback : EuclideanSpace ℝ (Fin d))
    {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ = 1) :
    LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback w = w := by
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  rw [normalize_of_ne_zero fallback hw0, hw, inv_one, one_smul]

lemma normalize_pos_smul {d : ℕ} (fallback w : EuclideanSpace ℝ (Fin d))
    {c : ℝ} (hc : 0 < c) :
    LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback (c • w) =
      LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback w := by
  by_cases hw : w = 0
  · simp [hw]
  · have hcw : c • w ≠ 0 := smul_ne_zero hc.ne' hw
    rw [normalize_of_ne_zero fallback hcw, normalize_of_ne_zero fallback hw,
      norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    congr 1
    field_simp

noncomputable def linearProduct {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)
  | 0 => ContinuousLinearMap.id ℝ _
  | n + 1 => B n ∘L linearProduct B n

noncomputable def normalizedPath {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (fallback v : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => v
  | n + 1 => LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback
      (B n (normalizedPath B fallback v n))

lemma linearProduct_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : ∀ k, Measurable (fun ω => B ω k)) (n : ℕ) :
    Measurable (fun ω => linearProduct (B ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hB n).mul ih

lemma normalize_measurable {d : ℕ} :
    Measurable (Function.uncurry (LongTails.Algorithms.HeavyTailedEnergyProbe.normalize
      (d := d))) := by
  change Measurable (fun t : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    if t.2 = 0 then t.1 else ‖t.2‖⁻¹ • t.2)
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_fst
    (measurable_snd.norm.inv.smul measurable_snd)

lemma normalizedPath_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : ∀ k, Measurable (fun ω => B ω k))
    (fallback v : Ω → EuclideanSpace ℝ (Fin d)) (hf : Measurable fallback) (hv : Measurable v)
    (n : ℕ) : Measurable (fun ω => normalizedPath (B ω) (fallback ω) (v ω) n) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
      exact normalize_measurable.comp (hf.prodMk
        ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
          (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp ((hB n).prodMk ih)))

lemma normalizedPath_eq_product {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (fallback v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (n : ℕ)
    (hn : linearProduct B n v ≠ 0) :
    normalizedPath B fallback v n = ‖linearProduct B n v‖⁻¹ • linearProduct B n v := by
  induction n with
  | zero => simp [normalizedPath, linearProduct, hv]
  | succ n ih =>
      have hprev : linearProduct B n v ≠ 0 := by
        intro hh
        apply hn
        simp [linearProduct, hh]
      rw [normalizedPath, ih hprev, map_smul,
        normalize_pos_smul fallback _ (inv_pos.mpr (norm_pos_iff.mpr hprev))]
      exact normalize_of_ne_zero fallback hn

lemma linearProduct_zero_persists {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) {n : ℕ} (hn : linearProduct B n v = 0) (k : ℕ) :
    linearProduct B (n + k) v = 0 := by
  induction k with
  | zero => simpa using hn
  | succ k ih => simp [linearProduct, ih]

lemma linearProduct_prefix_ne_zero {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) {n k : ℕ} (hkn : k ≤ n)
    (hn : linearProduct B n v ≠ 0) : linearProduct B k v ≠ 0 := by
  intro hk
  have hh := linearProduct_zero_persists B v hk (n - k)
  rw [Nat.add_sub_of_le hkn] at hh
  exact hn hh

lemma normalizedPath_norm {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {fallback v : EuclideanSpace ℝ (Fin d)} (hf : ‖fallback‖ = 1) (hv : ‖v‖ = 1)
    (n : ℕ) : ‖normalizedPath B fallback v n‖ = 1 := by
  cases n with
  | zero => exact hv
  | succ n => exact normalize_norm hf _

lemma product_log_increment {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (fallback v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (n : ℕ)
    (hn : linearProduct B (n + 1) v ≠ 0) :
    Real.log ‖B n (normalizedPath B fallback v n)‖ =
      Real.log ‖linearProduct B (n + 1) v‖ - Real.log ‖linearProduct B n v‖ := by
  have hprev := linearProduct_prefix_ne_zero B v (Nat.le_succ n) hn
  have hpos := norm_pos_iff.mpr hprev
  change B n (linearProduct B n v) ≠ 0 at hn
  rw [normalizedPath_eq_product B fallback v hv n hprev, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
    Real.log_mul (inv_ne_zero hpos.ne') (norm_ne_zero_iff.mpr hn), Real.log_inv]
  change -Real.log ‖linearProduct B n v‖ + Real.log ‖linearProduct B (n + 1) v‖ = _
  ring

lemma product_log_sum {d : ℕ}
    (B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (fallback v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (n : ℕ)
    (hn : linearProduct B n v ≠ 0) :
    ∑ k ∈ Finset.range n, Real.log ‖B k (normalizedPath B fallback v k)‖ =
      Real.log ‖linearProduct B n v‖ := by
  induction n with
  | zero => simp [linearProduct, hv]
  | succ n ih =>
      rw [Finset.sum_range_succ,
        ih (linearProduct_prefix_ne_zero B v (Nat.le_succ n) hn),
        product_log_increment B fallback v hv n hn]
      ring

end LongTails.Proofs.HeavyTailedProbeGeometry
