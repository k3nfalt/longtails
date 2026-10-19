import LongTails.Proofs.AdamHeavyTailedWindow
import LongTails.Proofs.AdamHeavyTailedTrajectory
import LongTails.Proofs.AdamHeavyTailedDescent
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

namespace LongTails.Proofs.AdamHeavyTailedHistory

lemma weighted_noise_moment {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    (P : Measure Ω) (a : ι → ℝ) (ha : ∀ k, 0 ≤ a k) (e : ι → Ω → EuclideanSpace ℝ κ)
    (he : ∀ k, Measurable (e k)) {p M : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hi : ∀ k, Integrable (fun ω => ∑ i, |e k ω i| ^ p) P)
    (hm : ∀ k, (∫ ω, ∑ i, |e k ω i| ^ p ∂P) ≤ M) :
    Integrable (fun ω => (Real.sqrt (∑ k, a k * ‖e k ω‖ ^ 2)) ^ p) P ∧
    (∫ ω, (Real.sqrt (∑ k, a k * ‖e k ω‖ ^ 2)) ^ p ∂P) ≤ M * ∑ k, (a k) ^ (p / 2) := by
  let F := fun ω => ∑ k, (a k) ^ (p / 2) * (∑ i, |e k ω i| ^ p)
  have hF : Integrable F P := integrable_finsetSum _ (fun k _ => (hi k).const_mul _)
  have hb (ω : Ω) : (Real.sqrt (∑ k, a k * ‖e k ω‖ ^ 2)) ^ p ≤ F ω := by
    have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.weighted_rms_power Finset.univ a
      (fun k => ‖e k ω‖) ha hp hp2
    simp only [abs_of_nonneg (norm_nonneg _)] at hh
    apply hh.trans
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left
      (LongTails.Proofs.AdamHeavyTailedWindow.norm_power_le_coordinate_sum (e k ω) hp hp2)
      (Real.rpow_nonneg (ha k) _)
  have hI : Integrable (fun ω => (Real.sqrt (∑ k, a k * ‖e k ω‖ ^ 2)) ^ p) P := by
    have hmeas : Measurable (fun ω => (Real.sqrt (∑ k, a k * ‖e k ω‖ ^ 2)) ^ p) := by fun_prop
    apply hF.mono' hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
      exact hb ω
  refine ⟨hI, (integral_mono hI hF hb).trans ?_⟩
  change (∫ ω, ∑ k, (a k) ^ (p / 2) * (∑ i, |e k ω i| ^ p) ∂P) ≤ _
  rw [integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ k, (a k) ^ (p / 2) * M := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hm k) (Real.rpow_nonneg (ha k) _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring


lemma first_moment_of_power_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) {p τ : ℝ} (hp : 1 ≤ p) (hτ : 0 ≤ τ)
    (hFp : Integrable (fun ω => (F ω) ^ p) P)
    (hbound : (∫ ω, (F ω) ^ p ∂P) ≤ 2 * τ ^ p) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤ 2 * τ := by
  have hp0 : 0 < p := by linarith
  have hi : Integrable F P := by
    apply ((integrable_const (1 : ℝ)).add hFp).mono' hF.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]
      change F ω ≤ 1 + (F ω) ^ p
      by_cases hsmall : F ω ≤ 1
      · linarith [Real.rpow_nonneg (hF0 ω) p]
      · exact (Real.self_le_rpow_of_one_le (le_of_lt (lt_of_not_ge hsmall)) hp).trans
          (le_add_of_nonneg_left (by norm_num))
  refine ⟨hi, ?_⟩
  have hj := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const hp0.le).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hF0) hi hFp
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ p := Real.self_le_rpow_of_one_le (by norm_num) hp
  have hh : (∫ ω, F ω ∂P) ^ p ≤ (2 * τ) ^ p := by
    apply hj.trans (hbound.trans _)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hτ]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hτ _)
  exact (Real.rpow_le_rpow_iff (integral_nonneg hF0) (by positivity) hp0).mp hh


lemma forgetting_noise_weights {ρ p : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (N : ℕ) :
    (∑ k ∈ Finset.range N, (ρ * (1 - ρ) ^ (k + 1)) ^ (p / 2)) ≤ 2 * ρ ^ (p / 2) / ρ := by
  let r := (1 - ρ) ^ (p / 2)
  have hb : 0 ≤ 1 - ρ := (sub_pos.mpr hρ1).le
  have hr : 0 ≤ r := Real.rpow_nonneg hb _
  have hgap : ρ / 2 ≤ 1 - r := LongTails.Proofs.AdamHeavyTailedAlgebra.forgetting_power_gap hρ.le hρ1.le hp hp2
  have hr1 : r < 1 := by linarith
  have hgeo : (∑ k ∈ Finset.range N, r ^ k) ≤ (1 - r)⁻¹ :=
    sum_le_hasSum (Finset.range N) (fun k _ => pow_nonneg hr _) (hasSum_geometric_of_lt_one hr hr1)
  have he (k : ℕ) : (ρ * (1 - ρ) ^ (k + 1)) ^ (p / 2) = ρ ^ (p / 2) * r ^ (k + 1) := by
    rw [Real.mul_rpow hρ.le (pow_nonneg hb _), ← Real.rpow_pow_comm hb]
  calc
    _ = ρ ^ (p / 2) * ∑ k ∈ Finset.range N, r ^ (k + 1) := by simp_rw [he]; rw [Finset.mul_sum]
    _ ≤ ρ ^ (p / 2) * ∑ k ∈ Finset.range N, r ^ k := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hρ.le _)
      apply Finset.sum_le_sum
      intro k _
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr _) hr1.le
    _ ≤ ρ ^ (p / 2) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg hρ.le _)
    _ ≤ _ := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ (sub_pos.mpr hr1)).2
      have hh := mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hρ.le (p / 2))
      apply (mul_le_mul_iff_of_pos_right hρ).mp
      field_simp
      nlinarith


lemma noise_history_expected {κ Ω : Type*} [Fintype κ] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (e : Fin N → Ω → EuclideanSpace ℝ κ)
    (he : ∀ k, Measurable (e k)) {p M ρ τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ) (hM : 0 ≤ M)
    (hi : ∀ k, Integrable (fun ω => ∑ i, |e k ω i| ^ p) P)
    (hm : ∀ k, (∫ ω, ∑ i, |e k ω i| ^ p ∂P) ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ) :
    Integrable (fun ω => Real.sqrt (∑ k, (ρ * (1 - ρ) ^ (k.val + 1)) * ‖e k ω‖ ^ 2)) P ∧
    (∫ ω, Real.sqrt (∑ k, (ρ * (1 - ρ) ^ (k.val + 1)) * ‖e k ω‖ ^ 2) ∂P) ≤ 2 * τ := by
  have hb : 0 ≤ 1 - ρ := (sub_pos.mpr hρ1).le
  have hpower := weighted_noise_moment P (fun k : Fin N => ρ * (1 - ρ) ^ (k.val + 1))
    (fun k => mul_nonneg hρ.le (pow_nonneg hb _)) e he (by linarith) hp2 hi hm
  have hsqrt : (Real.sqrt ρ) ^ p = ρ ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hρ.le]
    congr 1
    ring
  have hscale : M * ρ ^ (p / 2) ≤ ρ * τ ^ p := by
    have hh := hnoise
    rw [Real.div_rpow (Real.sqrt_nonneg _) hτ.le, hsqrt, ← mul_div_assoc] at hh
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hτ p)).mp hh
  have hw : (∑ k : Fin N, (ρ * (1 - ρ) ^ (k.val + 1)) ^ (p / 2)) ≤ 2 * ρ ^ (p / 2) / ρ := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (ρ * (1 - ρ) ^ (k + 1)) ^ (p / 2))]
    exact forgetting_noise_weights hρ hρ1 hp hp2 N
  have hbound : (∫ ω, (Real.sqrt (∑ k : Fin N, (ρ * (1 - ρ) ^ (k.val + 1)) * ‖e k ω‖ ^ 2)) ^ p ∂P) ≤ 2 * τ ^ p := by
    apply hpower.2.trans
    calc
      _ ≤ M * (2 * ρ ^ (p / 2) / ρ) := mul_le_mul_of_nonneg_left hw hM
      _ = 2 * (M * ρ ^ (p / 2)) / ρ := by ring
      _ ≤ 2 * (ρ * τ ^ p) / ρ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by norm_num)) hρ.le
      _ = _ := by field_simp
  exact first_moment_of_power_bound P (by fun_prop) (fun _ => Real.sqrt_nonneg _) hp hτ.le hpower.1 hbound


lemma trajectory_noise_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) {p M : ℝ}
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (t : ℕ) :
    Integrable (fun ξ => ∑ i, |(g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 (ξ t) -
      grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) i| ^ p) (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, ∑ i, |(g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 (ξ t) -
      grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) i| ^ p
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ M := by
  let F := fun s : OracleTemplate.Adam.Point d × OracleTemplate.Adam.Point d × OracleTemplate.Adam.Point d =>
    fun ω => ∑ i, |OracleTemplate.Adam.stateError g grad s ω i| ^ p
  have hF : Measurable (Function.uncurry F) := by
    apply Finset.measurable_sum
    intro i _
    exact (continuous_abs.measurable.comp ((measurable_pi_apply i).comp
      (OracleTemplate.Adam.measurable_stateError hg hgrad))).pow measurable_const
  have hh := AdamHeavyTailedProcess.stateAt_sample_integrable_bound P
    (OracleTemplate.Adam.measurable_stateTransition hg q ρ η τ) hF
    (fun s ω => Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    (fun s => hm s.1) (fun s => hmass s.1) (x0, 0, 0) ω0 t
  simpa only [F, OracleTemplate.Adam.stateAt_initial, OracleTemplate.Adam.stateError] using hh


noncomputable def weightedVector {ι κ : Type*} (a : ι → ℝ) (z : ι → EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) := WithLp.toLp 2 fun ik => Real.sqrt (a ik.1) * z ik.1 ik.2

lemma weightedVector_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (z : ι → EuclideanSpace ℝ κ) :
    ‖weightedVector a z‖ ^ 2 = ∑ i, a i * ‖z i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [weightedVector, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (ha i)]

lemma weightedVector_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (z : ι → EuclideanSpace ℝ κ) :
    ‖weightedVector a z‖ = Real.sqrt (∑ i, a i * ‖z i‖ ^ 2) := by
  rw [← weightedVector_norm_sq a ha z, Real.sqrt_sq (norm_nonneg _)]

lemma weighted_vector_minkowski {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (g h : ι → EuclideanSpace ℝ κ) :
    Real.sqrt (∑ i, a i * ‖g i‖ ^ 2) ≤ Real.sqrt (∑ i, a i * ‖h i‖ ^ 2) +
      Real.sqrt (∑ i, a i * ‖g i - h i‖ ^ 2) := by
  have he : weightedVector a g = weightedVector a h + weightedVector a (fun i => g i - h i) := by
    ext ik
    simp only [weightedVector, PiLp.add_apply, PiLp.sub_apply]
    ring
  have hh := norm_add_le (weightedVector a h) (weightedVector a (fun i => g i - h i))
  rw [← he] at hh
  simpa only [weightedVector_norm a ha] using hh

lemma weighted_vector_mean_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hmass : (∑ i, a i) ≤ 1)
    (g : ι → EuclideanSpace ℝ κ) (μ : EuclideanSpace ℝ κ) :
    Real.sqrt (∑ i, a i * ‖g i‖ ^ 2) ≤ ‖μ‖ + Real.sqrt (∑ i, a i * ‖g i - μ‖ ^ 2) := by
  have hh := weighted_vector_minkowski a ha g (fun _ => μ)
  have hc : Real.sqrt (∑ i, a i * ‖μ‖ ^ 2) ≤ ‖μ‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨norm_nonneg _, ?_⟩
    rw [← Finset.sum_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass (sq_nonneg ‖μ‖)
  exact hh.trans (add_le_add hc le_rfl)


noncomputable def trajectoryNoiseHistory {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  Real.sqrt (∑ k : Fin T, (ρ * (1 - ρ) ^ (k.val + 1)) *
    ‖g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (T - 1 - k.val)).1 (ξ (T - 1 - k.val)) -
      grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (T - 1 - k.val)).1‖ ^ 2)

lemma trajectoryNoiseHistory_expected {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) {p M : ℝ}
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    (q η : ℝ) {ρ τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (T : ℕ) :
    Integrable (fun ξ => trajectoryNoiseHistory g grad q ρ η τ x0 ξ T) (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, trajectoryNoiseHistory g grad q ρ η τ x0 ξ T ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 2 * τ := by
  let e := fun k : Fin T => fun ξ : ℕ → Ω =>
    g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (T - 1 - k.val)).1 (ξ (T - 1 - k.val)) -
      grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (T - 1 - k.val)).1
  have he (k : Fin T) : Measurable (e k) := by
    have hx := (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 (T - 1 - k.val)).fst
    exact (hg.comp (hx.prodMk (measurable_pi_apply _))).sub (hgrad.comp hx)
  have hmom (k : Fin T) := trajectory_noise_moment P hg hgrad hm hmass q ρ η τ x0 ω0 (T - 1 - k.val)
  exact noise_history_expected (Measure.infinitePi (fun _ : ℕ => P)) e he hp hp2 hρ hρ1 hτ hM
    (fun k => (hmom k).1) (fun k => (hmom k).2) hnoise


lemma weighted_coordinate_envelope {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (g μ : ι → EuclideanSpace ℝ κ) (k : κ) :
    Real.sqrt (∑ i, a i * (g i k) ^ 2) ≤
      Real.sqrt (∑ i, a i * ‖μ i‖ ^ 2) + Real.sqrt (∑ i, a i * ‖g i - μ i‖ ^ 2) := by
  apply le_trans _ (weighted_vector_minkowski a ha g μ)
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (ha i)
  have hh := PiLp.norm_apply_le (g i) k
  simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2

lemma trajectory_signal_variation_sum {d : ℕ} {Ω : Type*}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (q η τ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), ρ * (1 - ρ) ^ k *
      ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 -
        grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k)).1‖ ^ 2) ≤
      2 * (L * |η| / ρ) ^ 2 *
        ∑ t ∈ Finset.range T, ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 := by
  let E := fun s k => ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (s + k)).1 -
    grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ s).1‖ ^ 2
  let u := fun t => ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖
  have hh := AdamHeavyTailedAlgebra.weighted_history_overlap (fun k => ρ * (1 - ρ) ^ k)
    (fun k => mul_nonneg hρ.le (pow_nonneg (sub_nonneg.mpr hρ1) k)) u E
    (sq_nonneg (L * |η|)) (fun s k => by
      have hv := OracleTemplate.Adam.gradient_window_variation hL hlip g q ρ η τ x0 ξ s k
      have hs := pow_le_pow_left₀ (norm_nonneg _) hv 2
      simpa only [mul_pow] using hs) T
  have he : (∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), ρ * (1 - ρ) ^ k *
      ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 -
        grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k)).1‖ ^ 2) =
      ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), ρ * (1 - ρ) ^ k * E (t - k) k := by
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [E]
    rw [Nat.sub_add_cancel (by have := Finset.mem_range.mp hk; omega)]
  rw [he]
  calc
    _ ≤ _ := hh
    _ ≤ (L * |η|) ^ 2 * (2 / ρ ^ 2) * ∑ t ∈ Finset.range T, (u t) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (AdamHeavyTailedAlgebra.forgetting_lag_square_bound hρ hρ1 T) (sq_nonneg _))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by dsimp [u]; ring

noncomputable def trajectorySignalHistory {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) : ℝ :=
  Real.sqrt (∑ k : Fin (t + 1), ρ * (1 - ρ) ^ k.val *
    ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k.val)).1‖ ^ 2)

noncomputable def trajectorySignalVariation {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) : ℝ :=
  Real.sqrt (∑ k : Fin (t + 1), ρ * (1 - ρ) ^ k.val *
    ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k.val)).1 -
      grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ ^ 2)

lemma trajectorySignalHistory_le {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q η τ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) :
    trajectorySignalHistory g grad q ρ η τ x0 ξ t ≤
      ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ +
        trajectorySignalVariation g grad q ρ η τ x0 ξ t := by
  apply weighted_vector_mean_bound
    (fun k : Fin (t + 1) => ρ * (1 - ρ) ^ k.val)
    (fun k => mul_nonneg hρ.le (pow_nonneg (sub_nonneg.mpr hρ1) _))
  simpa only [Fin.sum_univ_eq_sum_range (fun k => ρ * (1 - ρ) ^ k)] using
    AdamHeavyTailedAlgebra.forgetting_mass_bound hρ hρ1 (t + 1)

lemma trajectory_secondMoment_reverse {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2 i =
      ∑ k : Fin t, ρ * (1 - ρ) ^ k.val *
        (g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - 1 - k.val)).1 (ξ (t - 1 - k.val)) i) ^ 2 := by
  have hh := OracleTemplate.Adam.secondMoment_window g q ρ η τ x0 ξ 0 t i
  simp only [OracleTemplate.Adam.trajectory, PiLp.zero_apply, mul_zero, zero_add] at hh
  rw [hh, Fin.sum_univ_eq_sum_range (fun k => ρ * (1 - ρ) ^ k *
    (g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - 1 - k)).1 (ξ (t - 1 - k)) i) ^ 2), Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show t - 1 - (t - 1 - k) = k by have := Finset.mem_range.mp hk; omega]
  ring

lemma trajectory_signal_denominator_le {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q η τ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    Real.sqrt ((1 - ρ) * (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2 i +
      ρ * (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 i) ^ 2) + τ ≤
      τ + trajectorySignalHistory g grad q ρ η τ x0 ξ t +
        trajectoryNoiseHistory g grad q ρ η τ x0 ξ t := by
  let a := fun k : Fin (t + 1) => ρ * (1 - ρ) ^ k.val
  let μ := fun k : Fin (t + 1) => grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k.val)).1
  let G := fun k : Fin (t + 1) => if k.val = 0 then μ k else
    g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k.val)).1 (ξ (t - k.val))
  have hc : (∑ k, a k * (G k i) ^ 2) =
      (1 - ρ) * (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2 i +
        ρ * (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 i) ^ 2 := by
    rw [Fin.sum_univ_succ, trajectory_secondMoment_reverse, Finset.mul_sum]
    simp only [a, G, μ, Fin.val_zero, Nat.sub_zero, ite_true, pow_zero, mul_one,
      Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show t - (k.val + 1) = t - 1 - k.val by omega, pow_succ]
    ring
  have hn : (∑ k, a k * ‖G k - μ k‖ ^ 2) =
      ∑ k : Fin t, ρ * (1 - ρ) ^ (k.val + 1) *
        ‖g (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - 1 - k.val)).1 (ξ (t - 1 - k.val)) -
          grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - 1 - k.val)).1‖ ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp only [a, G, μ, Fin.val_zero, Nat.sub_zero, ite_true, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add, Fin.val_succ,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    apply Finset.sum_congr rfl
    intro k _
    rw [show t - (k.val + 1) = t - 1 - k.val by omega]
  have hh := weighted_coordinate_envelope a
    (fun k => mul_nonneg hρ (pow_nonneg (sub_nonneg.mpr hρ1) _)) G μ i
  rw [hc, hn] at hh
  have he : Real.sqrt (∑ k, a k * ‖μ k‖ ^ 2) = trajectorySignalHistory g grad q ρ η τ x0 ξ t := rfl
  rw [he] at hh
  change _ ≤ τ + trajectorySignalHistory g grad q ρ η τ x0 ξ t + Real.sqrt _
  linarith

lemma integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω)
    (hF2 : Integrable (fun ω => (F ω) ^ 2) P) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ^ 2 ≤ ∫ ω, (F ω) ^ 2 ∂P := by
  have hi : Integrable F P := by
    apply ((integrable_const (1 : ℝ)).add hF2).mono' hF.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]
      change F ω ≤ 1 + (F ω) ^ 2
      nlinarith [sq_nonneg (F ω - 1)]
  refine ⟨hi, ?_⟩
  have hj := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 2)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hF0) hi (by simpa only [Function.comp_def, Real.rpow_two] using hF2)
  simpa only [Real.rpow_two] using hj

lemma finite_integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ)
    (hF : ∀ t, Measurable (F t)) (hF0 : ∀ t ω, 0 ≤ F t ω)
    (hF2 : ∀ t, Integrable (fun ω => (F t ω) ^ 2) P) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ω, F t ω ∂P) ^ 2 ≤
      (T : ℝ) * ∑ t ∈ Finset.range T, ∫ ω, (F t ω) ^ 2 ∂P := by
  have hh : (∑ t ∈ Finset.range T, ∫ ω, F t ω ∂P) ^ 2 ≤
      (T : ℝ) * ∑ t ∈ Finset.range T, (∫ ω, F t ω ∂P) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T)
      (fun _ => (1 : ℝ)) (fun t => ∫ ω, F t ω ∂P)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun t _ => (integral_square_le P (hF t) (hF0 t) (hF2 t)).2) (Nat.cast_nonneg T))

lemma measurable_velocity {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (q ρ η τ : ℝ)
    (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Measurable (fun ξ => OracleTemplate.Adam.velocity g q ρ η τ x0 ξ t) := by
  exact (OracleTemplate.Adam.measurable_direction τ).comp
    ((OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 t).snd.fst.prodMk
      (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 t).snd.snd)

lemma integrable_velocity_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) {q ρ η τ : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Integrable (fun ξ => ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ t‖ ^ 2) P := by
  apply Integrable.of_bound ((measurable_velocity hg q ρ η τ x0 t).norm.pow_const 2).aestronglyMeasurable
    ((((d : ℝ) + 1) * ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ)))) ^ 2)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (OracleTemplate.Adam.velocity_norm_bound g hq hq1 hρ hρ1 hτ hstable x0 ξ t) 2

lemma trajectorySignalVariation_square {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q η τ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) :
    (trajectorySignalVariation g grad q ρ η τ x0 ξ t) ^ 2 =
      ∑ k ∈ Finset.range (t + 1), ρ * (1 - ρ) ^ k *
        ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1 -
          grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k)).1‖ ^ 2 := by
  unfold trajectorySignalVariation
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => mul_nonneg
    (mul_nonneg hρ (pow_nonneg (sub_nonneg.mpr hρ1) _)) (sq_nonneg _)), Fin.sum_univ_eq_sum_range (fun k => ρ * (1 - ρ) ^ k *
      ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ (t - k)).1 -
        grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_sub_rev]

lemma trajectorySignalVariation_square_sum {d : ℕ} {Ω : Type*}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (q η τ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, (trajectorySignalVariation g grad q ρ η τ x0 ξ t) ^ 2) ≤
      2 * (L * |η| / ρ) ^ 2 *
        ∑ t ∈ Finset.range T, ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 := by
  simp_rw [trajectorySignalVariation_square g grad q η τ hρ.le hρ1]
  exact trajectory_signal_variation_sum hL hlip g q η τ hρ hρ1 x0 ξ T

lemma measurable_trajectorySignalVariation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Measurable (fun ξ => trajectorySignalVariation g grad q ρ η τ x0 ξ t) := by
  apply Real.continuous_sqrt.measurable.comp
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul (((hgrad.comp
    (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 (t - k.val)).fst).sub
    (hgrad.comp (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 t).fst)).norm.pow_const 2)

lemma integrable_trajectorySignalVariation_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g))
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Integrable (fun ξ => (trajectorySignalVariation g grad q ρ η τ x0 ξ t) ^ 2) P := by
  have hi := (integrable_finsetSum (Finset.range (t + 1))
    (fun s _ => integrable_velocity_square (P := P) (η := η) hg hq hq1 hρ hρ1 hτ hstable x0 (s + 1))).const_mul
      (2 * (L * |η| / ρ) ^ 2)
  apply hi.mono' ((measurable_trajectorySignalVariation hg
    (OracleTemplate.Adam.measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 t).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply le_trans _ (trajectorySignalVariation_square_sum hL hlip g q η τ hρ hρ1.le x0 ξ (t + 1))
    exact Finset.single_le_sum (fun s _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self t))

lemma trajectorySignalVariation_integral_square_sum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g))
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : OracleTemplate.Adam.Point d) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ξ, trajectorySignalVariation g grad q ρ η τ x0 ξ t ∂P) ^ 2 ≤
      2 * (L * |η| / ρ) ^ 2 * (T : ℝ) *
        ∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 ∂P := by
  have hm := fun t => measurable_trajectorySignalVariation hg
    (OracleTemplate.Adam.measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 t
  have hi := fun t => integrable_trajectorySignalVariation_square (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 t
  have hu := fun t => integrable_velocity_square (P := P) (η := η) hg hq hq1 hρ hρ1 hτ hstable x0 (t + 1)
  have hcs := finite_integral_square_le P
    (fun t ξ => trajectorySignalVariation g grad q ρ η τ x0 ξ t) hm
    (fun t ξ => Real.sqrt_nonneg _) hi T
  have hb := integral_mono (integrable_finsetSum (Finset.range T) (fun t _ => hi t))
    ((integrable_finsetSum (Finset.range T) (fun t _ => hu t)).const_mul (2 * (L * |η| / ρ) ^ 2))
    (fun ξ => trajectorySignalVariation_square_sum hL hlip g q η τ hρ hρ1.le x0 ξ T)
  rw [integral_finsetSum _ (fun t _ => hi t), integral_const_mul,
    integral_finsetSum _ (fun t _ => hu t)] at hb
  have hh := hcs.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg T))
  convert hh using 1
  ring

lemma integral_nonnegative_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F G : Ω → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hF0 : ∀ ω, 0 ≤ F ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hiF : Integrable (fun ω => (F ω) ^ 2) P) (hiG : Integrable (fun ω => (G ω) ^ 2) P) :
    (∫ ω, F ω * G ω ∂P) ≤ Real.sqrt (∫ ω, (F ω) ^ 2 ∂P) * Real.sqrt (∫ ω, (G ω) ^ 2 ∂P) := by
  have hf : MemLp F (ENNReal.ofReal (2 : ℝ)) P := by
    simpa using (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hiF
  have hg : MemLp G (ENNReal.ofReal (2 : ℝ)) P := by
    simpa using (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hiG
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0) hf hg
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

lemma finite_integral_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F G : ℕ → Ω → ℝ)
    (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t))
    (hF0 : ∀ t ω, 0 ≤ F t ω) (hG0 : ∀ t ω, 0 ≤ G t ω)
    (hiF : ∀ t, Integrable (fun ω => (F t ω) ^ 2) P)
    (hiG : ∀ t, Integrable (fun ω => (G t ω) ^ 2) P) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ω, F t ω * G t ω ∂P) ≤
      Real.sqrt (∑ t ∈ Finset.range T, ∫ ω, (F t ω) ^ 2 ∂P) *
        Real.sqrt (∑ t ∈ Finset.range T, ∫ ω, (G t ω) ^ 2 ∂P) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range T)
    (fun t => Real.sqrt (∫ ω, (F t ω) ^ 2 ∂P))
    (fun t => Real.sqrt (∫ ω, (G t ω) ^ 2 ∂P))
  simp only [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hh
  exact (Finset.sum_le_sum fun t _ => integral_nonnegative_cauchy P (hF t) (hG t)
    (hF0 t) (hG0 t) (hiF t) (hiG t)).trans hh

lemma signalEnergy_controls_norm {d : ℕ} {ρ τ B : ℝ} (hτ : 0 < τ)
    (v μ : OracleTemplate.Adam.Point d)
    (hB : ∀ i, Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ ≤ B) :
    ‖μ‖ ^ 2 ≤ OracleTemplate.Adam.signalEnergy ρ τ v μ * B := by
  rw [PiLp.norm_sq_eq_of_L2, OracleTemplate.Adam.signalEnergy, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  have hD : 0 < Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ := by positivity
  calc
    _ = ((μ i) ^ 2 / (Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ)) *
        (Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB i) (div_nonneg (sq_nonneg _) hD.le)

lemma trajectory_velocity_energy_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) {q ρ η τ : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : OracleTemplate.Adam.Point d) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 ∂P) ≤
      ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 *
        ∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.instantDirection g q ρ η τ x0 ξ t‖ ^ 2 ∂P := by
  have hu := fun t => integrable_velocity_square (P := P) (η := η) hg hq hq1 hρ hρ1 hτ hstable x0 (t + 1)
  have hr := fun t => OracleTemplate.Adam.integrable_instantDirection_square (P := P) hg q η hρ hρ1.le hτ x0 t
  have hh := integral_mono (integrable_finsetSum (Finset.range T) (fun t _ => hu t))
    ((integrable_finsetSum (Finset.range T) (fun t _ => hr t)).const_mul
      (((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2))
    (fun ξ => OracleTemplate.Adam.velocity_energy g hq hq1 hρ.le hρ1 hτ hstable x0 ξ T)
  rw [integral_finsetSum _ (fun t _ => hu t), integral_const_mul,
    integral_finsetSum _ (fun t _ => hr t)] at hh
  exact hh

noncomputable def trajectoryDenominatorBound {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) : ℝ :=
  τ + ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ +
    trajectorySignalVariation g grad q ρ η τ x0 ξ t + trajectoryNoiseHistory g grad q ρ η τ x0 ξ t

lemma trajectoryDenominatorBound_nonneg {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q ρ η : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) :
    0 ≤ trajectoryDenominatorBound g grad q ρ η τ x0 ξ t := by
  unfold trajectoryDenominatorBound trajectorySignalVariation trajectoryNoiseHistory
  positivity

lemma trajectoryDenominatorBound_controls_norm {d : ℕ} {Ω : Type*}
    (g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d)
    (grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ)
    (x0 : OracleTemplate.Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) :
    ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ ^ 2 ≤
      OracleTemplate.Adam.signalEnergy ρ τ (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
        (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) *
          trajectoryDenominatorBound g grad q ρ η τ x0 ξ t := by
  apply signalEnergy_controls_norm hτ
  intro i
  have hd := trajectory_signal_denominator_le g grad q η τ hρ.le hρ1 x0 ξ t i
  have hs := trajectorySignalHistory_le g grad q η τ hρ hρ1 x0 ξ t
  unfold trajectoryDenominatorBound
  linarith

lemma measurable_trajectoryNoiseHistory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Measurable (fun ξ => trajectoryNoiseHistory g grad q ρ η τ x0 ξ t) := by
  apply Real.continuous_sqrt.measurable.comp
  apply Finset.measurable_sum
  intro k _
  have hx := (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 (t - 1 - k.val)).fst
  exact measurable_const.mul
    (((hg.comp (hx.prodMk (measurable_pi_apply _))).sub (hgrad.comp hx)).norm.pow_const 2)

lemma measurable_trajectoryDenominatorBound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : OracleTemplate.Adam.Point d) (t : ℕ) :
    Measurable (fun ξ => trajectoryDenominatorBound g grad q ρ η τ x0 ξ t) := by
  exact ((measurable_const.add ((hgrad.comp
    (OracleTemplate.Adam.measurable_trajectory hg q ρ η τ x0 t).fst).norm)).add
    (measurable_trajectorySignalVariation hg hgrad q ρ η τ x0 t)).add
      (measurable_trajectoryNoiseHistory hg hgrad q ρ η τ x0 t)

lemma trajectoryDenominatorBound_expected {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g))
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (t : ℕ) :
    Integrable (fun ξ => trajectoryDenominatorBound g grad q ρ η τ x0 ξ t)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, trajectoryDenominatorBound g grad q ρ η τ x0 ξ t ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      3 * τ + (∫ ξ, ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ ∂Measure.infinitePi (fun _ : ℕ => P)) +
        ∫ ξ, trajectorySignalVariation g grad q ρ η τ x0 ξ t ∂Measure.infinitePi (fun _ : ℕ => P) := by
  have hgrad := OracleTemplate.Adam.measurable_gradient_of_lipschitz hL hlip
  have hiG := OracleTemplate.Adam.integrable_trajectory_gradient_norm
    (P := Measure.infinitePi (fun _ : ℕ => P)) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 t
  have hiA := (integral_square_le (Measure.infinitePi (fun _ : ℕ => P))
    (measurable_trajectorySignalVariation hg hgrad q ρ η τ x0 t)
    (fun ξ => Real.sqrt_nonneg _) (integrable_trajectorySignalVariation_square
      (P := Measure.infinitePi (fun _ : ℕ => P)) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 t)).1
  have hn := trajectoryNoiseHistory_expected P hg hgrad hm hmass q η hp hp2 hρ hρ1 hτ hM hnoise x0 ω0 t
  have hiGA : Integrable (fun ξ => τ + ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖)
      (Measure.infinitePi (fun _ : ℕ => P)) := by
    simpa only [Pi.add_def] using (integrable_const τ).add hiG
  have hiGAA : Integrable (fun ξ => τ + ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖ +
      trajectorySignalVariation g grad q ρ η τ x0 ξ t) (Measure.infinitePi (fun _ : ℕ => P)) := by
    simpa only [Pi.add_def] using hiGA.add hiA
  refine ⟨hiGAA.add hn.1, ?_⟩
  unfold trajectoryDenominatorBound
  rw [integral_add hiGAA hn.1, integral_add hiGA hiA, integral_add (integrable_const τ) hiG]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith [hn.2]

lemma integral_factor_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {G S B : Ω → ℝ}
    (hS0 : ∀ ω, 0 ≤ S ω) (hB0 : ∀ ω, 0 ≤ B ω)
    (hS : Measurable S) (hB : Measurable B)
    (hiG : Integrable G P) (hiS : Integrable S P) (hiB : Integrable B P)
    (hbound : ∀ ω, (G ω) ^ 2 ≤ S ω * B ω) :
    (∫ ω, G ω ∂P) ≤ Real.sqrt (∫ ω, S ω ∂P) * Real.sqrt (∫ ω, B ω ∂P) := by
  have hs := Real.continuous_sqrt.measurable.comp hS
  have hb := Real.continuous_sqrt.measurable.comp hB
  have hiS2 : Integrable (fun ω => (Real.sqrt (S ω)) ^ 2) P := by
    simpa only [Real.sq_sqrt (hS0 _)] using hiS
  have hiB2 : Integrable (fun ω => (Real.sqrt (B ω)) ^ 2) P := by
    simpa only [Real.sq_sqrt (hB0 _)] using hiB
  have his := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2 hiS2
  have hib := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).2 hiB2
  have hi : Integrable (fun ω => Real.sqrt (S ω) * Real.sqrt (B ω)) P := his.integrable_mul hib
  have hpoint (ω : Ω) : G ω ≤ Real.sqrt (S ω) * Real.sqrt (B ω) := by
    have he : (Real.sqrt (S ω) * Real.sqrt (B ω)) ^ 2 = S ω * B ω := by
      rw [mul_pow, Real.sq_sqrt (hS0 ω), Real.sq_sqrt (hB0 ω)]
    nlinarith [hbound ω, mul_nonneg (Real.sqrt_nonneg (S ω)) (Real.sqrt_nonneg (B ω))]
  have hh := integral_nonnegative_cauchy P hs hb (fun ω => Real.sqrt_nonneg (S ω))
    (fun ω => Real.sqrt_nonneg (B ω)) hiS2 hiB2
  simp only [Function.comp_def, Real.sq_sqrt (hS0 _), Real.sq_sqrt (hB0 _)] at hh
  exact (integral_mono hiG hi hpoint).trans hh

lemma finite_integral_factor_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G S B : ℕ → Ω → ℝ)
    (hG0 : ∀ t ω, 0 ≤ G t ω) (hS0 : ∀ t ω, 0 ≤ S t ω) (hB0 : ∀ t ω, 0 ≤ B t ω)
    (hS : ∀ t, Measurable (S t)) (hB : ∀ t, Measurable (B t))
    (hiG : ∀ t, Integrable (G t) P) (hiS : ∀ t, Integrable (S t) P) (hiB : ∀ t, Integrable (B t) P)
    (hbound : ∀ t ω, (G t ω) ^ 2 ≤ S t ω * B t ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ω, G t ω ∂P) ^ 2 ≤
      (∑ t ∈ Finset.range T, ∫ ω, S t ω ∂P) * (∑ t ∈ Finset.range T, ∫ ω, B t ω ∂P) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range T)
    (fun t => Real.sqrt (∫ ω, S t ω ∂P)) (fun t => Real.sqrt (∫ ω, B t ω ∂P))
  simp only [Real.sq_sqrt (integral_nonneg (hS0 _)), Real.sq_sqrt (integral_nonneg (hB0 _))] at hh
  have hs := (Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) =>
    integral_factor_bound P (hS0 t) (hB0 t) (hS t) (hB t) (hiG t) (hiS t) (hiB t) (hbound t)).trans hh
  have hn : 0 ≤ ∑ t ∈ Finset.range T, ∫ ω, G t ω ∂P :=
    Finset.sum_nonneg fun t _ => integral_nonneg (hG0 t)
  have hp := pow_le_pow_left₀ hn hs 2
  simpa only [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun t _ => integral_nonneg (hS0 t)),
    Real.sq_sqrt (Finset.sum_nonneg fun t _ => integral_nonneg (hB0 t))] using hp

lemma trajectory_gradient_sum_sq_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g))
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ξ, ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖
      ∂Measure.infinitePi (fun _ : ℕ => P)) ^ 2 ≤
    (∑ t ∈ Finset.range T, ∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ
      (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
      (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Measure.infinitePi (fun _ : ℕ => P)) *
    (3 * τ * (T : ℝ) + (∑ t ∈ Finset.range T, ∫ ξ, ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖
      ∂Measure.infinitePi (fun _ : ℕ => P)) +
      ∑ t ∈ Finset.range T, ∫ ξ, trajectorySignalVariation g grad q ρ η τ x0 ξ t
        ∂Measure.infinitePi (fun _ : ℕ => P)) := by
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let G := fun t ξ => ‖grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1‖
  let S := fun t ξ => OracleTemplate.Adam.signalEnergy ρ τ
    (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
    (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1)
  let B := fun t ξ => trajectoryDenominatorBound g grad q ρ η τ x0 ξ t
  have hgrad := OracleTemplate.Adam.measurable_gradient_of_lipschitz hL hlip
  have hiB (t : ℕ) := trajectoryDenominatorBound_expected (η := η) P hg hL hlip hp hp2 hM hm hmass
    hq hq1 hρ hρ1 hτ hstable hnoise x0 ω0 t
  have hf := finite_integral_factor_bound Q G S B (fun _ _ => norm_nonneg _)
    (fun _ _ => OracleTemplate.Adam.signalEnergy_nonneg (ρ := ρ) hτ _ _)
    (fun t ξ => trajectoryDenominatorBound_nonneg g grad q ρ η hτ.le x0 ξ t)
    (fun t => OracleTemplate.Adam.measurable_trajectory_signalEnergy hg hgrad q ρ η τ x0 t)
    (fun t => measurable_trajectoryDenominatorBound hg hgrad q ρ η τ x0 t)
    (fun t => OracleTemplate.Adam.integrable_trajectory_gradient_norm (P := Q) (η := η)
      hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 t)
    (fun t => OracleTemplate.Adam.integrable_trajectory_signalEnergy (P := Q) (η := η)
      hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 t)
    (fun t => (hiB t).1)
    (fun t ξ => trajectoryDenominatorBound_controls_norm g grad q η hρ hρ1.le hτ x0 ξ t) T
  have hb := Finset.sum_le_sum (s := Finset.range T) (fun t _ => (hiB t).2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
  have hn : 0 ≤ ∑ t ∈ Finset.range T, ∫ ξ, S t ξ ∂Q :=
    Finset.sum_nonneg fun t _ => integral_nonneg fun ξ => OracleTemplate.Adam.signalEnergy_nonneg (ρ := ρ) hτ _ _
  have hh := hf.trans (mul_le_mul_of_nonneg_left hb hn)
  convert hh using 1
  dsimp [Q, G, S, B]
  ring

lemma trajectory_energy_integral_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hfactor : ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 ≤ 4)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
    32 * ((∑ t ∈ Finset.range T, ∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ
      (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
      (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Measure.infinitePi (fun _ : ℕ => P)) / τ + (T : ℝ)) := by
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := ∑ t ∈ Finset.range T, ∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ
    (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
    (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Q
  let R := ∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.instantDirection g q ρ η τ x0 ξ t‖ ^ 2 ∂Q
  have hn : ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left hnoise (by positivity : 0 ≤ 8 / ρ)
    have he : (8 / ρ) * ρ = 8 := by field_simp
    rw [he] at hh
    nlinarith
  have hr (t : ℕ) := OracleTemplate.Adam.trajectory_instant_energy_integral P hg hgi hL hlip hp hp2 hm hmass
    (η := η) hq hq1 hρ hρ1 hτ hstable x0 ω0 t
  have hr' : R ≤ (2 / τ) * S + 8 * (T : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, ((2 / τ) *
          (∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
            (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Q) + 8) :=
        Finset.sum_le_sum fun t _ => (hr t).trans (add_le_add le_rfl hn)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [S]; ring
  have hR : 0 ≤ R := Finset.sum_nonneg fun t _ => integral_nonneg fun ξ => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun ξ =>
    OracleTemplate.Adam.signalEnergy_nonneg (ρ := ρ) hτ _ _
  have hu := trajectory_velocity_energy_integral (P := Q) (η := η) hg hq hq1 hρ hρ1 hτ hstable x0 T
  have hh := hu.trans (mul_le_mul_of_nonneg_right hfactor hR)
  change _ ≤ 32 * (S / τ + (T : ℝ))
  have he : (2 / τ) * S = 2 * (S / τ) := by ring
  rw [he] at hr'
  nlinarith [div_nonneg hS hτ.le]

lemma integrable_window_square {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (hu : ∀ t, Measurable (u t))
    (hi : ∀ t, Integrable (fun ω => (u t ω) ^ 2) P) (s j : ℕ) :
    Integrable (fun ω => (∑ r ∈ Finset.range j, u (s + r) ω) ^ 2) P := by
  have hmeas := (Finset.measurable_sum (Finset.range j) (fun r _ => hu (s + r))).pow_const 2
  apply ((integrable_finsetSum (Finset.range j) (fun r _ => hi (s + r))).const_mul (j : ℝ)).mono' hmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range j) (fun _ => (1 : ℝ)) (fun r => u (s + r) ω)

lemma window_integral_square_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (hu : ∀ t, Measurable (u t))
    (hi : ∀ t, Integrable (fun ω => (u t ω) ^ 2) P) (T j : ℕ) :
    (∑ s ∈ Finset.range (T - j), ∫ ω, (∑ r ∈ Finset.range j, u (s + r) ω) ^ 2 ∂P) ≤
      (j : ℝ) ^ 2 * ∑ t ∈ Finset.range T, ∫ ω, (u t ω) ^ 2 ∂P := by
  have hw := fun s => integrable_window_square P u hu hi s j
  have hh := integral_mono (integrable_finsetSum (Finset.range (T - j)) (fun s _ => hw s))
    ((integrable_finsetSum (Finset.range T) (fun t _ => hi t)).const_mul ((j : ℝ) ^ 2))
    (fun ω => AdamHeavyTailedAlgebra.window_overlap_square_sum (fun t => u t ω) T j)
  rw [integral_finsetSum _ (fun s _ => hw s), integral_const_mul, integral_finsetSum _ (fun t _ => hi t)] at hh
  exact hh

lemma integral_abs_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A F G : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hA : Measurable A) (hF : Measurable F) (hG : Measurable G)
    (hF0 : ∀ ω, 0 ≤ F ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hiF : Integrable (fun ω => (F ω) ^ 2) P) (hiG : Integrable (fun ω => (G ω) ^ 2) P)
    (hbound : ∀ ω, |A ω| ≤ C * (F ω * G ω)) :
    Integrable A P ∧ (∫ ω, |A ω| ∂P) ≤
      C * (Real.sqrt (∫ ω, (F ω) ^ 2 ∂P) * Real.sqrt (∫ ω, (G ω) ^ 2 ∂P)) := by
  have hf := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hiF
  have hg := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hiG
  have hi : Integrable (fun ω => F ω * G ω) P := hf.integrable_mul hg
  have hia : Integrable A P := (hi.const_mul C).mono' hA.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  refine ⟨hia, ?_⟩
  have hh := integral_mono hia.abs (hi.const_mul C) hbound
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (integral_nonnegative_cauchy P hF hG hF0 hG0 hiF hiG) hC)

lemma finite_integral_abs_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A F G : ℕ → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ t, Measurable (A t)) (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t))
    (hF0 : ∀ t ω, 0 ≤ F t ω) (hG0 : ∀ t ω, 0 ≤ G t ω)
    (hiF : ∀ t, Integrable (fun ω => (F t ω) ^ 2) P)
    (hiG : ∀ t, Integrable (fun ω => (G t ω) ^ 2) P)
    (hbound : ∀ t ω, |A t ω| ≤ C * (F t ω * G t ω)) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ω, |A t ω| ∂P) ≤
      C * (Real.sqrt (∑ t ∈ Finset.range T, ∫ ω, (F t ω) ^ 2 ∂P) *
        Real.sqrt (∑ t ∈ Finset.range T, ∫ ω, (G t ω) ^ 2 ∂P)) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range T)
    (fun t => Real.sqrt (∫ ω, (F t ω) ^ 2 ∂P)) (fun t => Real.sqrt (∫ ω, (G t ω) ^ 2 ∂P))
  simp only [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hh
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun t _ =>
    (integral_abs_product_bound P hC (hA t) (hF t) (hG t) (hF0 t) (hG0 t) (hiF t) (hiG t) (hbound t)).2)
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hh hC)

lemma finite_window_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A F u : ℕ → Ω → ℝ) {C X Y : ℝ} (hC : 0 ≤ C)
    (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (hA : ∀ t, Measurable (A t)) (hF : ∀ t, Measurable (F t)) (hu : ∀ t, Measurable (u t))
    (hF0 : ∀ t ω, 0 ≤ F t ω) (hu0 : ∀ t ω, 0 ≤ u t ω)
    (hiF : ∀ t, Integrable (fun ω => (F t ω) ^ 2) P)
    (hiu : ∀ t, Integrable (fun ω => (u t ω) ^ 2) P)
    (T j : ℕ)
    (hbound : ∀ t ω, |A t ω| ≤ C * (F t ω * ∑ r ∈ Finset.range j, u (t + r) ω))
    (hFX : (∑ t ∈ Finset.range (T - j), ∫ ω, (F t ω) ^ 2 ∂P) ≤ X)
    (huY : (∑ t ∈ Finset.range T, ∫ ω, (u t ω) ^ 2 ∂P) ≤ Y) :
    (∑ t ∈ Finset.range (T - j), ∫ ω, |A t ω| ∂P) ≤
      C * (j : ℝ) * (Real.sqrt X * Real.sqrt Y) := by
  let G := fun t ω => ∑ r ∈ Finset.range j, u (t + r) ω
  have hG : ∀ t, Measurable (G t) := fun t => Finset.measurable_sum _ (fun r _ => hu (t + r))
  have hG0 : ∀ t ω, 0 ≤ G t ω := fun t ω => Finset.sum_nonneg fun r _ => hu0 (t + r) ω
  have hiG := fun t => integrable_window_square P u hu hiu t j
  have hh := finite_integral_abs_product_bound P A F G hC hA hF hG hF0 hG0 hiF hiG hbound (T - j)
  have hg := (window_integral_square_sum P u hu hiu T j).trans
    (mul_le_mul_of_nonneg_left huY (sq_nonneg (j : ℝ)))
  have hroot : Real.sqrt ((j : ℝ) ^ 2 * Y) = (j : ℝ) * Real.sqrt Y := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc
    _ ≤ C * (Real.sqrt (∑ t ∈ Finset.range (T - j), ∫ ω, (F t ω) ^ 2 ∂P) *
        Real.sqrt (∑ t ∈ Finset.range (T - j), ∫ ω, (G t ω) ^ 2 ∂P)) := hh
    _ ≤ C * (Real.sqrt X * Real.sqrt ((j : ℝ) ^ 2 * Y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hFX)
        (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
    _ = _ := by rw [hroot]; ring

open OracleTemplate.Adam in
lemma trajectory_numerator_integral_sum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (T j : ℕ) :
    (∑ s ∈ Finset.range (T - j), ∫ ξ,
      |lagPairing g grad q ρ η τ x0 ξ s j j - lagPairing g grad q ρ η τ x0 ξ s j 0| ∂P) ≤
      (L * |η| / Real.sqrt ((1 - ρ) ^ j)) * (j : ℝ) *
        (Real.sqrt (∑ s ∈ Finset.range T, ∫ ξ, ‖instantDirection g q ρ η τ x0 ξ s‖ ^ 2 ∂P) *
          Real.sqrt (∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂P)) := by
  let A := fun s ξ => lagPairing g grad q ρ η τ x0 ξ s j j - lagPairing g grad q ρ η τ x0 ξ s j 0
  let F := fun s ξ => ‖instantDirection g q ρ η τ x0 ξ s‖
  let u := fun s ξ => ‖velocity g q ρ η τ x0 ξ (s + 1)‖
  have hgrad := measurable_gradient_of_lipschitz hL hlip
  have hA : ∀ s, Measurable (A s) := fun s =>
    (measurable_lagPairing hg hgrad q ρ η τ x0 s j j).sub
      (measurable_lagPairing hg hgrad q ρ η τ x0 s j 0)
  have hF : ∀ s, Measurable (F s) := fun s => by
    have hx := (measurable_trajectory hg q ρ η τ x0 s).fst
    have hv := (measurable_trajectory hg q ρ η τ x0 (s + 1)).snd.snd
    exact ((measurable_direction τ).comp ((hg.comp (hx.prodMk (measurable_pi_apply s))).prodMk hv)).norm
  have hu : ∀ s, Measurable (u s) := fun s => (measurable_velocity hg q ρ η τ x0 (s + 1)).norm
  have hiF : ∀ s, Integrable (fun ξ => (F s ξ) ^ 2) P := fun s =>
    integrable_instantDirection_square hg q η hρ hρ1.le hτ x0 s
  have hiu : ∀ s, Integrable (fun ξ => (u s ξ) ^ 2) P := fun s =>
    integrable_velocity_square hg hq hq1 hρ hρ1 hτ hstable x0 (s + 1)
  have hbound : ∀ s ξ, |A s ξ| ≤ (L * |η| / Real.sqrt ((1 - ρ) ^ j)) *
      (F s ξ * ∑ r ∈ Finset.range j, u (s + r) ξ) := by
    intro s ξ
    have hh := trajectory_numerator_transport hL hlip g q η hρ hρ1 hτ x0 ξ s j
    simpa only [A, lagPairing, Nat.add_zero, F, u, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hh
  apply finite_window_product_bound P A F u (by positivity)
    (Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => sq_nonneg _)
    (Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => sq_nonneg _)
    hA hF hu (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hiF hiu T j hbound
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le T j))
      (fun s _ _ => integral_nonneg fun ξ => sq_nonneg _)
  · exact le_rfl

open OracleTemplate.Adam in
lemma trajectory_denominator_integral_sum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (T j : ℕ) :
    let E := fun s ξ => ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
      (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2
    (∑ s ∈ Finset.range (T - j), ∫ ξ,
      |lagPairing g grad q ρ η τ x0 ξ s j 0 -
        frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))| ∂P) ≤
      (L * |η| * Real.sqrt j / Real.sqrt ((1 - ρ) ^ j)) * (j : ℝ) *
        (Real.sqrt (∑ s ∈ Finset.range (T - j), ∫ ξ, E s ξ ∂P) *
          Real.sqrt (∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂P)) := by
  dsimp only
  let E := fun s ξ => ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
    (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2
  let F := fun s ξ => Real.sqrt (E s ξ)
  let A := fun s ξ => lagPairing g grad q ρ η τ x0 ξ s j 0 -
    frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))
  let u := fun s ξ => ‖velocity g q ρ η τ x0 ξ (s + 1)‖
  have hgrad := measurable_gradient_of_lipschitz hL hlip
  have hE0 : ∀ s ξ, 0 ≤ E s ξ := fun s ξ => Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE : ∀ s, Measurable (E s) := fun s => by
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_coordinate i).comp (hgrad.comp (measurable_trajectory hg q ρ η τ x0 s).fst)).pow_const 2).div
      ((measurable_trajectory_frozenDenominator hg hgrad q ρ η τ x0 s j i).pow_const 2)
  have hA : ∀ s, Measurable (A s) := fun s =>
    (measurable_lagPairing hg hgrad q ρ η τ x0 s j 0).sub
      (measurable_trajectory_frozenPairing hg hgrad q ρ η τ x0 s j)
  have hF : ∀ s, Measurable (F s) := fun s => Real.continuous_sqrt.measurable.comp (hE s)
  have hu : ∀ s, Measurable (u s) := fun s => (measurable_velocity hg q ρ η τ x0 (s + 1)).norm
  have hFsq : ∀ s ξ, (F s ξ) ^ 2 = E s ξ := fun s ξ => Real.sq_sqrt (hE0 s ξ)
  have hiF : ∀ s, Integrable (fun ξ => (F s ξ) ^ 2) P := fun s => by
    simp_rw [hFsq]
    exact integrable_trajectory_frozenEnergy (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j
  have hiu : ∀ s, Integrable (fun ξ => (u s ξ) ^ 2) P := fun s =>
    integrable_velocity_square hg hq hq1 hρ hρ1 hτ hstable x0 (s + 1)
  have hbound : ∀ s ξ, |A s ξ| ≤ (L * |η| * Real.sqrt j / Real.sqrt ((1 - ρ) ^ j)) *
      (F s ξ * ∑ r ∈ Finset.range j, u (s + r) ξ) := by
    intro s ξ
    have hh := trajectory_denominator_pairing_transport hL hlip g q η hρ hρ1 hτ x0 ξ s j
    have he := AdamHeavyTailedAlgebra.sqrt_transport_identity hρ
      (Real.sqrt_pos.mpr (pow_pos (sub_pos.mpr hρ1) j)) (by positivity : (0 : ℝ) ≤ j)
      (by positivity : 0 ≤ L * |η| * ∑ r ∈ Finset.range j, u (s + r) ξ)
      (Z := E s ξ)
    change |A s ξ| ≤ _ at hh
    change _ = _ at he
    rw [he] at hh
    convert hh using 1
    dsimp [F, u]
    ring
  have hh := finite_window_product_bound P A F u (by positivity)
    (Finset.sum_nonneg fun s _ => integral_nonneg (hE0 s))
    (Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => sq_nonneg _)
    hA hF hu (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => norm_nonneg _) hiF hiu T j hbound
    (by simp only [hFsq]; exact le_rfl) le_rfl
  exact hh

lemma integral_transport_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A B F : Ω → ℝ}
    (hiA : Integrable A P) (hiB : Integrable B P) (hiF : Integrable F P) :
    (∫ ω, F ω ∂P) - (∫ ω, |A ω - B ω| ∂P) - (∫ ω, |B ω - F ω| ∂P) ≤
      ∫ ω, A ω ∂P := by
  have hiAB : Integrable (fun ω => |A ω - B ω|) P := (hiA.sub hiB).abs
  have hiBF : Integrable (fun ω => |B ω - F ω|) P := (hiB.sub hiF).abs
  have hh := integral_mono ((hiF.sub hiAB).sub hiBF) hiA (fun ω => by
    have ha := neg_abs_le (A ω - B ω)
    have hb := neg_abs_le (B ω - F ω)
    change F ω - |A ω - B ω| - |B ω - F ω| ≤ A ω
    linarith)
  have hiFAB : Integrable (fun ω => F ω - |A ω - B ω|) P := hiF.sub hiAB
  change (∫ ω, (F ω - |A ω - B ω|) - |B ω - F ω| ∂P) ≤ _ at hh
  rw [integral_sub hiFAB hiBF, integral_sub hiF hiAB] at hh
  exact hh

open OracleTemplate.Adam in
lemma trajectory_frozenEnergy_sum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : Point d) (ω0 : Ω) (T j : ℕ) :
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
      (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
    (∑ s ∈ Finset.range (T - (j + 1)), ∫ ξ, ∑ i,
      (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
        (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) (j + 1) (fun k => ξ (s + k)) i) ^ 2 ∂Q) ≤
      19 * (S / τ + T) / Real.sqrt ((1 - ρ) ^ (j + 1)) := by
  dsimp only
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let E := fun s => ∫ ξ, ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
    (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) (j + 1) (fun k => ξ (s + k)) i) ^ 2 ∂Q
  let S := fun s => ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
    (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
  have hS : ∀ s, 0 ≤ S s := fun s => integral_nonneg fun ξ => signalEnergy_nonneg hτ _ _
  have he := AdamHeavyTailedAlgebra.prefix_affine_sum_bound E S
    (by positivity : 0 ≤ 3 / (τ * Real.sqrt ((1 - ρ) ^ (j + 1))))
    (by positivity : 0 ≤ 16 * ρ) hS
    (fun s => trajectory_frozenEnergy_integral P hg hL hlip hm hmass hq hq1 hρ hρ1 hτ hstable hp hp2 hM hnoise x0 ω0 s j)
    (Nat.sub_le T (j + 1))
  have hc : 0 < Real.sqrt ((1 - ρ) ^ (j + 1)) := Real.sqrt_pos.mpr (pow_pos (sub_pos.mpr hρ1) _)
  have hc1 : Real.sqrt ((1 - ρ) ^ (j + 1)) ≤ 1 := Real.sqrt_le_iff.mpr
    ⟨by norm_num, by simpa using pow_le_one₀ (sub_pos.mpr hρ1).le (by linarith : 1 - ρ ≤ 1) (n := j + 1)⟩
  exact he.trans (AdamHeavyTailedAlgebra.frozen_energy_simplify
    (Finset.sum_nonneg fun s _ => hS s) (by positivity) hτ hρ.le hρ1.le hc hc1)

lemma trajectory_instant_energy_sum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : OracleTemplate.Adam.Point d → Ω → OracleTemplate.Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : OracleTemplate.Adam.Point d → OracleTemplate.Adam.Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : OracleTemplate.Adam.Point d) (ω0 : Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.instantDirection g q ρ η τ x0 ξ t‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
    8 * ((∑ t ∈ Finset.range T, ∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ
      (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
      (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Measure.infinitePi (fun _ : ℕ => P)) / τ + (T : ℝ)) := by
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := ∑ t ∈ Finset.range T, ∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ
    (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
    (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Q
  let R := ∑ t ∈ Finset.range T, ∫ ξ, ‖OracleTemplate.Adam.instantDirection g q ρ η τ x0 ξ t‖ ^ 2 ∂Q
  have hn : ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left hnoise (by positivity : 0 ≤ 8 / ρ)
    have he : (8 / ρ) * ρ = 8 := by field_simp
    rw [he] at hh
    nlinarith
  have hr (t : ℕ) := OracleTemplate.Adam.trajectory_instant_energy_integral P hg hgi hL hlip hp hp2 hm hmass
    (η := η) hq hq1 hρ hρ1 hτ hstable x0 ω0 t
  have hr' : R ≤ (2 / τ) * S + 8 * (T : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, ((2 / τ) *
          (∫ ξ, OracleTemplate.Adam.signalEnergy ρ τ (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).2.2
            (grad (OracleTemplate.Adam.trajectory g q ρ η τ x0 ξ t).1) ∂Q) + 8) :=
        Finset.sum_le_sum fun t _ => (hr t).trans (add_le_add le_rfl hn)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [S]; ring
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun ξ =>
    OracleTemplate.Adam.signalEnergy_nonneg (ρ := ρ) hτ _ _
  change R ≤ 8 * (S / τ + (T : ℝ))
  have he : (2 / τ) * S = 2 * (S / τ) := by ring
  rw [he] at hr'
  nlinarith [div_nonneg hS hτ.le]

open OracleTemplate.Adam in
lemma trajectory_expected_descent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {f : Point d → ℝ} {grad : Point d → Point d} {L Δ : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d)
    (hgap : ∀ x, f x0 - f x ≤ Δ) (T : ℕ) :
    η * ((1 - q) * (∑ j ∈ Finset.range T, q ^ j *
      (∑ s ∈ Finset.range (T - j), ∫ ξ, lagPairing g grad q ρ η τ x0 ξ s j j ∂P))) ≤
      Δ + L * η ^ 2 / 2 * (∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂P) := by
  let A := fun j s ξ => lagPairing g grad q ρ η τ x0 ξ s j j
  let F := fun ξ => (1 - q) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), A j s ξ))
  let U := fun ξ => ∑ s ∈ Finset.range T, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2
  have hiA : ∀ j s, Integrable (A j s) P := fun j s =>
    integrable_lagPairing hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j j
  have hirow (j : ℕ) : Integrable (fun ξ => q ^ j * (∑ s ∈ Finset.range (T - j), A j s ξ)) P :=
    (integrable_finsetSum _ (fun s _ => hiA j s)).const_mul _
  have hiF : Integrable F P := (integrable_finsetSum _ (fun j _ => hirow j)).const_mul _
  have hiv (s : ℕ) := integrable_velocity_square (P := P) (η := η) hg hq hq1 hρ hρ1 hτ hstable x0 (s + 1)
  have hiU : Integrable U P := integrable_finsetSum _ (fun s _ => hiv s)
  have hb (ξ : ℕ → Ω) : η * F ξ ≤ Δ + L * η ^ 2 / 2 * U ξ := by
    have hh := trajectory_descent_sum hf hlip g q ρ η τ x0 hgap ξ T
    rw [trajectory_momentum_pairing_sum] at hh
    exact hh
  have hh := integral_mono (hiF.const_mul η) ((integrable_const Δ).add (hiU.const_mul (L * η ^ 2 / 2))) hb
  simp only [Pi.add_def] at hh
  rw [integral_const_mul η, integral_add (integrable_const _) (hiU.const_mul _),
    integral_const_mul (L * η ^ 2 / 2)] at hh
  have heF : (∫ ξ, F ξ ∂P) = (1 - q) * (∑ j ∈ Finset.range T, q ^ j *
      (∑ s ∈ Finset.range (T - j), ∫ ξ, A j s ξ ∂P)) := by
    rw [show F = fun ξ => (1 - q) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), A j s ξ)) from rfl]
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hirow j)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_finsetSum _ (fun s _ => hiA j s)]
  have heU : (∫ ξ, U ξ ∂P) = ∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂P :=
    integral_finsetSum _ (fun s _ => hiv s)
  rw [heF, heU] at hh
  simpa only [A, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

open OracleTemplate.Adam in
lemma trajectory_transport_costs {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M) (hM : 0 ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hfactor : ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 ≤ 4)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ) (hrsmall : q / (1 - ρ) ^ 2 ≤ 91 / 100)
    (x0 : Point d) (ω0 : Ω) (T : ℕ) :
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
      (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
    let W := S / τ + (T : ℝ)
    ((1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), ∫ ξ,
      |lagPairing g grad q ρ η τ x0 ξ s j j - lagPairing g grad q ρ η τ x0 ξ s j 0| ∂Q)) ≤
      200 * (L * |η|) * W) ∧
    ((1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), ∫ ξ,
      |lagPairing g grad q ρ η τ x0 ξ s j 0 -
        frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))| ∂Q)) ≤
      9600 * (L * |η|) * W) := by
  dsimp only
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
    (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
  let W := S / τ + (T : ℝ)
  let R := ∑ s ∈ Finset.range T, ∫ ξ, ‖instantDirection g q ρ η τ x0 ξ s‖ ^ 2 ∂Q
  let U := ∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g q ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂Q
  let N := fun j => ∑ s ∈ Finset.range (T - j), ∫ ξ,
    |lagPairing g grad q ρ η τ x0 ξ s j j - lagPairing g grad q ρ η τ x0 ξ s j 0| ∂Q
  let D := fun j => ∑ s ∈ Finset.range (T - j), ∫ ξ,
    |lagPairing g grad q ρ η τ x0 ξ s j 0 -
      frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))| ∂Q
  have hS : 0 ≤ S := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => signalEnergy_nonneg hτ _ _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hR : 0 ≤ R := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => sq_nonneg _
  have hU : 0 ≤ U := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => sq_nonneg _
  have ha : 0 ≤ L * |η| := mul_nonneg hL (abs_nonneg _)
  have hRb : R ≤ 8 * W := trajectory_instant_energy_sum P hg hgi hL hlip (by linarith) hp2 hm hmass
    hq hq1 hρ hρ1 hτ hstable hnoise x0 ω0 T
  have hUb : U ≤ 32 * W := trajectory_energy_integral_bound P hg hgi hL hlip (by linarith) hp2 hm hmass
    hq hq1 hρ hρ1 hτ hstable hfactor hnoise x0 ω0 T
  have hc (j : ℕ) : 0 < Real.sqrt ((1 - ρ) ^ j) := Real.sqrt_pos.mpr (pow_pos (sub_pos.mpr hρ1) j)
  have hc1 (j : ℕ) : Real.sqrt ((1 - ρ) ^ j) ≤ 1 := Real.sqrt_le_iff.mpr
    ⟨by norm_num, by simpa using pow_le_one₀ (sub_pos.mpr hρ1).le (by linarith : 1 - ρ ≤ 1) (n := j)⟩
  have hn (j : ℕ) : N j ≤ 16 * (L * |η|) * (j : ℝ) / ((1 - ρ) ^ 2) ^ j * W := by
    have hh := trajectory_numerator_integral_sum (η := η) Q hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 T j
    have hb := AdamHeavyTailedAlgebra.lag_numerator_cost ha hW (hc j) (hc1 j) hR hU hRb hUb j hh
    simpa only [AdamHeavyTailedAlgebra.sqrt_power_four (sub_pos.mpr hρ1).le] using hb
  have hd (j : ℕ) : D j ≤ 32 * (L * |η|) * (j : ℝ) ^ 2 / ((1 - ρ) ^ 2) ^ j * W := by
    cases j with
    | zero =>
      have hh := trajectory_denominator_integral_sum (η := η) Q hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 T 0
      simpa only [D, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_div, zero_mul, zero_pow (by omega : 2 ≠ 0)] using hh
    | succ j =>
      let X := ∑ s ∈ Finset.range (T - (j + 1)), ∫ ξ, ∑ i,
        (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
          (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) (j + 1) (fun k => ξ (s + k)) i) ^ 2 ∂Q
      have hX : 0 ≤ X := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ =>
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
      have hXb : X ≤ 19 * W / Real.sqrt ((1 - ρ) ^ (j + 1)) :=
        trajectory_frozenEnergy_sum P hg hL hlip hm hmass hq hq1 hρ hρ1 hτ hstable hp hp2 hM hnoise x0 ω0 T j
      have hh := trajectory_denominator_integral_sum (η := η) Q hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 T (j + 1)
      have hb := AdamHeavyTailedAlgebra.lag_denominator_cost ha hW (hc (j + 1)) (hc1 (j + 1)) hX hU hXb hUb (j + 1) hh
      simpa only [AdamHeavyTailedAlgebra.sqrt_power_four (sub_pos.mpr hρ1).le] using hb
  exact ⟨AdamHeavyTailedAlgebra.weighted_lag_linear_cost hq (sub_pos.mpr hρ1) hrsmall ha hW N hn T,
    AdamHeavyTailedAlgebra.weighted_lag_square_cost hq (sub_pos.mpr hρ1) hrsmall ha hW D hd T⟩

open OracleTemplate.Adam in
lemma trajectory_pairing_signal_lower {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M) (hM : 0 ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hfactor : ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 ≤ 4)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ) (hrsmall : q / (1 - ρ) ^ 2 ≤ 91 / 100)
    (x0 : Point d) (ω0 : Ω) (T : ℕ) :
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
      (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
    (3 / 40 - 200 * ρ) * S - 200000 * τ * ρ * T - 9800 * (L * |η|) * (S / τ + T) ≤
      (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j *
        (∑ s ∈ Finset.range (T - j), ∫ ξ, lagPairing g grad q ρ η τ x0 ξ s j j ∂Q)) := by
  dsimp only
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := fun s => ∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
    (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Q
  let A := fun s j => ∫ ξ, lagPairing g grad q ρ η τ x0 ξ s j j ∂Q
  let F := fun s j => ∫ ξ, frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) ∂Q
  let V := fun s j => ∫ ξ, meanPairing ρ τ (trajectory g q ρ η τ x0 ξ s) grad j ∂Q
  let N := fun s j => ∫ ξ, |lagPairing g grad q ρ η τ x0 ξ s j j - lagPairing g grad q ρ η τ x0 ξ s j 0| ∂Q
  let D := fun s j => ∫ ξ, |lagPairing g grad q ρ η τ x0 ξ s j 0 -
    frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))| ∂Q
  let B := fun s j => V s j - F s j
  let H := fun s => (1 / 40 + 200 * ρ) * S s + 200000 * τ * ρ
  have hS : ∀ s, 0 ≤ S s := fun s => integral_nonneg fun ξ => signalEnergy_nonneg hτ _ _
  have hH : ∀ s, 0 ≤ H s := fun s => by
    have hs := hS s
    dsimp [H]
    positivity
  have hb (s j : ℕ) : B s j ≤ ((j : ℝ) + 1) / (25 * ((1 - ρ) ^ 2) ^ j) * H s :=
    trajectory_pairing_bias_integral P hg hL hlip hgi hmean hm hmass hq hq1 hρ hρ1 hτ hstable hp hp2 hM hnoise x0 ω0 s j
  have hbt := AdamHeavyTailedAlgebra.geometric_bias_total hq (sub_pos.mpr hρ1) hrsmall H hH B hb T
  have hm0 : ∀ s, V s 0 = S s := fun s => by dsimp [V, S]; simp_rw [meanPairing_zero]
  have hvm : ∀ s j, 0 ≤ V s j := fun s j => integral_nonneg fun ξ => meanPairing_nonneg hτ _ _ _
  have hvmSum := mul_le_mul_of_nonneg_left (AdamHeavyTailedAlgebra.mean_window_signal_sum hq V S hvm hm0 T)
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hpnt (s j : ℕ) : V s j - B s j - N s j - D s j ≤ A s j := by
    have hiA := integrable_lagPairing (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j j
    have hiB := integrable_lagPairing (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j 0
    have hiF := integrable_trajectory_frozenPairing (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j
    have hh := integral_transport_lower Q hiA hiB hiF
    change F s j - N s j - D s j ≤ A s j at hh
    dsimp only [B]
    linarith
  have ht := mul_le_mul_of_nonneg_left
    (AdamHeavyTailedAlgebra.triangular_linear_lower A V B N D (fun j => q ^ j) (fun j => pow_nonneg hq j) hpnt T)
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hcost := trajectory_transport_costs (η := η) P hg hgi hL hlip hp hp2 hm hmass hM hq hq1 hρ hρ1 hτ hstable hfactor hnoise hrsmall x0 ω0 T
  have heH : (∑ s ∈ Finset.range T, H s) = (1 / 40 + 200 * ρ) *
      (∑ s ∈ Finset.range T, S s) + 200000 * τ * ρ * T := by
    dsimp [H]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heH] at hbt
  dsimp only at hcost
  change (3 / 40 - 200 * ρ) * (∑ s ∈ Finset.range T, S s) - 200000 * τ * ρ * T -
    9800 * (L * |η|) * ((∑ s ∈ Finset.range T, S s) / τ + T) ≤
      (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), A s j))
  change ((1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), N s j)) ≤ _) ∧
    ((1 / 10 : ℝ) * (∑ j ∈ Finset.range T, q ^ j * (∑ s ∈ Finset.range (T - j), D s j)) ≤ _) at hcost
  linarith [hcost.1, hcost.2]

end LongTails.Proofs.AdamHeavyTailedHistory
