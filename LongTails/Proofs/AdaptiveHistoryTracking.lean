import LongTails.Proofs.AdaptiveHistoryAlgebra
import LongTails.Proofs.AdaptiveHistoryFinite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open LongTails.Proofs.AdaptiveHistoryAlgebra
open LongTails.Proofs.AdaptiveHistoryFinite

namespace LongTails.Proofs.AdaptiveHistoryTracking

lemma normalized_value_bound {a r δ C : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (hC : 0 ≤ C)
    (ha : |a| ≤ C * r) : |a / (δ + r)| ≤ C := by
  rw [abs_div, abs_of_pos (show 0 < δ + r by positivity), div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hC hδ.le]

lemma normalized_difference_capped {a b r s δ C D : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hC : 0 ≤ C)
    (ha : |a| ≤ C * r) (hb : |b| ≤ C * s)
    (hab : |a - b| ≤ C * D) (hrs : |r - s| ≤ D) :
    |a / (δ + r) - b / (δ + s)| ≤ 2 * C * min 1 (D / (δ + s)) := by
  have h1 : |a / (δ + r) - b / (δ + s)| ≤ 2 * C := by
    have hp := normalized_value_bound hr hδ hC ha
    have hq := normalized_value_bound hs hδ hC hb
    have ht := abs_sub_le (a / (δ + r)) 0 (b / (δ + s))
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith
  have h2 := normalized_difference hr hs hδ hC ha hab hrs
  by_cases hD : 1 ≤ D / (δ + s)
  · simpa [min_eq_left hD] using h1
  · rw [min_eq_right (le_of_not_ge hD)]
    convert h2 using 1
    ring

lemma normalized_inner_difference {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c v w : E) {δ : ℝ} (hδ : 0 < δ) :
    |inner ℝ c v / (δ + ‖v‖) - inner ℝ c w / (δ + ‖w‖)| ≤
      2 * ‖c‖ * min 1 (‖v - w‖ / (δ + ‖w‖)) := by
  apply normalized_difference_capped (norm_nonneg _) (norm_nonneg _) hδ (norm_nonneg _)
    (abs_real_inner_le_norm c v) (abs_real_inner_le_norm c w)
  · simpa only [inner_sub_right] using abs_real_inner_le_norm c (v - w)
  · exact abs_norm_sub_norm_le v w

noncomputable def weightedVector {ι : Type*} (b z : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (b i) * z i)

lemma weightedVector_norm {ι : Type*} [Fintype ι] (b z : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ‖weightedVector b z‖ = Real.sqrt (∑ i, b i * z i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedVector, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (hb i)]

lemma weightedVector_sub {ι : Type*} (b z w : ι → ℝ) :
    weightedVector b z - weightedVector b w = weightedVector b (fun i => z i - w i) := by
  ext i
  simp [weightedVector, mul_sub]

lemma weightedVector_inner {ι : Type*} [Fintype ι] (a b z : ι → ℝ)
    (hb : ∀ i, 0 < b i) :
    inner ℝ (WithLp.toLp 2 (fun i => a i / Real.sqrt (b i)) : EuclideanSpace ℝ ι)
      (weightedVector b z) = ∑ i, a i * z i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.sqrt (b i) * z i) * (a i / Real.sqrt (b i)) = a i * z i
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (hb i))]

lemma weighted_coeff_norm {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) :
    ‖(WithLp.toLp 2 (fun i => a i / Real.sqrt (b i)) : EuclideanSpace ℝ ι)‖ =
      Real.sqrt (∑ i, a i ^ 2 / b i) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hb i)]

lemma weighted_history_difference {ι : Type*} [Fintype ι] (a b z w : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ i, 0 < b i) :
    |(∑ i, a i * z i) / (δ + Real.sqrt (∑ i, b i * z i ^ 2)) -
      (∑ i, a i * w i) / (δ + Real.sqrt (∑ i, b i * w i ^ 2))| ≤
    2 * Real.sqrt (∑ i, a i ^ 2 / b i) *
      min 1 (Real.sqrt (∑ i, b i * (z i - w i) ^ 2) /
        (δ + Real.sqrt (∑ i, b i * w i ^ 2))) := by
  have h := normalized_inner_difference
    (WithLp.toLp 2 (fun i => a i / Real.sqrt (b i)) : EuclideanSpace ℝ ι)
    (weightedVector b z) (weightedVector b w) hδ
  rw [weightedVector_inner a b z hb, weightedVector_inner a b w hb,
    weightedVector_sub, weighted_coeff_norm a b (fun i => (hb i).le),
    weightedVector_norm b z (fun i => (hb i).le),
    weightedVector_norm b w (fun i => (hb i).le),
    weightedVector_norm b (fun i => z i - w i) (fun i => (hb i).le)] at h
  exact h

lemma geometric_coeff_square_sum (n : ℕ) {α β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hαβ : α ^ 2 < β) :
    (∑ i : Fin n, ((1 - α) * α ^ (i : ℕ)) ^ 2 / ((1 - β) * β ^ (i : ℕ))) ≤
      (1 - α) ^ 2 / ((1 - β) * (1 - α ^ 2 / β)) := by
  have hq0 : 0 ≤ α ^ 2 / β := by positivity
  have hq1 : α ^ 2 / β < 1 := (div_lt_one hβ).mpr hαβ
  have he (i : Fin n) : ((1 - α) * α ^ (i : ℕ)) ^ 2 / ((1 - β) * β ^ (i : ℕ)) =
      ((1 - α) ^ 2 / (1 - β)) * (α ^ 2 / β) ^ (i : ℕ) := by
    rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm (i : ℕ) 2, pow_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (finite_geometric_le n hq0 hq1)
    (show 0 ≤ (1 - α) ^ 2 / (1 - β) by positivity)
  convert hh using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma default_geometric_coeff (n : ℕ) :
    Real.sqrt (∑ i : Fin n,
      ((1 - (9 / 10 : ℝ)) * (9 / 10 : ℝ) ^ (i : ℕ)) ^ 2 /
        ((1 - (999 / 1000 : ℝ)) * (999 / 1000 : ℝ) ^ (i : ℕ))) ≤ 8 := by
  have hh := geometric_coeff_square_sum n (α := (9 / 10 : ℝ))
    (β := (999 / 1000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 8)).mpr
  norm_num at hh ⊢
  linarith


lemma first_success_domination {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (u : ℝ) (c : Fin n → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hu : ∀ k, p k → u ≤ c k) :
    (if ∃ k, p k then u else 0) ≤
      ∑ k : Fin n, if ∀ j, j < k → ¬p j then c k else 0 := by
  classical
  by_cases hp : ∃ k, p k
  · rw [ite_eq_left hp]
    let k := Fin.find p hp
    have hk : p k := Fin.find_spec hp
    have hmin : ∀ j, j < k → ¬p j := fun j hj => Fin.find_min hp hj
    calc
      u ≤ c k := hu k hk
      _ = (if ∀ j, j < k → ¬p j then c k else 0) := (ite_eq_left hmin).symm
      _ ≤ ∑ k : Fin n, if ∀ j, j < k → ¬p j then c k else 0 := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin n => if ∀ l, l < j → ¬p l then c j else 0)
        · intro j _
          split_ifs
          · exact hc j
          · exact le_rfl
        · exact Finset.mem_univ k
  · rw [ite_eq_right hp]
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hc j
    · exact le_rfl

lemma small_ball_geometric_sum (n : ℕ) {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    (∑ k : Fin n, (1 / 2 : ℝ) ^ (k : ℕ) * (4 / ((1 - β) * β ^ ((k : ℕ) + 1)))) ≤
      8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  have hb : 0 < β := by linarith
  have hd : 0 < 1 - β := by linarith
  have hq : 1 / (2 * β) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have he (k : Fin n) : (1 / 2 : ℝ) ^ (k : ℕ) * (4 / ((1 - β) * β ^ ((k : ℕ) + 1))) =
      (4 / ((1 - β) * β)) * (1 / (2 * β)) ^ (k : ℕ) := by
    rw [pow_succ]
    simp only [mul_pow, one_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (4 / ((1 - β) * β)) * (1 / (1 - 1 / (2 * β))) :=
      mul_le_mul_of_nonneg_left (finite_geometric_le n (by positivity) hq) (by positivity)
    _ = (4 / β) / ((1 - β) * (1 - 1 / (2 * β))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ hb).mpr
      linarith

lemma integral_first_success_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {n : ℕ} (s : Fin n → Set Ω) (c r : Fin n → ℝ)
    (u : Ω → ℝ) (hs : ∀ k, MeasurableSet (s k)) (hc : ∀ k, 0 ≤ c k)
    (hu : AEStronglyMeasurable u μ) (hu0 : ∀ ω, 0 ≤ u ω)
    (hzero : ∀ ω, (∀ k, ω ∉ s k) → u ω = 0)
    (hsuccess : ∀ ω k, ω ∈ s k → u ω ≤ c k)
    (hprob : ∀ k, μ.real {ω | ∀ j, j < k → ω ∉ s j} ≤ r k) :
    Integrable u μ ∧ (∫ ω, u ω ∂μ) ≤ ∑ k, r k * c k := by
  classical
  let F : Fin n → Set Ω := fun k => {ω | ∀ j, j < k → ω ∉ s j}
  have hF (k : Fin n) : MeasurableSet (F k) := by
    simp only [F, Set.ofPred_forall]
    exact MeasurableSet.iInter fun (j : Fin n) =>
      MeasurableSet.iInter fun (_ : j < k) => (hs j).compl
  let V : Ω → ℝ := fun ω => ∑ k, (F k).indicator (fun _ => c k) ω
  have hVi (k : Fin n) : Integrable ((F k).indicator (fun _ => c k)) μ :=
    (integrable_const (c k)).indicator (hF k)
  have hV : Integrable V μ := integrable_finsetSum _ (fun k _ => hVi k)
  have huv (ω : Ω) : u ω ≤ V ω := by
    have hh := first_success_domination (fun k => ω ∈ s k) (u ω) c hc (hsuccess ω)
    have he : (if ∃ k, ω ∈ s k then u ω else 0) = u ω := by
      split_ifs with hh
      · rfl
      · symm
        exact hzero ω (by simpa only [not_exists] using hh)
    rw [he] at hh
    simpa only [V, F, Set.indicator, Set.mem_ofPred_eq] using hh
  have hi : Integrable u μ := hV.mono' hu (Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hu0 ω)] using huv ω)
  refine ⟨hi, (integral_mono hi hV huv).trans ?_⟩
  rw [show (∫ ω, V ω ∂μ) = ∑ k, ∫ ω, (F k).indicator (fun _ => c k) ω ∂μ from
    integral_finsetSum _ (fun k _ => hVi k)]
  apply Finset.sum_le_sum
  intro k _
  rw [integral_indicator_const _ (hF k), smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hprob k) (hc k)

lemma inverse_ratio_of_success {g w b R : ℝ} (hg : g ≠ 0) (hb : 0 < b)
    (hsuccess : g ^ 2 ≤ 4 * w ^ 2) (hR : b * w ^ 2 ≤ R) :
    0 < R ∧ g ^ 2 / R ≤ 4 / b := by
  have hw : 0 < w ^ 2 := by nlinarith [sq_pos_of_ne_zero hg]
  have hRp : 0 < R := (mul_pos hb hw).trans_le hR
  refine ⟨hRp, ?_⟩
  apply (div_le_div_iff₀ hRp hb).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsuccess hb.le]

lemma deleted_index_weight_lower {n : ℕ} (i : Fin (n + 1)) (k : Fin n)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (1 - β) * β ^ ((k : ℕ) + 1) ≤ (1 - β) * β ^ (i.succAbove k : ℕ) := by
  have hj : (i.succAbove k : ℕ) ≤ (k : ℕ) + 1 := by
    by_cases h : k.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i k h]
      simp
    · rw [Fin.succAbove_of_le_castSucc i k (le_of_not_gt h)]
      rfl
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hβ hβ1 hj) (by linarith)

lemma default_small_ball_constant :
    8 / ((1 - (999 / 1000 : ℝ)) * (1 - 1 / (2 * (999 / 1000 : ℝ)))) ≤ 127 ^ 2 := by
  norm_num

lemma symmetric_halfline_failure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) :
    μ.real (Set.Iio 0) ≤ 1 / 2 ∧ μ.real (Set.Ioi 0) ≤ 1 / 2 := by
  have he : μ.real (Set.Iio 0) = μ.real (Set.Ioi 0) := by
    calc
      μ.real (Set.Iio 0) = (μ.map (fun x : ℝ => -x)).real (Set.Iio 0) := by rw [hsym]
      _ = μ.real (Set.Ioi 0) := by
        rw [map_measureReal_apply measurable_neg measurableSet_Iio]
        congr 1
        ext x
        simp
  have hm : μ.real (Set.Ioi 0) ≤ μ.real (Set.Iio 0)ᶜ := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Iio, not_lt]
    exact le_of_lt hx
  have hc := measureReal_add_measureReal_compl (μ := μ) (s := Set.Iio (0 : ℝ)) measurableSet_Iio
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hc
  change μ.real (Set.Iio 0) + μ.real (Set.Iio 0)ᶜ = 1 at hc
  constructor <;> linarith

lemma product_prefix_failure {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Fin n → Set Ω) (k : Fin n) (hs : ∀ j, μ.real (s j) ≤ 1 / 2) :
    (Measure.pi (fun _ : Fin n => μ)).real {z | ∀ j, j < k → z j ∈ s j} ≤
      (1 / 2 : ℝ) ^ (k : ℕ) := by
  classical
  have he : {z | ∀ j, j < k → z j ∈ s j} = (↑(Finset.Iio k) : Set (Fin n)).pi s := by
    ext z
    simp
  rw [he, Measure.real, Measure.pi_pi_finset, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ j ∈ Finset.Iio k, (1 / 2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact ENNReal.toReal_nonneg
      · intro j _
        exact hs j
    _ = (1 / 2 : ℝ) ^ (k : ℕ) := by simp

lemma symmetric_product_negative {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (g : ℝ) :
    μ.real {x | g * x < 0} ≤ 1 / 2 := by
  have hh := symmetric_halfline_failure hsym
  rcases lt_trichotomy g 0 with hg | hg | hg
  · apply le_trans (measureReal_mono (s₂ := Set.Ioi 0) _ (measure_ne_top _ _)) hh.2
    intro x hx
    change 0 < x
    change g * x < 0 at hx
    by_contra hn
    have := mul_nonneg_of_nonpos_of_nonpos hg.le (le_of_not_gt hn)
    linarith
  · subst g
    norm_num
  · apply le_trans (measureReal_mono (s₂ := Set.Iio 0) _ (measure_ne_top _ _)) hh.1
    intro x hx
    change x < 0
    change g * x < 0 at hx
    by_contra hn
    have := mul_nonneg hg.le (le_of_not_gt hn)
    linarith

lemma integral_truncated_inverse {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) {β g : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hg : g ≠ 0) (b : Fin n → ℝ)
    (hb : ∀ k : Fin n, (1 - β) * β ^ ((k : ℕ) + 1) ≤ b k) :
    let u := {z : Fin n → ℝ | ∃ k, 0 ≤ g * z k}.indicator
      (fun z => g ^ 2 / (∑ k, b k * (g + z k) ^ 2))
    Integrable u (Measure.pi (fun _ : Fin n => μ)) ∧
      (∫ z, u z ∂Measure.pi (fun _ : Fin n => μ)) ≤
        8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  classical
  dsimp only
  let P := Measure.pi (fun _ : Fin n => μ)
  let s : Fin n → Set (Fin n → ℝ) := fun k => {z | 0 ≤ g * z k}
  let A : Set (Fin n → ℝ) := {z | ∃ k, 0 ≤ g * z k}
  let R : (Fin n → ℝ) → ℝ := fun z => ∑ k, b k * (g + z k) ^ 2
  let u := A.indicator (fun z => g ^ 2 / R z)
  let c : Fin n → ℝ := fun k => 4 / ((1 - β) * β ^ ((k : ℕ) + 1))
  have hb0 : 0 < β := by linarith
  have hd : 0 < 1 - β := by linarith
  have hbpos (k : Fin n) : 0 < b k := (by positivity : 0 < (1 - β) * β ^ ((k : ℕ) + 1)).trans_le (hb k)
  have hs (k : Fin n) : MeasurableSet (s k) := by
    exact measurableSet_le measurable_const (measurable_const.mul (measurable_pi_apply k))
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_exists]
    exact MeasurableSet.iUnion hs
  have hR : Measurable R := by dsimp [R]; fun_prop
  have hu : AEStronglyMeasurable u P :=
    ((measurable_const.div hR).indicator hA).aestronglyMeasurable
  have hu0 (z) : 0 ≤ u z := by
    apply Set.indicator_nonneg
    intro _ _
    apply div_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hbpos k).le (sq_nonneg _))
  have hzero (z) (hz : ∀ k, z ∉ s k) : u z = 0 := by
    apply Set.indicator_of_notMem
    simpa only [A, s, Set.mem_ofPred_eq, not_exists] using hz
  have hsuccess (z) (k : Fin n) (hz : z ∈ s k) : u z ≤ c k := by
    have hzA : z ∈ A := ⟨k, hz⟩
    change A.indicator (fun z => g ^ 2 / R z) z ≤ c k
    rw [Set.indicator_of_mem hzA]
    have hsk : g ^ 2 ≤ 4 * (g + z k) ^ 2 := by
      change 0 ≤ g * z k at hz
      nlinarith [sq_nonneg g, sq_nonneg (z k)]
    have hterm : b k * (g + z k) ^ 2 ≤ R z := by
      apply Finset.single_le_sum (s := Finset.univ) (f := fun j => b j * (g + z j) ^ 2)
      · intro j _
        exact mul_nonneg (hbpos j).le (sq_nonneg _)
      · exact Finset.mem_univ k
    calc
      g ^ 2 / R z ≤ 4 / b k := (inverse_ratio_of_success hg (hbpos k) hsk hterm).2
      _ ≤ c k := div_le_div_of_nonneg_left (by norm_num) (by positivity) (hb k)
  have hprob (k : Fin n) : P.real {z | ∀ j, j < k → z ∉ s j} ≤ (1 / 2 : ℝ) ^ (k : ℕ) := by
    have hh := product_prefix_failure (μ := μ) (fun _ : Fin n => {x : ℝ | g * x < 0}) k
      (fun _ => symmetric_product_negative hsym g)
    simpa only [P, s, Set.mem_ofPred_eq, not_le] using hh
  have hh := integral_first_success_bound s c (fun k => (1 / 2 : ℝ) ^ (k : ℕ)) u hs
    (fun k => by dsimp [c]; positivity) hu hu0 hzero hsuccess hprob
  exact ⟨hh.1, hh.2.trans (small_ball_geometric_sum n hβ hβ1)⟩

lemma product_all_failure {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Fin n → Set Ω) (hs : ∀ j, μ.real (s j) ≤ 1 / 2) :
    (Measure.pi (fun _ : Fin n => μ)).real {z | ∀ j, z j ∈ s j} ≤
      (1 / 2 : ℝ) ^ n := by
  classical
  have he : {z | ∀ j, z j ∈ s j} = Set.univ.pi s := by ext z; simp
  rw [he, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ _j : Fin n, (1 / 2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact ENNReal.toReal_nonneg
      · intro j _
        exact hs j
    _ = (1 / 2 : ℝ) ^ n := by simp

lemma symmetric_all_failure {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (g : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {z : Fin n → ℝ | ∃ k, 0 ≤ g * z k}ᶜ ≤ (1 / 2 : ℝ) ^ n := by
  have hh := product_all_failure (μ := μ) (fun _ : Fin n => {x : ℝ | g * x < 0})
    (fun _ => symmetric_product_negative hsym g)
  convert hh using 1
  congr 1
  ext z
  simp


lemma truncated_inverse_root_moment {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) {β g : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hg : g ≠ 0) (b : Fin n → ℝ)
    (hb : ∀ k : Fin n, (1 - β) * β ^ ((k : ℕ) + 1) ≤ b k) :
    let r := {z : Fin n → ℝ | ∃ k, 0 ≤ g * z k}.indicator
      (fun z => |g| / Real.sqrt (∑ k, b k * (g + z k) ^ 2))
    MemLp r 2 (Measure.pi (fun _ : Fin n => μ)) ∧
      (∫ z, r z ^ 2 ∂Measure.pi (fun _ : Fin n => μ)) ≤
        8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  classical
  dsimp only
  let P := Measure.pi (fun _ : Fin n => μ)
  let A : Set (Fin n → ℝ) := {z | ∃ k, 0 ≤ g * z k}
  let R : (Fin n → ℝ) → ℝ := fun z => ∑ k, b k * (g + z k) ^ 2
  let r := A.indicator (fun z => |g| / Real.sqrt (R z))
  let u := A.indicator (fun z => g ^ 2 / R z)
  have hβ0 : 0 < β := by linarith
  have hd : 0 < 1 - β := by linarith
  have hb0 (k : Fin n) : 0 ≤ b k := (by positivity : 0 ≤ (1 - β) * β ^ ((k : ℕ) + 1)).trans (hb k)
  have hR0 (z) : 0 ≤ R z := Finset.sum_nonneg fun k _ => mul_nonneg (hb0 k) (sq_nonneg _)
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k =>
      measurableSet_le measurable_const (measurable_const.mul (measurable_pi_apply k))
  have hRm : Measurable R := by dsimp [R]; fun_prop
  have hr : AEStronglyMeasurable r P :=
    ((measurable_const.div hRm.sqrt).indicator hA).aestronglyMeasurable
  have he (z) : r z ^ 2 = u z := by
    by_cases hz : z ∈ A
    · simp only [r, u, Set.indicator_of_mem hz, div_pow, sq_abs, Real.sq_sqrt (hR0 z)]
    · simp only [r, u, Set.indicator_of_notMem hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hh := integral_truncated_inverse hsym hβ hβ1 hg b hb
  change Integrable u P ∧ (∫ z, u z ∂P) ≤ _ at hh
  have hi : Integrable (fun z => r z ^ 2) P := hh.1.congr (Filter.Eventually.of_forall fun z => (he z).symm)
  refine ⟨(memLp_two_iff_integrable_sq hr).mpr hi, ?_⟩
  change (∫ z, r z ^ 2 ∂P) ≤ _
  simpa only [he] using hh.2


lemma integral_mul_le_square_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d r : Ω → ℝ} (hd : MemLp d 2 P) (hr : MemLp r 2 P)
    (hd0 : ∀ ω, 0 ≤ d ω) (hr0 : ∀ ω, 0 ≤ r ω) :
    (∫ ω, d ω * r ω ∂P) ≤
      Real.sqrt (∫ ω, d ω ^ 2 ∂P) * Real.sqrt (∫ ω, r ω ^ 2 ∂P) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall hd0) (Filter.Eventually.of_forall hr0)
    (show MemLp d (ENNReal.ofReal 2) P by simpa using hd)
    (show MemLp r (ENNReal.ofReal 2) P by simpa using hr)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

lemma first_moment_factor_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure p] [SFinite P]
    {K : Ω → ℝ} {d r : Ξ → ℝ} {L M κ : ℝ}
    (hL : 0 ≤ L) (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω)
    (hM : (∫ ω, K ω ∂p) ≤ M) (hκ : 0 ≤ κ)
    (hd : MemLp d 2 P) (hr : MemLp r 2 P)
    (hd0 : ∀ ω, 0 ≤ d ω) (hr0 : ∀ ω, 0 ≤ r ω)
    (hr2 : (∫ ω, r ω ^ 2 ∂P) ≤ κ ^ 2) :
    Integrable (fun z : Ω × Ξ => (L + K z.1) * d z.2 * r z.2) (p.prod P) ∧
      (∫ z : Ω × Ξ, (L + K z.1) * d z.2 * r z.2 ∂p.prod P) ≤
        (L + M) * κ * Real.sqrt (∫ ω, d ω ^ 2 ∂P) := by
  have hki : Integrable (fun ω => L + K ω) p := (integrable_const L).add hK
  have hdri : Integrable (fun ω => d ω * r ω) P := hd.integrable_mul hr
  have hi := hki.mul_prod hdri
  have hkm : 0 ≤ L + ∫ ω, K ω ∂p := add_nonneg hL (integral_nonneg_of_ae hK0)
  have hMM : 0 ≤ L + M := by linarith
  have hrr : Real.sqrt (∫ ω, r ω ^ 2 ∂P) ≤ κ :=
    (Real.sqrt_le_left hκ).mpr hr2
  refine ⟨by simpa only [mul_assoc] using hi, ?_⟩
  simp_rw [mul_assoc]
  rw [integral_prod_mul (fun ω => L + K ω) (fun ω => d ω * r ω), integral_add (integrable_const L) hK, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  calc
    (L + ∫ ω, K ω ∂p) * (∫ ω, d ω * r ω ∂P) ≤
        (L + ∫ ω, K ω ∂p) *
          (Real.sqrt (∫ ω, d ω ^ 2 ∂P) * Real.sqrt (∫ ω, r ω ^ 2 ∂P)) :=
      mul_le_mul_of_nonneg_left (integral_mul_le_square_moments hd hr hd0 hr0) hkm
    _ ≤ (L + M) * (Real.sqrt (∫ ω, d ω ^ 2 ∂P) * κ) := by gcongr
    _ = (L + M) * (κ * Real.sqrt (∫ ω, d ω ^ 2 ∂P)) := by ring

lemma deleted_first_moment_factor_bound {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {n : ℕ} (i : Fin (n + 1))
    {K : Ω → ℝ} {d r : (Fin n → Ω) → ℝ} {L M κ : ℝ}
    (hL : 0 ≤ L) (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω)
    (hM : (∫ ω, K ω ∂p) ≤ M) (hκ : 0 ≤ κ)
    (hd : MemLp d 2 (Measure.pi (fun _ : Fin n => p)))
    (hr : MemLp r 2 (Measure.pi (fun _ : Fin n => p)))
    (hd0 : ∀ ω, 0 ≤ d ω) (hr0 : ∀ ω, 0 ≤ r ω)
    (hr2 : (∫ ω, r ω ^ 2 ∂Measure.pi (fun _ : Fin n => p)) ≤ κ ^ 2) :
    Integrable (fun z : Fin (n + 1) → Ω =>
      (L + K (z i)) * d (fun j => z (i.succAbove j)) * r (fun j => z (i.succAbove j)))
        (Measure.pi (fun _ : Fin (n + 1) => p)) ∧
      (∫ z : Fin (n + 1) → Ω,
        (L + K (z i)) * d (fun j => z (i.succAbove j)) * r (fun j => z (i.succAbove j))
        ∂Measure.pi (fun _ : Fin (n + 1) => p)) ≤
      (L + M) * κ * Real.sqrt (∫ ω, d ω ^ 2 ∂Measure.pi (fun _ : Fin n => p)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) i
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => p) i
  let f : Ω × (Fin n → Ω) → ℝ := fun z => (L + K z.1) * d z.2 * r z.2
  have hh := first_moment_factor_bound hL hK hK0 hM hκ hd hr hd0 hr0 hr2
  have he (z : Fin (n + 1) → Ω) :
      f (e z) = (L + K (z i)) * d (fun j => z (i.succAbove j)) * r (fun j => z (i.succAbove j)) := rfl
  constructor
  · have hi := hp.integrable_comp_of_integrable hh.1
    change Integrable (fun z => f (e z)) (Measure.pi (fun _ : Fin (n + 1) => p)) at hi
    simpa only [he] using hi
  · have hint := hp.integral_comp e.measurableEmbedding f
    rw [← hint] at hh
    exact hh.2


lemma truncated_inverse_root_noise_moment {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {noise : Ω → ℝ}
    (hm : Measurable noise) (hsym : (p.map noise).map (fun x : ℝ => -x) = p.map noise)
    {n : ℕ} {β g : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hg : g ≠ 0)
    (b : Fin n → ℝ) (hb : ∀ k : Fin n, (1 - β) * β ^ ((k : ℕ) + 1) ≤ b k) :
    let r := {z : Fin n → Ω | ∃ k, 0 ≤ g * noise (z k)}.indicator
      (fun z => |g| / Real.sqrt (∑ k, b k * (g + noise (z k)) ^ 2))
    MemLp r 2 (Measure.pi (fun _ : Fin n => p)) ∧
      (∫ z, r z ^ 2 ∂Measure.pi (fun _ : Fin n => p)) ≤
        8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  classical
  dsimp only
  let P := Measure.pi (fun _ : Fin n => p)
  let Q := Measure.pi (fun _ : Fin n => p.map noise)
  let T : (Fin n → Ω) → (Fin n → ℝ) := fun z k => noise (z k)
  let r := {z : Fin n → ℝ | ∃ k, 0 ≤ g * z k}.indicator
    (fun z => |g| / Real.sqrt (∑ k, b k * (g + z k) ^ 2))
  have hp : MeasurePreserving T P Q := measurePreserving_pi
    (fun _ : Fin n => p) (fun _ : Fin n => p.map noise) (fun _ => ⟨hm, rfl⟩)
  have hh := truncated_inverse_root_moment hsym hβ hβ1 hg b hb
  change MemLp r 2 Q ∧ (∫ z, r z ^ 2 ∂Q) ≤ _ at hh
  have hmem := hh.1.comp_measurePreserving hp
  have hint : (∫ z, r (T z) ^ 2 ∂P) = ∫ z, r z ^ 2 ∂Q := by
    have hi := integral_map hp.measurable.aemeasurable
      (f := fun z => r z ^ 2) (hp.map_eq.symm ▸ hh.1.integrable_sq.aestronglyMeasurable)
    simpa only [hp.map_eq] using hi.symm
  change MemLp (r ∘ T) 2 P ∧ (∫ z, r (T z) ^ 2 ∂P) ≤ _
  exact ⟨hmem, hint.le.trans hh.2⟩


lemma default_deleted_tracking_term {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {noise K : Ω → ℝ}
    (hm : Measurable noise) (hsym : (p.map noise).map (fun x : ℝ => -x) = p.map noise)
    {n : ℕ} (i : Fin (n + 1)) {g L M : ℝ} (hg : g ≠ 0) (hL : 0 ≤ L)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω) (hM : (∫ ω, K ω ∂p) ≤ M)
    {d : (Fin n → Ω) → ℝ} (hd : MemLp d 2 (Measure.pi (fun _ : Fin n => p)))
    (hd0 : ∀ z, 0 ≤ d z) :
    let r := {z : Fin n → Ω | ∃ k, 0 ≤ g * noise (z k)}.indicator
      (fun z => |g| / Real.sqrt (∑ k : Fin n,
        (1 - (999 / 1000 : ℝ)) * (999 / 1000 : ℝ) ^ (i.succAbove k : ℕ) * (g + noise (z k)) ^ 2))
    Integrable (fun z : Fin (n + 1) → Ω =>
      (L + K (z i)) * d (fun j => z (i.succAbove j)) * r (fun j => z (i.succAbove j)))
        (Measure.pi (fun _ : Fin (n + 1) => p)) ∧
      (∫ z : Fin (n + 1) → Ω,
        (L + K (z i)) * d (fun j => z (i.succAbove j)) * r (fun j => z (i.succAbove j))
        ∂Measure.pi (fun _ : Fin (n + 1) => p)) ≤
      (L + M) * 127 * Real.sqrt (∫ z, d z ^ 2 ∂Measure.pi (fun _ : Fin n => p)) := by
  classical
  dsimp only
  let b : Fin n → ℝ := fun k => (1 - (999 / 1000 : ℝ)) * (999 / 1000 : ℝ) ^ (i.succAbove k : ℕ)
  let r := {z : Fin n → Ω | ∃ k, 0 ≤ g * noise (z k)}.indicator
    (fun z => |g| / Real.sqrt (∑ k, b k * (g + noise (z k)) ^ 2))
  have hh := truncated_inverse_root_noise_moment hm hsym
    (β := (999 / 1000 : ℝ)) (by norm_num) (by norm_num) hg b
    (fun k => deleted_index_weight_lower i k (by norm_num) (by norm_num))
  have hr0 (z) : 0 ≤ r z := by
    apply Set.indicator_nonneg
    intro _ _
    positivity
  have hr2 : (∫ z, r z ^ 2 ∂Measure.pi (fun _ : Fin n => p)) ≤ (127 : ℝ) ^ 2 :=
    hh.2.trans default_small_ball_constant
  exact deleted_first_moment_factor_bound i hL hK hK0 hM (by norm_num) hd hh.1 hd0 hr0 hr2


lemma memLp_two_prod_of_uniform_square_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [SFinite P] {r : Ω × Ξ → ℝ} {κ : ℝ}
    (hr : Measurable r) (hs : ∀ x, MemLp (fun y => r (x, y)) 2 P)
    (hb : ∀ x, (∫ y, r (x, y) ^ 2 ∂P) ≤ κ ^ 2) :
    MemLp r 2 (p.prod P) ∧ (∫ z, r z ^ 2 ∂p.prod P) ≤ κ ^ 2 := by
  have hm : AEStronglyMeasurable (fun z => r z ^ 2) (p.prod P) :=
    (hr.pow_const 2).aestronglyMeasurable
  have hni : Integrable (fun x => ∫ y, ‖r (x, y) ^ 2‖ ∂P) p := by
    apply (integrable_const (κ ^ 2)).mono' hm.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simpa only [Real.norm_eq_abs, abs_sq] using hb x
  have hi : Integrable (fun z => r z ^ 2) (p.prod P) :=
    (integrable_prod_iff hm).mpr ⟨Filter.Eventually.of_forall (fun x => (hs x).integrable_sq), hni⟩
  refine ⟨(memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mpr hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : Ω, κ ^ 2 ∂p := integral_mono hi.integral_prod_left (integrable_const _) hb
    _ = κ ^ 2 := by simp

lemma prefix_truncated_inverse_root_moment {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {G : X → ℝ} {noise : X → Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    {n : ℕ} {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (b : Fin n → ℝ)
    (hb : ∀ k : Fin n, (1 - β) * β ^ ((k : ℕ) + 1) ≤ b k) :
    let r := {w : X × (Fin n → Ω) | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}.indicator
      (fun w => |G w.1| / Real.sqrt (∑ k, b k * (G w.1 + noise w.1 (w.2 k)) ^ 2))
    MemLp r 2 (P.prod (Measure.pi (fun _ : Fin n => p))) ∧
      (∫ w, r w ^ 2 ∂P.prod (Measure.pi (fun _ : Fin n => p))) ≤
        8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  classical
  dsimp only
  let Q := Measure.pi (fun _ : Fin n => p)
  let A : Set (X × (Fin n → Ω)) := {w | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}
  let r := A.indicator
    (fun w => |G w.1| / Real.sqrt (∑ k, b k * (G w.1 + noise w.1 (w.2 k)) ^ 2))
  have hn (k : Fin n) : Measurable (fun w : X × (Fin n → Ω) => noise w.1 (w.2 k)) :=
    hm.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const ((hG.comp measurable_fst).mul (hn k))
  have hr : Measurable r := by
    apply Measurable.indicator _ hA
    have hab : Measurable (fun w : X × (Fin n → Ω) => |G w.1|) := by fun_prop
    apply hab.div
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul (((hG.comp measurable_fst).add (hn k)).pow_const 2)
  let C := 8 / ((1 - β) * (1 - 1 / (2 * β)))
  have hC : 0 ≤ C := by
    have hb0 : 0 < β := by linarith
    have hq : 1 / (2 * β) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    dsimp [C]
    positivity
  have hs (x : X) : MemLp (fun z => r (x, z)) 2 Q ∧ (∫ z, r (x, z) ^ 2 ∂Q) ≤ C := by
    by_cases hx : G x = 0
    · have he : (fun z => r (x, z)) = fun _ => (0 : ℝ) := by
        funext z
        simp [r, Set.indicator, hx]
      have hz (z : Fin n → Ω) : r (x, z) = 0 := congrFun he z
      simp only [hz]
      simpa only [zero_pow (by decide : 2 ≠ 0), integral_zero] using
        And.intro (memLp_const (0 : ℝ) : MemLp (fun _ : Fin n → Ω => (0 : ℝ)) 2 Q) hC
    · have hh := truncated_inverse_root_noise_moment
        (hm.comp measurable_prodMk_left) (hsym x) hβ hβ1 hx b hb
      exact hh
  have hh := memLp_two_prod_of_uniform_square_moment (p := P) (P := Q) (κ := Real.sqrt C) hr (fun x => (hs x).1)
    (fun x => by simpa only [Real.sq_sqrt hC] using (hs x).2)
  change MemLp r 2 (P.prod Q) ∧ (∫ z, r z ^ 2 ∂P.prod Q) ≤ C
  simpa only [Real.sq_sqrt hC] using hh



lemma prefix_all_failure {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {G : X → ℝ} {noise : X → Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    (n : ℕ) :
    (P.prod (Measure.pi (fun _ : Fin n => p))).real
      {w : X × (Fin n → Ω) | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}ᶜ ≤
      (1 / 2 : ℝ) ^ n := by
  classical
  let Q := Measure.pi (fun _ : Fin n => p)
  let A : Set (X × (Fin n → Ω)) := {w | ∀ k, G w.1 * noise w.1 (w.2 k) < 0}
  have hn (k : Fin n) : Measurable (fun w : X × (Fin n → Ω) => noise w.1 (w.2 k)) :=
    hm.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt ((hG.comp measurable_fst).mul (hn k)) measurable_const
  have hs (x : X) : Q.real {z | (x,z) ∈ A} ≤ (1 / 2 : ℝ) ^ n := by
    apply product_all_failure (μ := p) (fun _ : Fin n => {ω | G x * noise x ω < 0})
    intro j
    have hx : Measurable (noise x) := hm.comp measurable_prodMk_left
    have hh := symmetric_product_negative (hsym x) (G x)
    have hset : MeasurableSet {z : ℝ | G x * z < 0} :=
      measurableSet_lt (measurable_const.mul measurable_id) measurable_const
    rw [map_measureReal_apply hx hset] at hh
    exact hh
  have hi : Integrable (A.indicator (1 : X × (Fin n → Ω) → ℝ)) (P.prod Q) :=
    (integrable_const 1).indicator hA
  have he : {w : X × (Fin n → Ω) | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}ᶜ = A := by
    ext w
    simp [A]
  rw [he]
  change (P.prod Q).real A ≤ _
  rw [← integral_indicator_one hA, integral_prod _ hi]
  calc
    _ ≤ ∫ _ : X, (1 / 2 : ℝ) ^ n ∂P := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro x
      have hx : MeasurableSet {z | (x,z) ∈ A} := hA.preimage measurable_prodMk_left
      have heq : (fun y => A.indicator (1 : X × (Fin n → Ω) → ℝ) (x,y)) =
          {z | (x,z) ∈ A}.indicator (1 : (Fin n → Ω) → ℝ) := by
        funext y
        simp [Set.indicator]
      change (∫ y, A.indicator (1 : X × (Fin n → Ω) → ℝ) (x,y) ∂Q) ≤ _
      rw [heq, integral_indicator_one hx]
      exact hs x
    _ = (1 / 2 : ℝ) ^ n := by simp



lemma prefix_deleted_first_moment_factor_bound {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {n : ℕ} (i : Fin (n + 1))
    {K : Ω → ℝ} {d r : X × (Fin n → Ω) → ℝ} {L M κ : ℝ}
    (hL : 0 ≤ L) (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω)
    (hM : (∫ ω, K ω ∂p) ≤ M) (hκ : 0 ≤ κ)
    (hd : MemLp d 2 (P.prod (Measure.pi (fun _ : Fin n => p))))
    (hr : MemLp r 2 (P.prod (Measure.pi (fun _ : Fin n => p))))
    (hd0 : ∀ ω, 0 ≤ d ω) (hr0 : ∀ ω, 0 ≤ r ω)
    (hr2 : (∫ ω, r ω ^ 2 ∂P.prod (Measure.pi (fun _ : Fin n => p))) ≤ κ ^ 2) :
    Integrable (fun z : X × (Fin (n + 1) → Ω) =>
      (L + K (z.2 i)) * d (z.1, fun j => z.2 (i.succAbove j)) *
        r (z.1, fun j => z.2 (i.succAbove j)))
        (P.prod (Measure.pi (fun _ : Fin (n + 1) => p))) ∧
      (∫ z : X × (Fin (n + 1) → Ω),
        (L + K (z.2 i)) * d (z.1, fun j => z.2 (i.succAbove j)) *
          r (z.1, fun j => z.2 (i.succAbove j))
        ∂P.prod (Measure.pi (fun _ : Fin (n + 1) => p))) ≤
      (L + M) * κ * Real.sqrt (∫ ω, d ω ^ 2 ∂P.prod (Measure.pi (fun _ : Fin n => p))) := by
  let Q := Measure.pi (fun _ : Fin n => p)
  have hp1 := (MeasurePreserving.id P).prod (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => p) i)
  have hp2 := (measurePreserving_prodAssoc P p Q).symm MeasurableEquiv.prodAssoc
  have hp3 := (Measure.measurePreserving_swap (μ := P) (ν := p)).prod (MeasurePreserving.id Q)
  have hp4 := measurePreserving_prodAssoc p P Q
  have hp := hp4.comp (hp3.comp (hp2.comp hp1))
  let F : (X × (Fin (n + 1) → Ω)) → Ω × (X × (Fin n → Ω)) :=
    fun z => (z.2 i, (z.1, fun j => z.2 (i.succAbove j)))
  change MeasurePreserving F (P.prod (Measure.pi (fun _ : Fin (n + 1) => p))) (p.prod (P.prod Q)) at hp
  have hh := first_moment_factor_bound hL hK hK0 hM hκ hd hr hd0 hr0 hr2
  refine ⟨hp.integrable_comp_of_integrable hh.1, ?_⟩
  have hi := integral_map hp.measurable.aemeasurable
    (hp.map_eq.symm ▸ hh.1.aestronglyMeasurable)
  rw [hp.map_eq] at hi
  exact hi.symm.trans_le hh.2



lemma weighted_history_difference_l1 {ι : Type*} [Fintype ι] (a b z w : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ i, 0 < b i) :
    |(∑ i, a i * z i) / (δ + Real.sqrt (∑ i, b i * z i ^ 2)) -
      (∑ i, a i * w i) / (δ + Real.sqrt (∑ i, b i * w i ^ 2))| ≤
    2 * Real.sqrt (∑ i, a i ^ 2 / b i) *
      ((∑ i, Real.sqrt (b i) * |z i - w i|) /
        (δ + Real.sqrt (∑ i, b i * w i ^ 2))) := by
  apply (weighted_history_difference a b z w hδ hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (min_le_right _ _).trans
  exact div_le_div_of_nonneg_right
    (LongTails.Proofs.AdaptiveHistoryFinite.weightedRoot_le b (fun i => z i - w i) (fun i => (hb i).le)) (by positivity)


lemma capped_history_tracking_good {ι : Type*} [Fintype ι] (b z w D R : ι → ℝ)
    {δ g C E : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hb : ∀ i, 0 ≤ b i)
    (hD : ∀ i, |z i-w i| ≤ D i) (hR : ∀ i, 0 < R i)
    (hRle : ∀ i, R i ≤ Real.sqrt (∑ j,b j*w j^2))
    (hcap : E ≤ C*min 1 (Real.sqrt (∑ i,b i*(z i-w i)^2)/(δ+Real.sqrt (∑ i,b i*w i^2)))) :
    |g| *E ≤ C * ∑ i, Real.sqrt (b i)*D i*(|g|/R i) := by
  have hD0 (i) : 0 ≤ D i := (abs_nonneg _).trans (hD i)
  have hl1 : Real.sqrt (∑ i,b i*(z i-w i)^2) ≤ ∑ i,Real.sqrt (b i)*D i := by
    apply (LongTails.Proofs.AdaptiveHistoryFinite.weightedRoot_le b (fun i => z i-w i) hb).trans
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hD i) (Real.sqrt_nonneg _)
  have he : E ≤ C*((∑ i,Real.sqrt (b i)*D i)/(δ+Real.sqrt (∑ i,b i*w i^2))) := by
    apply hcap.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_right hl1 (by positivity)
  calc
    _ ≤ |g| *(C*((∑ i,Real.sqrt (b i)*D i)/(δ+Real.sqrt (∑ i,b i*w i^2)))) :=
      mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ = C*∑ i,Real.sqrt (b i)*D i*(|g|/(δ+Real.sqrt (∑ j,b j*w j^2))) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.sqrt_nonneg _) (hD0 i))
      exact div_le_div_of_nonneg_left (abs_nonneg _) (hR i) (by linarith [hRle i])

lemma weighted_history_tracking_good {ι : Type*} [Fintype ι] (a b z w D R : ι → ℝ)
    {δ g : ℝ} (hδ : 0 < δ) (hb : ∀ i, 0 < b i)
    (hD : ∀ i, |z i - w i| ≤ D i) (hR : ∀ i, 0 < R i)
    (hRle : ∀ i, R i ≤ Real.sqrt (∑ j, b j * w j ^ 2)) :
    |g| * |(∑ i, a i * z i) / (δ + Real.sqrt (∑ i, b i * z i ^ 2)) -
      (∑ i, a i * w i) / (δ + Real.sqrt (∑ i, b i * w i ^ 2))| ≤
    2 * Real.sqrt (∑ i, a i ^ 2 / b i) *
      ∑ i, Real.sqrt (b i) * D i * (|g| / R i) := by
  exact capped_history_tracking_good b z w D R hδ (by positivity) (fun i => (hb i).le)
    hD hR hRle (weighted_history_difference a b z w hδ hb)

lemma deleted_weighted_root_le {n : ℕ} (b w : Fin (n+1) → ℝ)
    (hb : ∀ i, 0 ≤ b i) (i : Fin (n+1)) :
    Real.sqrt (∑ j : Fin n, b (i.succAbove j) * w (i.succAbove j)^2) ≤
      Real.sqrt (∑ j, b j * w j^2) := by
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_succAbove (fun j => b j * w j^2) i]
  exact le_add_of_nonneg_left (mul_nonneg (hb i) (sq_nonneg _))

lemma deleted_weighted_root_pos {n : ℕ} (b noise : Fin (n+1) → ℝ)
    {g : ℝ} (hg : g ≠ 0) (hb : ∀ i, 0 < b i) (i : Fin (n+1))
    (hs : ∃ j : Fin n, 0 ≤ g * noise (i.succAbove j)) :
    0 < Real.sqrt (∑ j : Fin n, b (i.succAbove j) * (g+noise (i.succAbove j))^2) := by
  obtain ⟨j,hj⟩ := hs
  apply Real.sqrt_pos.mpr
  have hw : 0 < (g+noise (i.succAbove j))^2 := by
    nlinarith [sq_nonneg (noise (i.succAbove j)), sq_pos_of_ne_zero hg]
  apply (mul_pos (hb (i.succAbove j)) hw).trans_le
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hb (i.succAbove k)).le (sq_nonneg (g+noise (i.succAbove k)))) (Finset.mem_univ j)

lemma capped_history_tracking_split {n : ℕ} (b z noise D : Fin (n+1) → ℝ)
    {δ g C E : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hb : ∀ i, 0 < b i)
    (hD : ∀ i, |z i-(g+noise i)| ≤ D i)
    (hcap : E ≤ C*min 1 (Real.sqrt (∑ i,b i*(z i-(g+noise i))^2)/(δ+Real.sqrt (∑ i,b i*(g+noise i)^2)))) :
    let r := fun i => if ∃ j : Fin n, 0 ≤ g*noise (i.succAbove j) then
      |g|/Real.sqrt (∑ j : Fin n,b (i.succAbove j)*(g+noise (i.succAbove j))^2) else 0
    let bad := if ∃ i : Fin (n+1), ∀ j : Fin n,g*noise (i.succAbove j)<0 then (1 : ℝ) else 0
    |g| *E ≤ C*((∑ i,Real.sqrt (b i)*D i*r i)+|g| *bad) := by
  classical
  dsimp only
  have hD0 (i) : 0 ≤ D i := (abs_nonneg _).trans (hD i)
  by_cases hg : g=0
  · subst g
    simp
  by_cases hgood : ∀ i : Fin (n+1), ∃ j : Fin n,0 ≤ g*noise (i.succAbove j)
  · have hbad : ¬∃ i : Fin (n+1), ∀ j : Fin n,g*noise (i.succAbove j)<0 := by
      simpa only [not_exists,not_forall,not_lt] using hgood
    simp only [hgood,ite_true,hbad,ite_false,mul_zero,add_zero]
    exact capped_history_tracking_good b z (fun i => g+noise i) D
      (fun i => Real.sqrt (∑ j : Fin n,b (i.succAbove j)*(g+noise (i.succAbove j))^2))
      hδ hC (fun i => (hb i).le) hD
      (fun i => deleted_weighted_root_pos b noise hg hb i (hgood i))
      (fun i => deleted_weighted_root_le b (fun j => g+noise j) (fun j => (hb j).le) i) hcap
  · have hbad : ∃ i : Fin (n+1), ∀ j : Fin n,g*noise (i.succAbove j)<0 := by
      simpa only [not_forall,not_exists,not_le] using hgood
    simp only [hbad,ite_true,mul_one]
    have hc : E ≤ C := hcap.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) _) hC)
    have hf := mul_le_mul_of_nonneg_left hc (abs_nonneg g)
    have hsum : 0 ≤ ∑ i : Fin (n+1),Real.sqrt (b i)*D i*
        (if ∃ j : Fin n,0 ≤ g*noise (i.succAbove j) then
          |g|/Real.sqrt (∑ j : Fin n,b (i.succAbove j)*(g+noise (i.succAbove j))^2) else 0) := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hD0 i))
      split_ifs <;> positivity
    nlinarith [mul_nonneg hC hsum]

lemma weighted_history_tracking_split {n : ℕ} (a b z noise D : Fin (n+1) → ℝ)
    {δ g : ℝ} (hδ : 0 < δ) (hb : ∀ i, 0 < b i)
    (hD : ∀ i, |z i - (g+noise i)| ≤ D i) :
    let r := fun i => if ∃ j : Fin n, 0 ≤ g * noise (i.succAbove j) then
      |g| / Real.sqrt (∑ j : Fin n, b (i.succAbove j) * (g+noise (i.succAbove j))^2) else 0
    let bad := if ∃ i : Fin (n+1), ∀ j : Fin n, g * noise (i.succAbove j) < 0 then (1 : ℝ) else 0
    |g| * |(∑ i, a i * z i) / (δ + Real.sqrt (∑ i, b i * z i ^ 2)) -
      (∑ i, a i * (g+noise i)) / (δ + Real.sqrt (∑ i, b i * (g+noise i)^2))| ≤
    2 * Real.sqrt (∑ i, a i ^ 2 / b i) *
      ((∑ i, Real.sqrt (b i) * D i * r i) + |g| * bad) := by
  exact capped_history_tracking_split b z noise D hδ (by positivity) hb hD
    (weighted_history_difference a b z (fun i => g+noise i) hδ hb)

lemma prefix_deleted_failure {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {G : X → ℝ} {noise : X → Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    {n : ℕ} (i : Fin (n+1)) :
    (P.prod (Measure.pi (fun _ : Fin (n+1) => p))).real
      {w : X × (Fin (n+1) → Ω) | ∀ j : Fin n, G w.1 * noise w.1 (w.2 (i.succAbove j)) < 0} ≤
      (1 / 2 : ℝ) ^ n := by
  let Q := Measure.pi (fun _ : Fin n => p)
  have hp0 := (measurePreserving_snd (μ := p) (ν := Q)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => p) i)
  have hp := (MeasurePreserving.id P).prod hp0
  let A : Set (X × (Fin n → Ω)) := {w | ∃ j, 0 ≤ G w.1 * noise w.1 (w.2 j)}ᶜ
  have hA : MeasurableSet A := by
    apply MeasurableSet.compl
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    apply measurableSet_le measurable_const
    exact (hG.comp measurable_fst).mul (hm.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))
  have hh := prefix_all_failure (P := P) hG hm hsym n
  change (P.prod Q).real A ≤ _ at hh
  rw [← hp.map_eq, map_measureReal_apply hp.measurable hA] at hh
  convert hh using 1
  congr 1
  ext w
  simp [A, Fin.removeNth]

lemma prefix_any_deleted_failure {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {G : X → ℝ} {noise : X → Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    (n : ℕ) :
    (P.prod (Measure.pi (fun _ : Fin (n+1) => p))).real
      {w : X × (Fin (n+1) → Ω) | ∃ i : Fin (n+1), ∀ j : Fin n,
        G w.1 * noise w.1 (w.2 (i.succAbove j)) < 0} ≤
      (n+1) * (1 / 2 : ℝ) ^ n := by
  simp only [Set.ofPred_exists]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _ : Fin (n+1), (1 / 2 : ℝ)^n := Finset.sum_le_sum fun i _ =>
      prefix_deleted_failure hG hm hsym i
    _ = _ := by simp



lemma integral_tracking_split {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → ℝ} {U : ι → Ω → ℝ}
    {A : Set Ω} {C B ρ : ℝ} {bounds : ι → ℝ}
    (hA : MeasurableSet A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hu : AEStronglyMeasurable u P) (hu0 : ∀ᵐ ω ∂P, 0 ≤ u ω)
    (hU : ∀ i, Integrable (U i) P)
    (hbound : ∀ᵐ ω ∂P, u ω ≤ C * ((∑ i, U i ω) + B * A.indicator (1 : Ω → ℝ) ω))
    (hI : ∀ i, (∫ ω, U i ω ∂P) ≤ bounds i) (hprob : P.real A ≤ ρ) :
    Integrable u P ∧ (∫ ω, u ω ∂P) ≤ C * ((∑ i, bounds i) + B * ρ) := by
  have hsum : Integrable (fun ω => ∑ i, U i ω) P := integrable_finsetSum _ (fun i _ => hU i)
  have hind : Integrable (A.indicator (1 : Ω → ℝ)) P := (integrable_const 1).indicator hA
  have hi := (hsum.add (hind.const_mul B)).const_mul C
  have hui : Integrable u P := hi.mono' hu (by
    filter_upwards [hu0,hbound] with ω h0 hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0, Pi.add_apply] using hb)
  refine ⟨hui, ?_⟩
  calc
    _ ≤ ∫ ω, C * ((∑ i, U i ω) + B * A.indicator (1 : Ω → ℝ) ω) ∂P :=
      integral_mono_ae hui hi hbound
    _ = C * ((∑ i, ∫ ω, U i ω ∂P) + B * P.real A) := by
      rw [integral_const_mul, integral_add hsum (hind.const_mul B),
        integral_finsetSum _ (fun i _ => hU i), integral_const_mul, integral_indicator_one hA]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add (Finset.sum_le_sum fun i _ => hI i) (mul_le_mul_of_nonneg_left hprob hB)



lemma default_prefix_deleted_tracking_term {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G : X → ℝ} {noise : X → Ω → ℝ} {K : Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    {n : ℕ} (i : Fin (n+1)) {L M : ℝ} (hL : 0 ≤ L)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω) (hM : (∫ ω, K ω ∂p) ≤ M)
    {d : X × (Fin n → Ω) → ℝ} (hd : MemLp d 2 (P.prod (Measure.pi (fun _ : Fin n => p))))
    (hd0 : ∀ z, 0 ≤ d z) :
    let r := {z : X × (Fin n → Ω) | ∃ k, 0 ≤ G z.1 * noise z.1 (z.2 k)}.indicator
      (fun z => |G z.1| / Real.sqrt (∑ k : Fin n,
        (1-(999/1000 : ℝ)) * (999/1000 : ℝ)^(i.succAbove k : ℕ) *
          (G z.1 + noise z.1 (z.2 k))^2))
    Integrable (fun z : X × (Fin (n+1) → Ω) =>
      (L+K (z.2 i)) * d (z.1,fun j => z.2 (i.succAbove j)) *
        r (z.1,fun j => z.2 (i.succAbove j)))
        (P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ∧
      (∫ z : X × (Fin (n+1) → Ω),
        (L+K (z.2 i)) * d (z.1,fun j => z.2 (i.succAbove j)) *
          r (z.1,fun j => z.2 (i.succAbove j))
        ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ≤
      (L+M)*127*Real.sqrt (∫ z, d z^2 ∂P.prod (Measure.pi (fun _ : Fin n => p))) := by
  dsimp only
  let b : Fin n → ℝ := fun k => (1-(999/1000 : ℝ)) * (999/1000 : ℝ)^(i.succAbove k : ℕ)
  let r := {z : X × (Fin n → Ω) | ∃ k, 0 ≤ G z.1 * noise z.1 (z.2 k)}.indicator
    (fun z => |G z.1| / Real.sqrt (∑ k, b k * (G z.1 + noise z.1 (z.2 k))^2))
  have hh := prefix_truncated_inverse_root_moment (P := P) hG hm hsym
    (β := (999/1000 : ℝ)) (by norm_num) (by norm_num) b
    (fun k => deleted_index_weight_lower i k (by norm_num) (by norm_num))
  have hr0 (z) : 0 ≤ r z := by
    apply Set.indicator_nonneg
    intro _ _
    positivity
  have hr2 : (∫ z, r z^2 ∂P.prod (Measure.pi (fun _ : Fin n => p))) ≤ (127 : ℝ)^2 :=
    hh.2.trans default_small_ball_constant
  exact prefix_deleted_first_moment_factor_bound i hL hK hK0 hM (by norm_num) hd hh.1 hd0 hr0 hr2



lemma prefix_first_moment_multiplier {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {V : X → ℝ} {r : X × Ω → ℝ} {κ : ℝ}
    (hV : Measurable V) (hVi : Integrable V P) (hV0 : ∀ x, 0 ≤ V x)
    (hr : Measurable r) (hr0 : ∀ z, 0 ≤ r z) (hκ : 0 ≤ κ)
    (hs : ∀ x, MemLp (fun ω => r (x,ω)) 2 p)
    (hb : ∀ x, (∫ ω, r (x,ω)^2 ∂p) ≤ κ^2) :
    Integrable (fun z => V z.1 * r z) (P.prod p) ∧
      (∫ z, V z.1 * r z ∂P.prod p) ≤ κ * (∫ x, V x ∂P) := by
  have hrI (x) : Integrable (fun ω => r (x,ω)) p := (hs x).integrable (by norm_num)
  have hrB (x) : (∫ ω, r (x,ω) ∂p) ≤ κ := by
    have hh := integral_mul_le_square_moments
      (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 p) (hs x)
      (fun _ => by norm_num) (fun ω => hr0 (x,ω))
    simp only [one_mul, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one,
      Real.sqrt_one, one_mul] at hh
    exact hh.trans ((Real.sqrt_le_left hκ).mpr (hb x))
  have hm : AEStronglyMeasurable (fun z => V z.1 * r z) (P.prod p) :=
    ((hV.comp measurable_fst).mul hr).aestronglyMeasurable
  have hni : Integrable (fun x => ∫ ω, ‖V x * r (x,ω)‖ ∂p) P := by
    apply (hVi.mul_const κ).mono' hm.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hV0 x) (hr0 _)), integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hrB x) (hV0 x)
  have hi : Integrable (fun z => V z.1 * r z) (P.prod p) :=
    (integrable_prod_iff hm).mpr ⟨Filter.Eventually.of_forall (fun x => (hrI x).const_mul (V x)), hni⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, V x * κ ∂P := by
      apply integral_mono hi.integral_prod_left (hVi.mul_const κ)
      intro x
      change (∫ y, V x * r (x,y) ∂p) ≤ V x * κ
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hrB x) (hV0 x)
    _ = κ * (∫ x, V x ∂P) := by rw [integral_mul_const]; ring


open LongTails.Proofs.AdaptiveHistoryAlgebra

lemma old_history_difference {m₁ m₀ v₀ v₁ δ : ℝ}
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hδ : 0 < δ)
    (hm₁ : m₁^2 ≤ 64*(v₀+v₁)) (hm₀ : m₀^2 ≤ 64*v₀)
    (hd : |m₁-m₀| ≤ 8*Real.sqrt v₁) :
    |m₁/(δ+Real.sqrt (v₀+v₁)) - m₀/(δ+Real.sqrt v₀)| ≤
      16 * min 1 (Real.sqrt v₁/(δ+Real.sqrt v₀)) := by
  have hr : |Real.sqrt (v₀+v₁) - Real.sqrt v₀| ≤ Real.sqrt v₁ := by
    have hle : Real.sqrt v₀ ≤ Real.sqrt (v₀+v₁) := Real.sqrt_le_sqrt (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith [Real.sq_sqrt hv₀, Real.sq_sqrt hv₁, Real.sq_sqrt (add_nonneg hv₀ hv₁),
      Real.sqrt_nonneg v₀, Real.sqrt_nonneg v₁, Real.sqrt_nonneg (v₀+v₁),
      mul_nonneg (Real.sqrt_nonneg v₀) (Real.sqrt_nonneg v₁)]
  simpa only [show (2 : ℝ)*8=16 by norm_num] using
    normalized_difference_capped (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hδ (by norm_num : (0 : ℝ) ≤ 8)
      (momentum_sqrt_bound (add_nonneg hv₀ hv₁) hm₁) (momentum_sqrt_bound hv₀ hm₀) hd hr

lemma old_history_difference_split {m₁ m₀ v₀ v₁ δ g : ℝ} (good : Prop) [Decidable good]
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hδ : 0 < δ)
    (hm₁ : m₁^2 ≤ 64*(v₀+v₁)) (hm₀ : m₀^2 ≤ 64*v₀)
    (hd : |m₁-m₀| ≤ 8*Real.sqrt v₁) (hgood : good → 0 < v₀) :
    |g| * |m₁/(δ+Real.sqrt (v₀+v₁)) - m₀/(δ+Real.sqrt v₀)| ≤
      16 * (Real.sqrt v₁ * (if good then |g|/Real.sqrt v₀ else 0) +
        |g| * (if good then 0 else 1)) := by
  have hh := old_history_difference hv₀ hv₁ hδ hm₁ hm₀ hd
  by_cases hg : good
  · simp only [hg, ite_true, mul_zero, add_zero]
    have hvp := Real.sqrt_pos.mpr (hgood hg)
    have hratio : Real.sqrt v₁/(δ+Real.sqrt v₀) ≤ Real.sqrt v₁/Real.sqrt v₀ :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hvp (by linarith)
    have hc := hh.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hratio) (by norm_num))
    have hf := mul_le_mul_of_nonneg_left hc (abs_nonneg g)
    convert hf using 1; ring
  · simp only [hg, ite_false, mul_zero, zero_add, mul_one]
    have hc := hh.trans (mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) _) (by norm_num))
    have hf := mul_le_mul_of_nonneg_left hc (abs_nonneg g)
    nlinarith


open LongTails.Proofs.AdaptiveHistoryAlgebra

lemma weighted_history_offset_difference {ι : Type*} [Fintype ι] (a b z w : ι → ℝ)
    {m R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hb : ∀ i, 0 < b i)
    (hc : Real.sqrt (∑ i,a i^2/b i) ≤ 8)
    (hz : (m+∑ i,a i*z i)^2 ≤ 64*(R+∑ i,b i*z i^2))
    (hw : (m+∑ i,a i*w i)^2 ≤ 64*(R+∑ i,b i*w i^2)) :
    |(m+∑ i,a i*z i)/(δ+Real.sqrt (R+∑ i,b i*z i^2)) -
      (m+∑ i,a i*w i)/(δ+Real.sqrt (R+∑ i,b i*w i^2))| ≤
      16*min 1 (Real.sqrt (∑ i,b i*(z i-w i)^2)/(δ+Real.sqrt (∑ i,b i*w i^2))) := by
  have hsz : 0 ≤ ∑ i,b i*z i^2 := Finset.sum_nonneg fun i _ => mul_nonneg (hb i).le (sq_nonneg _)
  have hsw : 0 ≤ ∑ i,b i*w i^2 := Finset.sum_nonneg fun i _ => mul_nonneg (hb i).le (sq_nonneg _)
  have hn : |(m+∑ i,a i*z i)-(m+∑ i,a i*w i)| ≤ 8*Real.sqrt (∑ i,b i*(z i-w i)^2) := by
    have hh := abs_real_inner_le_norm
      (WithLp.toLp 2 (fun i => a i/Real.sqrt (b i)) : EuclideanSpace ℝ ι)
      (weightedVector b (fun i => z i-w i))
    rw [weightedVector_inner a b _ hb, weighted_coeff_norm a b (fun i => (hb i).le),
      weightedVector_norm b _ (fun i => (hb i).le)] at hh
    have he : (m+∑ i,a i*z i)-(m+∑ i,a i*w i) = ∑ i,a i*(z i-w i) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have hr := sqrt_offset_norm_difference hR (weightedVector b z) (weightedVector b w)
  rw [weightedVector_sub, weightedVector_norm b z (fun i => (hb i).le),
    weightedVector_norm b w (fun i => (hb i).le), weightedVector_norm b _ (fun i => (hb i).le),
    Real.sq_sqrt hsz, Real.sq_sqrt hsw] at hr
  have hh := normalized_difference_capped (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hδ
    (by norm_num : (0 : ℝ) ≤ 8) (momentum_sqrt_bound (add_nonneg hR hsz) hz)
    (momentum_sqrt_bound (add_nonneg hR hsw) hw) hn hr
  simp only [show (2 : ℝ)*8=16 by norm_num] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply min_le_min_left
  apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
  have hs := Real.sqrt_le_sqrt (show (∑ i,b i*w i^2) ≤ R+∑ i,b i*w i^2 by linarith)
  linarith



lemma default_prefix_capped_tracking {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {n : ℕ}
    {G : X → ℝ} {noise : X → Ω → ℝ} {K : Ω → ℝ}
    {E : X × (Fin (n+1) → Ω) → ℝ}
    {Z : Fin (n+1) → X × (Fin (n+1) → Ω) → ℝ}
    {d : Fin (n+1) → X × (Fin n → Ω) → ℝ} {L M B δ : ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    (hE : Measurable E) (hE0 : ∀ w, 0 ≤ E w) (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hGB : ∀ x, |G x| ≤ B)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p, 0 ≤ K ω) (hM : (∫ ω, K ω ∂p) ≤ M)
    (hd : ∀ i, MemLp (d i) 2 (P.prod (Measure.pi (fun _ : Fin n => p))))
    (hd0 : ∀ i z, 0 ≤ d i z)
    (hcap : ∀ᵐ w ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p)),
      E w ≤ 16 * min 1 (Real.sqrt (∑ i : Fin (n+1),
        (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(Z i w-(G w.1+noise w.1 (w.2 i)))^2) /
        (δ+Real.sqrt (∑ i : Fin (n+1), (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*
          (G w.1+noise w.1 (w.2 i))^2))))
    (herror : ∀ᵐ w ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p)), ∀ i,
      |Z i w - (G w.1 + noise w.1 (w.2 i))| ≤
        (L+K (w.2 i)) * d i (w.1,fun j => w.2 (i.succAbove j))) :
    let b := fun i : Fin (n+1) => (1-(999/1000 : ℝ)) * (999/1000 : ℝ)^(i : ℕ)
    let u := fun w : X × (Fin (n+1) → Ω) =>
      |G w.1| * E w
    Integrable u (P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ∧
      (∫ w, u w ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ≤
      16 * ((L+M)*127 * (∑ i, Real.sqrt (b i) *
        Real.sqrt (∫ z, d i z^2 ∂P.prod (Measure.pi (fun _ : Fin n => p)))) +
          B * ((n+1)*(1/2 : ℝ)^n)) := by
  classical
  dsimp only
  let Q := P.prod (Measure.pi (fun _ : Fin (n+1) => p))
  let Qd := P.prod (Measure.pi (fun _ : Fin n => p))
  let b := fun i : Fin (n+1) => (1-(999/1000 : ℝ)) * (999/1000 : ℝ)^(i : ℕ)
  let u := fun w : X × (Fin (n+1) → Ω) =>
    |G w.1| * E w
  let r := fun i : Fin (n+1) =>
    {z : X × (Fin n → Ω) | ∃ k, 0 ≤ G z.1 * noise z.1 (z.2 k)}.indicator
      (fun z => |G z.1| / Real.sqrt (∑ k : Fin n, b (i.succAbove k) * (G z.1+noise z.1 (z.2 k))^2))
  let U := fun i (w : X × (Fin (n+1) → Ω)) => Real.sqrt (b i) *
    ((L+K (w.2 i)) * d i (w.1,fun j => w.2 (i.succAbove j)) * r i (w.1,fun j => w.2 (i.succAbove j)))
  let A : Set (X × (Fin (n+1) → Ω)) :=
    {w | ∃ i : Fin (n+1), ∀ j : Fin n, G w.1 * noise w.1 (w.2 (i.succAbove j)) < 0}
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have hr0 (i z) : 0 ≤ r i z := by
    apply Set.indicator_nonneg
    intro _ _
    positivity
  have hn (i : Fin (n+1)) : Measurable (fun w : X × (Fin (n+1) → Ω) => noise w.1 (w.2 i)) :=
    hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_exists, Set.ofPred_forall]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iInter fun j =>
      measurableSet_lt ((hG.comp measurable_fst).mul (hn (i.succAbove j))) measurable_const
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hterm (i) := default_prefix_deleted_tracking_term (P := P) hG hm hsym i hL hK hK0 hM (hd i) (hd0 i)
  have hUi (i) : Integrable (U i) Q := (hterm i).1.const_mul (Real.sqrt (b i))
  have hIb (i) : (∫ w, U i w ∂Q) ≤ Real.sqrt (b i) * ((L+M)*127*Real.sqrt (∫ z,d i z^2 ∂Qd)) := by
    rw [show U i = fun w => Real.sqrt (b i) * ((L+K (w.2 i)) * d i (w.1,fun j => w.2 (i.succAbove j)) * r i (w.1,fun j => w.2 (i.succAbove j))) from rfl, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hterm i).2 (Real.sqrt_nonneg _)
  have hbound : ∀ᵐ w ∂Q, u w ≤ 16 * ((∑ i, U i w) + B*A.indicator (1 : X × (Fin (n+1) → Ω) → ℝ) w) := by
    filter_upwards [herror,hcap] with w hw hc
    have hh := capped_history_tracking_split b (fun i => Z i w) (fun i => noise w.1 (w.2 i))
      (fun i => (L+K (w.2 i))*d i (w.1,fun j => w.2 (i.succAbove j)))
      hδ (by norm_num : (0 : ℝ) ≤ 16) hb hw hc
    have hA0 : 0 ≤ A.indicator (1 : X × (Fin (n+1) → Ω) → ℝ) w := Set.indicator_nonneg (fun _ _ => by norm_num) _
    have he : u w ≤ 16 * ((∑ i,U i w)+|G w.1| * A.indicator (1 : X × (Fin (n+1) → Ω) → ℝ) w) := by
      simpa only [u,r,U,A,Set.indicator,Set.mem_ofPred_eq,Pi.one_apply,mul_assoc] using hh
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add_right (mul_le_mul_of_nonneg_right (hGB w.1) hA0) _
  have hh := integral_tracking_split hA (by norm_num : (0 : ℝ) ≤ 16) hB hu.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => mul_nonneg (abs_nonneg _) (hE0 w))) hUi hbound hIb
    (prefix_any_deleted_failure (P := P) hG hm hsym n)
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring



lemma prefix_old_history_capped_tracking {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {n : ℕ}
    {G V : X → ℝ} {noise : X → Ω → ℝ} {E : X × (Fin n → Ω) → ℝ}
    {B δ : ℝ} (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    (hV : Measurable V) (hVi : Integrable V P) (hV0 : ∀ x, 0 ≤ V x)
    (hE : Measurable E) (hE0 : ∀ w, 0 ≤ E w)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) (hδ : 0 < δ)
    (hcap : ∀ᵐ w ∂P.prod (Measure.pi (fun _ : Fin n => p)),
      E w ≤ 16 * min 1 (V w.1 / (δ + Real.sqrt (∑ i : Fin n,
        (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(G w.1+noise w.1 (w.2 i))^2)))) :
    Integrable (fun w => |G w.1| * E w) (P.prod (Measure.pi (fun _ : Fin n => p))) ∧
      (∫ w, |G w.1| * E w ∂P.prod (Measure.pi (fun _ : Fin n => p))) ≤
        16 * (127 * (∫ x, V x ∂P) + B*(1/2 : ℝ)^n) := by
  classical
  let Q := Measure.pi (fun _ : Fin n => p)
  let b := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  let A : Set (X × (Fin n → Ω)) := {w | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}
  let R := fun w : X × (Fin n → Ω) => Real.sqrt (∑ k,b k*(G w.1+noise w.1 (w.2 k))^2)
  let r := A.indicator (fun w => |G w.1| / R w)
  have hn (k : Fin n) : Measurable (fun w : X × (Fin n → Ω) => noise w.1 (w.2 k)) :=
    hm.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const ((hG.comp measurable_fst).mul (hn k))
  have hR : Measurable R := by
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul (((hG.comp measurable_fst).add (hn k)).pow_const 2)
  have hr : Measurable r := by
    apply Measurable.indicator _ hA
    exact (by fun_prop : Measurable (fun w : X × (Fin n → Ω) => |G w.1|)).div hR
  have hr0 (w) : 0 ≤ r w := by apply Set.indicator_nonneg; intro _ _; positivity
  have hb (k : Fin n) : (1-(999/1000 : ℝ))*(999/1000 : ℝ)^((k : ℕ)+1) ≤ b k := by
    dsimp [b]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hs (x : X) : MemLp (fun z => r (x,z)) 2 Q ∧ (∫ z,r (x,z)^2 ∂Q) ≤ (127 : ℝ)^2 := by
    by_cases hx : G x = 0
    · have hz (z) : r (x,z)=0 := by simp [r,hx]
      simp only [hz,zero_pow (by decide : 2 ≠ 0),integral_zero]
      exact ⟨memLp_const 0, by norm_num⟩
    · have hh := truncated_inverse_root_noise_moment (hm.comp measurable_prodMk_left) (hsym x)
        (by norm_num : (1/2 : ℝ)<999/1000) (by norm_num : (999/1000 : ℝ)<1) hx b hb
      exact ⟨hh.1,hh.2.trans default_small_ball_constant⟩
  have hi := prefix_first_moment_multiplier hV hVi hV0 hr hr0 (by norm_num : (0 : ℝ)≤127)
    (fun x => (hs x).1) (fun x => (hs x).2)
  let U := fun (_ : Unit) (w : X × (Fin n → Ω)) => V w.1 * r w
  have hu : Measurable (fun w : X × (Fin n → Ω) => |G w.1| * E w) := by fun_prop
  have hbound : ∀ᵐ w ∂P.prod Q, |G w.1| * E w ≤
      16*((∑ i : Unit,U i w)+B*Aᶜ.indicator (1 : X × (Fin n → Ω) → ℝ) w) := by
    filter_upwards [hcap] with w hw
    simp only [Fintype.sum_unique,U]
    by_cases hg : G w.1=0
    · simp only [hg,abs_zero,zero_mul]
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (hV0 _) (hr0 _))
        (mul_nonneg hB (Set.indicator_nonneg (fun _ _ => by norm_num) _)))
    by_cases ha : w∈A
    · obtain ⟨k,hk⟩ := ha
      have hpos : 0 < R w := by
        apply Real.sqrt_pos.mpr
        apply lt_of_lt_of_le _ (Finset.single_le_sum (fun j _ => mul_nonneg (by dsimp [b]; positivity) (sq_nonneg _)) (Finset.mem_univ k))
        apply mul_pos (by dsimp [b]; positivity)
        apply sq_pos_of_ne_zero
        intro he
        have he' : noise w.1 (w.2 k) = -G w.1 := by linarith
        rw [he'] at hk
        nlinarith [sq_pos_of_ne_zero hg]
      have he := hw.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
      have hd : V w.1/(δ+R w) ≤ V w.1/R w :=
        div_le_div_of_nonneg_left (hV0 _) hpos (by linarith)
      have he' := mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hd (by norm_num))) (abs_nonneg (G w.1))
      have ham : w∈A := ⟨k,hk⟩
      simp only [r,Set.indicator_of_mem ham,Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ham),mul_zero,add_zero]
      convert he' using 1; ring
    · have he := hw.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
      simp only [mul_one] at he
      have he' := mul_le_mul_of_nonneg_left he (abs_nonneg (G w.1))
      simp only [r,Set.indicator_of_notMem ha,Set.indicator_of_mem (show w∈Aᶜ from ha),Pi.one_apply,mul_zero,zero_add,mul_one]
      nlinarith [hGB w.1]
  have hh := integral_tracking_split hA.compl (by norm_num : (0 : ℝ)≤16) hB hu.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => mul_nonneg (abs_nonneg _) (hE0 w)))
    (fun _ : Unit => hi.1) hbound (fun _ : Unit => hi.2)
    (prefix_all_failure (P := P) hG hm hsym n)
  simpa only [Fintype.sum_unique] using hh



lemma prefix_absolute_moment {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G : X × Ω → ℝ} {B : ℝ} (hm : Measurable G)
    (hi : ∀ x, Integrable (fun ω => G (x,ω)) p)
    (hB : ∀ x, (∫ ω, |G (x,ω)| ∂p) ≤ B) :
    Integrable G (P.prod p) ∧ (∫ w, |G w| ∂P.prod p) ≤ B := by
  have hnorm : Integrable (fun x => ∫ ω, ‖G (x,ω)‖ ∂p) P := by
    apply (integrable_const B).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using hB x
  have hGi : Integrable G (P.prod p) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall hi,hnorm⟩
  refine ⟨hGi,?_⟩
  rw [integral_prod _ hGi.abs]
  have hh := integral_mono hGi.abs.integral_prod_left (integrable_const B) hB
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh



lemma default_full_history_caps {n : ℕ} {m v δ : ℝ}
    (hv : 0 ≤ v) (hm : m^2 ≤ 64*v) (hδ : 0 < δ) (z w : Fin n → ℝ) :
    let a := fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
    let b := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
    let F := fun (M V : ℝ) (u : Fin n → ℝ) =>
      (M+∑ i,a i*u i)/(δ+Real.sqrt (V+∑ i,b i*(u i)^2))
    |F ((9/10 : ℝ)^n*m) ((999/1000 : ℝ)^n*v) z-
      F ((9/10 : ℝ)^n*m) ((999/1000 : ℝ)^n*v) w| ≤
        16*min 1 (Real.sqrt (∑ i,b i*(z i-w i)^2)/(δ+Real.sqrt (∑ i,b i*(w i)^2))) ∧
    |F ((9/10 : ℝ)^n*m) ((999/1000 : ℝ)^n*v) w-F 0 0 w| ≤
      16*min 1 (Real.sqrt ((999/1000 : ℝ)^n*v)/(δ+Real.sqrt (∑ i,b i*(w i)^2))) := by
  dsimp only
  let a := fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
  let b := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  have hR : 0 ≤ (999/1000 : ℝ)^n*v := mul_nonneg (by positivity) hv
  have hb (i : Fin n) : 0 < b i := by dsimp [b]; positivity
  have hwin (u : Fin n → ℝ) := default_finite_history_invariant hv hm n u
  constructor
  · exact weighted_history_offset_difference a b z w hR hδ hb (default_geometric_coeff n) (hwin z) (hwin w)
  · have hzero := default_finite_history_invariant (m := 0) (v := 0) (by norm_num) (by norm_num) n w
    simp only [mul_zero,zero_add] at hzero
    have hdec := decayed_momentum_bound hv hm (α := (9/10 : ℝ)) (β := (999/1000 : ℝ)) (by norm_num) n
    have hd : |((9/10 : ℝ)^n*m+∑ i,a i*w i)-(∑ i,a i*w i)| ≤
        8*Real.sqrt ((999/1000 : ℝ)^n*v) := by simpa only [add_sub_cancel_right] using hdec
    have hh := old_history_difference (v₀ := ∑ i,b i*(w i)^2)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i).le (sq_nonneg _))) hR hδ
      (by simpa only [add_comm] using hwin w) hzero hd
    simpa only [zero_add,add_comm] using hh



lemma default_prefix_full_history_tracking {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {n : ℕ}
    {G M V : X → ℝ} {noise : X → Ω → ℝ} {K : Ω → ℝ}
    {Z : Fin (n+1) → X × (Fin (n+1) → Ω) → ℝ}
    {d : Fin (n+1) → X × (Fin n → Ω) → ℝ} {L μ B δ : ℝ}
    (hG : Measurable G) (hM : Measurable M) (hV : Measurable V)
    (hV0 : ∀ x,0 ≤ V x) (hMV : ∀ x,(M x)^2 ≤ 64*V x)
    (hVi : Integrable (fun x => Real.sqrt ((999/1000 : ℝ)^(n+1)*V x)) P)
    (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    (hZ : ∀ i,Measurable (Z i)) (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hGB : ∀ x,|G x| ≤ B)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hμ : (∫ ω,K ω ∂p) ≤ μ)
    (hd : ∀ i,MemLp (d i) 2 (P.prod (Measure.pi (fun _ : Fin n => p))))
    (hd0 : ∀ i z,0 ≤ d i z)
    (herror : ∀ᵐ w ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p)),∀ i,
      |Z i w-(G w.1+noise w.1 (w.2 i))| ≤
        (L+K (w.2 i))*d i (w.1,fun j => w.2 (i.succAbove j))) :
    let a := fun i : Fin (n+1) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
    let b := fun i : Fin (n+1) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
    let W := fun i (w : X × (Fin (n+1) → Ω)) => G w.1+noise w.1 (w.2 i)
    let u := fun w : X × (Fin (n+1) → Ω) => |G w.1| *
      |((9/10 : ℝ)^(n+1)*M w.1+∑ i,a i*Z i w)/
        (δ+Real.sqrt ((999/1000 : ℝ)^(n+1)*V w.1+∑ i,b i*(Z i w)^2))-
        (∑ i,a i*W i w)/(δ+Real.sqrt (∑ i,b i*(W i w)^2))|
    Integrable u (P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ∧
      (∫ w,u w ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p))) ≤
        16*((L+μ)*127*(∑ i,Real.sqrt (b i)*Real.sqrt (∫ z,d i z^2 ∂P.prod (Measure.pi (fun _ : Fin n => p))))+
          B*((n+1)*(1/2 : ℝ)^n))+
        16*(127*(∫ x,Real.sqrt ((999/1000 : ℝ)^(n+1)*V x) ∂P)+B*(1/2 : ℝ)^(n+1)) := by
  classical
  dsimp only
  let Q := P.prod (Measure.pi (fun _ : Fin (n+1) => p))
  let a := fun i : Fin (n+1) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
  let b := fun i : Fin (n+1) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  let W := fun i (w : X × (Fin (n+1) → Ω)) => G w.1+noise w.1 (w.2 i)
  let F := fun (U : Fin (n+1) → X × (Fin (n+1) → Ω) → ℝ) (w : X × (Fin (n+1) → Ω)) =>
    ((9/10 : ℝ)^(n+1)*M w.1+∑ i,a i*U i w)/
      (δ+Real.sqrt ((999/1000 : ℝ)^(n+1)*V w.1+∑ i,b i*(U i w)^2))
  let H := fun w : X × (Fin (n+1) → Ω) => (∑ i,a i*W i w)/(δ+Real.sqrt (∑ i,b i*(W i w)^2))
  let E₁ := fun w => |F Z w-F W w|
  let E₂ := fun w => |F W w-H w|
  let u := fun w => |G w.1| * |F Z w-H w|
  have hW (i) : Measurable (W i) := (hG.comp measurable_fst).add
    (hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hF (U : Fin (n+1) → X × (Fin (n+1) → Ω) → ℝ) (hU : ∀ i,Measurable (U i)) : Measurable (F U) := by
    dsimp [F]
    fun_prop
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hE₁ : Measurable E₁ := by dsimp [E₁]; fun_prop
  have hE₂ : Measurable E₂ := by dsimp [E₂]; fun_prop
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hcaps (w : X × (Fin (n+1) → Ω)) := default_full_history_caps
    (hV0 w.1) (hMV w.1) hδ (fun i => Z i w) (fun i => W i w)
  have hfirst := default_prefix_capped_tracking hG hm hsym hE₁ (fun _ => abs_nonneg _) hL hB hδ hGB hK hK0 hμ hd hd0
    (Filter.Eventually.of_forall (fun w => (hcaps w).1)) herror
  have hsecond := prefix_old_history_capped_tracking hG hm hsym
    (by fun_prop : Measurable (fun x => Real.sqrt ((999/1000 : ℝ)^(n+1)*V x))) hVi
    (fun _ => Real.sqrt_nonneg _) hE₂ (fun _ => abs_nonneg _) hB hGB hδ
    (Filter.Eventually.of_forall (fun w => by simpa only [zero_add] using (hcaps w).2))
  have hi := hfirst.1.add hsecond.1
  have hbound (w : X × (Fin (n+1) → Ω)) : u w ≤ |G w.1| * E₁ w+|G w.1| * E₂ w := by
    have hh := mul_le_mul_of_nonneg_left (abs_sub_le (F Z w) (F W w) (H w)) (abs_nonneg (G w.1))
    simpa only [mul_add] using hh
  have hui : Integrable u Q := hi.mono' hu.aestronglyMeasurable (by
    filter_upwards [] with w
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hbound w)
  refine ⟨hui,?_⟩
  calc
    _ ≤ ∫ w,|G w.1| * E₁ w+|G w.1| * E₂ w ∂Q := integral_mono hui hi hbound
    _ = (∫ w,|G w.1| * E₁ w ∂Q)+(∫ w,|G w.1| * E₂ w ∂Q) := integral_add hfirst.1 hsecond.1
    _ ≤ _ := add_le_add hfirst.2 hsecond.2



lemma default_historyField_bound {n : ℕ} {δ g : ℝ} (hδ : 0 < δ) (z : Fin n → ℝ) :
    |historyField δ
      (fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
      (fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)) g z| ≤ 8 := by
  have hi := default_finite_history_invariant (m := 0) (v := 0) (by norm_num) (by norm_num) n (fun i => g+z i)
  simp only [mul_zero,zero_add] at hi
  have hv : 0 ≤ ∑ i : Fin n,(1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(g+z i)^2 := by positivity
  exact normalized_value_bound (Real.sqrt_nonneg _) hδ (by norm_num) (momentum_sqrt_bound hv hi)

lemma integral_default_noise_history_coercive {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {noise : Ω → ℝ} {n : ℕ} {δ g σ : ℝ}
    (hδ : 0 < δ) (hm : Measurable noise) (hi : Integrable noise p)
    (hsym : (p.map noise).map (fun z : ℝ => -z)=p.map noise)
    (hσ : (∫ ω,|noise ω| ∂p) ≤ σ) :
    let F := fun z : Fin (n+2) → Ω => historyField δ
      (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
      (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)) g (fun i => noise (z i))
    Integrable F (Measure.pi (fun _ : Fin (n+2) => p)) ∧
      g^2/(90*(δ+66*(|g|+σ))) ≤ g*(∫ z,F z ∂Measure.pi (fun _ : Fin (n+2) => p)) := by
  dsimp only
  let μ := p.map noise
  let Q := Measure.pi (fun _ : Fin (n+2) => μ)
  let P := Measure.pi (fun _ : Fin (n+2) => p)
  let T := fun z : Fin (n+2) → Ω => fun i => noise (z i)
  let F := historyField δ
    (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
    (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)) g
  have hFm : Measurable F := by
    change Measurable (fun z : Fin (n+2) → ℝ => F z)
    dsimp [F,historyField]
    fun_prop
  have hFi : Integrable F Q :=
    (show MemLp F 1 Q from MemLp.of_bound hFm.aestronglyMeasurable (8 : ℝ)
      (Filter.Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using default_historyField_bound hδ z))).integrable (by norm_num)
  have hμi : Integrable (fun z : ℝ => z) μ :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hm.aemeasurable).mpr hi
  have hμσ : (∫ z : ℝ,|z| ∂μ) ≤ σ := by
    rw [show μ=p.map noise from rfl,integral_map hm.aemeasurable (by fun_prop : AEStronglyMeasurable (fun z : ℝ => |z|) (p.map noise))]
    exact hσ
  have hh := integral_default_history_coercive (n := n) (g := g) hδ hsym hμi hμσ
  have hp : MeasurePreserving T P Q := measurePreserving_pi
    (fun _ : Fin (n+2) => p) (fun _ : Fin (n+2) => μ) (fun _ => ⟨hm,rfl⟩)
  have hFc := hp.integrable_comp_of_integrable hFi
  have he := integral_map hp.measurable.aemeasurable (f := F) (hp.map_eq.symm ▸ hFi.aestronglyMeasurable)
  simp only [hp.map_eq] at he
  refine ⟨hFc,?_⟩
  change g^2/(90*(δ+66*(|g|+σ))) ≤ g*(∫ z,F (T z) ∂P)
  rw [← he]
  exact hh


lemma prefix_default_history_coercive {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G S : X → ℝ} {noise : X → Ω → ℝ} {δ B : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hG : Measurable G) (hS : Measurable S)
    (hGB : ∀ x,|G x| ≤ B) (hm : Measurable (Function.uncurry noise))
    (hi : ∀ x,Integrable (noise x) p)
    (hsym : ∀ x,(p.map (noise x)).map (fun z : ℝ => -z)=p.map (noise x))
    (hSbound : ∀ x,(∫ ω,|noise x ω| ∂p) ≤ S x) :
    let H := fun w : X × (Fin (n+2) → Ω) => G w.1*historyField δ
      (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
      (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))
      (G w.1) (fun i => noise w.1 (w.2 i))
    Integrable H (P.prod (Measure.pi (fun _ : Fin (n+2) => p))) ∧
      Integrable (fun x => (G x)^2/(90*(δ+66*(|G x|+S x)))) P ∧
      (∫ x,(G x)^2/(90*(δ+66*(|G x|+S x))) ∂P) ≤
        ∫ w,H w ∂P.prod (Measure.pi (fun _ : Fin (n+2) => p)) := by
  dsimp only
  let Q := Measure.pi (fun _ : Fin (n+2) => p)
  let H := fun w : X × (Fin (n+2) → Ω) => G w.1*historyField δ
    (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
    (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))
    (G w.1) (fun i => noise w.1 (w.2 i))
  let φ := fun x => (G x)^2/(90*(δ+66*(|G x|+S x)))
  have hS0 (x) : 0 ≤ S x := (integral_nonneg (fun _ => abs_nonneg _)).trans (hSbound x)
  have hn (i : Fin (n+2)) : Measurable (fun w : X × (Fin (n+2) → Ω) => noise w.1 (w.2 i)) :=
    hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hHm : Measurable H := by dsimp [H,historyField]; fun_prop
  have hHbound (w) : ‖H w‖ ≤ B*8 := by
    rw [Real.norm_eq_abs]
    dsimp [H]
    rw [abs_mul]
    exact mul_le_mul (hGB w.1) (default_historyField_bound hδ _) (abs_nonneg _) hB
  have hHi : Integrable H (P.prod Q) :=
    (show MemLp H 1 (P.prod Q) from MemLp.of_bound hHm.aestronglyMeasurable (B*8)
      (Filter.Eventually.of_forall hHbound)).integrable (by norm_num)
  have hφm : Measurable φ := by dsimp [φ]; fun_prop
  have hφ0 (x) : 0 ≤ φ x := by
    have hs0 := hS0 x
    dsimp [φ]
    positivity
  have hφbound (x) : φ x ≤ B^2/(90*δ) := by
    have hden : 0 < 90*(δ+66*(|G x|+S x)) := by
      have hs0 := hS0 x
      positivity
    have hsq : (G x)^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hGB x)
    exact (div_le_div_of_nonneg_right hsq hden.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg B) (by positivity) (by nlinarith [hS0 x,abs_nonneg (G x)]))
  have hφi : Integrable φ P :=
    (show MemLp φ 1 P from MemLp.of_bound hφm.aestronglyMeasurable (B^2/(90*δ))
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hφ0 x)] using hφbound x)).integrable (by norm_num)
  refine ⟨hHi,hφi,?_⟩
  rw [integral_prod _ hHi]
  apply integral_mono hφi hHi.integral_prod_left
  intro x
  have hh := integral_default_noise_history_coercive (n := n) (g := G x) hδ
    (hm.comp measurable_prodMk_left) (hi x) (hsym x) (hSbound x)
  change φ x ≤ ∫ z,G x*historyField δ _ _ (G x) (fun i => noise x (z i)) ∂Q
  rw [integral_const_mul]
  exact hh.2


end LongTails.Proofs.AdaptiveHistoryTracking
